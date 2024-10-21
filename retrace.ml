open Printf
open ExtLib
open Devkit

module U = ExtUnix.Specific

(* TODO cli option *)
module Config = struct

type show_cmd = Basename | Full | Cmd | Short | Pretty

let show_cmd = Pretty

end

type pid = int
type event = Exit | Exec of string * string list | Spawn of pid
type entry = { first : Time.t; pid : pid; mutable events : (Time.t * event) list; }
type pids = { pids : (pid,entry) Hashtbl.t; last_event : Time.t }

type line =
| Detached
| Signal of string
| Event of string
| Unfinished of string
| Syscall of string * string * string
| Failed of { line : string; reason : string }

let of_time s =
  let (time,frac) = Stre.splitc s '.' in
  U.timegm (U.strptime "%H:%M:%S" time) +. float_of_string ("." ^ frac)

let unquote s = try Scanf.sscanf s "%S%!" Fun.id with _ -> s

let discard_duration s = if String.ends_with s ">" then fst @@ Stre.rsplitc s ' ' else s

(* can be translated *)
let discard_error_description s = if String.ends_with s ")" then String.trim @@ fst @@ Stre.rsplitc s '(' else s

let cleanup s = discard_error_description @@ discard_duration s

let sh_quote s = try Scanf.sscanf s "%_[a-zA-Z0-9_.,:/=-]%!" (); s with _ -> Filename.quote s

let show_line (pid,_time,line) =
  sprintf "pid=%d " pid ^
  match line with
  | Detached -> sprintf "detached"
  | Signal rest -> sprintf "signal %s" rest
  | Event rest -> sprintf "event %s" rest
  | Unfinished name -> sprintf "unfinished %s" name
  | Syscall (name,args,ret) -> sprintf "syscall %s (%s) => %s" name args ret
  | Failed {line;reason} -> sprintf "FAILED(%s) %s" reason line

let to_spawn_event event =
  match event with
  | Signal _ -> None
  | Unfinished _ -> None
  | Event s when String.starts_with s "exited " -> Some Exit
  | Syscall ("execve",_,"-1 ENOENT")
  | Syscall (_,_,"? ERESTARTNOINTR") -> None
  | Syscall ("execve",args,_) ->
    let (cmd,rest) = String.split args  ", [" in (* naive *)
    let (args,_) = String.split rest "], " in
    let args = List.map unquote @@ String.nsplit args ", " in
    Some (Exec (unquote cmd, List.tl args))
  | Syscall (("clone"|"clone3"|"vfork"|"fork"), _args, ret) -> Some (Spawn (atoi "spawn pid" ret))
  | _ -> None

let compute_runtimes pids =
  (* unfinished pids ignored *)
  pids |> Seq.filter_map (fun ({ first; events; _ } as p) ->
    match List.find_opt (function (_,Exit) -> true | _ -> false) events with None -> None
      | Some (exit,_) -> Some (p, exit -. first))

module ARGS = struct
  let rec arg a = function
  | [] -> []
  | a'::v::_ when String.equal a a' -> [a;v]
  | _::xs -> arg a xs

  let rec last = function [] -> [] | [x] -> [x] | _::xs -> last xs

  let filter =
    let rec loop ~a acc = function
    | [] -> []
    | x::xs when List.mem x a -> loop ~a (x::acc) xs
    | _::xs -> loop ~a acc xs
  in
  loop []

end

let show_skipped cmd ~orig args =
  match args with
  | [] -> cmd
  | _ when List.length orig = List.length args -> String.concat " " (cmd :: args)
  | l -> String.concat " " (cmd :: "..." :: l)

let show_cmd cmd args =
  match Config.show_cmd with
  | Basename -> Filename.basename cmd
  | Cmd -> cmd
  | Full -> String.concat " " (cmd :: List.map sh_quote args)
  | Short | Pretty as t ->
    let cmd = if t = Pretty then Filename.basename cmd else cmd in
    let quoted_full = String.concat " " (cmd :: List.map sh_quote args) in
    match String.length quoted_full < 100 with
    | true -> quoted_full
    | false ->
      let selected_args =
        let open ARGS in
        match Filename.basename cmd with
        | "ppx.exe" -> arg "-o" args
        | "atdgen" -> filter ~a:["-t";"-j"] args @ last args (* not completely correct *)
        | _ -> match last args with ["..."] (* TODO detect strace truncate earlier * ) *) -> arg "-o" args | l -> l
      in
      if List.length args = List.length selected_args then
        quoted_full
      else
        String.concat " " (cmd :: "..." :: List.map sh_quote selected_args)

let get_cmd pid = List.find_map_opt (function _, Exec (cmd,args) -> Some (show_cmd cmd args) | _ -> None) pid.events

let print_runtimes ~all pids =
  Hashtbl.to_seq_values pids.pids
  |> compute_runtimes
  |> Seq.filter (fun (_,t) -> t > 0.) (* filter out zero run-time - usually threads (no fork = no time) TODO detect better *)
  |> Seq.filter_map (fun (p,t) ->
    match all, get_cmd p with
    | _, Some s -> Some (t,s)
    | true, None -> Some (t,sprintf "<pid %d>" p.pid)
    | false, None -> None)
  |> List.of_seq
  |> List.sort ~cmp:(fun (_,a) (_,b) -> String.compare b a)
  |> List.enum
  |> ExtEnum.group
      (fun (_,_,a) (_,b) -> String.equal a b)
      (fun (x,n,_) (y,k) -> x+.y,n+1,k)
      (0.,0,"")
  |> List.of_enum
  |> List.sort ~cmp:(fun (a,_,_) (b,_,_) -> Float.compare b a)
  |> List.iter begin fun (t,n,cmd) ->
    printfn "%s %d %s" (Time.compact_duration t) n cmd
  end

let indent n = if n > 0 then print_string (String.make ((n-1)*2) ' ' ^ "↳ ")

let print_cmd cmd args = print_endline @@ show_cmd cmd args

let cmd_duration pids t rest =
  let until = List.find_map (function (_,Spawn _) -> None | (t, (Exec _| Exit)) -> Some t) rest in
  Option.default pids.last_event until -. t

let iter_exec pids k =
  let module S = Set.Make(struct type t = entry let compare a b = if a.pid = b.pid then 0 else compare (a.first,a.pid) (b.first,b.pid) end) in
  let rec visit parents set p =
    let rec loop set = function
    | (_t, Spawn pid) :: rest ->
       begin match Hashtbl.find_opt pids.pids pid with
       | None -> Exn.fail "pid %d not found" pid
       | Some x -> loop (visit (p.pid::parents) set x) rest
       end
    | (t, Exec (cmd,args)) :: rest ->
      k t p.pid parents (cmd_duration pids t rest) cmd args;
      loop set rest
    | (_,Exit)::[] | [] -> set
    | (_,Exit)::_ -> Exn.fail "unexpected events after Exit for pid %d" p.pid
    (* | [] -> Exn.fail "no exit for %d" p.pid *)
    in
    loop (S.remove p set) p.events
  in
  let rec loop set =
    match S.min_elt_opt set with
    | None -> ()
    | Some p -> loop @@ visit [] set p
  in
  pids.pids |> Hashtbl.to_seq_values |> S.of_seq |> loop

let print_tree pids = iter_exec pids (fun _ _ parents _ cmd args -> indent (List.length parents + 1); print_cmd cmd args)

let print_exec pids =
  print_endline @@ String.concat "\t" ["time";"parent";"pid";"duration";"cmd"];
  iter_exec pids begin fun t pid parents duration cmd args ->
  	let parent = match parents with p::_ -> p | [] -> 0 in
   	printfn "%.3f\t%d\t%d\t%.3f\t%s" t parent pid duration (show_cmd cmd args);
  end

let print_parallelism pids =
  let spans = ref [] in
  iter_exec pids (fun t _ _ duration _ _ -> tuck spans (t,duration));
  let timeline = Array.create (1 + (int_of_float @@ ceil pids.last_event)) 0 in
  !spans |> List.iter begin fun (t,duration) ->
  	for i = int_of_float t to int_of_float @@ ceil (t +. duration) do
    	timeline.(i) <- timeline.(i) + 1
    done
  end;
  timeline |> Array.iteri (fun i n -> printfn "%d\t%d\t%s" i n (String.make n '#'))

let parse_line () =
  let unfinished = Hashtbl.create 10 in
  fun line ->
  try
    let (pid,s) = Stre.dividec line ' ' in
    let (time,s) = Stre.dividec (String.trim s) ' ' in
    let pid = atoi "caller pid" pid in
    let time = of_time time in
    let line =
      if String.ends_with s "<detached ...>" then
        Detached
      else
      match%pcre s with
      | {|^--- SIG(?<rest>.*)$|} -> Signal rest
      | {|^\+\+\+ (?<rest>.*)$|} -> Event rest
      | {|^<\.\.\. (?<name>[^ ]+) resumed>(?<rest>.*)$|} ->
        begin match CCString.Split.right (cleanup rest) ~by:" = " with
        | None -> Failed { line; reason = "bad resumed" }
        | Some (args,ret) ->
          match Hashtbl.find_opt unfinished pid with
          | None -> Failed { line; reason = "unexpected resumed" }
          | Some (n,_) when n <> name -> Failed { line; reason = "resumed didn't match, expected " ^ n }
          | Some (_,a) -> Syscall (name, a ^ args, ret)
        end
      | {|^(?<name>[^(]+)\((?<rest>.*)$|} ->
        begin match CCString.Split.right rest ~by:" <" with
        | Some (s, "unfinished ...>") -> (* TODO check state *) Hashtbl.replace unfinished pid (name,s); Unfinished name
        | _ ->
          match CCString.Split.right (cleanup rest) ~by:" = " with
          | None -> Failed { line; reason = "bad return" }
          | Some (args,ret) -> Syscall (name, args, ret)
        end
      | _ -> Failed { line; reason = "unknown line" }
    in
    (pid,time,line)
  with exn -> Exn.fail ~exn "failed to parse line %s" line

let input_lines cin =
  let rec aux () =
    match input_line cin with
    | exception End_of_file -> Seq.Nil
    | s -> Cons (s,aux)
  in
  aux

let input_events cin =
  let parse_line = parse_line () in
  input_lines cin |> Seq.map parse_line

let process_event pids (pid,time,event) =
  (* always create entry for pid *)
  let entry =
    match Hashtbl.find_option pids pid with
    | None -> let entry = { first = time; pid; events = [] } in Hashtbl.add pids pid entry; entry
    | Some e -> e
  in
  match to_spawn_event event with
  | None -> ()
  | Some ev -> entry.events <- (time, ev) :: entry.events

let parse_in cin =
  let h = Hashtbl.create 10 in
  input_events cin |> Seq.iter (process_event h);
  let first_event = Hashtbl.fold (fun _ { first; _; } acc -> min acc first) h 0. in
  if Hashtbl.length h = 0 then exit 1;
  let last = ref first_event in
  h |> Hashtbl.iter (fun _ v -> v.events <- List.rev_map (fun (time,x) -> let t = time -. first_event in last := max t !last; t,x) v.events);
  eprintfn "total %d %8.3fs" (Hashtbl.length h) !last;
  { pids = h; last_event = !last }

let main () =
  match Nix.args with
  | [] | ["time"] -> print_runtimes ~all:false @@ parse_in stdin
  | ["alltime"] -> print_runtimes ~all:true @@ parse_in stdin
  | ["tree"] -> print_tree @@ parse_in stdin
  | ["exec"] -> print_exec @@ parse_in stdin
  | ["parallelism"] -> print_parallelism @@ parse_in stdin
  | ["parse"] -> input_events stdin |> Seq.map show_line |> Seq.iter print_endline
  | _ -> prerr_endline "Available commands : exec, time, alltime, tree"

let () = main ()
