open Printf
open ExtLib
open Devkit

module U = ExtUnix.Specific

(* TODO cli option *)
module Config = struct

let debug = false

type show_cmd = Basename | Full | Cmd | Short | Pretty

let show_cmd = Pretty

end

type pid = int
type event = Exit | Exec of string * string list | Spawn of pid
type entry = { first : Time.t; pid : pid; mutable events : (Time.t * event) list; }

let of_time s =
  let (time,frac) = Stre.splitc s '.' in
  U.timegm (U.strptime "%H:%M:%S" time) +. float_of_string ("." ^ frac)

let unquote s = try Scanf.sscanf s "%S%!" Fun.id with _ -> s

let discard_duration s = if String.ends_with s ">" then fst @@ Stre.rsplitc s ' ' else s

(* can be translated *)
let discard_error_description s = if String.ends_with s ")" then String.trim @@ fst @@ Stre.rsplitc s '(' else s

let sh_quote s = try Scanf.sscanf s "%_[a-zA-Z0-9_.,:/=-]%!" (); s with _ -> Filename.quote s

let parse s =
  let cleanup s = discard_error_description @@ discard_duration s in
  let spawn s =
    let s = cleanup s in
    match String.ends_with s " = ? ERESTARTNOINTR" with
    | true -> None
    | false ->
    let pid = atoi "spawn pid" @@ snd @@ Stre.rsplitc (discard_duration s) ' ' in
    Some (Spawn pid)
  in
  [
    "--- SIG", (fun _ -> None);
    "+++ exited ", (fun _ -> Some Exit);
    "execve(", begin fun s ->
      let s = cleanup s in
      match String.ends_with s " = -1 ENOENT" with
      | true -> None
      | false ->
      let (cmd,rest) = String.split s  ", [" in (* naive *)
      let (args,_) = String.split rest "], " in
      let args = List.map unquote @@ String.nsplit args ", " in
      Some (Exec (unquote cmd, List.tl args))
    end;
    "clone3(", begin fun s -> if String.ends_with s " <unfinished ...>" then None else spawn s end;
    "<... clone3 resumed>) ", spawn;
    "<... vfork resumed>) ", spawn;
  ] |> List.find_map begin fun (pre,f) ->
(*     if String.starts_with s pre then (printfn "got %S" s; f @@ Stre.drop_prefix s pre) else (printfn "NOT %S" s; None) *)
    if String.starts_with s pre then f @@ Stre.drop_prefix s pre else None
  end
  |> (fun r -> if Config.debug && r = None then eprintfn "skipping %S" s; r)

let process pids pid time event =
  let entry =
    match Hashtbl.find_option pids pid with
    | None -> let entry = { first = time; pid; events = [] } in Hashtbl.add pids pid entry; entry
    | Some e -> e
  in
  match event with
  | None -> ()
  | Some ev -> entry.events <- (time, ev) :: entry.events

let parse_line pids s' =
  try
    let (pid,s) = Stre.dividec s' ' ' in
    let (time,s) = Stre.dividec (String.trim s) ' ' in
    process pids (atoi "caller pid" pid) (of_time time) (parse s)
  with
    exn -> eprintfn "E: failed to parse line %S : %s" s' (Printexc.to_string exn)

let compute_runtimes pids =
  (* unfinished pids ignored *)
  pids |> Seq.filter_map (fun ({ first; events; _ } as p) ->
    match List.find_opt (function (_,Exit) -> true | _ -> false) events with None -> None
      | Some (exit,_) -> Some (p, exit -. first))

let show_skipped cmd args =
  match args with
  | [] -> cmd
  | l -> String.concat " " (cmd :: "..." :: l)


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

let show_cmd cmd args =
  match Config.show_cmd with
  | Basename -> Filename.basename cmd
  | Cmd -> cmd
  | Full -> String.concat " " (cmd :: List.map sh_quote args)
  | Short | Pretty as t ->
    let args =
      let open ARGS in
      match Filename.basename cmd with
      | "ppx.exe" -> arg "-o" args
      | "atdgen" -> filter ~a:["-t";"-j"] args @ last args (* not completely correct *)
      | _ -> last args
    in
    let cmd = if t = Pretty then Filename.basename cmd else cmd in
    show_skipped cmd (List.map sh_quote args)

let get_cmd pid = List.find_map_opt (function _, Exec (cmd,args) -> Some (show_cmd cmd args) | _ -> None) pid.events

let print_runtimes ~all pids =
  Hashtbl.to_seq_values pids
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

let print_exec ~tree pids =
  let module S = Set.Make(struct type t = entry let compare a b = if a.pid = b.pid then 0 else compare (a.first,a.pid) (b.first,b.pid) end) in
  let rec visit depth set p =
    let set = S.remove p set in
    List.fold_left (fun set (_t,e) ->
      match e with
      | Spawn pid -> visit (depth + 1) set (Hashtbl.find pids pid)
      | Exec (cmd,args) -> if tree then indent depth; print_cmd cmd args; set
      | _ -> set
    ) set (List.rev p.events)
  in
  let rec loop depth set =
    match S.min_elt_opt set with
    | None -> ()
    | Some p -> loop depth @@ visit depth set p
  in
  pids |> Hashtbl.to_seq_values |> S.of_seq |> loop 0

let main () =
  let pids = Hashtbl.create 10 in
  let rec loop () =
    match input_line stdin with
    | exception End_of_file -> ()
    | s -> parse_line pids s; loop ()
  in
  loop ();
  if Hashtbl.length pids = 0 then exit 1;
  printfn "%d" (Hashtbl.length pids);
  match Nix.args with
  | [] | ["time"] -> print_runtimes ~all:false pids
  | ["alltime"] -> print_runtimes ~all:true pids
  | ["tree"] -> print_exec ~tree:true pids
  | ["exec"] -> print_exec ~tree:false pids
  | _ -> prerr_endline "Available commands : exec, time, alltime, tree"

let () = main ()
