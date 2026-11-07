(* Explicit definition-only loader. Run through scripts/worker.ml.
   Fail closed: a failed #use never becomes a successful load record.
   No mathematical searches run while definitions are loaded. *)
#use "topfind";;
#require "interval.top";;
#directory "+compiler-libs";;

let pentagon_root =
  try Sys.getenv "PENTAGON_ROOT"
  with Not_found -> failwith "Use python3 run.py; PENTAGON_ROOT is not set.";;
let pentagon_loaded = Hashtbl.create 17;;
let pentagon_load_relative name =
  let path = Filename.concat pentagon_root name in
  if Hashtbl.mem pentagon_loaded name then
    failwith ("Duplicate load: " ^ name);
  if not (Sys.file_exists path) then failwith ("Missing source: " ^ path);
  if not (Toploop.use_file Format.err_formatter path) then
    failwith ("Source load failed: " ^ name);
  Hashtbl.add pentagon_loaded name (Digest.file path);;
let needs name =
  let rel = "ocaml/" ^ name in
  if not (Hashtbl.mem pentagon_loaded rel) then
    failwith ("Undeclared dependency: " ^ name);
  if Hashtbl.find pentagon_loaded rel <>
     Digest.file (Filename.concat pentagon_root rel) then
    failwith ("Source changed after loading: " ^ name);;
let reneeds = needs;;
let pentagon_assert_unchanged () =
  Hashtbl.iter (fun name before ->
    if Digest.file (Filename.concat pentagon_root name) <> before then
      failwith ("Source changed during job: " ^ name)) pentagon_loaded;;

let () =
  Printexc.record_backtrace true;
  Sys.catch_break true;
  Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };
  if (Gc.get()).Gc.stack_limit <> 16777216 then failwith "Wrong bytecode stack limit";
  Printf.printf "PENTAGON RUNTIME: OCaml %s; stack=16777216 words; CRlibm\n%!" Sys.ocaml_version;;
let () = pentagon_load_relative "ocaml/lib.ml";;
open Lib;;
let () = pentagon_load_relative "ocaml/interval_compat.ml";;
open Interval;;
exception Unstable;;
exception Fatal;;
let calcs : (string * (unit -> int * bool)) list ref = ref [];;
let mkcalc (name,f) =
  if List.mem_assoc name !calcs then failwith ("Duplicate calculation: " ^ name);
  calcs := (name,f) :: !calcs;;
let () = pentagon_load_relative "ocaml/pent.ml";;
open Pent;;
let () = pentagon_load_relative "ocaml/pet.ml";;
let () = pentagon_load_relative "ocaml/banana.ml";;
let () = pentagon_load_relative "ocaml/dimer.ml";;
let () = pentagon_load_relative "ocaml/autodiff.ml";;
let () = pentagon_load_relative "ocaml/meet-in-middle.ml";;
let () = pentagon_load_relative "ocaml/mitm-calcs.ml";;

(* Contact-sign geometry uses its own qualified interval operators. *)
open Stdlib;;
let () = pentagon_load_relative "ocaml/squeeze_sign.ml";;
open Pent;;
