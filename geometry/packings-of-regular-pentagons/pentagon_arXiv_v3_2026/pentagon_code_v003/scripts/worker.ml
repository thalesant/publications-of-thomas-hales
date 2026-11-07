(* Isolated OCaml bytecode worker. The Python driver selects the job by
   environment variable; no source text is interpolated into expressions. *)
#directory "+compiler-libs";;
let () =
  Printexc.record_backtrace true;
  try
    let root = Sys.getenv "PENTAGON_ROOT" in
    let load p =
      if not (Toploop.use_file Format.err_formatter (Filename.concat root p)) then
        failwith ("Failed to load " ^ p)
    in
    load "ocaml/loader.ml"
  with exn ->
    Printf.eprintf "PENTAGON SETUP ERROR: %s\n%s\n%!"
      (Printexc.to_string exn) (Printexc.get_backtrace()); exit 1;;
open Stdlib;;
let () = pentagon_load_relative "tests/ocaml/squeeze_tests.ml";;
open Pent;;
let () =
  pentagon_load_relative "tests/ocaml/tests.ml";
  pentagon_load_relative "ocaml/jobs.ml";;
let () =
  let open Stdlib in
  try
    let job = Sys.getenv "PENTAGON_JOB" in
    let started = Sys.time () in
    let before = !(Interval.sqrt_domain_error_count) in
    Printf.printf "PENTAGON JOB START: %s\n%!" job;
    List.iter (fun (key,label) -> match Sys.getenv_opt key with
      | Some text -> Printf.printf "%s: %s\n%!" label text
      | None -> ())
      [("PENTAGON_DESCRIPTION","Calculation"); ("PENTAGON_CLAIMS","Paper");
       ("PENTAGON_COMMENT_CODES","Source navigation")];
    pentagon_dispatch job;
    pentagon_assert_unchanged ();
    if (Gc.get()).Gc.stack_limit <> 16777216 then failwith "Stack setting changed";
    Printf.printf "CPU seconds: %.6f\n" (Sys.time () -. started);
    Printf.printf "Square-root translations during job: %d\n" (!(Interval.sqrt_domain_error_count)-before);
    Printf.printf "PENTAGON STACK RETAINED: 16777216\n";
    Printf.printf "PENTAGON JOB PASS: %s\n%!" job
  with exn ->
    Printf.eprintf "PENTAGON JOB ERROR: %s\n%s\n%!"
      (Printexc.to_string exn) (Printexc.get_backtrace()); exit 1;;
