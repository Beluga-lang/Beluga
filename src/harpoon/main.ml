(** Harpoon

    Harpoon is an interactive mode for Beluga that uses a small set of
    tactics for elaborating proofs.

    @author Jacob Thomas Errington
    @author Clare Jang
    @author Marcel Goh *)

open Support
module B = Beluga
open Harpoon

let realMain () =
  let (arg0 :: args) = Array.to_list Sys.argv in
  let open Options in
  let options = parse_arguments args in

  if Debug.is_enabled () then Debug.init (Option.some "debug.out");

  let open B in
  let all_paths, sgn' = Load.load_fresh options.path in

  let disambiguation_states, last_disambiguation_state =
    Revisit.revisit_disambiguation sgn'
  in
  let indexing_states, last_indexing_state = Revisit.revisit_indexing sgn' in

  let ppf = Format.std_formatter in
  let stubs =
    if options.load_holes then B.Holes.get_harpoon_subgoals () else []
  in
  let io =
    IO.make (InputPrompt.make options.test_file options.test_start) ppf
  in
  REPL.start
    (disambiguation_states, last_disambiguation_state)
    (indexing_states, last_indexing_state)
    options.save_back options.test_stop options.path all_paths stubs io

let main () =
  try realMain () with
  | e ->
      prerr_string (Printexc.to_string e);
      exit 1

let () = main ()
