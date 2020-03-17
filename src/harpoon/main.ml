(** Harpoon

@author Jacob Thomas Errington
@author Clare Jang
@author Marcel Goh

Harpoon is an interactive mode for Beluga that uses a small set of
tactics for elaborating proofs.
 *)

module B = Beluga

let realMain () =
  B.Debug.init (Some "debug.out");
  let (arg0 :: args) = Array.to_list Sys.argv in
  let open Options in
  let options = parse_arguments args |> elaborate in

  let ppf = Format.std_formatter in
  let stubs =
    if options.load_holes then
      B.Holes.get_harpoon_subgoals ()
      |> List.map snd
    else
      []
  in
  let io =
    IO.make (InputPrompt.make options.test_file options.test_start) ppf
  in
  REPL.start
    options.save_back
    options.test_stop
    options.path
    options.all_paths
    stubs
    io

let main () =
  try
    realMain ()
  with
  | e ->
     print_string (Printexc.to_string e);
     exit 1

let _ =
  main ()
