open Support
open Beluga
open Beluga_syntax
module LF = Syntax.Int.LF
module P = Prettyint.DefaultPrinter

exception Too_many_input_files

exception Invalid_argument

let () =
  Error.register_exception_printer (function
    | Too_many_input_files -> Format.dprintf "Please supply only 1 file."
    | cause -> Error.raise_unsupported_exception_printing cause)

module Options = struct
  let emacs = ref false

  let interrupt_count = ref 0
end

let process_option arg : unit =
  match arg with
  | "-emacs" ->
      Options.emacs := true;
      Chatter.level := 0
  | _ -> Error.raise_notrace Invalid_argument

let is_option arg =
  let first = String.get arg 0 in
  first = '-' || first = '+'

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      if is_option arg then (
        process_option arg;
        process_options rest)
      else
        (* reached end of options: return this and remaining arguments *)
        arg :: rest

let rec loop state =
  step state;
  loop state

and step state =
  try
    if Bool.not !Options.emacs then Command.fprintf state "# @?";
    let input = read_line () in
    Command.interpret_command state ~input
  with
  | End_of_file -> exit 0
  | Sys.Break ->
      if !Options.interrupt_count = 2 then (
        Command.fprintf state "@\n@\n";
        exit 0)
      else (
        incr Options.interrupt_count;
        Command.fprintf state "Interrupted (press %d more times to quit).@\n"
          (3 - !Options.interrupt_count))

let init_repl state =
  Command.fprintf state "        Beluga (interactive) version %s@\n@\n%s"
    (Version.get ()) Interactive.whale

let run args =
  let state = Command.create_initial_state () in
  let files = process_options args in

  if Debug.is_enabled () then Debug.init (Option.some "debug.out");

  (match files with
  | _ :: _ :: _ -> Error.raise Too_many_input_files
  | [] -> ()
  | [ filename ] ->
      let sgn' = Command.load state ~filename in
      Chatter.print 1 (fun ppf -> Format.fprintf ppf "%a" P.fmt_ppr_sgn sgn');
      Command.fprintf state "The file has been successfully loaded.\n");

  if Bool.not !Options.emacs then (
    init_repl state;
    Command.print_usage state);

  Sys.catch_break true;
  loop state
