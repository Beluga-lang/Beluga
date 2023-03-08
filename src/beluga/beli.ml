open Support
open Beluga
open Beluga_syntax
module LF = Syntax.Int.LF
module P = Pretty.Int.DefaultPrinter

module Options = struct
  let emacs = ref false

  let interrupt_count = ref 0
end

exception Invalid_Arg

let process_option arg : unit =
  match arg with
  | "-emacs" ->
      Options.emacs := true;
      Chatter.level := 0
  | _ -> raise Invalid_Arg

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      let first = String.get arg 0 in
      if first = '-' || first = '+' then (
        process_option arg;
        process_options rest)
      else
        (* reached end of options: return this and remaining arguments *)
        arg :: rest

let init_repl ppf =
  Format.fprintf ppf "        Beluga (interactive) version %s@\n@\n%s"
    (Version.get ()) Interactive.whale

let rec loop ppf =
  (try
     if Bool.not !Options.emacs then Format.fprintf ppf "# @?";
     let input = read_line () in
     match Command.is_command input with
     | `Cmd cmd -> Command.do_command ppf cmd
     | `Input input when input <> "" ->
         let _location = Beluga_syntax.Location.initial "<interactive>" in
         let exp, tau =
           Obj.magic ()
           (* TODO: Parse only a computation-level expression from [input] at
              [_location] *)
           |> Interactive.elaborate_exp' LF.Empty LF.Empty
           |> Pair.map_right Whnf.cnormCTyp
         in
         Format.fprintf ppf "%a : %a"
           (P.fmt_ppr_cmp_exp LF.Empty LF.Empty P.l0)
           exp
           (P.fmt_ppr_cmp_typ LF.Empty P.l0)
           tau
     | `Input _ -> ()
   with
  | End_of_file -> exit 0
  | Sys.Break ->
      if !Options.interrupt_count = 2 then (
        Format.fprintf ppf "@\n@.";
        exit 0)
      else (
        incr Options.interrupt_count;
        Format.fprintf ppf "Interrupted (press %d more times to quit).@."
          (3 - !Options.interrupt_count)));
  loop ppf

exception Missing_input_file

exception Too_many_input_files

let run args =
  let ppf = Format.std_formatter in
  let files = process_options args in
  Debug.init (Option.some "debug.out");

  match files with
  | [] -> Error.raise Missing_input_file
  | _ :: _ :: _ -> Error.raise Too_many_input_files
  | [ arg ] ->
      let _location = Beluga_syntax.Location.initial arg in
      let[@warning "-26"] sgn =
        Obj.magic () (* TODO: Parse only a signature from the file [arg] *)
      in
      let sgn' =
        Obj.magic
          () (* TODO: Reconstruct [sgn] and raise on leftover variables *)
      in
      Chatter.print 1 (fun ppf -> Format.fprintf ppf "%a" P.fmt_ppr_sgn sgn');
      Format.fprintf ppf "The file has been successfully loaded.\n";

      if Bool.not !Options.emacs then (
        init_repl ppf;
        Command.print_usage ppf);

      Sys.catch_break true;
      loop ppf

let () =
  Error.register_exception_printer (function
    | Missing_input_file -> Format.dprintf "Please provide the file name."
    | Too_many_input_files -> Format.dprintf "Please supply only 1 file."
    | cause -> Error.raise_unsupported_exception_printing cause)
