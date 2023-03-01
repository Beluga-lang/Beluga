open Support
open Format
open Beluga

module LF = Syntax.Int.LF

module P = Pretty.Int.DefaultPrinter

module Options = struct
  let emacs = ref false
  let interrupt_count = ref 0
end

exception Invalid_Arg

let process_option arg : unit = match arg with
  | "-emacs" ->
     Options.emacs := true;
     Chatter.level := 0
  | _ ->
     raise Invalid_Arg

let rec process_options = function
  | [] -> []
  | arg :: rest ->
    let first = String.get arg 0 in
    if first = '-' || first = '+' then
      (process_option arg; process_options rest)
    else
      (* reached end of options: return this and remaining arguments *)
      arg :: rest

let init_repl ppf =
  fprintf ppf "        Beluga (interactive) version %s@.@.%s"
    (Version.get ())
    Interactive.whale

let rec loop ppf =
  begin
    try
      if Bool.not !Options.emacs then fprintf ppf "# @?";
      let input = read_line () in
      match Command.is_command input with
      | `Cmd cmd ->
         Command.do_command ppf cmd
      | `Input input when input <> "" ->
         let _location = Beluga_syntax.Location.initial "<interactive>" in
         let (exp, tau) =
           Obj.magic () (* TODO: Parse only a computation-level expression from [input] at [_location] *)
           |> Interactive.elaborate_exp' LF.Empty LF.Empty
           |> Pair.map_right Whnf.cnormCTyp
         in
         fprintf ppf "%a : %a"
           (P.fmt_ppr_cmp_exp LF.Empty LF.Empty P.l0) exp
           (P.fmt_ppr_cmp_typ LF.Empty P.l0) tau
      | `Input _ -> ()
    with
      | End_of_file -> exit 0
      | Sys.Break ->
          if !Options.interrupt_count = 2 then begin fprintf ppf "@\n@."; exit 0 end else begin
          incr Options.interrupt_count;
          fprintf ppf "Interrupted (press %d more times to quit).@." (3 - !Options.interrupt_count) end
      | err ->
        output_string stderr (Printexc.to_string err);
        flush stderr
  end;
  loop ppf

let run args =
  let ppf = Format.std_formatter in
  let files = process_options args in
  Debug.init (Some "debug.out");

  if List.length files = 1 then
    try
      let arg = List.hd files in
      let _location = Beluga_syntax.Location.initial arg in
      let[@warning "-26"] sgn = Obj.magic () (* TODO: Parse only a signature from the file [arg] *) in
      let sgn' = Obj.magic () (* TODO: Reconstruct [sgn] and raise on leftover variables *) in
      Chatter.print 1 (fun ppf -> Format.fprintf ppf "%a" P.fmt_ppr_sgn sgn');
      fprintf ppf "The file has been successfully loaded.\n"
    with
    |Failure _ -> fprintf ppf "Please provide the file name\n" ;
  else begin if List.length files > 1 then fprintf ppf "Please supply only 1 file" end;

  if Bool.not !Options.emacs then
    begin
      init_repl ppf;
      Command.print_usage ppf
    end;

  Sys.catch_break true;
  loop ppf
