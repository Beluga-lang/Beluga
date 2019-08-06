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
     Options.emacs := true; Debug.chatter := 0
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
      if not !Options.emacs then fprintf ppf "# @?";
      let input = read_line () in
      match Command.is_command input with
      | `Cmd cmd ->
         Command.do_command ppf cmd
      | `Input input when input <> "" ->
         let (exp, tau) =
           Runparser.parse_string "<interactive>" input Parser.(only cmp_exp_syn)
           |> Parser.extract
           |> Interactive.elaborate_exp' LF.Empty LF.Empty
           |> Pair.rmap Whnf.cnormCTyp
         in
         fprintf ppf "%a : %a"
           (P.fmt_ppr_cmp_exp_syn LF.Empty LF.Empty Pretty.std_lvl) exp
           (P.fmt_ppr_cmp_typ LF.Empty Pretty.std_lvl) tau
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
      let sgn = Runparser.parse_file arg Parser.(only sgn) |> Parser.extract in
      let sgn' = begin match Recsgn.recSgnDecls sgn with
    | sgn', None -> sgn'
    | _, Some _ ->
      raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
      end
      in
        if !Debug.chatter <> 0 then
          List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn';
      fprintf ppf "The file has been successfully loaded.\n"
    with
    |Failure _ -> fprintf ppf "Please provide the file name\n" ;
  else begin if List.length files > 1 then fprintf ppf "Please supply only 1 file" end;

  if not !Options.emacs then
    begin
      init_repl ppf;
      Command.print_usage ppf
    end;

  Sys.catch_break true;
  loop ppf
