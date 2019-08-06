module P = Pretty.Ext.DefaultPrinter
module LF = Syntax.Ext.LF

(* This program is to facilitate parser debugging.
   It reads the given file (use "-" or no input for reading stdin)
 *)
let _ =
  let (name, chan) =
    let path = lazy (Array.get Sys.argv 1) in
    match () with
    | _ when Array.length Sys.argv = 1 || Lazy.force path = "-" -> ("<stdin>", stdin)
    | _ -> let p = Lazy.force path in (p, open_in p)
  in
  let open Format in
  let ppf = formatter_of_out_channel stdout in
  Printexc.record_backtrace true;
  try
    Runparser.parse_channel name chan Parser.(only cmp_exp_syn)
    |> snd
    |> Parser.handle
         (fun e ->
           Parser.format_error ppf e)
         (fun x ->
           fprintf ppf "Parse OK!@.%a@."
             (P.fmt_ppr_cmp_exp_syn LF.Empty 0) x
         )
  with
  | e ->
     fprintf ppf "@[<v>%s@,@,%s@]" (Printexc.to_string e) (Printexc.get_backtrace ())
