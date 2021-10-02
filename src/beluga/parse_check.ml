open Support

module P = Beluga.Pretty.Ext.DefaultPrinter
module LF = Beluga.Syntax.Ext.LF

(** The thing we're trying to parse in the file.
    Usually this should be `only sgn', but for testing it's convenient
    to change it to something smaller.
 *)
let target = Beluga.Parser.(only sgn)

(** Processes a .bel file. *)
let process_bel name chan =
  let open Format in
  let open Beluga in
  let ppf = formatter_of_out_channel stdout in
  Printexc.record_backtrace true;
  try
    Runparser.parse_channel (Location.initial name) chan target
    |> snd
    |> Parser.handle
         (fun e ->
           Parser.print_error ppf e;
           exit 1)
         (fun _ -> ())
  with
  | e ->
     fprintf ppf "@[<v>%s@,@,%s@]" (Printexc.to_string e) (Printexc.get_backtrace ());
     exit 1

(* This program is to facilitate parser debugging.
   To read stdin, use `parse_check <(cat)` because I can't be bothered
   to implement a special case for the `-` path.
 *)
let _ =
  let name = Array.get Sys.argv 1 in
  let ppf = Format.std_formatter in
  Beluga.Load.load ppf name
  |> List.iter
       (fun path ->
         let h = open_in path in
         process_bel path h;
         close_in h)
