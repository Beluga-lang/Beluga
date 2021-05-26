(**
 * usage: lex_dump FILE
 * synopsis: pretty-prints the output of the Beluga lexer run on FILE.
 *)
open Support
open Beluga

let print_loc ppf l =
  Format.fprintf ppf "L %d C %d-%d" (Location.start_line l) (Location.start_column l) (Location.stop_column l)

let dump_lex path =
  Gen.IO.with_in path
    (fun stream ->
      let out = Lexer.mk (Location.initial path) stream in
      let ppf = Format.formatter_of_out_channel stdout in
      let f (l, t) = Format.fprintf ppf "%a %a: %a\n" (Token.print `CLASS) t (Token.print `TOKEN) t print_loc l in
      Gen.iter f out)

let main () =
  Debug.enable ();
  dump_lex (Array.get Sys.argv 1)

let _ = main ()
