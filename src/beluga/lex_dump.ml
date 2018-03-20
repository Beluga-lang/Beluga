(**
 * usage: lex_dump FILE
 * synopsis: pretty-prints the output of the Beluga lexer run on FILE.
 *)
module Loc = Lexer.Loc
module Token = Lexer.Token
open Printf

let string_of_loc l =
  (Loc.start_off l |> string_of_int) ^ "-" ^ (Loc.stop_off l |> string_of_int)

let dump_lex path =
  let chan = open_in path in
  let stream = Stream.of_channel chan in
  let out = Lexer.mk () (Loc.mk path) stream in
  let f (t, l) = printf "%s: %s\n" (Token.to_string t) (string_of_loc l) in
  Stream.iter f out

let main () = dump_lex (Array.get Sys.argv 1)

let _ = main ()
