(* The Parser and Lexer modules are independent.
   This module brings them together by providing a high-level
   interface for running parsers.
 *)

type filename = string

val parse_file : filename -> 'a Parser.t -> Parser.state * 'a Parser.result
val parse_string : filename -> string -> 'a Parser.t -> Parser.state * 'a Parser.result
val parse_gen : filename -> char Gen.t -> 'a Parser.t -> Parser.state * 'a Parser.result
val parse_channel : filename -> in_channel -> 'a Parser.t -> Parser.state * 'a Parser.result
