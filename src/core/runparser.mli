(* The Parser and Lexer modules are independent.
   This module brings them together by providing a high-level
   interface for running parsers.
 *)

type filename = string

val parse_file : Location.t -> 'a Parser.t -> Parser.state * 'a Parser.result
val parse_string : Location.t -> string -> 'a Parser.t -> Parser.state * 'a Parser.result
val parse_gen : Location.t -> char Gen.t -> 'a Parser.t -> Parser.state * 'a Parser.result
val parse_channel : Location.t -> in_channel -> 'a Parser.t -> Parser.state * 'a Parser.result
