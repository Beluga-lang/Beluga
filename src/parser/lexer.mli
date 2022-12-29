open Support
open Beluga_syntax

val lex_string :
  initial_location:Location.t -> string -> (Location.t * Token.t) Seq.t

val lex_file : filename:string -> (Location.t * Token.t) Seq.t

val lex_input_channel :
  initial_location:Location.t -> in_channel -> (Location.t * Token.t) Seq.t
