open Support
open Beluga_syntax

val lex_string :
  initial_location:Location.t -> string -> Located_token.t Seq.t

val lex_input_channel :
  initial_location:Location.t -> in_channel -> Located_token.t Seq.t
