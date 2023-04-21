open Support
open Beluga_syntax

(** [lex_string initial_location input] is the persistent sequence of tokens
    lexed from the string [input], with token locations starting at
    [initial_location]. *)
val lex_string :
  initial_location:Location.t -> string -> Located_token.t Seq.t

(** [lex_string initial_location input] is the persistent sequence of tokens
    lexed from input channel [input], with token locations starting at
    [initial_location]. You need to make sure to keep the input channel open
    throughout lexing, otherwise reading of subsequent tokens will fail. *)
val lex_input_channel :
  initial_location:Location.t -> in_channel -> Located_token.t Seq.t
