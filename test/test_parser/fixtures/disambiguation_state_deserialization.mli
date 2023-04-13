open Beluga_parser.Beluga_parser

exception Unsupported_sort of string

exception Unsupported_fixity of string

exception Unsupported_associativity of string

val read_disambiguation_state : string -> Disambiguation_state.state
