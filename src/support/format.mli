include module type of Stdlib.Format

type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

val stringify : (formatter -> 'a -> unit) -> 'a -> string

val punctuation : string -> formatter -> unit -> unit
val semicolon : formatter -> unit -> unit
val comma : formatter -> unit -> unit

val between : (formatter -> unit -> unit) ->
              (formatter -> unit -> unit) ->
              (formatter -> unit -> unit) ->
              formatter -> unit -> unit
