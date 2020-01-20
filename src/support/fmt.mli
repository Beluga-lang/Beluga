open Format


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

(** surrounded f1 f2 ppf x
    renders x using f2, but renders f1 before and after.
 *)
val surrounded : (formatter -> unit -> unit) ->
                 (formatter -> 'a -> unit) ->
                 formatter -> 'a -> unit

(** Constructs a formatting function that ignores its argument and
    prints the given string literally. *)
val string : string -> formatter -> unit -> unit
