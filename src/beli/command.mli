
val register : string -> (Format.formatter -> string list -> unit) -> string -> unit

val is_command : string -> [> `Cmd of string | `Input of string]

val do_command : Format.formatter -> string -> unit
