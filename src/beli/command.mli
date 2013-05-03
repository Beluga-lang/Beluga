
val register : string -> (string list -> unit) -> string -> unit

val is_command : string -> [> `Cmd of string | `Input of string]

val do_command : string -> unit
