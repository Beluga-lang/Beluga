(**
 * Registers a new bespoke command
 *)
val register : string -> (Format.formatter -> string list -> unit) -> string -> unit

(**
 * Decides whether an input string is some Beluga code (constructor
 * `Input) or an interactive mode command to run (constructor `Cmd).
 *)
val is_command : string -> [> `Cmd of string | `Input of string]

(** Given a formatter for command output, parses the given string as a
 * command and runs it.
 *)
val do_command : Format.formatter -> string -> unit

val print_usage : Format.formatter -> unit
