type t = string -> string option -> unit -> string option

val create : Options.test_file option -> int option -> t
