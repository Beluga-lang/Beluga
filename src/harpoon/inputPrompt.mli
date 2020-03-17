type t = string -> string option -> unit -> string option

val make : Options.test_file option -> int option -> t
