type t = string -> string option -> string Gen.gen

val make : Options.test_file option -> int option -> t
