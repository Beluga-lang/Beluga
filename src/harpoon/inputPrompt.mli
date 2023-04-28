type t = msg:string -> history_file:string option -> string Gen.gen

val make : Options.test_file option -> int option -> t
