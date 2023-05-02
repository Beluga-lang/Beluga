type t

val make : Options.test_file option -> int option -> t

val next_line_opt :
  t -> msg:string -> history_file:string option -> string option
