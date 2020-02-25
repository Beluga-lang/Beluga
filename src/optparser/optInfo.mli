type 'a unchecked

val long_name : string -> 'a unchecked
val short_name : char -> 'a unchecked
val other_names : string list -> 'a unchecked
val meta_vars : string list -> 'a unchecked
val help_msg : string -> 'a unchecked
val default_argument : 'a -> 'a unchecked
val condition : ('a -> bool) -> 'a unchecked
val optional : 'a -> 'a unchecked

val lift : unit unchecked -> 'a unchecked

val merge : 'a unchecked list -> 'a unchecked

type 'a checked =
  { name : OptName.t
  ; meta_vars : string list
  ; help_msg : string option
  ; default_argument : 'a option
  ; condition : ('a -> bool) option
  ; optional : 'a option
  }

type check_error =
  | NoName

val check : 'a unchecked -> ('a checked, check_error) result
