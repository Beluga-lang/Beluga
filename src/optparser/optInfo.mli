(** The type of unchecked command line option information.
*)
type 'a unchecked

(** The neutral element of unchecked command line option information.
*)
val empty : 'a unchecked

val long_name : string -> 'a unchecked
val short_name : char -> 'a unchecked
val other_names : string list -> 'a unchecked
val meta_vars : string list -> 'a unchecked
val help_msg : string -> 'a unchecked
val default_argument : 'a -> 'a unchecked
val optional : 'a -> 'a unchecked

val lift : unit unchecked -> 'a unchecked

(** [s1 <|> s2] is the combination of [s1] and [s2] where undefined fields of
    [s1] are given the value of the fields of [s2]. This operation is
    associative.
*)
val (<|>) : 'a unchecked -> 'a unchecked -> 'a unchecked

(** [merge [s1; s2; ...; sn]] is [s1 <|> s2 <|> ... <|> sn]. Defaults to
    {!empty} if the list is empty.
*)
val merge : 'a unchecked list -> 'a unchecked

type 'a checked =
  { name : OptName.t
  ; meta_vars : string list
  ; help_msg : string option
  ; default_argument : 'a option
  ; optional : 'a option
  }

type check_error =
  | NoName

val check : 'a unchecked -> ('a checked, check_error) result
