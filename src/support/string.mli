include module type of Stdlib.String

(** [unpack s] is [s] as a list of characters.
*)
val unpack : string -> char list

(** [pack cs] is the string concatenation of [cs].
*)
val pack : char list -> string

(** [drop n s] is the substring of [s] without the first [n] leading
    characters.
*)
val drop : int -> string -> string
