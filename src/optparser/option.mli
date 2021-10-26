include module type of Stdlib.Option

(** [o1 <|> o2] is [o1] if [o1] is [Some v], and [o2] otherwise.
*)
val (<|>) : 'a option -> 'a option -> 'a option
