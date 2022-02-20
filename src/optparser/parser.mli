(** [parse spec args] parses [args] using the specification [spec]. *)
val parse : 'a OptSpec.t -> string list -> ('a, OptSpec.Error.t) result
