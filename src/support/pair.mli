(** Transforms the right component of a pair. *)
val rmap : ('a -> 'b) -> 'x * 'a -> 'x * 'b

(** Transforms the left component of a pair. *)
val lmap : ('a -> 'b) -> 'a * 'x -> 'b * 'x

(** Transforms both components of a pair. *)
val bimap : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
