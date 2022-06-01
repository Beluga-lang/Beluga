type ('a, 'b) t = 'a * 'b

(** [fst (x, _)] is [x]. *)
val fst : 'a * _ -> 'a

(** [snd (_, y)] is [y]. *)
val snd : _ * 'b -> 'b

(** [map ~fst ~snd (x, y)] is [(fst x, snd y)]. *)
val map : fst:('a -> 'b) -> snd:('c -> 'd) -> 'a * 'c -> 'b * 'd

(** Transforms the right component of a pair. *)
val map_right : ('a -> 'b) -> 'x * 'a -> 'x * 'b

(** Transforms the left component of a pair. *)
val map_left : ('a -> 'b) -> 'a * 'x -> 'b * 'x

(** Transforms both components of a pair. *)
val bimap : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd

(** Transforms both components of a pair in the same way. *)
val both : ('a -> 'b) -> 'a * 'a -> 'b * 'b

(** Forms a pair from left to right. *)
val left : 'a -> 'b -> 'a * 'b

(** Forms a pair from right to left. *)
val right : 'a -> 'b -> 'b * 'a

(** Swaps a pair. *)
val swap : 'a * 'b -> 'b * 'a

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
