(** The type of pairs. *)
type ('a, 'b) t = 'a * 'b

(** {1 Constructors} *)

(** [left l r] is [(l, r)]. *)
val left : 'a -> 'b -> 'a * 'b

(** [right r l] is [(l, r)]. *)
val right : 'a -> 'b -> 'b * 'a

(** {1 Destructors} *)

(** [fst (x, _)] is [x]. *)
val fst : 'a * _ -> 'a

(** [snd (_, y)] is [y]. *)
val snd : _ * 'b -> 'b

(** {1 Mapping} *)

(** [map ~fst ~snd (x, y)] is [(fst x, snd y)]. *)
val map : fst:('a -> 'b) -> snd:('c -> 'd) -> 'a * 'c -> 'b * 'd

(** [map_right f (x, y)] is [(x, f y)]. *)
val map_right : ('a -> 'b) -> 'x * 'a -> 'x * 'b

(** [map_left f (x, y)] is [(f x, y)]. *)
val map_left : ('a -> 'b) -> 'a * 'x -> 'b * 'x

(** [bimap f g (x, y)] is [f x, f y]. *)
val bimap : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd

(** [both f (x, y)] is [(f x, f y)]. *)
val both : ('a -> 'b) -> 'a * 'a -> 'b * 'b

(** {1 Miscellaneous} *)

(** [swap (x, y)] is [(y, x)]. *)
val swap : 'a * 'b -> 'b * 'a

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
