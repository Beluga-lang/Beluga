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

val equal :
     ('a -> 'a -> bool)
  -> ('b -> 'b -> bool)
  -> ('a, 'b) t
  -> ('a, 'b) t
  -> bool

val compare :
  ('a -> 'a -> int) -> ('b -> 'b -> int) -> ('a, 'b) t -> ('a, 'b) t -> int

val pp :
     (Format.formatter -> 'a -> unit)
  -> (Format.formatter -> 'b -> unit)
  -> Format.formatter
  -> 'a * 'b
  -> unit

val show :
     (Format.formatter -> 'a -> unit)
  -> (Format.formatter -> 'b -> unit)
  -> 'a * 'b
  -> string

(** {1 Instances} *)

module MakeEq (E1 : Eq.EQ) (E2 : Eq.EQ) : Eq.EQ with type t = (E1.t, E2.t) t

module MakeOrd (O1 : Ord.ORD) (O2 : Ord.ORD) :
  Ord.ORD with type t = (O1.t, O2.t) t

module MakeShow (S1 : Show.SHOW) (S2 : Show.SHOW) :
  Show.SHOW with type t = (S1.t, S2.t) t
