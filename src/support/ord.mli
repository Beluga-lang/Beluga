(** Totally ordered types. *)

(** Module type for totally ordered types. *)
module type ORD = sig
  (** The type of elements to compare. *)
  type t

  (** [compare a b] compares [a] and [b] for ordering.

      - [compare a b < 0] if [a] precedes [b] (denoted [a < b]),
      - [compare a b = 0] if [a] is equal to [b] (denoted [a = b]),
      - [compare a b > 0] if [a] succeeds [b] (denoted [a > b]).

      This should satisfy the following properties:

      - {b Comparability}: [(compare a b <= 0 || compare b a >= 0) = true],
      - {b Transitivity}: if [(compare a b <= 0) = true] and
        [(compare b c <= 0) = true], then [(compare a c <= 0) = true],
      - {b Reflexivity}: [(compare a a = 0) = true],
      - {b Antisymmetry}: if [(compare a b <= 0) = true] and
        [(compare a b >= 0) = true] then [(compare a b = 0) = true]. *)
  val compare : t -> t -> int

  val ( < ) : t -> t -> bool

  val ( <= ) : t -> t -> bool

  val ( > ) : t -> t -> bool

  val ( >= ) : t -> t -> bool

  (** [max a b] is [a] if [a >= b] and [b] otherwise. *)
  val max : t -> t -> t

  (** [min a b] is [a] if [a <= b] and [b] otherwise. *)
  val min : t -> t -> t

  include Eq.EQ with type t := t
end

(** Functor building an implementation of {!ORD} given a type with a total
    comparator. *)
module Make (T : sig
  (** See {!type:ORD.t} *)
  type t

  (** See {!val:ORD.compare}. *)
  val compare : t -> t -> int
end) : ORD with type t = T.t

(** Functor building an implementation of {!ORD} whose ordering is the
    reverse of the given totally ordered type. *)
module Reverse (Ord : ORD) : ORD with type t = Ord.t

(** If [val f : 't -> 's], then [contramap ord f] is an instance of {!ORD}
    for values of type ['t] by the {!ORD} insance [ord] for values of type
    ['s]. *)
val contramap :
     (module ORD with type t = 's)
  -> ('t -> 's)
  -> (module ORD with type t = 't)

(** If [val f1 : 't -> 's1] and [val f2 : 't -> 's2], then
    [sequence ord1 ord2 f1 f2] is an instance of {!ORD} for values of type
    ['t] whose ordering is first ordered by contramapping by [ord1] and [f1],
    and if that ordering is equal then ordered by contramapping by [ord2] and
    [f2]. *)
val sequence :
     (module ORD with type t = 's1)
  -> (module ORD with type t = 's2)
  -> ('t -> 's1)
  -> ('t -> 's2)
  -> (module ORD with type t = 't)
