(** Types having an equality operator. *)

(** Module type for types with an equality predicate and operators. *)
module type EQ = sig
  (** The type of elements to check for equality. *)
  type t

  (** [equal a b] is [true] if and only if [a] and [b] are equal. This should
      satisfy the following properties:

      - {b Reflexivity}: [equal a a = true]
      - {b Symmetry}: [equal a b] is equivalent to [equal b a]
      - {b Transitivity}: if [equal a b = true] and [equal b c = true], then
        [equal a c = true] *)
  val equal : t -> t -> bool

  (** Operator alias of {!equal}. *)
  val ( = ) : t -> t -> bool

  (** Negation of operator {!(=)}. *)
  val ( <> ) : t -> t -> bool
end

(** Functor building an implementation of {!EQ} given a type with a
    structural equality function.*)
module Make (T : sig
  (** See {!type:EQ.t}. *)
  type t

  (** See {!val:EQ.equal}. *)
  val equal : t -> t -> bool
end) : EQ with type t = T.t

(** [make equal] is equivalent to the functor [Make (T)] with
    [T.equal = equal]. *)
val make : ('t -> 't -> bool) -> (module EQ with type t = 't)

(** If [val f : 't -> 's], then [contramap eq f] is an instance of {!EQ} for
    values of type ['t] by the {!EQ} instance [eq] for values of type ['s]. *)
val contramap :
  (module EQ with type t = 's) -> ('t -> 's) -> (module EQ with type t = 't)

(** If [val f1 : 't -> 's1] and [val f2 : 't -> 's2], then
    [conjunction eq1 eq2 f1 f2] is an instance of {!EQ} for values of type
    ['t] that first checks equality by contramapping by [eq1] and [f1], and
    if that check was [true] then checks equality by contramapping by [eq2]
    and [f2]. *)
val conjunction :
     (module EQ with type t = 's1)
  -> (module EQ with type t = 's2)
  -> ('t -> 's1)
  -> ('t -> 's2)
  -> (module EQ with type t = 't)
