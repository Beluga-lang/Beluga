(** Mutable state helper definitions.

    This is analogous to the state monad defined in {!State}, but the
    imperative state type assumes that the state is mutable. *)

(** Abstract definition of helpers for stateful operations using a strictly
    mutable state. *)
module type IMPERATIVE_STATE = sig
  type state

  val traverse_tuple2 :
       state
    -> (state -> 'a1 -> 'b1)
    -> (state -> 'a2 -> 'b2)
    -> 'a1 * 'a2
    -> 'b1 * 'b2

  val traverse_tuple3 :
       state
    -> (state -> 'a1 -> 'b1)
    -> (state -> 'a2 -> 'b2)
    -> (state -> 'a3 -> 'b3)
    -> 'a1 * 'a2 * 'a3
    -> 'b1 * 'b2 * 'b3

  (** [traverse_list state f \[x1; x2; ...; xn\]] is [\[y1; y2; ...; yn\]]
      where [yi = f state xi], and [y1], [y2], ..., [yn] are computed in
      order, meaning that [y1] is computed first, then [y2], etc. *)
  val traverse_list : state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t

  (** [iter_list state f \[x1; x2; ...; xn\]] is
      [f state x1; f state x2; ...; f state xn]. *)
  val iter_list : state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val iter_list1 : state -> (state -> 'a -> Unit.t) -> 'a List1.t -> Unit.t

  val iter_list2 : state -> (state -> 'a -> Unit.t) -> 'a List2.t -> Unit.t

  (** [traverse_reverse_list state f \[x1; x2; ...; xn\]] is
      [\[y1; y2; ...; yn\]] where [yi = f state xi], and [y1], [y2], ...,
      [yn] are computed in reverse order, meaning that [yn] is computed
      first, then [y(n-1)], etc. *)
  val traverse_reverse_list :
    state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_reverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_reverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t

  val iter_rev_list : state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val iter_rev_list1 :
    state -> (state -> 'a -> Unit.t) -> 'a List1.t -> Unit.t

  val iter_rev_list2 :
    state -> (state -> 'a -> Unit.t) -> 'a List2.t -> Unit.t

  val traverse_option :
    state -> (state -> 'a -> 'b) -> 'a Option.t -> 'b Option.t

  val iter_option : state -> (state -> 'a -> Unit.t) -> 'a Option.t -> Unit.t

  val seq_list : state -> (state -> 'a) List.t -> 'a List.t

  val seq_list1 : state -> (state -> 'a) List1.t -> 'a List1.t

  val iter_seq : state -> (state -> Unit.t) List.t -> Unit.t
end

(** Functor building an implementation of {!IMPERATIVE_STATE} for a given
    type of states. *)
module Make : functor
  (State : sig
     type state
   end)
  -> IMPERATIVE_STATE with type state = State.state
