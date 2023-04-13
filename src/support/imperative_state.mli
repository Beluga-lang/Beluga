(** Mutable state helper definitions. *)

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

  val traverse_list : state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t

  val traverse_list_void :
    state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val traverse_list1_void :
    state -> (state -> 'a -> Unit.t) -> 'a List1.t -> Unit.t

  val traverse_list2_void :
    state -> (state -> 'a -> Unit.t) -> 'a List2.t -> Unit.t

  val traverse_reverse_list :
    state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_reverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_reverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t

  val traverse_reverse_list_void :
    state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val traverse_reverse_list1_void :
    state -> (state -> 'a -> Unit.t) -> 'a List1.t -> Unit.t

  val traverse_reverse_list2_void :
    state -> (state -> 'a -> Unit.t) -> 'a List2.t -> Unit.t

  val traverse_option :
    state -> (state -> 'a -> 'b) -> 'a Option.t -> 'b Option.t

  val traverse_option_void :
    state -> (state -> 'a -> Unit.t) -> 'a Option.t -> Unit.t

  val seq_list : state -> (state -> 'a) List.t -> 'a List.t

  val seq_list1 : state -> (state -> 'a) List1.t -> 'a List1.t

  val seq_list_void : state -> (state -> Unit.t) List.t -> Unit.t
end

(** Functor building an implementation of {!IMPERATIVE_STATE} for a given
    type of states. *)
module Make : functor
  (State : sig
     type state
   end)
  -> IMPERATIVE_STATE with type state = State.state
