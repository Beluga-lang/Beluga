(** State monad definition.

    The state monad is used to define stateful actions, i.e. actions that can
    read or write to some auxiliary data structure. In general, using the
    state monad is slower than using side effects because of extra memory
    allocations and eager closure constructions. For helpers to operations
    defined with respect to mutable states, see {!Imperative_state}.

    In order to effectively use the state monad, you should define:

    + An abstract module type definition for the state data structure. This
      acts as an interface between concrete implementations of the state data
      structure and modules that are defined with respect to that state. Even
      if only an immutable data structure is intended to be implemented for
      this abstract definition, its operations should be implementable using
      a mutable state.
    + A concrete implementation for that abstract state definition.
    + A functor taking an abstract state definition as argument, and
      producing operations that use that state.

    For instance:

    {[
      module type DISAMBIGUATION_STATE = sig
        include State.STATE

        val with_bound_lf_variable : Identifier.t -> 'a t -> 'a t
        (* ... *)
      end

      module Immutable_disambiguation_state : sig
        include DISAMBIGUATION_STATE

        val initial_state : state
      end = struct
        (* ... *)
      end

      module Mutable_disambiguation_state : sig
        include DISAMBIGUATION_STATE

        val create_initial_state : unit -> state
      end = struct
        (* ... *)
      end

      module type LF_DISAMBIGUATION = sig
        include State.STATE

        val disambiguate_lf_kind : Synprs.lf_object -> Synext.lf_kind t
        (* ... *)
      end

      module Make_lf_disambiguation
          (Disambiguation_state : DISAMBIGUATION_STATE) :
        LF_DISAMBIGUATION with type state = Disambiguation_state.state =
      struct
        (* ... *)
      end
    ]} *)

(** The type of state monads. *)
module type STATE = sig
  (** The type of states inside the monad. *)
  type state

  type 'a t = state -> state * 'a

  (** Return the state from the internals of the monad. *)
  val get : state t

  (** Replace the state inside the monad. *)
  val put : state -> unit t

  (** Modify the state inside the monad. *)
  val modify : (state -> state) -> unit t

  (** [run a init] runs [a] with initial state [init], returning [(final, v)]
      where [final] is the final state and [v] is the output. *)
  val run : 'a t -> state -> state * 'a

  (** [eval a init] is [run a init = (final, v)], but outputs only [v]. *)
  val eval : 'a t -> state -> 'a

  (** [exec a init] is [run a init = (final, v)], but outputs only [final]. *)
  val exec : 'a t -> state -> state

  (** {1 Traversals} *)

  val traverse_tuple2 :
    ('a1 -> 'b1 t) -> ('a2 -> 'b2 t) -> 'a1 * 'a2 -> ('b1 * 'b2) t

  val traverse_tuple3 :
       ('a1 -> 'b1 t)
    -> ('a2 -> 'b2 t)
    -> ('a3 -> 'b3 t)
    -> 'a1 * 'a2 * 'a3
    -> ('b1 * 'b2 * 'b3) t

  val traverse_list : ('a -> 'b t) -> 'a List.t -> 'b List.t t

  val traverse_list1 : ('a -> 'b t) -> 'a List1.t -> 'b List1.t t

  val traverse_list2 : ('a -> 'b t) -> 'a List2.t -> 'b List2.t t

  val traverse_list_void : ('a -> _ t) -> 'a List.t -> Unit.t t

  val traverse_list1_void : ('a -> _ t) -> 'a List1.t -> Unit.t t

  val traverse_list2_void : ('a -> _ t) -> 'a List2.t -> Unit.t t

  val traverse_reverse_list : ('a -> 'b t) -> 'a List.t -> 'b List.t t

  val traverse_reverse_list1 : ('a -> 'b t) -> 'a List1.t -> 'b List1.t t

  val traverse_reverse_list2 : ('a -> 'b t) -> 'a List2.t -> 'b List2.t t

  val traverse_reverse_list_void : ('a -> _ t) -> 'a List.t -> Unit.t t

  val traverse_reverse_list1_void : ('a -> _ t) -> 'a List1.t -> Unit.t t

  val traverse_reverse_list2_void : ('a -> _ t) -> 'a List2.t -> Unit.t t

  val traverse_option : ('a -> 'b t) -> 'a Option.t -> 'b Option.t t

  val traverse_option_void : ('a -> _ t) -> 'a Option.t -> Unit.t t

  val seq_list : 'a t List.t -> 'a List.t t

  val seq_list1 : 'a t List1.t -> 'a List1.t t

  (** [seq_list_void \[x1; x2; ...; xn\]] performs [x1], [x2], ..., [xn] in
      order. *)
  val seq_list_void : unit t list -> unit t

  (** {1 Instances} *)

  include Monad.MONAD with type 'a t := 'a t

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

(** Functor building an implementation of {!STATE} for a given type of
    states. *)
module Make (State : sig
  type t
end) : STATE with type state = State.t
