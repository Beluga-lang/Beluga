(** The type of state monads. *)
module type STATE = sig
  (** The type of states inside the monad. *)
  type state

  include Monad.MONAD with type 'a t = state -> state * 'a

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

  (** [locally f m a init] runs [a] with state [f init] and returns
      [(init, v)] where [v] is the output from running [a]. *)
  val locally : (state -> state) -> 'a t -> 'a t

  (** [scoped ~set ~unset m initial_state] executes [set], then [m], then
      [unset] and returns the value from [m]. This allows for computations
      with scoped mutations to the state. [set] and [unset] can be thought of
      apply and undo operations for the mutation. This is less strict than
      [locally] which ignores the output state. *)
  val scoped : set:Unit.t t -> unset:Unit.t t -> 'a t -> 'a t

  (** [try_catch m ~on_exn state] is [on_exn cause] if [run m state] raises
      [cause], and [run m state] otherwise.

      Not tail-recursive. *)
  val try_catch : 'a t -> on_exn:(exn -> 'a t) -> 'a t

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

  (** {1 Instances} *)

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

(** Functor building an implementation of {!STATE} for a given type of
    states. *)
module Make (State : sig
  type t
end) : STATE with type state = State.t
