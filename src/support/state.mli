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

  (** [try_catch m ~on_exn state] is [on_exn cause] if [run m state] raises
      [cause], and [run m state] otherwise.

      Not tail-recursive. *)
  val try_catch : 'a t Lazy.t -> on_exn:(exn -> 'a t) -> 'a t

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

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

(** Functor building an implementation of {!STATE} for a given type of
    states. *)
module Make (State : sig
  type t
end) : STATE with type state = State.t
