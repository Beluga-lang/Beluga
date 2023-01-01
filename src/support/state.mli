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

  (** [eval a init] is [run a init], but outputs only [v]. *)
  val eval : 'a t -> state -> 'a

  (** [locally f m a init] runs [a] with state [f init] and returns
      [(init, v)] where [v] is the output from running [a]. *)
  val locally : (state -> state) -> 'a t -> 'a t

  (** {1 Instances} *)

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

(** Functor building an implementation of {!STATE} for a given type of
    states. *)
module Make (State : sig
  type t
end) : STATE with type state = State.t
