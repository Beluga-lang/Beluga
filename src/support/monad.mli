(** Definition of monadic types, which are abstract descriptors of
    computations.

    For better performance, avoid using monads. *)

(** The abstract datatype of actions.

    Instances of {!MONAD} should satisfy the following laws for
    {!MONAD.(>>=)}:

    - {b Left identity}: [(return a >>= h) = (h a)],
    - {b Right identity}: [(m >>= return) = m],
    - {b Associativity}: [((m >>= g) >>= h) = (m >>= (fun x -> g x >>= h))].

    Using the Kleisli-composition operator {!MONAD.( >=> )}:

    - {b Left identity}: [(return >=> h) = h],
    - {b Right identity}: [(f >=> return) = f],
    - {b Associativity}: [((f >=> g) >=> h) = (f >=> (g >=> h))]. *)
module type MONAD = sig
  (** The type of actions in the monad. *)
  type +'a t

  (** [return a] injects [a] into the monadic type. *)
  val return : 'a -> 'a t

  (** [bind f a] is the sequential composition of two actions, passing any
      value produced by [a] as argument to [f]. *)
  val bind : ('a -> 'b t) -> 'a t -> 'b t

  (** Operator alias of {!bind}. *)
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  (** [compose g f] is the Kleisli composition of [f] and [g], passing the
      input to [f], then binding the output to [g]. *)
  val compose : ('b -> 'c t) -> ('a -> 'b t) -> 'a -> 'c t

  (** Operator alias of {!compose}. *)
  val ( >=> ) : ('a -> 'b t) -> ('b -> 'c t) -> 'a -> 'c t

  (** [( let* ) ma f] is [bind f ma]. This is a binding operator, and it is
      used as [let* a = ma in f a]. *)
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

  (** [( and* ) ma mb] is [let* a = ma in let* b = mb in return (a, b)]. This
      is a binding operator, and it is used as
      [let* a = ma and* b = mb in ...]. *)
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
end

(** Functor building the aliases for a minimal implementation for {!MONAD}. *)
module Make (Monad : sig
  (** The type of actions in the monad. *)
  type +'a t

  (** [return a] injects [a] into the monadic type. *)
  val return : 'a -> 'a t

  (** [bind f a] is the sequential composition of two actions, passing any
      value produced by [a] as argument to [f]. *)
  val bind : ('a -> 'b t) -> 'a t -> 'b t
end) : MONAD with type 'a t = 'a Monad.t
