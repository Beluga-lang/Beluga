(** Module type for abstract datatypes with a mapping function. *)
module type FUNCTOR = sig
  type 'a t

  (** {1 Combinators} *)

  (** [map f] is the function that maps values of {!type:t} by [f]. The order
      of arguments is for use in function pipelines as
      [fb = fa |> map (fun a -> (* ... *))]. *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** [( $> )] is an infix synonym for {!map}. *)
  val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

  (** [( let+ ) ma f] is [map f a]. This is a binding operator, and is used
      as [let+ a = ma in f a] *)
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  (** [( and+ ) ma mb] is [let+ a = ma in let+ b = mb in return (a, b)]. This
      is a binding operator, and it is used as
      [let+ a = ma and+ b = mb in ...]. *)
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
end

(** Functor building an implementation of {!FUNCTOR} over a monad. *)
module Make (M : Monad.MONAD) : FUNCTOR with type 'a t = 'a M.t
