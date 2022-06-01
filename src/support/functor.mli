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
end

(** Functor building an implementation of {!FUNCTOR} over a monad. *)
module Make (M : Monad.MONAD) : FUNCTOR with type 'a t = 'a M.t
