(** Module type for abstract datatypes with an associative operator and a
    left and right identity element for choosing between values. *)
module type ALTERNATIVE = sig
  type 'a t

  (** The identity element of {!( <|> )}. *)
  val empty : 'a t

  (** [alt a1 a2] is [a1] if it is not {!empty}, and [a2] otherwise. *)
  val alt : 'a t -> 'a t -> 'a t

  (** Infix synonym of {!alt}. *)
  val ( <|> ) : 'a t -> 'a t -> 'a t
end
