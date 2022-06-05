module type ALTERNATIVE = sig
  type 'a t

  val empty : 'a t

  val alt : 'a t -> 'a t -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
