module type FUNCTOR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
end

module Make (M : Monad.MONAD) : FUNCTOR with type 'a t = 'a M.t = struct
  include M

  let[@inline] map f a = a >>= fun x -> return (f x)

  let[@inline] ( $> ) a f = map f a

  let[@inline] ( let+ ) a f = map f a

  let ( and+ ) = ( and* )
end
