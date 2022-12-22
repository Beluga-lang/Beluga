module type MONAD = sig
  type +'a t

  val return : 'a -> 'a t

  val bind : ('a -> 'b t) -> 'a t -> 'b t

  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  val compose : ('b -> 'c t) -> ('a -> 'b t) -> 'a -> 'c t

  val ( >=> ) : ('a -> 'b t) -> ('b -> 'c t) -> 'a -> 'c t

  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
end

module Make (Monad : sig
  type +'a t

  val return : 'a -> 'a t

  val bind : ('a -> 'b t) -> 'a t -> 'b t
end) =
struct
  include Monad

  let[@inline] ( >>= ) a f = bind f a

  let compose g f x = f x >>= g

  let ( >=> ) f g = compose g f

  let ( let* ) ma f = bind f ma

  let ( and* ) ma mb =
    let* a = ma in
    let* b = mb in
    return (a, b)
end
