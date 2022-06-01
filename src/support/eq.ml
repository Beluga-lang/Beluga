module type EQ = sig
  type t

  val equal : t -> t -> bool

  val ( = ) : t -> t -> bool

  val ( <> ) : t -> t -> bool
end

module Make (T : sig
  type t

  val equal : t -> t -> bool
end) : EQ with type t = T.t = struct
  include T

  let ( = ) = equal

  let[@inline] ( <> ) x y = Bool.not (x = y)
end

let contramap (type t t') (eq : (module EQ with type t = t')) (f : t -> t') =
  (module Make (struct
    type nonrec t = t

    let equal x y =
      let (module Eq) = eq in
      Eq.equal (f x) (f y)
  end) : EQ
    with type t = t)
