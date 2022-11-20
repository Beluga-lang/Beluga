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

let make (type t) (equal : t -> t -> bool) =
  (module Make (struct
    type nonrec t = t

    let equal = equal
  end) : EQ
    with type t = t)

let contramap (type t s) (module Eq : EQ with type t = s) f =
  (module Make (struct
    type nonrec t = t

    let equal x y = Eq.equal (f x) (f y)
  end) : EQ
    with type t = t)

let conjunction (type s1 s2 t) (module Eq1 : EQ with type t = s1)
    (module Eq2 : EQ with type t = s2) f1 f2 =
  (module Make (struct
    type nonrec t = t

    let equal x y = Eq1.equal (f1 x) (f1 y) && Eq2.equal (f2 x) (f2 y)
  end) : EQ
    with type t = t)
