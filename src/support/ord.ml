module type ORD = sig
  type t

  val compare : t -> t -> int

  val ( < ) : t -> t -> bool

  val ( <= ) : t -> t -> bool

  val ( > ) : t -> t -> bool

  val ( >= ) : t -> t -> bool

  val max : t -> t -> t

  val min : t -> t -> t

  include Eq.EQ with type t := t
end

module Make (T : sig
  type t

  val compare : t -> t -> int
end) : ORD with type t = T.t = struct
  include T

  let[@inline] ( = ) x y = compare x y = 0

  let equal x y = x = y

  let[@inline] ( <> ) x y = compare x y <> 0

  let[@inline] ( < ) x y = compare x y < 0

  let[@inline] ( <= ) x y = compare x y <= 0

  let[@inline] ( > ) x y = compare x y > 0

  let[@inline] ( >= ) x y = compare x y >= 0

  let[@inline] min x y = if x <= y then x else y

  let[@inline] max x y = if x >= y then x else y
end

module Reverse (Ord : ORD) : ORD with type t = Ord.t = Make (struct
  type t = Ord.t

  let compare x y = -Ord.compare x y
end)

let contramap (type t t') (ord : (module ORD with type t = t')) (f : t -> t')
    =
  (module Make (struct
    type nonrec t = t

    let compare x y =
      let (module Ord) = ord in
      Ord.compare (f x) (f y)
  end) : ORD
    with type t = t)
