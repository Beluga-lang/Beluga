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

let make (type t) (compare : t -> t -> int) =
  (module Make (struct
    type nonrec t = t

    let compare = compare
  end) : ORD
    with type t = t)

module Reverse (Ord : ORD) : ORD with type t = Ord.t = Make (struct
  type t = Ord.t

  let compare x y = Ord.compare y x
end)

let contramap (type t s) (module Ord : ORD with type t = s) (f : t -> s) =
  (module Make (struct
    type nonrec t = t

    let compare x y = Ord.compare (f x) (f y)
  end) : ORD
    with type t = t)

let sequence (type s1 s2 t) (module Ord1 : ORD with type t = s1)
    (module Ord2 : ORD with type t = s2) f1 f2 =
  (module Make (struct
    type nonrec t = t

    let compare x y =
      let cmp1 = Ord1.compare (f1 x) (f1 y) in
      if cmp1 = 0 then Ord2.compare (f2 x) (f2 y) else cmp1
  end) : ORD
    with type t = t)
