type ('a, 'b) t = 'a * 'b

let fst = fst

let snd = snd

let map ~fst ~snd (x, y) = (fst x, snd y)

let map_right f (x, a) = (x, f a)

let map_left f (a, x) = (f a, x)

let bimap f g (x, y) = (f x, g y)

let both f p = bimap f f p

let left x y = (x, y)

let right x y = (y, x)

let swap (x, y) = (y, x)

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y

let equal eqx eqy (x1, y1) (x2, y2) = eqx x1 x2 && eqy y1 y2

let compare ordx ordy (x1, y1) (x2, y2) =
  match ordx x1 x2 with
  | 0 -> ordy y1 y2
  | x -> x

let pp ppx ppy ppf (x, y) = Format.fprintf ppf "(%a, %a)" ppx x ppy y

let show ppx ppy pair = Format.stringify (pp ppx ppy) pair

module MakeEq (E1 : Eq.EQ) (E2 : Eq.EQ) :
  Eq.EQ with type t = (E1.t, E2.t) t = Eq.Make (struct
  type nonrec t = (E1.t, E2.t) t

  let equal = equal E1.equal E2.equal
end)

module MakeOrd (O1 : Ord.ORD) (O2 : Ord.ORD) :
  Ord.ORD with type t = (O1.t, O2.t) t = Ord.Make (struct
  type nonrec t = (O1.t, O2.t) t

  let compare = compare O1.compare O2.compare
end)

module MakeShow (S1 : Show.SHOW) (S2 : Show.SHOW) :
  Show.SHOW with type t = (S1.t, S2.t) t = Show.Make (struct
  type nonrec t = (S1.t, S2.t) t

  let pp = pp S1.pp S2.pp
end)
