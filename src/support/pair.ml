let rmap (f : 'a -> 'b) (p : 'x * 'a) : 'x * 'b =
  let (x, a) = p in (x, f a)

let lmap (f : 'a -> 'b) (p : 'a * 'x) : 'b * 'x =
  let (a, x) = p in (f a, x)

let bimap (f : 'a -> 'b) (g : 'c -> 'd) (p : 'a * 'c) =
  let (x, y) = p in (f x, g y)
