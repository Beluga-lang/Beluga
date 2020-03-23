type ('a, 'b) t = 'a * 'b

let rmap (f : 'a -> 'b) (p : 'x * 'a) : 'x * 'b =
  let (x, a) = p in (x, f a)

let lmap (f : 'a -> 'b) (p : 'a * 'x) : 'b * 'x =
  let (a, x) = p in (f a, x)

let bimap (f : 'a -> 'b) (g : 'c -> 'd) (p : 'a * 'c) =
  let (x, y) = p in (f x, g y)

let both (f : 'a -> 'b) (p : 'a * 'a) : 'b * 'b =
  bimap f f p

let left (x : 'a) (y : 'b) : 'a * 'b = (x, y)

let right (x : 'a) (y : 'b) : 'b * 'a = (y, x)

let swap (p : 'a * 'b) : 'b * 'a =
  let (x, y) = p in (y, x)

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y
