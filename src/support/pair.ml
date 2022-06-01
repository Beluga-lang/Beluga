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
