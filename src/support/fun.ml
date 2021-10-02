include Stdlib.Fun

let (++) f g x = f (g x)

let flip f y x = f x y

let rec until f =
  if f () then until f
  else ()

let through f x = f x; x

let after f x = f (); x

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y
