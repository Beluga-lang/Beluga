include Stdlib.Fun

let[@inline] ( ++ ) f g x = x |> g |> f

let[@inline] ( >> ) f g x = x |> f |> g

let[@inline] apply x f = f x

let[@inline] flip f y x = f x y

let rec until f = if f () then until f else ()

let[@inline] through f x =
  f x;
  x

let after f x =
  f ();
  x

let[@inline] curry f x y = f (x, y)

let[@inline] uncurry f (x, y) = f x y

let fix f =
  let rec f' = lazy (f (fun t -> Lazy.force f' t)) in
  Lazy.force f'

let rec repeat n f =
  if n = 0 then ()
  else (
    f ();
    repeat (n - 1) f)
