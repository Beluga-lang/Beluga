include Stdlib.Either

let eliminate left right = function
  | Left e -> left e
  | Right x -> right x

let bimap f g = function
  | Left x -> left (f x)
  | Right x -> right (g x)

let void_right = function
  | Right _ -> right ()
  | Left x -> left x

let void_left = function
  | Left _ -> left ()
  | Right x -> right x

let void = function
  | Right _ -> right ()
  | Left _ -> left ()

let bind k = function
  | Left x -> left x
  | Right x -> k x

let forget = function
  | Left _ -> Option.none
  | Right x -> Option.some x

let of_option = function
  | Option.None -> left ()
  | Option.Some x -> right x

let of_option' f = function
  | Option.None -> left (f ())
  | Option.Some x -> right x

let to_option = function
  | Right x -> Option.some x
  | Left _ -> Option.none

let ( >>= ) e k = bind k e

let ( $> ) e f = map_right f e

let trap f =
  try right (f ()) with
  | e -> left e
