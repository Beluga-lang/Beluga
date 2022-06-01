type ('e, 'a) t =
  | Left of 'e
  | Right of 'a

let eliminate left right = function
  | Left e -> left e
  | Right x -> right x

let is_right e = eliminate (Fun.const false) (Fun.const true) e

let is_left e = not @@ is_right e

let pure x = Right x

let left x = Left x

let rmap f e = eliminate left (fun x -> Right (f x)) e

let lmap f e = eliminate (fun e -> Left (f e)) pure e

let bimap f g e = eliminate (fun e -> Left (f e)) (fun x -> Right (g x)) e

let rvoid e = rmap (fun _ -> ()) e

let lvoid e = lmap (fun _ -> ()) e

let void e = bimap (fun _ -> ()) (fun _ -> ()) e

let bind k e = eliminate left k e

let forget e = eliminate (fun _ -> None) Option.some e

let of_option o = Option.eliminate (fun () -> Left ()) pure o

let of_option' f o = Option.eliminate (fun () -> f () |> left) pure o

let to_option = function
  | Right x -> Some x
  | Left _ -> None

let ( >>= ) e k = bind k e

let ( $> ) e f = rmap f e

let trap f = try Right (f ()) with e -> Left e
