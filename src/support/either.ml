type ('e, 'a) t =
  | Left of 'e
  | Right of 'a

let eliminate left right = function
  | Left e -> left e
  | Right x -> right x

let is_right e = eliminate (Fun.const false) (Fun.const true) e

let is_left e = not @@ is_right e

let right x = Right x

let left x = Left x

let map_right f e = eliminate left (fun x -> Right (f x)) e

let map_left f e = eliminate (fun e -> Left (f e)) right e

let bimap f g e = eliminate (fun e -> Left (f e)) (fun x -> Right (g x)) e

let void_right e = map_right (fun _ -> ()) e

let void_left e = map_left (fun _ -> ()) e

let void e = bimap (fun _ -> ()) (fun _ -> ()) e

let bind k e = eliminate left k e

let forget e = eliminate (fun _ -> None) Option.some e

let of_option o = Option.eliminate (fun () -> Left ()) right o

let of_option' f o = Option.eliminate (fun () -> f () |> left) right o

let to_option = function
  | Right x -> Some x
  | Left _ -> None

let ( >>= ) e k = bind k e

let ( $> ) e f = map_right f e

let trap f = try Right (f ()) with e -> Left e
