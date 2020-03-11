type ('e, 'a) t =
  | Left of 'e
  | Right of 'a

let eliminate (left : 'e -> 'c) (right : 'a -> 'c) : ('e, 'a) t -> 'c =
  function
  | Left e -> left e
  | Right x -> right x

let is_right (e : ('e, 'a) t) : bool =
  eliminate (fun _ -> false) (fun _ -> true) e

let is_left (e : ('e, 'a) t) : bool = is_right e |> not

let pure (x : 'a) : ('e, 'a) t = Right x

let left (x : 'e) : ('e, 'a) t = Left x

let rmap (f : 'a -> 'b) (e : ('e, 'a) t) : ('e, 'b) t =
  eliminate left (fun x -> Right (f x)) e

let lmap (f : 'e1 -> 'e2) (e : ('e1, 'a) t) : ('e2, 'a) t =
  eliminate (fun e -> Left (f e)) pure e

let bimap (f : 'e1 -> 'e2) (g : 'a -> 'b) (e : ('e1, 'a) t) :
      ('e2, 'b) t =
  eliminate (fun e -> Left (f e)) (fun x -> Right (g x)) e

let rvoid (e : ('e, 'a) t) : ('e, unit) t =
  rmap (fun _ -> ()) e

let lvoid (e : ('e, 'a) t) : (unit, 'a) t =
  lmap (fun _ -> ()) e

let void (e : ('e, 'a) t) : (unit, unit) t =
  bimap (fun _ -> ()) (fun _ -> ()) e

let bind (k : 'a -> ('e, 'b) t) (e : ('e, 'a) t) : ('e, 'b) t =
  eliminate left k e

let forget (e : ('e, 'a) t) : 'a option =
  eliminate (fun _ -> None) Maybe.pure e

let of_option (o : 'a option) : (unit, 'a) t =
  Maybe.eliminate (fun _ -> Left ()) pure o

let of_option' (f : unit -> 'e) (o : 'a option) : ('e, 'a) t =
  Maybe.eliminate (fun () -> f () |> left) (fun x -> x |> pure) o

let to_option (e : ('e, 'a) t) : 'a option =
  match e with
  | Right x -> Some x
  | _ -> None

let ( $ ) (e : ('e, 'a) t) (k : ('a -> ('e, 'b) t)) : ('e, 'b) t =
  bind k e

let ( $> ) (e : ('e, 'a) t) (f : ('a -> 'b)) : ('e, 'b) t =
  rmap f e

let trap (f : unit -> 'a) =
  try
    Right (f ())
  with
  | e -> Left e
