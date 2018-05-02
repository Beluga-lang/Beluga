let eliminate (def : unit -> 'b) (f : 'a -> 'b) : 'a option -> 'b =
  function
  | None -> def ()
  | Some x -> f x

let is_some (o : 'a option) : bool =
  eliminate (fun _ -> false) (fun _ -> true) o

let map (f : 'a -> 'b) (o : 'a option) : 'b option =
  eliminate (fun _ -> None) (fun x -> Some (f x)) o

let ( $ ) (o : 'a option) (k : 'a -> 'b option) : 'b option =
  eliminate (fun _ -> None) k o

let pure (x : 'a) : 'a option =
  Some x

let none : 'a option =
  None

let ( $> ) (o : 'a option) (f : 'a -> 'b) : 'b option =
  o $ fun x -> pure (f x)

let void (o : 'a option) : unit option =
  o $> fun _ -> ()
