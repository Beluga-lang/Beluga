type 'a t =
  | Nothing
  | Just of 'a
  
let eliminate (def : unit -> 'b) (f : 'a -> 'b) : 'a t -> 'b =
  function
  | Nothing -> def ()
  | Just x -> f x

let is_some (o : 'a t) : bool =
  eliminate (fun _ -> false) (fun _ -> true) o

let map (f : 'a -> 'b) (o : 'a t) : 'b t =
  eliminate (fun _ -> Nothing) (fun x -> Just (f x)) o

let ( $ ) (o : 'a t) (k : 'a -> 'b t) : 'b t =
  eliminate (fun _ -> Nothing) k o

let pure (x : 'a) : 'a t =
  Just x

let ( $> ) (o : 'a t) (f : 'a -> 'b) : 'b t =
  o $ fun x -> pure (f x)

let void (o : 'a t) : unit t =
  o $> fun _ -> ()
