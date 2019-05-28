exception NoValue

let eliminate (def : unit -> 'b) (f : 'a -> 'b) : 'a option -> 'b =
  function
  | None -> def ()
  | Some x -> f x

let is_some (o : 'a option) : bool =
  eliminate (fun _ -> false) (fun _ -> true) o

(** Extracts the value from an option, throwing an exception if
    there's None.
 *)
let get' (e : exn) (o : 'a option) : 'a =
  eliminate
    (Misc.throw e)
    (Misc.id)
    o

let get o = get' NoValue o

let of_bool =
  function
  | true -> Some ()
  | false -> None

let map (f : 'a -> 'b) (o : 'a option) : 'b option =
  eliminate (fun _ -> None) (fun x -> Some (f x)) o

let ( $ ) (o : 'a option) (k : 'a -> 'b option) : 'b option =
  eliminate (fun _ -> None) k o

let pure (x : 'a) : 'a option =
  Some x

let rec traverse (f : 'a -> 'b option) (xs : 'a list) : 'b list option =
  match xs with
  | [] -> Some []
  | x :: xs ->
     f x
     $ fun y ->
       traverse f xs
       $ fun ys ->
         pure (y :: ys)

let rec fold_left
          (f : 'b -> 'a -> 'b option) (acc : 'b) (xs : 'a list)
        : 'b option =
  match xs with
  | [] -> Some acc
  | x :: xs ->
     f acc x $ fun acc' -> fold_left f acc' xs

let none : 'a option =
  None

let ( $> ) (o : 'a option) (f : 'a -> 'b) : 'b option =
  o $ fun x -> pure (f x)

let void (o : 'a option) : unit option =
  o $> fun _ -> ()

let rec filter_map (f : 'a -> 'b option) (l : 'a list) : 'b list =
  match l with
  | [] -> []
  | x :: xs ->
     let y' = f x in
     let ys = filter_map f xs in
     eliminate (fun () -> ys) (fun y -> y :: ys) y'

let cat_options (l : 'a option list) : 'a list =
  filter_map Misc.id l

let print
      (f : Format.formatter -> 'a -> unit)
      (ppf : Format.formatter)
      (m : 'a option)
    : unit =
  eliminate (fun () -> ()) (f ppf) m
