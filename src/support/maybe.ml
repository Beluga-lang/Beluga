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

let get_default def o =
  eliminate
    (Misc.const def)
    (Misc.id)
    o

let of_bool =
  function
  | true -> Some ()
  | false -> None

let map (f : 'a -> 'b) (o : 'a option) : 'b option =
  eliminate (fun _ -> None) (fun x -> Some (f x)) o

let ( $ ) (o : 'a option) (k : 'a -> 'b option) : 'b option =
  eliminate (fun _ -> None) k o

(** Prioritized choice between options.
    This will force the first option, but will never force the second.
    This operation is associative.
 *)
let ( <|> ) (p : 'a option Lazy.t) (q : 'a option Lazy.t) : 'a option Lazy.t =
  begin match Lazy.force p with
  | Some _ -> p
  | None -> q
  end

(* This is hoisted out so that forcing becomes a no-op after the first force. *)
let lazy_none = lazy None

let choice (ps : 'a option Lazy.t list) : 'a option Lazy.t =
  List.fold_left ( <|> ) lazy_none ps

(** Non-lazy version of `<|>'. *)
let alt (o1 : 'a option) (o2 : 'a option) : 'a option =
  match o1, o2 with
  | Some x, _ -> Some x
  | _, Some y -> Some y
  | _ -> None

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

(** Ignores the result of the first option and gives the second. *)
let ( &> ) (o : 'a option) (o' : 'b option) : 'b option =
  o $ fun _ -> o'

let void (o : 'a option) : unit option =
  o $> fun _ -> ()

let rec filter_map (f : 'a -> 'b option) (l : 'a list) : 'b list =
  match l with
  | [] -> []
  | x :: xs ->
     f x
     |> eliminate
       (fun () -> filter_map f xs)
       (fun y -> y :: filter_map f xs)

let cat_options (l : 'a option list) : 'a list =
  filter_map Misc.id l

let print
      (f : Format.formatter -> 'a -> unit)
      (ppf : Format.formatter)
      (m : 'a option)
    : unit =
  eliminate (fun () -> ()) (f ppf) m
