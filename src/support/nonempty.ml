(** Nonempty list. *)
type 'a t = 'a * 'a list

type 'a nonempty = 'a t

let uncons : 'a t -> 'a * 'a list = Misc.id
let head = fst
let tail = snd

(** Gets the last element of the nonempty list and the list of all elements
    before the last.
    Not tail-recursive.
 *)
let rec unsnoc (h, t) =
  match t with
  | [] -> ([], h)
  | x :: xs ->
     let (t', last) = unsnoc (x, xs) in
     (h :: t', last)

(** Gets the last element of a nonempty list. *)
let rec last (h, t) =
  match t with
  | [] -> h
  | x :: xs -> last (x, xs)

let length (_, l) = 1 + List.length l

let from x l = x , l

let rec fold_right f g (h, l) =
  match l with
  | [] -> f h
  | x :: xs -> g h (fold_right f g (x, xs))

let fold_left (type a) (type b) (f : a -> b) (g : b -> a -> b) (x, l) =
  List.fold_left g (f x) l

let of_list (l : 'a list) : 'a t option =
  match l with
  | [] -> None
  | x :: xs -> Some (x, xs)

let to_list ((x, l) : 'a t) : 'a list =
  x :: l

let map (f : 'a -> 'b) (x, l : 'a t) : 'b t =
  (f x, List.map f l)

(** Prints a nonempty sequence with the given separator, which defaults to Format.pp_print_cut. *)
let print ?(pp_sep = Format.pp_print_cut)
      (f : Format.formatter -> 'a -> unit) (ppf : Format.formatter) (l : 'a t) =
  Format.pp_print_list ~pp_sep: pp_sep f ppf (to_list l)

module Syntax = struct
  let ($>) (p : 'a t) (f : 'a -> 'b) : 'b t =
    map f p
end
