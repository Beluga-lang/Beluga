(** Nonempty list. *)
type 'a t = 'a * 'a list

type 'a nonempty = 'a t

let uncons : 'a t -> 'a * 'a list = Fun.id
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

exception Empty

(** Converts the list to a nonempty list.
    Raises the exception Empty if the list was empty.
 *)
let unsafe_of_list (l : 'a list) : 'a t =
  Option.get' Empty (of_list l)

let to_list ((x, l) : 'a t) : 'a list =
  x :: l

let map (f : 'a -> 'b) (x, l : 'a t) : 'b t =
  (f x, List.map f l)

let iter (f : 'a -> unit) (x, l : 'a t) : unit =
  List.iter f (x :: l)

let for_all (f : 'a -> bool) (x, l : 'a t) : bool =
  List.for_all f (x :: l)

(** Prints a nonempty sequence with the given separator, which defaults to Format.pp_print_cut. *)
let print ?(pp_sep = Format.pp_print_cut)
      (f : Format.formatter -> 'a -> unit) (ppf : Format.formatter) (l : 'a t) =
  Format.pp_print_list ~pp_sep: pp_sep f ppf (to_list l)

let rec all_equal (x, l : 'a t) : 'a option =
  match l with
  | [] -> Some x
  | x' :: xs when x = x' -> all_equal (x, xs)
  | _ -> None

let minimum_by (<) (x, l) =
  List.fold_left (fun min x -> if x < min then x else min) x l

let minimum l = minimum_by (<) l

let maximum l = minimum_by (>) l

let group_by (p : 'a -> 'key) (l : 'a list) : ('key * 'a t) list =
  let h = Hashtbl.create 32 in
  let () =
    let insert k x =
      let d =
        match Hashtbl.find_opt h k with
        | None -> DynArray.make 32
        | Some d -> d
      in
      DynArray.add d x;
      Hashtbl.replace h k d
    in
    List.for_each_ l (fun x -> insert (p x) x)
  in
  (* The use of unsafe_of_list here is justified because every
     dynarray we create has one element added immediately to it, and is
     hence nonempty
   *)
  Hashtbl.to_seq h
  |> Seq.map (Pair.rmap Fun.(unsafe_of_list ++ DynArray.to_list))
  |> Seq.to_list

module Syntax = struct
  let ($>) (p : 'a t) (f : 'a -> 'b) : 'b t =
    map f p
end
