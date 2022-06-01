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

let from x l = x, l

let singleton x = x, []

let rec fold_right f g (h, l) =
  match l with
  | [] -> f h
  | x :: xs -> g h (fold_right f g (x, xs))

let fold_left (type a) (type b) (f : a -> b) (g : b -> a -> b) (x, l) =
  List.fold_left g (f x) l

let destructure f l = f (head l) (tail l)

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
  let h = f x in
  let t = List.map f l in
  h, t

let map2 f (h1, t1) (h2, t2) =
  f h1 h2, List.map2 f t1 t2

let filter_map f (h, t) =
  let rest = List.filter_map f t in
  f h
  |> Option.fold
    ~none:rest
    ~some:(fun h -> h :: rest)

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
    List.iter (fun x -> insert (p x) x) l
  in
  (* The use of unsafe_of_list here is justified because every
     dynarray we create has one element added immediately to it, and is
     hence nonempty
   *)
  Hashtbl.to_seq h
  |> Seq.map (Pair.map_right Fun.(unsafe_of_list ++ DynArray.to_list))
  |> Seq.to_list

let split ((x, y), t) =
  let (xs, ys) = List.split t in
  (x, xs), (y, ys)

let combine (a, l1) (b, l2) =
  ((a, b), List.combine l1 l2)

let partition f (h, l) =
  let (l1, l2) = List.partition f l in
  if f h then (h :: l1, l2) else (l1, h :: l2)

let ap xs = map2 (fun x f -> f x) xs

let ap_one x = map (fun f -> f x)

module Syntax = struct
  let ($>) (p : 'a t) (f : 'a -> 'b) : 'b t =
    map f p
end
