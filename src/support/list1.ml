type 'a t = 'a * 'a list

let from x l = (x, l)

let singleton x = (x, [])

let cons element (h, l) = (element, h :: l)

let uncons = Fun.id

let head = Pair.fst

let tail = Pair.snd

let rev =
  let rec rev l ((hd, tl) as acc) =
    match l with
    | [] -> acc
    | x :: xs -> rev xs (x, hd :: tl)
  in
  fun (hd, tl) -> rev tl (hd, [])

let unsnoc =
  let rec unsnoc (h, t) return =
    match t with
    | [] -> return ([], h)
    | x :: xs -> unsnoc (x, xs) (fun (t', last) -> return (h :: t', last))
  in
  fun l -> unsnoc l Fun.id

let rec last (h, t) =
  match t with
  | [] -> h
  | x :: xs -> last (x, xs)

let to_list (x, l) = x :: l

let length (_, l) = 1 + List.length l

let equal eq (h1, t1) (h2, t2) = eq h1 h2 && List.equal eq t1 t2

let compare_lengths (_, t1) (_, t2) = List.compare_lengths t1 t2

let compare cmp (h1, t1) (h2, t2) =
  match cmp h1 h2 with
  | 0 -> List.compare cmp t1 t2
  | x -> x

let iter f l = List.iter f (to_list l)

let map f (x, l) =
  let h = f x in
  let t = List.map f l in
  (h, t)

let fold_right f g l =
  let rec fold_right (h, l) return =
    match l with
    | [] -> return (f h)
    | x :: xs -> fold_right (x, xs) (fun a -> return (g h a))
  in
  fold_right l Fun.id

let fold_left f g (x, l) = List.fold_left g (f x) l

let filter_map f (h, t) =
  let rest = List.filter_map f t in
  f h |> Option.fold ~none:rest ~some:(fun h -> h :: rest)

let for_all f l = List.for_all f (to_list l)

let rec all_equal (x, l) =
  match l with
  | [] -> Some x
  | x' :: xs when x = x' -> all_equal (x, xs)
  | _ -> None

let traverse f (x, l) =
  Option.(
    f x >>= fun y ->
    traverse f l >>= fun ys -> Some (y, ys))

let map2 f (h1, t1) (h2, t2) =
  try (f h1 h2, List.map2 f t1 t2)
  with Invalid_argument _ -> invalid_arg "List1.map2"

let of_list l =
  match l with
  | [] -> None
  | x :: xs -> Some (x, xs)

exception Empty

(** Converts the list to a nonempty list. Raises the exception Empty if the
    list was empty. *)
let unsafe_of_list l = Option.get' Empty (of_list l)

let find_opt p l = l |> to_list |> List.find_opt p

let minimum_by ( < ) (x, l) =
  List.fold_left (fun min x -> if x < min then x else min) x l

let minimum l = minimum_by ( < ) l

let maximum l = minimum_by ( > ) l

let partition f (h, l) =
  let l1, l2 = List.partition f l in
  if f h then (h :: l1, l2) else (l1, h :: l2)

let group_by p l =
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
  (* The use of unsafe_of_list here is justified because every dynarray we
     create has one element added immediately to it, and is hence nonempty *)
  Hashtbl.to_seq h
  |> Seq.map (Pair.map_right Fun.(DynArray.to_list >> unsafe_of_list))
  |> Seq.to_list

let split ((x, y), t) =
  let xs, ys = List.split t in
  ((x, xs), (y, ys))

let combine (a, l1) (b, l2) =
  try ((a, b), List.combine l1 l2)
  with Invalid_argument _ -> invalid_arg "List1.combine"

let ap xs = map2 Fun.apply xs

let ap_one x = map (Fun.apply x)

let pp ?(pp_sep = Format.pp_print_cut) pp_v ppf (h, t) =
  pp_v ppf h;
  List.iter
    (fun v ->
      pp_sep ppf ();
      pp_v ppf v)
    t

let show ?(pp_sep = Format.pp_print_cut) pp_v l =
  Format.asprintf "%a" (pp ~pp_sep pp_v) l

module Syntax = struct
  let ( $> ) p f = map f p
end

module MakeEq (E : Eq.EQ) : Eq.EQ with type t = E.t t = Eq.Make (struct
  type nonrec t = E.t t

  let equal = equal E.equal
end)

module MakeOrd (O : Ord.ORD) : Ord.ORD with type t = O.t t = Ord.Make (struct
  type nonrec t = O.t t

  let compare = compare O.compare
end)

module MakeShow (S : Show.SHOW) : Show.SHOW with type t = S.t t =
Show.Make (struct
  type nonrec t = S.t t

  let pp = pp S.pp
end)
