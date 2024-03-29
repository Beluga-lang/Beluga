type +'a t = T of 'a * 'a list [@unboxed]

let[@inline] from x l = T (x, l)

let[@inline] singleton x = T (x, [])

let[@inline] cons element (T (h, l)) = T (element, h :: l)

let[@inline] uncons (T (h, t)) = (h, t)

let[@inline] head (T (h, _)) = h

let[@inline] tail (T (_, t)) = t

let rev =
  let rec rev l (T (hd, tl) as acc) =
    match l with
    | [] -> acc
    | x :: xs -> rev xs (T (x, hd :: tl))
  in
  fun (T (hd, tl)) -> rev tl (T (hd, []))

let replace_first f (T (x, xs)) = T (f x, xs)

let unsnoc =
  let rec unsnoc (T (hd, tl)) ~return =
    match tl with
    | [] -> return ([], hd)
    | x :: xs ->
        unsnoc
          (T (x, xs))
          ~return:(fun (t', last) -> return (hd :: t', last))
  in
  fun l -> unsnoc l ~return:Fun.id

let last = function
  | T (hd, []) -> hd
  | T (_, tl) -> List.last tl

let to_list (T (hd, tl)) = hd :: tl

let length (T (_, tl)) = 1 + List.length tl

let compare_length_with (T (_, tl)) n =
  if n >= 1 then List.compare_length_with tl (n - 1)
  else (* The list has length greater than [n] *) 1

let equal eq (T (h1, t1)) (T (h2, t2)) = eq h1 h2 && List.equal eq t1 t2

let compare_lengths (T (_, t1)) (T (_, t2)) = List.compare_lengths t1 t2

let compare cmp (T (h1, t1)) (T (h2, t2)) =
  match cmp h1 h2 with
  | 0 -> List.compare cmp t1 t2
  | x -> x

let iter f (T (x, xs)) =
  f x;
  List.iter f xs

let map f (T (x, xs)) =
  let y = f x in
  let ys = List.map f xs in
  T (y, ys)

let mapi f (T (x, xs)) =
  let y = f 0 x in
  let ys = List.mapi (fun i x -> f (i + 1) x) xs in
  T (y, ys)

let index l = mapi (fun i x -> (i, x)) l

let fold_right =
  let rec fold_right f g (T (h, l)) return =
    match l with
    | [] -> return (f h)
    | x :: xs -> fold_right f g (T (x, xs)) (fun a -> return (g h a))
  in
  fun f g l -> fold_right f g l Fun.id

let fold_left sing cons (T (x, xs)) = List.fold_left cons (sing x) xs

let filter_map f (T (x, xs)) =
  match f x with
  | Option.Some y -> y :: List.filter_map f xs
  | Option.None -> List.filter_map f xs

let append xs ys = fold_right (fun x -> cons x ys) cons xs

let append_list l1 l2 = List.fold_right cons l1 l2

let rec flatten (T (hd, tl)) =
  match tl with
  | [] -> hd
  | x :: xs -> append hd (flatten (T (x, xs)))

let rec concat_map f (T (hd, tl)) =
  match tl with
  | [] -> f hd
  | x :: xs -> append (f x) (concat_map f (T (x, xs)))

let for_all p (T (x, xs)) = p x && List.for_all p xs

let exists p (T (x, xs)) = p x || List.exists p xs

let all_equal (T (x, xs)) =
  if List.for_all (Stdlib.( = ) x) xs then Option.some x else Option.none

let traverse f (T (x, l)) =
  let open Option in
  f x >>= fun y ->
  List.traverse f l >>= fun ys -> Option.some (T (y, ys))

let map2 f (T (x, xs)) (T (y, ys)) =
  let z = f x y
  and zs = List.map2 f xs ys in
  T (z, zs)

let of_list = function
  | [] -> Option.none
  | x :: xs -> Option.some (T (x, xs))

exception Empty

let unsafe_of_list l =
  match l with
  | [] -> raise Empty
  | x :: xs -> T (x, xs)

let find_opt p l = List.find_opt p (to_list l)

let find_map f l = List.find_map f (to_list l)

let minimum_by ( < ) (T (x, l)) =
  List.fold_left (fun min x -> if x < min then x else min) x l

let maximum_by ( > ) (T (x, l)) =
  List.fold_left (fun max x -> if x > max then x else max) x l

let minimum l = minimum_by ( < ) l

let maximum l = maximum_by ( < ) l

let partition f (T (h, l)) =
  let l1, l2 = List.partition f l in
  if f h then (h :: l1, l2) else (l1, h :: l2)

let partition_map f (T (h, l)) =
  match f h with
  | Stdlib.Either.Left x ->
      let l1, l2 = List.partition_map f l in
      Stdlib.Either.left (T (x, l1), l2)
  | Stdlib.Either.Right x ->
      let l1, l2 = List.partition_map f l in
      Stdlib.Either.right (l1, T (x, l2))

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

let split (T ((x, y), t)) =
  let xs, ys = List.split t in
  (T (x, xs), T (y, ys))

let combine (T (a, l1)) (T (b, l2)) = T ((a, b), List.combine l1 l2)

let ap xs fs = map2 Fun.apply xs fs

let flap x fs = map (Fun.apply x) fs

let pp ?(pp_sep = Format.pp_print_cut) pp_v ppf (T (h, t)) =
  pp_v ppf h;
  List.iter
    (fun v ->
      pp_sep ppf ();
      pp_v ppf v)
    t

let show ?pp_sep pp_v l = Format.stringify (pp ?pp_sep pp_v) l

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
