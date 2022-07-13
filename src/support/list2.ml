type 'a t = T of 'a * 'a * 'a list [@unboxed]

let[@inline] from x1 x2 l = T (x1, x2, l)

let[@inline] from1 x1 (List1.T (x2, l)) = from x1 x2 l

let[@inline] pair x1 x2 = from x1 x2 []

let[@inline] cons element (T (x1, x2, l)) = T (element, x1, x2 :: l)

let rev =
  let rec rev l (T (x1, x2, tl) as acc) =
    match l with
    | [] -> acc
    | x :: xs -> rev xs (T (x, x1, x2 :: tl))
  in
  fun (T (x1, x2, tl)) -> rev tl (T (x2, x1, []))

let last = function
  | T (_, x2, []) -> x2
  | T (_, _, tl) -> List.last tl

let to_list (T (x1, x2, xs)) = x1 :: x2 :: xs

let of_list = function
  | x1 :: x2 :: xs -> Option.some (T (x1, x2, xs))
  | _ :: _ | [] -> Option.none

let to_list1 (T (x1, x2, xs)) = List1.from x1 (x2 :: xs)

let of_list1 = function
  | List1.T (x1, x2 :: xs) -> Option.some (T (x1, x2, xs))
  | List1.T (_, []) -> Option.none

let length (T (_, _, xs)) = 2 + List.length xs

let equal eq (T (x1, x2, xs)) (T (y1, y2, ys)) =
  eq x1 y1 && eq x2 y2 && List.equal eq xs ys

let compare_lengths (T (_, _, xs)) (T (_, _, ys)) =
  List.compare_lengths xs ys

let compare cmp (T (x1, x2, xs)) (T (y1, y2, ys)) =
  match cmp x1 y1 with
  | 0 -> List1.compare cmp (List1.from x2 xs) (List1.from y2 ys)
  | x -> x

let iter f l = List.iter f (to_list l)

let map f (T (x1, x2, xs)) =
  let y1 = f x1 in
  let y2 = f x2 in
  let ys = List.map f xs in
  T (y1, y2, ys)

let fold_right fst snd cons l =
  let rec fold_right (T (x1, x2, xs)) return =
    match xs with
    | [] -> return (snd x1 (fst x2))
    | x :: xs -> fold_right (T (x2, x, xs)) (fun a -> return (cons x1 a))
  in
  fold_right l Fun.id

let fold_left fst snd cons (T (x1, x2, xs)) =
  List.fold_left cons (snd (fst x1) x2) xs

let filter_map f l = List.filter_map f (to_list l)

let for_all f l = List.for_all f (to_list l)

let for_all2 f l1 l2 = List.for_all2 f (to_list l1) (to_list l2)

let exists f l = List.exists f (to_list l)

let traverse f (T (x1, x2, xs)) =
  let open Option in
  f x1 >>= fun y1 ->
  f x2 >>= fun y2 ->
  traverse f xs >>= fun ys -> Some (T (y1, y2, ys))

let map2 f (T (x1, x2, xs)) (T (y1, y2, ys)) =
  try T (f x1 y1, f x2 y2, List.map2 f xs ys)
  with Invalid_argument _ -> invalid_arg "List2.map2"

let find_opt p l = List.find_opt p (to_list l)

let find_map f l = List.find_map f (to_list l)

let partition f (T (x1, x2, xs)) =
  let l1, l2 = List1.partition f (List1.from x2 xs) in
  if f x1 then (x1 :: l1, l2) else (l1, x1 :: l2)

let split (T ((x1, y1), (x2, y2), t)) =
  let xs, ys = List.split t in
  (T (x1, x2, xs), T (y1, y2, ys))

let combine (T (x1, x2, l1)) (T (y1, y2, l2)) =
  try T ((x1, y1), (x2, y2), List.combine l1 l2)
  with Invalid_argument _ -> invalid_arg "List2.combine"

let ap xs = map2 Fun.apply xs

let ap_one x = map (Fun.apply x)

let pp ?(pp_sep = Format.pp_print_cut) pp_v ppf (T (x1, x2, t)) =
  pp_v ppf x1;
  pp_sep ppf ();
  pp_v ppf x2;
  List.iter
    (fun v ->
      pp_sep ppf ();
      pp_v ppf v)
    t

let show ?pp_sep pp_v l = Format.asprintf "%a" (pp ?pp_sep pp_v) l

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
