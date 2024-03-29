include Stdlib.List

let rec last = function
  | [] -> raise (Invalid_argument "List.last")
  | [ x ] -> x
  | _ :: xs -> last xs

let rec pairs = function
  | []
  | [ _ ] ->
      []
  | x1 :: x2 :: xs -> (x1, x2) :: pairs (x2 :: xs)

let null = function
  | [] -> true
  | _ :: _ -> false

let nonempty l = Bool.not (null l)

let rec traverse f xs =
  match xs with
  | [] -> Stdlib.Option.some []
  | x :: xs ->
      Stdlib.Option.bind (f x) (fun y ->
          Stdlib.Option.bind (traverse f xs) (fun ys ->
              Stdlib.Option.some (y :: ys)))

let rec traverse_ f xs =
  match xs with
  | [] -> Stdlib.Option.some ()
  | x :: xs -> Stdlib.Option.bind (f x) (fun _y -> traverse_ f xs)

let rec fold_left_opt f acc xs =
  match xs with
  | [] -> Stdlib.Option.some acc
  | x :: xs ->
      Stdlib.Option.bind (f acc x) (fun acc' -> fold_left_opt f acc' xs)

let filter_rev p l =
  let rec go acc = function
    | [] -> acc
    | x :: xs -> go (if p x then x :: acc else acc) xs
  in
  go [] l

let rec find_map f = function
  | [] -> Stdlib.Option.none
  | x :: l -> (
      match f x with
      | Stdlib.Option.Some _ as result -> result
      | Stdlib.Option.None -> find_map f l)

let rec find_apply fs a =
  match fs with
  | [] -> Stdlib.Option.none
  | f :: fs -> (
      match f a with
      | Stdlib.Option.Some _ as v -> v
      | Stdlib.Option.None -> find_apply fs a)

let uncons = function
  | [] -> Stdlib.Option.none
  | x :: xs -> Stdlib.Option.some (x, xs)

let concat_mapi f =
  let rec go i = function
    | [] -> []
    | x :: xs -> f i x @ go (i + 1) xs
  in
  go 0

let index_of p l =
  let rec go k = function
    | [] -> None
    | x :: _ when p x -> Some k
    | _ :: xs -> go (k + 1) xs
  in
  go 0 l

let rec equal eq l1 l2 =
  match (l1, l2) with
  | [], [] -> true
  | x :: xs, y :: ys -> if eq x y then equal eq xs ys else false
  | _ -> false

let hd_opt = function
  | [] -> Stdlib.Option.none
  | x :: _ -> Stdlib.Option.some x

let index l = mapi (fun i x -> (i, x)) l

let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
  | [], [], [] -> accu
  | a1 :: l1, a2 :: l2, a3 :: l3 -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | _, _, _ -> invalid_arg "List.fold_left3"

let rec fold_left4 f accu l1 l2 l3 l4 =
  match (l1, l2, l3, l4) with
  | [], [], [], [] -> accu
  | a1 :: l1, a2 :: l2, a3 :: l3, a4 :: l4 ->
      fold_left4 f (f accu a1 a2 a3 a4) l1 l2 l3 l4
  | _, _, _, _ -> invalid_arg "List.fold_left4"

let mapi2 f l1 l2 =
  let rec mapi2 index l1 l2 return =
    match (l1, l2) with
    | [], [] -> return []
    | x :: xs, y :: ys ->
        mapi2 (index + 1) xs ys (fun tl -> return (f index x y :: tl))
    | _ -> raise (Invalid_argument "List.mapi2")
  in
  mapi2 0 l1 l2 Fun.id

let rec drop n = function
  | l when n <= 0 -> l
  | [] -> []
  | _ :: xs (* n > 0 *) -> drop (n - 1) xs

let ap xs fs = map2 Fun.apply xs fs

let flap x fs = map (Fun.apply x) fs

let split l =
  let rec split l return =
    match l with
    | [] -> return ([], [])
    | (x, y) :: l -> split l (fun (xs, ys) -> return (x :: xs, y :: ys))
  in
  split l Fun.id

let combine l1 l2 =
  let rec combine l1 l2 return =
    match (l1, l2) with
    | [], [] -> return []
    | a1 :: l1, a2 :: l2 ->
        combine l1 l2 (fun rest -> return ((a1, a2) :: rest))
    | _ -> raise (Invalid_argument "List.combine")
  in
  combine l1 l2 Fun.id

let take =
  let rec take k l acc =
    match l with
    | x :: xs when k > 0 -> take (k - 1) xs (x :: acc)
    | _ -> (rev acc, l)
  in
  fun k l -> take k l []

let take_opt =
  let rec take_opt k l acc =
    if k = 0 then Stdlib.Option.some (rev acc, l)
    else
      match l with
      | x :: xs -> take_opt (k - 1) xs (x :: acc)
      | [] -> Stdlib.Option.none
  in
  fun k l ->
    if k < 0 then raise (Invalid_argument "List.take_opt")
    else take_opt k l []

let take_while p =
  let rec take_while l acc =
    match l with
    | x :: xs when p x -> take_while xs (x :: acc)
    | _ -> (rev acc, l)
  in
  fun l -> take_while l []

let take_while_map p =
  let rec take_while_map_tl l acc =
    match l with
    | x :: xs -> (
        match p x with
        | Stdlib.Option.Some y -> take_while_map_tl xs (y :: acc)
        | Stdlib.Option.None -> (rev acc, l))
    | [] -> (rev acc, [])
  in
  fun l -> take_while_map_tl l []

let rec iter_rev f l =
  match l with
  | [] -> ()
  | x :: xs ->
      iter_rev f xs;
      f x

let rec compare cmp l1 l2 =
  match (l1, l2) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
      let c = cmp x y in
      if c <> 0 then c else compare cmp xs ys

let pp = Format.pp_print_list

let show ?(pp_sep = Format.pp_print_cut) pp_v l =
  Format.stringify (pp ~pp_sep pp_v) l

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
