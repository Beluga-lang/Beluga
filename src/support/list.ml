include Stdlib.List

let rec last l = match l with
  | [] -> raise (Invalid_argument "last")
  | [x] -> x
  | _ :: xs -> last xs

let rec pairs l =
  match l with
  | [] | [_] -> []
  | x1 :: x2 :: xs -> (x1, x2) :: pairs (x2 :: xs)

let null = function
  | [] -> true
  | _ -> false

let nonempty l = not (null l)

let filter_rev p l =
  let rec go acc = function
    | [] -> acc
    | x :: xs -> go (if p x then x :: acc else acc) xs
  in
  go [] l

let uncons = function
  | [] -> None
  | x :: xs -> Some (x, xs)

let rec concat_map f = function
  | [] -> []
  | x :: xs -> f x @ concat_map f xs

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

let rec equal eq l1 l2 = match l1, l2 with
  | [], [] -> true
  | x :: xs, y :: ys -> if eq x y then equal eq xs ys else false
  | _ -> false

let hd_opt = function
  | [] -> None
  | x :: _ -> Some x

let index l = mapi (fun i x -> (i, x)) l

let mapi2 f l1 l2 =
  let rec mapi2 index l1 l2 return =
    match l1, l2 with
    | [], [] -> return []
    | x :: xs, y :: ys ->
      mapi2 (index + 1) xs ys (fun tl -> return (f index x y :: tl))
    | _ -> raise (Invalid_argument "mapi2")
  in
  mapi2 0 l1 l2 Fun.id

let rec drop n = function
  | l when n <= 0 -> l
  | [] -> []
  | _ :: xs (* n > 0 *) -> drop (n - 1) xs

let ap xs = map2 (fun x f -> f x) xs

let ap_one x = map (fun f -> f x)

let split l =
  let rec split l return =
    match l with
    | [] -> return ([], [])
    | (x, y) :: l -> split l (fun (xs, ys) -> return (x :: xs, y :: ys))
  in
  split l Fun.id

let combine l1 l2 =
  let rec combine l1 l2 return =
    match l1, l2 with
    | [], [] -> return []
    | a1 :: l1, a2 :: l2 ->
      combine l1 l2 (fun rest -> return ((a1, a2) :: rest))
    | _ -> raise (Invalid_argument "List.combine")
  in
  combine l1 l2 Fun.id
