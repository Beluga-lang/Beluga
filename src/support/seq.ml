include Stdlib.Seq

let rec of_gen g () =
  match g () with
  | Option.None -> Nil
  | Option.Some x -> Cons (x, of_gen g)

let of_list l =
  let rec go l () =
    match l with
    | [] -> Nil
    | x :: xs -> Cons (x, go xs)
  in
  go l

let to_list s =
  let rec go s return =
    match s () with
    | Nil -> return []
    | Cons (x, s) -> go s (fun xs -> return (x :: xs))
  in
  go s Fun.id
