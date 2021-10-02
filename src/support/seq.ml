include Stdlib.Seq

let to_list s =
  let rec go s return =
    match s () with
    | Nil -> return []
    | Cons (x, s) -> go s (fun xs -> return (x :: xs))
  in go s Fun.id
