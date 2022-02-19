include Stdlib.List

let take_circularly n ls =
  let rec go n = function
    | _ when n <= 0 ->
        []
    | [] ->
        go n ls
    | x :: xs ->
        x :: go (n - 1) xs
  in
  if ls = []
  then raise (Invalid_argument "'ls' should have more than one element")
  else go n ls


let maximum_element : type a. (a -> a -> a) -> a -> a list -> a =
 fun maximum default -> fold_left maximum default


let split =
  let rec split n list return =
    match list with
    | x :: xs when n > 0 ->
        split (n - 1) xs (fun (xs', ys) -> return (x :: xs', ys))
    | xs ->
        return ([], xs)
  in
  fun n list -> split n list Fun.id
