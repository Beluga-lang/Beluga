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


let split n =
  let rec loop n = function
    | x :: xs when n > 0 ->
        let xs', ys = loop (n - 1) xs in
        (x :: xs', ys)
    | xs ->
        ([], xs)
  in
  loop n
