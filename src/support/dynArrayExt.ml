include DynArray

let rec append_list d = function
  | [] -> ()
  | x :: xs ->
    add d x;
    append_list d xs

let head = function
  | d when empty d -> None
  | d -> Some (get d 0)

let get_opt d i = try Some (get d i) with Invalid_arg _ -> None

let rfind_opt_idx d p =
  let rec go = function
    | -1 -> None
    | k ->
      let x = get d k in
      if p x then Some (k, x) else go (k - 1)
  in
  go (length d - 1)
