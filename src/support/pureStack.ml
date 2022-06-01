type 'a t =
  { get : 'a list
  ; len : int
  }

let empty = { get = []; len = 0 }

let length s = s.len

let to_list s = s.get

let is_empty s = s.len = 0

let push x s = { get = x :: s.get; len = s.len + 1 }

let pop s =
  match s.get with
  | [] -> Option.none
  | x :: xs -> Option.some (x, { get = xs; len = s.len - 1 })

let cut n s =
  let rec go n s acc =
    if n <= 0 then Some (acc, s)
    else
      match pop s with
      | None -> None
      | Some (x, s') -> go (n - 1) s' (x :: acc)
  in
  go n s []
