type 'a t =
  { get : 'a list;
    len : int;
  }

let empty : 'a t =
  { get = []; len = 0 }

let length (s : 'a t) : int =
  s.len

let to_list (s : 'a t) : 'a list =
  s.get

let is_empty (s : 'a t) : bool =
  s.len = 0

let push (x : 'a) (s : 'a t) =
  { get = x :: s.get; len = s.len + 1 }

let pop (s : 'a t) : ('a * 'a t) option =
  match s.get with
  | [] -> None
  | (x :: xs) -> Some (x, { get = xs; len = s.len - 1 })

let cut (n : int) (s : 'a t) : ('a list * 'a t) option =
  let rec go (n : int) (s : 'a t) (acc : 'a list) : ('a list * 'a t) option =
    if n <= 0 then
      Some (acc, s)
    else
      match pop s with
      | None -> None
      | Some (x, s') -> go (n - 1) s' (x :: acc)
  in
  go n s []
