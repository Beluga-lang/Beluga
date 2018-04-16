open Loc
type loc = Loc.t
   
type t =
  { start : loc;
    stop : loc;
  }

let of_pair (start : loc) (stop : loc) : t Maybe.t =
  let open Maybe in
  if compare start stop <= 0 then
    Just { start = start; stop = stop }
  else
    Nothing

exception InvalidSpan
let of_pair' (start : loc) (stop : loc) : t =
  let open Maybe in
  match of_pair start stop with
  | Nothing -> raise InvalidSpan
  | Just x -> x

let to_string (s : t) : string =
  let open Printf in
  if s.start.line = s.stop.line then
    sprintf "line %d column %d-%d" s.start.line (column s.start) (column s.stop)
  else
    sprintf "line %d column %d to line %d column %d"
      s.start.line (column s.start) s.stop.line (column s.stop)
