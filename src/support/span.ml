open Loc
type loc = Loc.t

type t =
  { start : loc;
    stop : loc;
  }

let of_pair (start : loc) (stop : loc) : t option =
  if compare start stop <= 0 then
    Some { start = start; stop = stop }
  else
    None

exception InvalidSpan
let of_pair' (start : loc) (stop : loc) : t =
  of_pair start stop |>
    Maybe.eliminate
      (fun () -> raise InvalidSpan)
      (fun x -> x)

let to_string (s : t) : string =
  let open Printf in
  if s.start.line = s.stop.line then
    sprintf "line %d column %d-%d" s.start.line (column s.start) (column s.stop)
  else
    sprintf "line %d column %d to line %d column %d"
      s.start.line (column s.start) s.stop.line (column s.stop)
