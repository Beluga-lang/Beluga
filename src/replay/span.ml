open Support
open Loc

type loc = Loc.t

type t =
  { start : loc
  ; stop : loc
  }

let of_pair start stop =
  if Loc.(start <= stop) then Option.some { start; stop } else Option.none

exception InvalidSpan

let of_pair' (start : loc) (stop : loc) : t =
  of_pair start stop |> Option.get_or_else (fun () -> raise InvalidSpan)

let to_string (s : t) : string =
  let open Printf in
  if Int.(s.start.line = s.stop.line) then
    sprintf "line %d column %d-%d" s.start.line (column s.start)
      (column s.stop)
  else
    sprintf "line %d column %d to line %d column %d" s.start.line
      (column s.start) s.stop.line (column s.stop)
