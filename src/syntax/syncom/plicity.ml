open Support

type t =
  | Implicit
  | Explicit

let implicit = Implicit

let explicit = Explicit

let max p1 p2 =
  match (p1, p2) with
  | Implicit, Implicit -> Implicit
  | _ -> Explicit

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = ( = )
  end) :
    Eq.EQ with type t := t)

let is_explicit = ( = ) explicit

let is_implicit = ( = ) implicit
