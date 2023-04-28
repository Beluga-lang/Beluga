open Support

type t =
  | Yes
  | Maybe
  | No

let yes = Yes

let maybe = Maybe

let no = No

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = ( = )
  end) :
    Eq.EQ with type t := t)
