open Support

type t =
  | Prefix
  | Infix
  | Postfix

let prefix = Prefix

let infix = Infix

let postfix = Postfix

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = Stdlib.( = )
  end) :
    Eq.EQ with type t := t)

let is_prefix = ( = ) Prefix

let is_infix = ( = ) Infix

let is_postfix = ( = ) Postfix
