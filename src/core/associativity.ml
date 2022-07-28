open Support

type t =
  | Left_associative
  | Right_associative
  | Non_associative

let left_associative = Left_associative

let right_associative = Right_associative

let non_associative = Non_associative

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = Stdlib.( = )
  end) :
    Eq.EQ with type t := t)

let is_left_associative = ( = ) Left_associative

let is_right_associative = ( = ) Right_associative

let is_non_associative = ( = ) Non_associative
