open Support

type t =
  | Inductive
  | NotInductive

let not_inductive = NotInductive

let inductive = Inductive

let max ind1 ind2 =
  match (ind1, ind2) with
  | NotInductive, NotInductive -> NotInductive
  | _ -> Inductive

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = ( = )
  end) :
    Eq.EQ with type t := t)

let is_not_inductive = ( = ) not_inductive

let is_inductive = ( = ) inductive
