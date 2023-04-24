open Support

type t =
  | Inductive
  | Not_inductive

let not_inductive = Not_inductive

let inductive = Inductive

let max ind1 ind2 =
  match (ind1, ind2) with
  | Not_inductive, Not_inductive -> Not_inductive
  | _ -> Inductive

let min ind1 ind2 =
  match (ind1, ind2) with
  | Inductive, Inductive -> Inductive
  | _ -> Not_inductive

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = ( = )
  end) :
    Eq.EQ with type t := t)

let is_not_inductive = ( = ) not_inductive

let is_inductive = ( = ) inductive
