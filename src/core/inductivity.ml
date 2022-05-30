type t =
  | Inductive
  | NotInductive

let not_inductive = NotInductive

let inductive = Inductive

let max ind1 ind2 =
  match (ind1, ind2) with
  | NotInductive, NotInductive -> NotInductive
  | _ -> Inductive

let is_not_inductive = ( = ) not_inductive

let is_inductive = ( = ) inductive
