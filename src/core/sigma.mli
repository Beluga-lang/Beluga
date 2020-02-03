module LF = Syntax.Int.LF

(** Calculates the type of a projection of a sigma.
    project k tH tRec = Some (tA, s)
    if k is a valid projection for tRec
    where tH is a head representing the parameter variable we're
    projecting.
 *)
val project : int -> LF.head -> LF.typ_rec -> LF.tclo option
