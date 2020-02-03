module LF = Syntax.Int.LF

let rec project' fuel k tH s = function
  | LF.SigmaLast (_, tA) when fuel = 0 -> Some (tA, s)
  | LF.SigmaElem (_, tA, _) when fuel = 0 -> Some (tA, s)
  | LF.SigmaElem (_, tA, tRec) ->
     project' (fuel - 1) (k + 1) tH
       LF.(Dot (Head (Proj (tH, k)), s))
       tRec
  | _ -> None

let project k tH typ_rec = project' 1 (k - 1) tH (LF.Shift 0) typ_rec
