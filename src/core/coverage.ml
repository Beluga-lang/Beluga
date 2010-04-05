open Syntax.Int
open Syntax.Int.Comp

exception NoCover

let enableCoverage = ref false

let obj cO cD cPsi tA k = match tA with
(*
  | LF.PiTyp ((TypDecl(name, tA1), depend) as typdecl, tA2) ->
      obj cO cD (*extend cPsi *)cPsi tA2
          (fun cO cD _cPsi tM tA ->
             k cO cD cPsi (Lam(None, name, tM)) (PiTyp(typdecl, tA2)))
  | LF.Sigma typ_rec -> 
*)
  | LF.Atom (_loc, a, spine) -> raise NoCover

let covered_by branch cO cD cPsi tM tA = raise NoCover (* match branch with
  | BranchBox (cO', cD', (cPsi', tR', msub, csub), _body) ->
      (* under cO / cO' ?
         Pi cD. box(?. tM) : tA[cPsi]  =.  Pi cD'. box(?. tR') : ?[?]
                                                       *) *)

let covered_by_set branches cO cD cPsi tM tA = match branches with
  | [] -> raise NoCover
  | branch :: branches ->
      covered_by branch cO cD cPsi tM tA

(* covers : Int.LF.mctx -> Int.LF.mctx -> Int.Comp.ctyp_decl LF.ctx -> Int.Comp.branch list -> (Int.LF.typ * Int.LF.dctx) -> unit
 *
 * covers cO cD cG branches (tA, cPsi)
 *   returns () if the patterns in `branches' cover all values of tA[cPsi];
 *   otherwise, raises NoCover
 *
 * Also returns () if !enableCoverage is false.
 *)
let covers cO cD cG branches (tA, cPsi) =
  if not (!enableCoverage) then ()
  else
    let _ = print_string ("coverage check a case with " ^ string_of_int (List.length branches) ^ " branch(es)\n") in
      obj cO cD cPsi tA (covered_by_set branches)
