open Beluga
module L = Syntax.Int.LF
module C = Syntax.Int.Comp
module Loc = Location

(* peels off assumptions, prepending the appropriate mlam- and fn-expressions
 * along the way)
 *)
let rec unroll cD cG term : C.exp_chk =
  match cD with
  | L.Dec (cD', L.Decl (name, _, _)) ->
      let t' = unroll cD' cG term in
      C.MLam (Loc.ghost, name, t')
  | L.Empty ->
      (match cG with
       | L.Dec (cG', C.CTypDecl (name, _, _)) ->
           let t' = unroll cD cG' term in
           C.Fn (Loc.ghost, name, t')
       | L.Empty -> term)

(* translate a Harpoon proof into Beluga internal syntax *)
let rec translate_proof cD cG (p : C.proof) tau : C.exp_chk =
  match p with
| C.Incomplete p_state -> Error.violation "Proof incomplete."
| C.Command (cmd, p') ->
    begin match cmd with
    | C.By (e_syn, name, tau, bty) ->
       let cG' = L.Dec (cG, C.CTypDecl (name, tau, false)) in
       C.Let (Loc.ghost, e_syn, (name, translate_proof cD cG' p' tau))
    | C.Unbox (e_syn, name, mT) ->
       let cD' = L.Dec (cD, L.Decl (name, mT, L.Maybe)) in
       begin match mT with
       | L.ClTyp (cltyp, psi) ->
          let n = L.Root (Loc.ghost, L.MVar (L.Offset 1, L.EmptySub), L.Nil) in
          let mfront = L.ClObj (Context.dctxToHat psi, L.MObj n) in
          let pat = C.PatMetaObj (Loc.ghost, (Loc.ghost, mfront)) in
          let body = translate_proof cD' cG p' tau in
          let b = C.Branch (Loc.ghost, cD', cG, pat, L.MShift 1, body) in
          C.Case (Loc.ghost, C.PragmaCase, e_syn, [b])
       | L.CTyp _ -> Error.violation "Syntax.Int.LF.CTyp found in Unbox."
       end
    end
| C.Directive d -> translate_directive cD cG d tau

and translate_directive cD cG (d : C.directive) tau : C.exp_chk =
  match d with
| C.Intros (C.Hypothetical (hyp, p)) ->
    let (cD', cG', tau') = Check.Comp.unroll cD cG tau in
    let term = translate_proof cD' cG' p tau in
    unroll cD cG term
| C.Solve e_chk -> e_chk
| C.MetaSplit (e_syn, tau, m_branches) -> assert false
| C.CompSplit (e_syn, tau, c_branches) -> assert false
