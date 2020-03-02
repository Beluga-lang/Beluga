open Support
open Beluga
open Syntax.Int
module Loc = Location

type error =
  | IncompleteProof

exception Error of error
let throw e = raise (Error e)

(* peels off assumptions, prepending the appropriate mlam- and fn-expressions
 * along the way)
 *)
let rec unroll cD cG = function
  | Comp.TypArr (_, _, tau2) ->
     let (cD', cG', f) = unroll cD cG tau2 in
     let LF.Dec (cG', Comp.CTypDecl (x, _, _)) = cG' in
     (cD', cG', fun e -> Comp.Fn (Loc.ghost, x, f e))
  | Comp.TypPiBox (_, _, tau2) ->
     let (cD', cG', f) = unroll cD cG tau2 in
     let LF.Dec (cD', LF.Decl (x, cU, _)) = cD' in
     (cD', cG', fun e -> Comp.MLam (Loc.ghost, x, f e))
  | _ -> (cD, cG, fun e -> e)

let by cD cG i x tau =
  ( LF.Dec (cG, Comp.CTypDecl (x, tau, false))
  , fun e -> Comp.Let (Loc.ghost, i, (x, e))
  )

let unbox cD cG i x cU =
  let cD' = LF.(Dec (cD, Decl (x, cU, No))) in
  let pat =
    Comp.PatMetaObj
      ( Loc.ghost
      , ( Loc.ghost
        , let open LF in
          match cU with
          | (ClTyp ( (MTyp tA | PTyp tA), cPsi )) ->
             let tM =
               Root
                 ( Loc.ghost
                 , MVar (Offset 1, LF.EmptySub)
                 , Nil
                 )
             in
             ClObj (Context.dctxToHat cPsi, MObj tM)
          | CTyp _ ->
             CObj (CtxVar (CtxOffset 1))
        )
      )
  in
  ( cD'
  , fun e ->
    let open Comp in
    let b = Branch (Loc.ghost, cD', cG, pat, LF.MShift 1, e) in
    Case (Loc.ghost, PragmaCase, i, [b])
  )

(* translate a Harpoon proof into Beluga internal syntax *)
let rec proof cD cG (p : Comp.proof) tau : Comp.exp_chk =
  match p with
  | Comp.Incomplete (_, g) ->
     begin match !Comp.(g.solution) with
     | Some p ->
        proof cD cG p tau
     | None -> throw IncompleteProof
     end

  | Comp.Command (cmd, p') ->
     begin match cmd with
     | Comp.By (i, x, tau') ->
        let (cG', f) = by cD cG i x tau' in
        f (proof cD cG' p' tau)
     | Comp.Unbox (i, x, cU) ->
        let (cD', f) = unbox cD cG i x cU in
        let t = LF.MShift 1 in
        let cG' = Whnf.cnormGCtx (cG, t) in
        let tau' = Whnf.cnormCTyp (tau, t) in
        f (proof cD' cG' p' tau')
     end
  | Comp.Directive d -> directive cD cG d tau

and directive cD cG (d : Comp.directive) tau : Comp.exp_chk =
  match d with
  | Comp.Intros (Comp.Hypothetical (hyp, p)) ->
     let (cD', cG', tau', _) = Check.Comp.unroll cD cG tau in
     let e = proof cD' cG' p tau' in
     let (cD_orig, cG_orig, f) = unroll cD' cG' tau in
     assert Whnf.(convMCtx cD_orig cD && convGCtx (cG_orig, m_id) (cG, m_id));
     f e
  | Comp.Solve e_chk -> e_chk
  | Comp.MetaSplit (e_syn, tau, m_branches) -> assert false
  | Comp.CompSplit (e_syn, tau, c_branches) -> assert false


let theorem thm tau = match thm with
  | Comp.Proof p -> proof LF.Empty LF.Empty p tau
  | Comp.Program e -> e

let trap f =
  try
    Either.Right (f ())
  with
  | Error e -> Either.Left e

let fmt_ppr_error ppf =
  let open Format in
  function
  | IncompleteProof ->
     fprintf ppf "The proof is incomplete."
