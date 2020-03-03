open Support
open Beluga
open Syntax.Int
module Loc = Location

module P = Pretty.Int.DefaultPrinter

type error =
  | IncompleteProof

exception Error of error
let throw e = raise (Error e)

type result = (error, Comp.exp_chk) Either.t

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
    let b = Branch (Loc.ghost, LF.Empty, (cD', cG), pat, LF.MShift 1, e) in
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

and split_branch cD cG (cG_p, pat) t hyp tau =
  let tau_b = Whnf.cnormCTyp (tau, t) in
  let Comp.Hypothetical (h, p) = hyp in
  let cD_b, cG_b = Comp.(h.cD, h.cG) in
  let e = proof cD_b cG_b p tau_b in
  Comp.Branch
    ( Loc.ghost
    , LF.Empty
    , (cD_b, cG_p)
    , pat
    , t
    , e
    )

and meta_split_branch cD cG (Comp.SplitBranch (_, (cG_p, pat), t, hyp)) tau =
  split_branch cD cG (cG_p, pat) t hyp tau

and comp_split_branch cD cG (Comp.SplitBranch (_, (cG_p, pat), t, hyp)) tau =
  split_branch cD cG (cG_p, pat) t hyp tau

and context_split_branch cD cG (Comp.SplitBranch (_, (cG_p, pat), t, hyp)) tau =
  split_branch cD cG (cG_p, pat) t hyp tau

and directive cD cG (d : Comp.directive) tau : Comp.exp_chk =
  match d with
  | Comp.Solve e_chk -> e_chk

  | Comp.Intros (Comp.Hypothetical (hyp, p)) ->
     let (cD', cG', tau', _) = Check.Comp.unroll cD cG tau in
     let e = proof cD' cG' p tau' in
     let (cD_orig, cG_orig, f) = unroll cD' cG' tau in
     assert Whnf.(convMCtx cD_orig cD && convGCtx (cG_orig, m_id) (cG, m_id));
     f e

  | Comp.MetaSplit (i, _, sbs) ->
     let bs = List.map (fun b -> meta_split_branch cD cG b tau) sbs in
     Comp.Case (Loc.ghost, Comp.PragmaCase, i, bs)

  | Comp.CompSplit (i, _, sbs) ->
     let bs = List.map (fun b -> comp_split_branch cD cG b tau) sbs in
     Comp.Case (Loc.ghost, Comp.PragmaCase, i, bs)

  | Comp.ContextSplit (i, _, sbs) ->
     let bs = List.map (fun b -> context_split_branch cD cG b tau) sbs in
     Comp.Case (Loc.ghost, Comp.PragmaCase, i, bs)

  | Comp.ImpossibleSplit i -> Comp.Impossible (Loc.ghost, i)

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

let fmt_ppr_result ppf =
  let open Format in
  function
  | Either.Right e ->
     fprintf ppf
       "@[<v>Translation generated program:\
        @,  @[%a@]@,@,@]"
       P.(fmt_ppr_cmp_exp_chk LF.Empty LF.Empty l0) e
  | Either.Left err ->
     fprintf ppf
       "@[<v>Translation failed.\
        @,@[%a@]@]"
       fmt_ppr_error err
