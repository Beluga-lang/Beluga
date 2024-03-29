open Support
open Beluga
open Beluga_syntax.Syncom
open Synint

let (dprintf, _, _) = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

module P = Prettyint.DefaultPrinter

type error =
  | IncompleteProof

exception Error of error
let throw e = raise (Error e)

type result = (error, Comp.exp) Either.t

(* peels off assumptions, prepending the appropriate mlam- and fn-expressions
 * along the way)
 *)
let rec unroll cD cG = function
  | Comp.TypArr (_, _, tau2) ->
     let (cD', cG', f) = unroll cD cG tau2 in
     let LF.Dec (cG', Comp.CTypDecl (x, _, _)) = cG' in
     (cD', cG', fun e -> Comp.Fn (Location.ghost, x, f e))
  | Comp.TypPiBox (_, _, tau2) ->
     let (cD', cG', f) = unroll cD cG tau2 in
     let LF.Dec (cD', LF.Decl { name = x; plicity; _ }) = cD' in
     ( cD'
     , cG'
     , fun e -> Comp.MLam (Location.ghost, x, f e, plicity)
     )
  | _ -> (cD, cG, fun e -> e)

let by cD cG i x tau =
  ( LF.Dec (cG, Comp.CTypDecl (x, tau, false))
  , fun e -> Comp.Let (Location.ghost, i, (x, e))
  )

let unbox cD cG i x cU modifier =
  let cU', s =
    Beluga.Check.Comp.apply_unbox_modifier_opt cD modifier cU
  in
  dprintf begin fun p ->
    p.fmt "[unbox] cU = @[%a@]"
      P.(fmt_ppr_cmp_meta_typ cD) cU
    end;
  let cD' = LF.(Dec (cD, Decl { name = x; typ = cU'; plicity = Plicity.explicit; inductivity = Inductivity.not_inductive })) in
  let t = LF.MShift 1 in
  let pat =
    Comp.PatMetaObj
      ( Location.ghost
      , ( Location.ghost
        , let open LF in
          match cU with
          | (ClTyp ( (MTyp _ | PTyp _), cPsi )) ->
             let tM =
               Root
                 ( Location.ghost
                 , MVar (Offset 1, s)
                 , Nil
                 , Plicity.explicit
                 )
             in
             ClObj (Context.dctxToHat (Whnf.cnormDCtx (cPsi, t)), MObj tM)
          | CTyp _ ->
             CObj (CtxVar (CtxOffset 1))
        )
      )
  in
  ( cD'
  , fun e ->
    let open Comp in
    let b = Branch (Location.ghost, LF.Empty, (cD', LF.Empty), pat, t, e) in
    Case (Location.ghost, PragmaCase, i, [b])
  )

(* translate a Harpoon proof into Beluga internal syntax *)
let rec proof cD cG (p : Comp.proof) tau : Comp.exp =
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
     | Comp.Unbox (i, x, cU, modifier) ->
        let (cD', f) = unbox cD cG i x cU modifier in
        let t = LF.MShift 1 in
        let cG' = Whnf.cnormGCtx (cG, t) in
        let tau' = Whnf.cnormCTyp (tau, t) in
        f (proof cD' cG' p' tau')
     end
  | Comp.Directive d -> directive cD cG d tau

and split_branch cD cG (cG_p, pat) t hyp tau =
  let tau_b = Whnf.cnormCTyp (tau, t) in
  let Comp.Hypothetical (_, h, p) = hyp in
  let cD_b, cG_b = Comp.(h.cD, h.cG) in
  let e = proof cD_b cG_b p tau_b in
  Comp.Branch
    ( Location.ghost
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

and directive cD cG (d : Comp.directive) tau : Comp.exp =
  match d with
  | Comp.Solve e_chk -> e_chk

  | Comp.Intros (Comp.Hypothetical (_, hyp, p)) ->
     let (cD', cG', LF.Empty, tau', t) =
       Check.Comp.unroll cD cG LF.Empty tau
     in
     (* cD' |- t : cD
        is a weakening meta-substitution *)
     let e = proof cD' cG' p tau' in
     let (cD_orig, cG_orig, f) = unroll cD' cG' tau in
     dprintf begin fun p ->
       p.fmt "[translate] [intros] @[<v>cD = @[%a@]\
              @,cD_orig = @[%a@]\
              @,cG = @[%a@]\
              @,cG_orig = @[%a@]@]"
         P.(fmt_ppr_lf_mctx l0) cD
         P.(fmt_ppr_lf_mctx l0) cD_orig
         P.(fmt_ppr_cmp_gctx cD l0) cG
         P.(fmt_ppr_cmp_gctx cD_orig l0) cG_orig
         end;
     assert (Whnf.convMCtx cD_orig cD && Whnf.convGCtx (cG_orig, Whnf.m_id) (cG, t));
     f e

  | Comp.MetaSplit (i, _, sbs) ->
     let bs = List.map (fun b -> meta_split_branch cD cG b tau) sbs in
     Comp.Case (Location.ghost, Comp.PragmaCase, i, bs)

  | Comp.CompSplit (i, _, sbs) ->
     let bs = List.map (fun b -> comp_split_branch cD cG b tau) sbs in
     Comp.Case (Location.ghost, Comp.PragmaCase, i, bs)

  | Comp.ContextSplit (i, _, sbs) ->
     let bs = List.map (fun b -> context_split_branch cD cG b tau) sbs in
     Comp.Case (Location.ghost, Comp.PragmaCase, i, bs)

  | Comp.ImpossibleSplit i -> Comp.Impossible (Location.ghost, i)

  | Comp.Suffices (i, args) ->
     (* FIXME: consider storing tau_i inside Suffices to avoid
        needing to synthesize it here? -je *)
     let _, ttau_i = Check.Comp.syn None cD cG [] i in
     let loc = Comp.loc_of_exp i in
     let _, (i', ttau_i') =
       Check.Comp.genMApp
         Location.ghost
         (Fun.const true)
         cD
         (i, ttau_i)
     in
     let tau_i' = Whnf.cnormCTyp ttau_i' in
     (* cD; cG |- i' ==> tau_i' *)
     let tau_args =
       List.map (fun (_, tau, _) -> `exact tau) args
     in
     (* here we use unify_suffices *after* having done genMApp so that
        the unification will instantiate the MMVars used as MApp
        arguments.
        We are essentially skipping the part of unify_suffices that
        eliminates PiBoxes for us.
      *)
     Check.Comp.unify_suffices loc cD tau_i' tau_args tau
     |> ignore;
     let es =
       List.map (fun (_, tau_p, p) -> proof cD cG p tau_p) args
     in
     Comp.apply_many i' es

let theorem thm tau = match thm with
  | Comp.Proof p -> proof LF.Empty LF.Empty p tau
  | Comp.Program e -> e

let trap f =
  try
    Either.right (f ())
  with
  | Error e -> Either.left e

let fmt_ppr_error ppf =
  function
  | IncompleteProof ->
     Format.fprintf ppf "The proof is incomplete."

let fmt_ppr_result ppf =
  function
  | Either.Right e ->
     Printer.with_implicits false
       begin fun _ ->
       Format.fprintf ppf
         "@[<v>Translation generated program:\
          @,  @[%a@]@,@,@]"
         P.(fmt_ppr_cmp_exp LF.Empty LF.Empty l0) e
       end
  | Either.Left err ->
     Format.fprintf ppf
       "@[<v>Translation failed.\
        @,@[%a@]@]"
       fmt_ppr_error err

let entry { Store.Cid.Comp.Entry.prog; typ = tau; name; _ } =
  let prog =
    match prog with
    | Option.Some prog -> prog
    | Option.None ->
      (Error.raise_violation
         (Format.asprintf
           "The body of theorem %a is unknown." Name.pp name))
  in
  let thm =
    match prog with
    | Comp.ThmValue (cid', thm, t, rho) ->
       assert (match rho with Comp.Empty -> true | _ -> false);
       assert (match t with LF.MShift 0 -> true | _ -> false);
       thm
    | _ ->
      Error.raise_violation
         "Looked up theorem is not a theorem value."
  in
  trap (fun () -> theorem thm tau)
