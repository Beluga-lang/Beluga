(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module F = Support.Misc.Function
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
open Support

let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [5])
open Debug.Fmt

module LF = Lfcheck
module List = Misc.List

module Comp = struct
  open Syntax

  module Unify = Unify.EmptyTrail
    (* NOTES on handling context variables: -bp
     *
     *  - We should maybe put context variables into a context Omega (not Delta)
     *    It makes it difficult to deal with branches.
     *
     *  Recall: Case(e, branches)  where branch 1 = Pi Delta1. box(psihat. tM1) : A1[Psi1] -> e1
     *
     *  Note that any context variable occurring in Delta, psihat, A and Psi is bound OUTSIDE.
     *  So if
     *
     *  D ; G |- Case (e, branches)  and ctxvar psi in D the branch 1 is actually well formed iff
     *
     *  D, D1 ; Psi1 |- tM1 <= tA1  (where only psi declared in D is relevant to the rest.)
     *
     *  Also, ctx variables are not subject to instantiations during unification / matching
     *  which is used in type checking and type reconstruction.
     *
     *  This has wider implications;
     *
     * - revise indexing structure; the offset of ctxvar is with respect to
     *   a context Omega
     *
     * - Applying substitution for context variables; does it make sense to
     *   deal with it lazily?   It seems complicated to handle lazy context substitutions
     *   AND lazy msubs.
     *
     *  If we keep them in Delta, we need to rewrite mctxToMSub for example;
     *)

  open Store
  open Cid
  module Loc = Syntax.Loc
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  type typeVariant =
    | VariantCross
    | VariantArrow
    | VariantCtxPi
    | VariantPiBox
    | VariantBox

  type mismatch_kind =
    [ `fn
    | `mlam
    | `box
    | `ctxfun
    | `pair
    ]

  type error =
    | IllegalParamTyp of I.mctx * I.dctx * I.typ
    | MismatchChk of I.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn of I.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped of I.mctx * gctx * pattern * tclo * tclo
    | BasicMismatch of mismatch_kind * I.mctx * gctx * tclo
    | SBoxMismatch of I.mctx * gctx * I.dctx * I.dctx
    | SynMismatch
      of I.mctx
         * tclo (* expected *)
         * tclo (* inferred *)
    | TypMismatch of I.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name option * string
    | InvalidRecCall
    | MissingTotal of Id.cid_prog
    | NotImpossible of I.mctx * gctx * typ * exp_syn
    | InvalidHypotheses
      of Int.Comp.hypotheses (* expected *)
         * Int.Comp.hypotheses (* actual *)
    | SufficesDecompositionFailed of I.mctx * typ
    | SufficesLengthsMismatch
      of I.mctx
         * typ (* type that was decomposed *)
         * int (* number of simple arguments in that type *)
         * int (* number of given types *)
    | SufficesBadAnnotation
      of I.mctx
         * typ (* suffices scrutinee's type *)
         * int (* index of the scrutinee premise that didn't unify *)
         * typ (* type annotation given by the user (valid in cD) *)
    | SufficesBadGoal
      of I.mctx
         * typ (* scrutinee type *)
         * typ (* goal type *)
    | SufficesPremiseNotClosed
      of I.mctx
         * int (* premise index *)
         * suffices_typ (* given type annotation *)

  exception Error of Syntax.Loc.t * error

  let throw loc e = raise (Error (loc, e))

  let convToParamTyp =
    function
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT

  (** Analyzes a contextual object to decide whether it's a
      (contextual) variable and rewrites its type from MTyp to PTyp if
      necessary. This is crucial for coverage checking of a case analysis
      on a parameter variable.
      Also returns the index of the variable (so we can later decide
      if it's a variable we're doing induction on) as well what
      projection, if any, is applied to the parameter variable.
   *)
  let fixParamTyp mC mT =
    match mC with
    (* cases for a parameter variable without a projection *)
    | I.(ClObj (_, PObj (PVar (x, _))))
      | I.(ClObj (_, MObj (Root (_, PVar (x, _), _, _)))) ->
       (Some x, convToParamTyp mT, None)
    (* cases for a parameter variable with a projection *)
    | I.(ClObj (_, PObj (Proj (PVar (x, _), k))))
      | I.(ClObj (_, MObj (Root (_, Proj (PVar (x, _), k), _, _)))) ->
       (Some x, convToParamTyp mT, Some k)
    (* cases for a context variable or a metavariable *)
    | I.(CObj (CtxVar (CtxOffset x)))
      | I.(ClObj (_, MObj (Root (_, MVar (Offset x, _), _, _)))) ->
       (Some x, mT, None)

    | _ -> (None, mT, None)

  let string_of_typeVariant =
    function
    | VariantCross -> "product type"
    | VariantArrow -> "function type"
    | VariantCtxPi -> "context abstraction"
    | VariantPiBox -> "dependent function type"
    | VariantBox -> "contextual type"

  let format_error ppf =
    let open Format in
    function
    | MissingTotal prog ->
       fprintf ppf "Function %s not known to be total."
         (R.render_cid_prog prog)
    | InvalidRecCall ->
       fprintf ppf "Recursive call not structurally smaller."
    | IllegalParamTyp (cD, cPsi, tA) ->
       fprintf ppf
         "Parameter type %a is illegal."
         (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tA, Substitution.LF.id))
    | UnsolvableConstraints (f, cnstrs) ->
       let fname =
         match f with
         | None -> ""
         | Some g -> " " ^ (Id.render_name g)
       in
       let msg1 =
         "Unification in type reconstruction encountered constraints \
          because the given signature contains unification problems \
          which fall outside the (decidable) pattern fragment;"
       in
       let msg2 =
         "there are meta-variables which are not only applied \
          to a distinct set of bound variables;"
       in
       let msg3 =
         "a meta-variable in the program depends on a context, but \
          that meta-varaible must be in fact closed."
       in
       let open Format in
       fprintf ppf
         "@[<v>%a@,@,\
          Common causes are:@,
          @[<v>\
          - @[%a@]@,\
          - @[%a@]@,@]@,@,\
          The constraint@,  @[%a@]@,\
          could not be solved.@,
          The program @[%a@] is considered ill-typed.@]"
         pp_print_string msg1
         pp_print_string msg2
         pp_print_string msg3
         pp_print_string cnstrs
         pp_print_string fname

    | MismatchChk (cD, cG, e, theta_tau (* expected *), theta_tau' (* inferred *)) ->
       Error.report_mismatch ppf
         "Ill-typed expression."
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau');
       fprintf ppf
         "In expression: %a@."
         (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e

    | MismatchSyn (cD, cG, i, variant, theta_tau) ->
       Error.report_mismatch ppf
         "Ill-typed expression."
         "Expected" pp_print_string (string_of_typeVariant variant)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau);
       fprintf ppf
         "In expression: %a@."
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i

    | PatIllTyped (cD, cG, pat, theta_tau (* expected *), theta_tau' (* inferred *)) ->
       Error.report_mismatch ppf
         "Ill-typed pattern."
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau');
       fprintf ppf
         "In pattern: %a@."
         (P.fmt_ppr_cmp_pattern cD cG P.l0) pat

    | BasicMismatch (k, cD, _, ttau) ->
       let tau = Whnf.cnormCTyp ttau in
       let print_mismatch_kind ppf : mismatch_kind -> unit =
         let p s = fprintf ppf "%s" s in
         function
         | `fn -> p "function abstraction"
         | `mlam -> p "meta abstraction (mlam)"
         | `ctxfun -> p "context abstraction"
         | `box -> p "box-expression"
         | `pair -> p "tuple"
       in
       fprintf ppf "@[<v>Found@,  %a@,but expected expression of type@,  %a@]"
         print_mismatch_kind k
         (P.fmt_ppr_cmp_typ cD P.l0) tau

    | SBoxMismatch (cD, _, cPsi, cPhi) ->
       fprintf ppf
         "Found substitution that does not have type %a[%a]."
         (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx cPsi)
         (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx cPhi)

    | SynMismatch (cD, theta_tau, theta_tau') ->
       Error.report_mismatch ppf
         "Ill-typed expression."
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau')

    | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
       Error.report_mismatch ppf
         "Type of destructor did not match the type it was expected to have."
         "Type of destructor" (P.fmt_ppr_cmp_typ cD P.l0)
         (Whnf.cnormCTyp (tau1, theta1))
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0)
         (Whnf.cnormCTyp (tau2, theta2))

    | NotImpossible (cD, cG, tau, i) ->
       fprintf ppf
         "@[<v>The expression@,  @[%a@]@,is not impossible.@,Its type@,  @[%a@]@,is (possibly) inhabited.@]"
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
         (P.fmt_ppr_cmp_typ cD P.l0) tau

    | InvalidHypotheses (exp, act) ->
       fprintf ppf
         "@[<v>Invalid hypotheses.\
          @,Expected hypotheses:\
          @,  @[%a@]
          @,Actual hypotheses:\
          @,  @[%a@]
          @]"
         P.fmt_ppr_cmp_hypotheses_listing exp
         P.fmt_ppr_cmp_hypotheses_listing act

    | SufficesDecompositionFailed (cD, tau) ->
       fprintf ppf
         "@[<v>Type decomposition failed.\
          @,The type\
          @,  @[%a@]\
          @,could not be decomposed.\
          @,@[%a@]@]"
         P.(fmt_ppr_cmp_typ cD l0) tau
         pp_print_string
         "Decomposition requires that the type consist of Pi-types
          following by arrow-types with no further Pi-types."

    | SufficesLengthsMismatch (cD, tau, exp_k, act_k) ->
       fprintf ppf
         "@[<v>Incorrect number of type annotations given.\
          @,The type\
          @,  @[%a@]\
          @,requires exactly\
          @,  %d\
          @,annotations, but\
          @,  %d\
          @,were provided.\
          @]"
         P.(fmt_ppr_cmp_typ cD l0) tau
         exp_k
         act_k

    | SufficesBadAnnotation (cD, tau_i, bad_index, tau_ann) ->
       fprintf ppf
         "@[<v>The provided type annotation\
          @,  @[%a@]\
          @,is not compatible with premise\
          @,  %d\
          @,of the synthesized type\
          @,  @[%a@]\
          @]"
         P.(fmt_ppr_cmp_typ cD l0) tau_ann
         bad_index
         P.(fmt_ppr_cmp_typ cD l0) tau_i

    | SufficesBadGoal (cD, tau_i, tau_goal) ->
       fprintf ppf
         "@[<v>Bad goal type.\
          @,The current goal type\
          @,  @[%a@]\
          @,is not compatible with the conclusion of\
          @,  @[%a@]
          @,`suffices' cannot be used in this case.
          @]"
         P.(fmt_ppr_cmp_typ cD l0) tau_goal
         P.(fmt_ppr_cmp_typ cD l0) tau_i

    | SufficesPremiseNotClosed (cD, k, stau) ->
       fprintf ppf
         "@[<v>Premise not closed.\
          @,The premise at position\
          @,  %d\
          @,namely\
          @,  @[%a@]\
          @,is not closed.@]"
         k
         P.(fmt_ppr_cmp_suffices_typ cD) stau

  let _ =
    Error.register_printer
      begin fun (Error (loc, err)) ->
      Error.print_with_location loc
        begin fun ppf ->
        Format.fprintf ppf "Type-checking error.@.";
        format_error ppf err
        end
      end

  (** Combines two sets of hypotheses.
      IHs and computational hypotheses are MShifted by the length of the appended cD !
      IHs are also shifted by the length of appended cG.
   *)
  let append_hypotheses (h1 : hypotheses) (h2 : hypotheses) : hypotheses =
    let { cD = cD1; cG = cG1; cIH = cIH1 } = h1 in
    let { cD = cD2; cG = cG2; cIH = cIH2 } = h2 in
    let t = I.MShift (Context.length cD2) in
    let cD = Context.append cD1 cD2 in
    let cG = Context.append (Whnf.cnormGCtx (cG1, t)) cG2 in
    let cIH =
      Context.append
        (Whnf.cnormIHCtx (cIH1, t)
         |> Total.shiftIH (Context.length cG2))
        cIH2
    in
    { cD; cG; cIH }

  (** Verifies that the pairs of contexts are convertible. *)
  let validate_contexts loc (cD, cD') (cG, cG') =
    if not Whnf.(convMCtx cD cD' && convGCtx (cG, m_id) (cG', m_id))
    then
      InvalidHypotheses
        ( { cD; cG; cIH = Int.LF.Empty }
        , { cD = cD'; cG = cG'; cIH = Int.LF.Empty }
        )
      |> throw loc;
    Context.(steal_mctx_names cD cD', steal_gctx_names cG cG')

  let apply_unbox_modifier cD modifier cU =
    match modifier with
    | `strengthened ->
       begin match cU with
       | Int.LF.CTyp _ ->
          (* TODO proper error; cannot strengthen a schema *)
          assert false
       | Int.LF.(ClTyp (mT, cPsi)) ->
          begin match mT with
          | Int.LF.(MTyp (Atom (_, a, _) as tA)) ->
             let (cPhi, lazy s_proj, lazy s_tup) = ConvSigma.gen_flattening cD cPsi in
             (* cPhi |- s_tup : cPsi *)
             let (ss', cPhi') =
               Subord.thin' cD a cPhi
               |> Pair.rmap Whnf.normDCtx
             in
             dprintf
               begin fun p ->
               p.fmt "[apply_unbox_modifier] @[<v>strengthening !\
                      @,cPhi' = @[%a@]@]"
                 P.(fmt_ppr_lf_dctx cD l0) cPhi'
               end;
             (* cPhi |- ss' : cPhi' *)
             let ssi' = S.LF.invert ss' in
             (* cPhi' |- ssi' : cPhi *)
             let ss_tup = S.LF.comp s_tup ssi' in
             let ss_proj = S.LF.comp ss' s_proj in
             (Int.LF.(ClTyp (MTyp (Whnf.normTyp (tA, ss_tup)), cPhi')), ss_proj)
          | _ ->
             (* TODO proper error; cannot strengthen non-atomic types. *)
             assert false
          end
       end

  let apply_unbox_modifier_opt cD modifier_opt =
    Maybe.(get_default (fun x -> (x, S.LF.id)) (modifier_opt $> apply_unbox_modifier cD))

  (** Marks the variable at index k in cD as Inductive. *)
  let mark_ind cD k =
    let rec lookup cD k' =
      match (cD, k') with
      | (I.Dec (cD, I.Decl (u, cdec,dep)), 1) ->
         I.Dec (cD, I.Decl (u, cdec, I.Inductive))

      | (I.Dec (_, I.DeclOpt (u, _)), 1) ->
         raise (Error.Violation "Expected declaration to have type")

      | (I.Dec (cD, dec), k') -> I.Dec (lookup cD (k' - 1), dec)
      | (I.Empty, _) ->
         raise (Error.Violation ("Meta-variable out of bounds -- looking for " ^ string_of_int k ^ "in context"))
    in
    lookup cD k

  let rec fmv_normal (cD : I.mctx) =
    function
    | I.Root (_, h, tS, _) -> fmv_spine (fmv_head cD h) tS
    | I.Lam (_, _, tM) -> fmv_normal cD tM
    | I.LFHole _ -> cD
    | I.Tuple (_, tuple) -> fmv_tuple cD tuple

  and fmv_head (cD : I.mctx) =
    function
    | I.MVar (I.Offset k, s) | I.PVar (k, s) ->
       fmv_subst (mark_ind cD k) s
    | I.Proj (h, _) -> fmv_head cD h
    | _ -> cD

  and fmv_tuple (cD : I.mctx) =
    function
    | I.Last tM -> fmv_normal cD tM
    | I.Cons (tM, tuple) -> fmv_tuple (fmv_normal cD tM) tuple

  and fmv_spine (cD : I.mctx) =
    function
    | I.Nil -> cD
    | I.App (tM, tS) -> fmv_spine (fmv_normal cD tM) tS

  and fmv_hat (cD : I.mctx) =
    function
    | (Some (I.CtxOffset k), _) -> mark_ind cD k
    | _ -> cD

  and fmv_dctx (cD : I.mctx) =
    function
    | I.Null -> cD
    | I.CtxVar (I.CtxOffset k) -> mark_ind cD k
    | I.DDec (cPsi, decl) -> fmv_decl (fmv_dctx cD cPsi) decl

  and fmv_decl (cD : I.mctx) =
    function
    | I.TypDecl (_, tA) -> fmv_typ cD tA
    | _ -> cD

  and fmv_typ (cD : I.mctx) =
    function
    | I.Atom (_, _, tS) -> fmv_spine cD tS
    | I.PiTyp ((decl, _), tA) -> fmv_typ (fmv_decl cD decl) tA
    | I.Sigma trec -> fmv_trec cD trec

  and fmv_trec (cD : I.mctx) =
    function
    | I.SigmaLast (_, tA) -> fmv_typ cD tA
    | I.SigmaElem (_, tA, trec) -> fmv_trec (fmv_typ cD tA) trec

  and fmv_subst (cD : I.mctx) =
    function
    | I.Dot (f, s) -> fmv_subst (fmv_front cD f) s
    | I.SVar (k, _, s) -> fmv_subst (mark_ind cD k) s
    | _ -> cD

  and fmv_front (cD : I.mctx) =
    function
    | I.Head h -> fmv_head cD h
    | I.Obj tM -> fmv_normal cD tM
    | I.Undef -> cD

  let fmv_mobj cD =
    function
    | (_, I.CObj (cPsi)) -> fmv_dctx cD cPsi
    | (_, I.ClObj (phat, I.MObj tM)) -> fmv_normal cD tM
    | (_, I.ClObj (phat, I.PObj h)) -> fmv_head (fmv_hat cD phat) h
    | (_, I.ClObj (phat, I.SObj s)) -> fmv_subst (fmv_hat cD phat) s

  let rec fmv cD =
    function
    | PatConst (_, _, pat_spine) -> fmv_pat_spine cD pat_spine
    | PatVar _
      | PatFVar _ -> cD
    | PatPair (_, pat1, pat2) -> fmv (fmv cD pat1) pat2
    | PatMetaObj (_, cM) -> fmv_mobj cD cM
    | PatAnn (_, pat, _, _) -> fmv cD pat

  and fmv_pat_spine cD =
    function
    | PatNil -> cD
    | PatApp (_, pat, pat_spine) ->
       fmv_pat_spine (fmv cD pat) pat_spine

  let mvars_in_patt cD pat = fmv cD pat

  let rec id_map_ind (cD1' : I.mctx) t (cD : I.mctx) : I.mctx =
    match (t, cD) with
    | (I.MShift k, I.Empty) -> cD1'
    | (I.MShift k, cD)
         when k < 0 ->
       raise (Error.Violation "Contextual substitution ill-formed")
    | (I.MDot _, I.Empty) ->
       Error.violation "Contextual substitution ill-formed"

    | (I.MShift k, cD) -> (* k >= 0 *)
       id_map_ind cD1' (I.MDot (I.MV (k+1), I.MShift (k+1))) cD

    | (I.MDot (I.MV u, ms), I.Dec (cD, I.Decl (_, mtyp1, dep))) ->
       if Total.is_inductive dep
       then
         begin
           let cD1' = mark_ind cD1' u in
           id_map_ind cD1' ms cD
         end
       else
         id_map_ind cD1' ms cD

    | (I.MDot (mf, ms), I.Dec (cD, I.Decl (_, mtyp1, dep))) ->
       begin match mf with
       | I.(ClObj (_, MObj (Root (_, MVar (Offset u, Shift 0), Nil, _))))
         | I.(ClObj (_, MObj (Root (_, PVar (u, Shift 0), Nil, _))))
         | I.(ClObj (_, PObj (PVar (u, Shift 0))))
         | I.(CObj (CtxVar (CtxOffset u)))
         | I.(ClObj (_, SObj (SVar (u, 0, Shift 0)))) ->
          if Total.is_inductive dep
          then
            begin
              let cD1' = mark_ind cD1' u in
              id_map_ind cD1' ms cD
            end
          else
            id_map_ind cD1' ms cD
       | _ -> id_map_ind cD1' ms cD
       end

  (*  let ind_to_string case_typ = match case_typ with
      | IndDataObj -> "IndDataObj"
      | IndIndexObj _ -> "IndIndexObj"
      | _ -> "NON-INDUCTIVE"
   *)

  (*  let is_ind _ _ = true
      match x with
      | I.Offset x, sigma ->
      let (_, tA, cPsi', dp) = Whnf.mctxMDec cD u in
      let d = match dep with
      | I.Inductive -> true
      | _ -> false in
      is_id sigma && dep
   *)

  let getLoc (loc, _) = loc

  let lookup cG k =
    Context.lookup' cG k
    |> Maybe.get
    |> fun (CTypDecl (u, tau, wf_tag)) ->
       (u, tau, wf_tag)

  let lookup' cG k =
    let (_, tau, _) = lookup cG k in
    tau

  (** Prepares the contexts for entering a branch.
      prepare_branch_contexts cD_b pat t cD cG cIH i total_decs
      computes (cD_b', cG_b, cIH_b)

      If
      * cD_b |- t : cD
      * cD |- cG gctx
      * cD_b; cG |- pat => tau_p
      * cD |- cIH ihctx
      * cD; cG |- i => tau_s
      then
      * cD_b' is convertible with cD_b, but containing annotations for
        induction.
      * cG_b = [t]cG
      * cIH_b = [t]cIH, cIH1, cIH2
        where cIH1 contains IHs generated from mvars in the pattern
        and cIH2 contains IHs generated from comp vars in the pattern
   *)
  let prepare_branch_contexts cD_b pat t cD (cG, cG_pat) cIH i total_decs =
    (*
    dprintf
      begin fun p ->
      p.fmt "@[<v 2>[directive] [check_branch]
             @,cD    = @[%a@]\
             @,cG    = @[%a@]\
             @,cIH   = @[%a@]\
             @,i     = @[%a@]\
             @,@[<hv 2>t     =@ @[%a@]@]\
             @]"
        P.(fmt_ppr_lf_mctx l0) cD
        P.(fmt_ppr_cmp_gctx cD l0) cG
        P.(fmt_ppr_cmp_ihctx cD cG) cIH
        P.(fmt_ppr_cmp_exp_syn cD cG l0) i
        P.fmt_ppr_lf_msub_typing (cD_b, t, cD)
      end;
     *)
    let (cD_b, cIH1) =
      if Total.is_inductive_split cD cG i && Total.struct_smaller pat
      then
        begin
          let cD1 = mvars_in_patt cD_b pat in
          let cIH = Total.wf_rec_calls cD1 I.Empty total_decs in
          dprnt "[prepare_branch_contexts] did it";
          (cD1, cIH)
        end
      else
        begin
          dprnt "[prepare_branch_contexts] nope";
          (cD_b, I.Empty)
        end
    in
    let cD_b = id_map_ind cD_b t cD in
    let cG_out_refined = Whnf.cnormGCtx (cG, t) in
    let cG_b =
      Context.append cG_out_refined
        (* if the pattern is smaller, then all comp vars coming from
           the pattern are potentially usable for induction (subject to
           compatibility with the totality declarations, later)
           so we mark all these variables with stars.
         *)
        begin
          if Total.struct_smaller pat
          then Total.mark_gctx cG_pat
          else cG_pat
        end
    in
    dprintf
      begin fun p ->
      p.fmt "[prepare_branch_contexts]\
             @[<v>@[<hv 2>cG_out =@ @[%a@]@]\
             @,@[<hv 2>cG_pat =@ @[%a@]@]\
             @,@[<hv 2>cD_b =@ @[%a@]@]@]"
        P.(fmt_ppr_cmp_gctx cD_b l0) cG_out_refined
        P.(fmt_ppr_cmp_gctx cD_b l0) cG_pat
        P.(fmt_ppr_lf_mctx l0) cD_b
      end;
    let cIH_b = Whnf.cnormIHCtx (cIH, t) in
    let cIH2 = Total.wf_rec_calls cD_b cG_b total_decs in
    let cIH_b = Context.concat [cIH_b; cIH1; cIH2] in
    dprintf
      begin fun p ->
      p.fmt "[prepare_branch_contexts] @[<hv>cIH_b =@ @[%a@]@]"
        P.(fmt_ppr_cmp_ihctx cD_b cG_b) cIH_b
      end;
    (cD_b, cG_b, cIH_b)

  (** Generates application of leading PiBox arguments (meta-applications).
      The applications are stacked onto `i` and the new `i` is returned
      together with its type (plus a delayed msub).
      The count of implicit arguments is also returned.
      You can configure the stopping condition via the given function
      argument: genMApp will eliminate a leading PiBoxes while the
      predicate returns true.
   *)
  let rec genMApp loc (p : Int.LF.ctyp_decl -> bool) cD (i, tau_t)
          : int * (Int.Comp.exp_syn * Int.Comp.tclo) =
    genMAppW loc p cD (i, Whnf.cwhnfCTyp tau_t)

  and genMAppW loc p cD (i, tau_t) =
    match tau_t with
    | (Int.Comp.TypPiBox (_, (Int.LF.Decl (u, cU, dep) as d), tau), theta)
         when p d ->
       let (cM, t') = Whnf.dotMMVar loc cD theta (u, cU, dep) in
       let i =
         Int.Comp.MApp
           ( loc
           , i
           , cM
           , Whnf.cnormMTyp (cU, theta)
           , Int.LF.Depend.to_plicity dep
           (* the MApp's plicity depends on the type of the PiBox that
              it eliminates. *)
           )
       in
       genMApp loc p cD (i, (tau, t'))
       |> Pair.lmap ((+) 1)

    | _ ->
       dprintf
         begin fun p ->
         p.fmt "[genMApp] @[<v>done:@,@[<hv>@[%a@] |-@ @[%a@]@]@]"
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp tau_t)
         end;
       (0, (i, tau_t))

  let rec checkParamTypeValid loc cD cPsi tA =
    let rec checkParamTypeValid' (cPsi0, n) =
      match cPsi0 with
      | Int.LF.Null -> () (* raise (Error (Syntax.Loc.ghost, IllegalParamTyp (cD, cPsi, tA))) *)
      | Int.LF.CtxVar psi ->
         (* tA is an instance of a schema block *)
         let { Schema.Entry.name; schema = Int.LF.Schema elems; decl = _ } =
           Schema.get (Context.lookupCtxVarSchema cD psi)
         in
         begin
           try
             ignore (LF.checkTypeAgainstSchema loc cD cPsi tA name elems)
           with
           | _ -> throw loc (IllegalParamTyp (cD, cPsi, tA))
         end

      | Syntax.Int.LF.DDec (cPsi0', Syntax.Int.LF.TypDecl (x, tB)) ->
         (* tA is instance of tB *)
         let tB' = Syntax.Int.LF.TClo (tB, Syntax.Int.LF.Shift n) in
         let ms = Ctxsub.mctxToMSub cD in
         let tB0 = Whnf.cnormTyp (tB', ms) in
         begin
           try
             Unify.unifyTyp cD cPsi (tA, Substitution.LF.id) (tB0, Substitution.LF.id)
           with
           | _ -> checkParamTypeValid' (cPsi0', n + 1)
         end
    in
    checkParamTypeValid' (cPsi, 1)

  and checkMetaSpine loc cD mS cKt =
    match (mS, cKt) with
    | (MetaNil, (Ctype _, _)) -> ()
    | (MetaApp (mO, mT, mS, plicity), (PiKind (_, I.Decl (_, ctyp, dep), cK), t)) ->
       if Stdlib.(<>) (Int.LF.Depend.to_plicity dep) plicity
       then Error.violation "[checkMetaSpine] plicity mismatch";
       let loc = getLoc mO in
       LF.checkMetaObj cD mO (ctyp, t);
       begin
         try
           (* need to use unification here instead of
              convertibility because ctyp might contain MMVars *)
           Unify.unifyMetaTyp cD (ctyp, t) (mT, C.m_id)
         with
         | Unify.Failure _ ->
            Error.violation
              ("[syn] type annotation not unifiable with PiBox type "
               ^ Fmt.stringify Loc.print_short loc
              )
       end;
       checkMetaSpine loc cD mS (cK, I.MDot (metaObjToMFront mO, t))

  let checkClTyp loc cD cPsi =
    function
    | I.MTyp tA ->
       LF.checkTyp cD cPsi (tA, S.LF.id)
    | I.PTyp tA ->
       LF.checkTyp cD cPsi (tA, S.LF.id);
       checkParamTypeValid loc cD cPsi tA
    | I.STyp (_, cPhi) ->
       LF.checkDCtx cD cPhi

  let checkCLFTyp loc cD =
    function
    | I.CTyp (Some schema_cid) ->
       begin
         try
           ignore (Schema.get_schema schema_cid)
         with
         | _ -> raise (Error.Violation "Schema undefined")
       end
    | I.CTyp None -> ()
    | I.ClTyp (tp, cPsi) ->
       LF.checkDCtx cD cPsi;
       checkClTyp loc cD cPsi tp

  let checkCDecl cD (I.Decl (x, ctyp, _)) =
    checkCLFTyp (Id.loc_of_name x) cD ctyp

  let rec checkKind cD =
    function
    | Ctype _ -> ()
    | PiKind (_, cdecl, cK) ->
       checkCDecl cD cdecl;
       checkKind (I.Dec (cD, cdecl)) cK

  let rec checkTyp cD =
    function
    | TypBase (loc, c, mS) ->
       let cK = (CompTyp.get c).CompTyp.Entry.kind in
       checkMetaSpine loc cD mS (cK, C.m_id)

    | TypCobase (loc, c, mS) ->
       let cK = (CompCotyp.get c).CompCotyp.Entry.kind in
       checkMetaSpine loc cD mS (cK, C.m_id)

    | TypBox (loc, ctyp) -> checkCLFTyp loc cD ctyp

    | TypArr (_, tau1, tau2) ->
       checkTyp cD tau1;
       checkTyp cD tau2

    | TypCross (_, tau1, tau2) ->
       checkTyp cD tau1;
       checkTyp cD tau2

    | TypPiBox (_, cdecl, tau') as tau ->
       dprintf
         begin fun p ->
         p.fmt "[checkCompTyp] @[%a@ |- %a@]"
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       checkCDecl cD cdecl;
       dprintf
         begin fun p ->
         p.fmt "[checkCompTyp] @[%a@ |- %a@]"
           (P.fmt_ppr_lf_mctx P.l0) (I.Dec (cD, cdecl))
           (P.fmt_ppr_cmp_typ (I.Dec (cD, cdecl)) P.l0) tau'
         end;
       checkTyp (I.Dec (cD, cdecl)) tau'

    | TypInd tau -> checkTyp cD tau


  (* extend_mctx cD (x, cdecl, t) = cD'

     if cD mctx
     cD' |- cU   where cdecl = _ : cU
     cD  |- t : cD
     the
     cD, x:[t]U  mctx

   *)
  let extend_mctx cD (x, (I.Decl (_, cU, dep)), t) =
    I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t), dep))

  let rec extract_var =
    function
    | Var (_, x) -> Some x
    | Apply (_, i, _) -> extract_var i
    | MApp (_, i, _, _, _) -> extract_var i
    | _ -> None

  let useIH loc cD cG cIH_opt e2 =
    match cIH_opt with
    | None -> None
    | Some cIH ->
       let cIH =
         match cIH with
         | I.Empty -> raise (Error (loc, InvalidRecCall))
         | cIH ->
            begin match e2 with
            | Box (_, cM, _) | Syn (_, AnnBox (cM, _)) ->
               dprintf
                 begin fun p ->
                 p.fmt "[useIH] @[<v>check whether compatible IH exists@,\
                        cIH = @[%a@]@,\
                        recursive call on: @[%a@]@]"
                   P.(fmt_ppr_cmp_ihctx cD cG) cIH
                   P.(fmt_ppr_cmp_meta_obj cD l0) cM
                 end;
               Total.filter cD cG cIH (loc, M cM)
            | Syn (_, i) ->
               begin match extract_var i with
               | Some x -> Total.filter cD cG cIH (loc, V x)
               | None -> Total.filter cD cG cIH (loc, E)
               end
            end
       in
       dprintf
         begin fun p ->
         p.fmt "[useIH] Partially used IH: %a"
           P.(fmt_ppr_cmp_ihctx cD cG) cIH
         end;
       (* We have now partially checked for the recursive call *)
       match cIH with
       | I.Dec (_, WfRec (_, [], _)) ->
          (* We have fully used a recursive call and we now are finished checking for well-formedness
             of rec. call. *)
          None
       | I.Empty -> raise (Error (loc, InvalidRecCall))
       | _ -> Some cIH

  (* check cD cG e (tau, theta) = ()
   *
   * Invariant:
   *
   * If  ; cD ; cG |- e wf-exp
   * and ; cD |- theta <= cD'
   * and ; cD'|- tau <= c_typ
   * returns ()
   * if  ; cD ; cG |- e <= [|t|]tau
   *
   * otherwise exception Error is raised
   *)

  let checkMetaObj cD cM cT t =
    try
      LF.checkMetaObj cD cM (cT, t);
      Typeinfo.Comp.add (getLoc cM)
        (Typeinfo.Comp.mk_entry cD (TypBox (getLoc cM, cT), t))
        ("Box " ^ Fmt.stringify (P.fmt_ppr_cmp_meta_obj cD P.l0) cM)
    with
    | Whnf.FreeMVar (I.FMVar (u, _)) ->
       Error.violation ("Free meta-variable " ^ Id.render_name u)

  let rec checkW mcid cD (cG, (cIH : ihctx)) total_decs e ttau =
    (** If cD; cG; cIH |- i ==> tau_sc then
        prepare_case_scrutinee_type i = tau_sc, tau_sc', projOpt
        * tau_sc is simply the synthesized type of the scrutinee.
          For calling checkBranches, this is what one must use.
        * tau_sc' is this type, but with the parameter type fix applied.
          This is the type that must be used as the scrutinee type for
          coverage checking, and ONLY for coverage checking.
        * projOpt must also be passed to coverage, to correctly check
          coverage on a projection. *)
    let prepare_case_scrutinee_type i =
       let (_, tau_sc, t') = syn mcid cD (cG, cIH) total_decs i in
       let tau_sc = Whnf.cnormCTyp (tau_sc, t') in
       match (i, tau_sc) with
       | (AnnBox ((l, mC), _), TypBox (loc, mT)) ->
          let (_, mT, projOpt) = fixParamTyp mC (Whnf.cnormMTyp (mT, C.m_id)) in
          (tau_sc, TypBox (loc, mT), projOpt)
       | _ -> (tau_sc, tau_sc, None)
    in
    match (e, ttau) with
    | (Fn (loc, x, e), (TypArr (_, tau1, tau2), t)) ->
       check mcid cD (I.Dec (cG, CTypDecl (x, Whnf.cnormCTyp (tau1, t), false)), (Total.shift cIH)) total_decs e (tau2, t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Fn " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (Fun (loc, fbr), _) ->
       checkFBranches mcid cD (cG, cIH) total_decs fbr ttau

    | (MLam (loc, u, e, _), (TypPiBox (_, cdec, tau), t)) ->
       check mcid (extend_mctx cD (u, cdec, t))
         (C.cnormGCtx (cG, I.MShift 1), C.cnormIHCtx (cIH, I.MShift 1)) total_decs e (tau, C.mvar_dot1 t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("MLam " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (Pair (loc, e1, e2), (TypCross (_, tau1, tau2), t)) ->
       check mcid cD (cG,cIH) total_decs e1 (tau1, t);
       check mcid cD (cG,cIH) total_decs e2 (tau2, t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Pair " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (Let (loc, i, (x, e)), (tau, t)) ->
       let (_, tau', t') = syn mcid cD (cG,cIH) total_decs i in
       let (tau', t') = C.cwhnfCTyp (tau',t') in
       let cG' = I.Dec (cG, CTypDecl (x, Whnf.cnormCTyp (tau', t'), false)) in
       check mcid cD (cG', Total.shift cIH) total_decs e (tau,t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Let " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
       let (_, tau', t') = syn mcid cD (cG,cIH) total_decs i in
       let (tau', t') = C.cwhnfCTyp (tau',t') in
       begin match (tau',t') with
       | (TypCross (_, tau1, tau2), t') ->
          let cG' =
            I.Dec
              ( I.Dec (cG, CTypDecl (x, Whnf.cnormCTyp (tau1, t'), false))
              , CTypDecl (y, Whnf.cnormCTyp (tau2, t'), false)
              )
          in
          check mcid cD (cG', (Total.shift (Total.shift cIH))) total_decs e (tau,t)
       | _ -> raise (Error.Violation "Case scrutinee not of product type")
       end

    | (Box (loc, cM, cU), (TypBox (l, cU'), t)) ->
       begin
         try
           Unify.unifyMetaTyp cD (cU, C.m_id) (cU', t)
         with
         | Unify.Failure _ ->
            Error.violation "[check] box's type annotation does not unify with target type"
       end;
       checkMetaObj cD cM cU' t

    | Impossible (loc, i), (tau, t) ->
       let (tau_sc, tau_sc', projOpt) = prepare_case_scrutinee_type i in
       if not (Coverage.is_impossible cD tau_sc')
       then throw loc (NotImpossible (cD, cG, tau_sc, i));

    | (Case (loc, prag, i, branches), (tau, t)) ->
       let (tau_sc, tau_sc', projOpt) = prepare_case_scrutinee_type i in
       (* Instead of None, we can give Some (l, cM) in order to start
          the coverage checker out with the current LF normal term.
          However, this causes some tests to fail, so we leave it out.
          Theoretically, this improves the coverage checker by
          allowing to consider more cases as covering, especially in
          situations with nested cases.  *)
       let problem = Coverage.make loc prag cD branches tau_sc' None in
       checkBranches mcid cD (cG,cIH) total_decs
         (i, tau_sc)
         branches
         (tau, t);
       Coverage.process problem projOpt

    | (Syn (loc, i), (tau, t)) ->
       dprint (fun () -> "check --> syn");
       let (_, tau', t') = syn mcid cD (cG,cIH) total_decs i in
       let (tau', t') = Whnf.cwhnfCTyp (tau', t') in
       let tau' = Whnf.cnormCTyp (tau', t') in
       let tau = Whnf.cnormCTyp (tau, t) in
       if C.convCTyp (tau, Whnf.m_id) (tau', Whnf.m_id)
       then
         Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
           ("Syn " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)
       else
         raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), (tau',t'))))

    | (Hole (loc, id, name), (tau, t)) ->
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Hole " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e);
       let open Holes in
       begin match get (by_id id) with
       | None ->
          let info = { Holes.cG; compGoal = (tau, t); compSolution = None } in
          let h = { Holes.loc; name; cD; info } in
          let h = Holes.Exists (Holes.CompInfo, h) in
          Holes.assign id h
       | Some (_, (Exists (w, h))) ->
          begin match w with
          | LFInfo -> Error.violation "wrong hole kind"
          | CompInfo ->
             let { compSolution; compGoal; _ } = h.info in
             if not (Whnf.convCTyp compGoal (tau, t))
             then Error.violation "mismatched hole type";
             begin match compSolution with
             | None -> ()
             | Some e -> checkW mcid cD (cG, cIH) total_decs e (tau, t)
             end
          end
       end
    | (e, ttau) ->
       dprintf
         begin fun p ->
         p.fmt "[checkW] @[<v>fallthrough for\
                @,e = @[%a@]\
                @,tau = @[%a@]@]"
           P.(fmt_ppr_cmp_exp_chk cD cG l0) e
           P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp ttau)
         end;
       Error.violation "[checkW] fallthrough"

  and check mcid cD (cG, cIH) total_decs e (tau, t) =
    dprintf
      begin fun p ->
      p.fmt "[check] @[<v>%a against\
             @,@[<hv 2>@[<v>%a@] |-@ @[%a@]@]@]"
        (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e
        (P.fmt_ppr_lf_mctx P.l0) cD
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau, t))
      end;
    checkW mcid cD (cG, cIH) total_decs e (C.cwhnfCTyp (tau, t));

  and syn mcid cD (cG,cIH) total_decs : exp_syn -> ihctx option * typ * I.msub =
    function
    | Var (loc, x) as e ->
       let (f,tau', _) = lookup cG x in
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau', C.m_id))
         ("Var " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);

       (* We need to strip the type of any variable here because check
          works with annotated types in general. So variables would
          get introduced with a star-type, but just one level deep. *)
       let tau =
         match Whnf.cnormCTyp (tau', Whnf.m_id) with
         | TypInd tau -> tau
         | _ -> tau'
       in
       (None, tau, C.m_id)

    | DataConst (loc, c) as e ->
       let tau = CompConst.((get c).Entry.typ) in
       Typeinfo.Comp.add loc
         (Typeinfo.Comp.mk_entry cD (tau, C.m_id))
         ("DataConst " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);
       (None, tau, C.m_id)

    | Obs (loc, e, t, obs) ->
       let tau0 = (CompDest.get obs).CompDest.Entry.obs_type in
       let tau1 = (CompDest.get obs).CompDest.Entry.return_type in
       check mcid cD (cG, cIH) total_decs e (tau0, t);
       (None, tau1, t)

    (* | DataDest (loc, c) -> *)
    (*     (dprint (fun () -> "DataDest ... "); *)
    (*     (None,(CompDest.get c).CompDest.typ, C.m_id)) *)

    | Const (loc, prog) as e ->
       let entry = Comp.get prog in
       let tau, d1, name =
         let open! Comp.Entry in
         entry.typ, entry.decl, entry.name
       in
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, C.m_id))
         ("Const " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);
       (* First we need to decide whether we are calling a function in
          the current mutual block. *)
       begin match Total.lookup_dec entry.Comp.Entry.name total_decs with
       | None -> (* No, we aren't. *)
          (* Since we're not calling a function in the mutual block,
             we need to decide whether the call is well-scoped.
             Harpoon violates the traditional scoping assumption that
             everything in the store is in scope: an incomplete
             harpoon proof could be defined before other functions,
             and we must prevent the user from calling those functions
             interactively, else the resulting proof script refer to
             out-of-scope values. *)
          ScopeCheck.thm_thm loc prog mcid;
          (None, tau, C.m_id)
       | Some d -> (* Yes we are, and d is its total dec *)
          (* Second, need to check whether the function we're calling
             actually requires totality checking. *)
          begin match option_of_total_dec_kind d.order with
          | None -> (* No, it doesn't. *)
             (None, tau, C.m_id)
          | Some _ -> (* yes, it actually requires totality checking *)
             Some cIH, tau, C.m_id
          end
       end

    | Apply (loc, e1, e2) as e ->
       let (cIH_opt, tau1, t1) = syn mcid cD (cG,cIH) total_decs e1 in
       let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
       begin match (tau1, t1) with
       | (TypArr (_, tau2, tau), t) ->
          check mcid cD (cG,cIH) total_decs e2 (tau2, t);
          Typeinfo.Comp.add
            loc
            (Typeinfo.Comp.mk_entry cD (tau, t))
            ("Apply " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);
          (useIH loc cD cG cIH_opt e2, tau, t)

       | (tau, t) ->
          raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
       end

    | MApp (loc, e, mC, cU, _) ->
       let (cIH_opt, tau1, t1) = syn mcid cD (cG, cIH) total_decs e in
       dprintf
         begin fun p ->
         p.fmt "[syn] @[<v>MApp synthesized function type at %a\
                @,tau1 = @[%a@]\
                @,cU = @[%a@]@]"
           Loc.print_short loc
           P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp (tau1, t1))
           P.(fmt_ppr_cmp_meta_typ cD) cU
         end;
       begin match (C.cwhnfCTyp (tau1,t1)) with
       | (TypPiBox (_, (I.Decl (_, ctyp, _)), tau), t) ->
          dprintf
            begin fun p ->
            p.fmt "[syn] @[<v>MApp\
                   @,cD = @[%a@]\
                   @,cU = @[%a@]\
                   @,@[<hv 2>@[%a@] <=?@ @[%a@]@]@]"
              P.(fmt_ppr_lf_mctx l0) cD
              P.(fmt_ppr_cmp_meta_typ cD) cU
              P.(fmt_ppr_cmp_meta_obj cD l0) mC
              P.(fmt_ppr_cmp_meta_typ cD) (C.cnormMTyp (ctyp, t))
            end;
          LF.checkMetaObj cD mC (ctyp, t);
          begin
            try
              (* need to use unification here instead of
                 convertibility because ctyp might contain MMVars *)
              Unify.unifyMetaTyp cD (ctyp, t) (cU, C.m_id)
            with
            | Unify.Failure _ ->
               Error.violation
                 ("[syn] type annotation not unifiable with PiBox type "
                  ^ Fmt.stringify Loc.print_short loc)
          end;
          dprintf
            begin fun p ->
            let open Maybe in
            ignore
              begin
                cIH_opt
                $> fun cIH ->
                   p.fmt "[syn] [MApp] @[<v>cIH = @[%a@]@]"
                     P.(fmt_ppr_cmp_ihctx cD cG) cIH
              end
            end;
          (useIH loc cD cG cIH_opt (Box (loc, mC, cU)), tau, I.MDot (metaObjToMFront mC, t))
       | (tau, t) ->
          raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
       end

    | PairVal (loc, i1, i2) ->
       let (_, tau1, t1) = syn mcid cD (cG, cIH) total_decs i1 in
       let (_, tau2, t2) = syn mcid cD (cG, cIH) total_decs i2 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       let (tau2, t2) = C.cwhnfCTyp (tau2, t2) in
       ( None
       , TypCross
           ( loc
           , TypClo (tau1, t1)
           , TypClo (tau2, t2)
           )
       , C.m_id
       )

    | AnnBox (cM, cT) ->
       checkMetaObj cD cM cT C.m_id;
       (None, TypBox (getLoc cM, cT), C.m_id)

  (* and synObs cD csp ttau1 ttau2 = match (csp, ttau1, ttau2) with *)
  (*   | (CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) -> *)
  (*       if Whnf.convCTyp (tau1, theta) (tau', theta') then *)
  (*         (tau2, theta) *)
  (*       else *)
  (*         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta')))) *)
  (*   | (CopatApp (loc, dest, csp'), (TypArr (tau1, tau2), theta), (tau', theta')) -> *)
  (*       if Whnf.convCTyp (tau1, theta) (tau', theta') then *)
  (*         synObs cD csp' ((CompDest.get dest).CompDest.typ, Whnf.m_id) (tau2, theta) *)
  (*       else *)
  (*         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta')))) *)

  and checkPattern cD cG pat ttau =
    match pat with
    | PatMetaObj (loc, mO) ->
       begin match ttau with
       | (TypBox (_, ctyp), theta) ->
          LF.checkMetaObj cD mO (ctyp, theta)
       | _ -> raise (Error (loc, BasicMismatch (`box, cD, I.Empty, ttau)))
       end
    | PatPair (loc, pat1, pat2) ->
       begin match ttau with
       | (TypCross (_, tau1, tau2), theta) ->
          checkPattern cD cG pat1 (tau1, theta);
          checkPattern cD cG pat2 (tau2, theta)
       | _ -> raise (Error (loc, BasicMismatch (`pair, cD, cG, ttau)))
       end

    | pat ->
       let (loc, ttau') = synPattern cD cG pat in
       let tau' = Whnf.cnormCTyp ttau' in
       let tau = Whnf.cnormCTyp ttau in
       let ttau' = (tau', Whnf.m_id) in
       let ttau = (tau, Whnf.m_id) in
       dprintf
         begin fun p ->
         p.fmt "[checkPattern] @[<v>Checking conv: @[%a@ ==@ %a@]@]"
           (P.fmt_ppr_cmp_typ cD P.l0) tau
           (P.fmt_ppr_cmp_typ cD P.l0) tau'
         end;
       if not (C.convCTyp ttau ttau')
       then raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG =
    function
    | PatConst (loc, c, pat_spine) ->
       let tau = (CompConst.get c).CompConst.Entry.typ in
       (loc, synPatSpine cD cG pat_spine (tau, C.m_id))
    | PatVar (loc, k) -> (loc, (lookup' cG k, C.m_id))
    | PatAnn (loc, pat, tau, _) ->
       checkPattern cD cG pat (tau, C.m_id);
       (loc, (tau, C.m_id))

    | PatFVar (_, x) ->
       dprintf
         begin fun p ->
         p.fmt "[synPattern] PatFVar %a impossible"
           Id.print x
         end;
       Error.violation "[synPattern] PatFVar impossible"
    | pat ->
       dprintf
         begin fun p ->
         p.fmt "[synPattern] @[<v>fallthrough for\
                @,pat = @[%a@]@]"
           P.(fmt_ppr_cmp_pattern cD cG l0) pat
         end;
       Error.violation "[synPattern] fallthrough"

  and synPatSpine cD cG pat_spine (tau, theta) =
    match pat_spine with
    | PatNil -> (tau, theta)
    | PatApp (_, pat, pat_spine) ->
       begin match (tau, theta) with
       | (TypArr (_, tau1, tau2), theta) ->
          checkPattern cD cG pat (tau1, theta);
          synPatSpine cD cG pat_spine (tau2, theta)
       | (TypPiBox (_, cdecl, tau), theta) ->
          let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
          synPatSpine cD cG pat_spine (tau, theta')
       end
    | PatObs (loc, obs, t, pat_spine) ->
       dprintf
         begin fun p ->
         p.fmt "[synPatSpine] t = %a"
           (P.fmt_ppr_lf_msub cD P.l0) t
         end;
       let tau0 = (CompDest.get obs).CompDest.Entry.obs_type in
       let tau1 = (CompDest.get obs).CompDest.Entry.return_type in
       if Whnf.convCTyp (tau,theta) (tau0,t)
       then synPatSpine cD cG pat_spine (tau1, t)
       else raise (Error (loc, TypMismatch (cD, (tau,theta), (tau0,t))))

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl (_, ctyp, _), theta) =
    LF.checkMetaObj cD mO (ctyp, theta);
    I.MDot (metaObjToMFront mO, theta)

  and checkBranches mcid cD cG total_decs (i, tau_s) bs ttau =
    List.iter
      begin fun b ->
      checkBranch mcid cD cG total_decs (i, tau_s) b ttau
      end
      bs

  and checkBranch mcid cD (cG, cIH) total_decs (i, tau_s) (Branch (loc, _, (cD_b, cG_pat), pat, t', e)) ttau =
    LF.checkMSub loc cD_b t' cD;
    let tau_p = Whnf.cnormCTyp (tau_s, t') in
    let (cD_b, cG_b, cIH_b) =
      prepare_branch_contexts cD_b pat t' cD (cG, cG_pat) cIH i total_decs
    in
    checkPattern cD_b cG_b pat (tau_p, Whnf.m_id);
    check mcid
      cD_b
      (cG_b, cIH_b)
      total_decs
      e
      (Pair.rmap (Whnf.mcomp' t') ttau)

  and checkFBranches mcid cD (cG, cIH) total_decs fbr ttau =
    match fbr with
    | NilFBranch _ -> ()
    | ConsFBranch (_, (cD', cG', patS, e), fbr') ->
       let (tau2', t') = synPatSpine cD' cG' patS ttau in
       dprintf
         begin fun p ->
         p.fmt "[checkFBranches] tau2' = @[%a@]"
           (P.fmt_ppr_cmp_typ cD' P.l0) (Whnf.cnormCTyp (tau2', t'))
         end;
       check mcid cD' (cG', (Total.shift cIH)) total_decs e (tau2', t');
       checkFBranches mcid cD (cG, cIH) total_decs fbr' ttau

  let rec wf_mctx =
    function
    | I.Empty -> ()
    | I.Dec (cD, cdecl) ->
       wf_mctx cD;
       checkCDecl cD cdecl

  (** See documentation in check.mli *)
  let decompose_function_type cD =
    let open Maybe in
    (* Checks that there are no interleaved Pis later and splits
       nested arrow types into a list of input types and one output type.
       Returns None if the type contained interleaved Pis (invalid type).
     *)
    let rec decomp_arrows =
      function
      | TypArr (_, tau_1, tau_2) ->
         decomp_arrows tau_2
         $> fun (inputs, output) -> (tau_1 :: inputs, output)
      | TypPiBox _ -> None
      | tau -> Some ([], tau) (* base type *)
    in
    let rec decomp_pis t =
      function
      | TypPiBox (loc, d, tau) ->
         let (_, t') = Whnf.dotMMVar loc cD t (Int.LF.require_decl d) in
         decomp_pis t' tau
      | tau -> (tau, t)
    in
    F.(decomp_arrows ++ Whnf.cnormCTyp ++ decomp_pis Whnf.m_id)

  (** See documentation in check.mli *)
  let unify_suffices loc cD tau_i (tau_anns : suffices_typ list) tau_g =
    dprintf
      begin fun p ->
      p.fmt "[unify_suffices] @[<v>tau_i = @[%a@]\
             @,@[<v 2>tau_anns =@,@[<v>%a@]@]\
             @,tau_g = @[%a@]@]"
        P.(fmt_ppr_cmp_typ cD l0) tau_i
        (Format.pp_print_list ~pp_sep:Format.pp_print_cut
           P.(fmt_ppr_cmp_suffices_typ cD))
        tau_anns
        P.(fmt_ppr_cmp_typ cD l0) tau_g
      end;
    match decompose_function_type cD tau_i with
    | None ->
       SufficesDecompositionFailed (cD, tau_i)
       |> throw loc
    | Some (tau_args, tau_out) ->
       let unify tau_1 tau_2 =
         try
           dprintf
             begin fun p ->
             p.fmt "[unify_suffices] @[<v>unifying @[%a@]@,\
                    against @[%a@]@]"
               P.(fmt_ppr_cmp_typ cD l0) tau_1
               P.(fmt_ppr_cmp_typ cD l0) tau_2
             end;
           Unify.unifyCompTyp cD
             (tau_1, Whnf.m_id)
             (tau_2, Whnf.m_id);
           (tau_2, true)
         with
         | Unify.Failure msg ->
            (tau_2, false)
       in
       let unify_s tau_1 = map_suffices_typ (unify tau_1) in
       let unify_anns taus1 taus2 =
         try
           List.mapi2 (fun i x y -> (i, (fun () -> unify_s x y), x, y)) taus1 taus2
         with
         | Invalid_argument _ ->
            let exp_k = List.length tau_args in
            let act_k = List.length tau_anns in
            SufficesLengthsMismatch (cD, tau_i, exp_k, act_k)
            |> throw loc
       in
       (* first unify the goal *)
       if unify tau_out tau_g |> snd |> not
       then SufficesBadGoal (cD, tau_i, tau_g) |> throw loc;

       (* Two phases:
          1. Unify *all* the arguments (that the user supplied)
          2. For each synthesized type we need to check that it is
             closed. *)
       unify_anns tau_args tau_anns
       |> List.map
            begin fun (i, f, tau_arg, tau_ann) ->
            let l = lazy (loc_of_suffices_typ tau_ann) in
            (* actually do the unification here *)
            match f () with
            | `infer loc ->
               (* user did not provide an explicit type *)
               (* instead, consider that the synthesized argument type
                  was specified by the user *)
               (i, lazy loc, Either.Left tau_arg)
            | `exact (tau_ann, true) ->
               (* user provided an explicit type & we could unify it *)
               (i, l, Either.Right tau_ann)
            | `exact (tau_ann, false) ->
               (* used provided an explicit type & we couldn't unify it *)
               SufficesBadAnnotation (cD, tau_i, (i + 1), tau_ann) |> throw loc
            end
       |> List.map
            begin fun (k, l, e) ->
            let open Either in
            match e with
            | Left tau_arg
                 when not (Whnf.closedCTyp tau_arg) ->
               SufficesPremiseNotClosed (cD, k, `infer (Lazy.force l))
               |> throw (Lazy.force l)

            | Right tau_ann
                 when not (Whnf.closedCTyp tau_ann) ->
               (* This error should be rare; perhaps it is impossible.
                  If the user provides an explicit type, how could the
                  unification result in a type still containing
                  MMVars? The only way I can think that this would
                  happen is if the user uses LF underscores. *)
               SufficesPremiseNotClosed
                 ( cD
                 , k
                 , `exact Whnf.(cnormCTyp (tau_ann, m_id))
                 )
               |> throw (Lazy.force l)

            | (Left tau_arg | Right tau_arg) -> tau_arg
            end

  let require_syn_typbox cD cG loc i (tau, t) =
    match tau with
    | TypBox (_, cU) -> (cU, t)
    | _ -> throw loc (MismatchSyn (cD, cG, i, VariantBox, (tau, t)))

  let rec unroll' cD cG tau =
    match tau with
    | TypPiBox (_, c_decl, tau') ->
       (* TODO ensure c_decl name is unique in context *)
       let cD' = I.Dec (cD, c_decl) in
       unroll' cD' cG tau' |> Pair.rmap ((+) 1)
    | TypArr (_, t1, t2) ->
       (* TODO use contextual name generation *)
       let name = Id.mk_name Id.NoName in
       let cG' = I.(Dec (cG, CTypDecl (name, t1, false))) in
       unroll' cD cG' t2
    | _ -> (cD, cG, tau), 0

  (* See documentation in check.mli *)
  let unroll cD cG cIH tau =
    (* cD |- cG <= ctx
       If we simply extend cG with the new entries computed from the
       TypArrs in tau, then the resulting context doesn't make sense
       anymore.
       Instead, we pass an initial empty context as cG to unroll' so as to calculate
       cG' s.t.
       cD' |- cG' <= ctx
       Then, we can compute the concatenation [t]cG, cG'
       as cD' |- [t]cG <= ctx, so
       cD' |- [t]cG, cG' <= ctx as required.
     *)
    let (cD', cG', tau'), k = unroll' cD I.Empty tau in
    (* to compute the weakening t, unroll' counts the number k of
       entries added to cD *)
    let t = I.MShift k in
    let cIH' =
      Whnf.cnormIHCtx (cIH, t)
      |> Total.shiftIH (Context.length cG')
    in
    ( cD'
    , Context.append (Whnf.cnormGCtx (cG, t)) cG'
    , cIH'
    , tau'
    , t
    )

  let rec proof mcid cD cG cIH total_decs p ttau =
    match p with
    | Incomplete (loc, g) ->
       (* TODO check that g's contexts and goal match the current
          contexts and goal up to inductivity metadata
        *)
       begin match !(g.solution) with
       | Some p -> proof mcid cD cG cIH total_decs p ttau
       | None ->
          begin match mcid with
          | None ->
             Error.violation "[check] [proof] no cid to register subgoal with"
          | Some cid ->
             let g =
               { g with
                 context = { cD; cG; cIH };
                 goal = ttau
               }
             in
             Holes.add_harpoon_subgoal (loc, (cid, g))
          end
       end

    | Command (cmd, p) ->
       let (cD, cG, cIH, t) = command mcid cD cG cIH total_decs cmd in
       let ttau = Pair.rmap (Whnf.mcomp' t) ttau in
       proof mcid cD cG cIH total_decs p ttau

    | Directive d ->
       dprnt "[check] [proof] --> directive";
       directive mcid cD cG cIH total_decs d ttau

  and command mcid cD cG cIH total_decs =
    let extend_meta d =
      let t = I.MShift 1 in
      ( I.Dec (cD, d)
      , Whnf.cnormGCtx (cG, t)
      , Whnf.cnormIHCtx (cIH, t)
      , t
      )
    in
    function
    | By (i, name, _) ->
       let (_, tau', t) = syn mcid cD (cG, cIH) total_decs i in
       let tau = Whnf.cnormCTyp (tau', t) in
       let cG = I.Dec (cG, CTypDecl (name, tau, false)) in
       (cD, cG, Total.shift cIH, Whnf.m_id)
    | Unbox (i, name, _, modifier) ->
       let (_, tau', t) = syn mcid cD (cG, cIH) total_decs i in
       dprintf
         begin fun p ->
         p.fmt "[check] [command] @[<v>@[<hv 2>by @[%a@] as@ %a@]\
                @,tau' = @[%a@]@]"
           P.(fmt_ppr_cmp_exp_syn cD cG l0) i
           Id.print name
           P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp (tau', t))
         end;
       let (cU, _) =
         require_syn_typbox cD cG Loc.ghost i (tau', t)
         |> Whnf.cnormMTyp
         |> apply_unbox_modifier_opt cD modifier
       in
       dprintf
         begin fun p ->
         p.fmt "[check] [command] [Unbox] result ctyp = @[%a@]"
           P.(fmt_ppr_cmp_meta_typ cD) cU
         end;
       extend_meta I.(Decl (name, cU, No))

  (** Check a hypothetical derivation.
      Ensures that the contexts in the hypothetical are convertible
      with the outer contexts before elaborating the body against
      ttau.
   *)
  and hypothetical mcid cD cG cIH total_decs (Hypothetical (loc, h, p) : hypothetical) ttau =
    let { cD = cD'; cG = cG'; cIH = I.Empty } = h in
    let (cD, cG) = validate_contexts loc (cD, cD') (cG, cG') in
    proof mcid cD cG cIH total_decs p ttau

  and directive mcid cD cG cIH total_decs (d : directive) ttau =
    let check_branch cG_pat pat t h i =
      let (cD_b, cG_b, cIH_b) =
        let Hypothetical (_, ctx, _) = h in
        prepare_branch_contexts ctx.cD pat t cD (cG, cG_pat) cIH i total_decs
      in
      let ttau_b = Pair.rmap (Whnf.mcomp' t) ttau in
      hypothetical mcid cD_b cG_b cIH_b total_decs h ttau_b
    in
    match d with
    | Intros hyp ->
       let tau = Whnf.cnormCTyp ttau in
       let (cD', cG', cIH', tau', t) = unroll cD cG cIH tau in
       dprintf
         begin fun p ->
         p.fmt "[check] [directive] @[<v>[intros] unroll\
                @,tau  = @[%a@]\
                @,tau' = @[%a@]\
                @,cD   = @[<v>%a@]\
                @,cD'  = @[<v>%a@]\
                @,cG   = @[<v>%a@]\
                @,cG'  = @[<v>%a@]@]"
           P.(fmt_ppr_cmp_typ cD l0) tau
           P.(fmt_ppr_cmp_typ cD' l0) tau'
           P.(fmt_ppr_lf_mctx l0) cD
           P.(fmt_ppr_lf_mctx l0) cD'
           P.(fmt_ppr_cmp_gctx cD l0) cG
           P.(fmt_ppr_cmp_gctx cD' l0) cG'
         end;
       hypothetical mcid cD' cG' cIH' total_decs hyp (tau', Whnf.m_id)

    | Solve e ->
       check mcid cD (cG, cIH) total_decs e ttau

    | ContextSplit (i, tau, bs) ->
       List.iter
         begin fun (SplitBranch (_, (cG_pat, pat), t, h)) ->
         check_branch cG_pat pat t h i
         end
         bs

    | MetaSplit (i, tau, bs) ->
       List.iter
         begin fun (SplitBranch (_, (cG_pat, pat), t, h)) ->
         check_branch cG_pat pat t h i
         end
         bs

    | CompSplit (i, tau, bs) ->
       List.iter
         begin fun (SplitBranch (_, (cG_pat, pat), t, h)) ->
         check_branch cG_pat pat t h i
         end
         bs

    | Suffices (i, args) ->
       (* TODO verify that `i` is not an IH call.
          IH is unsupported with Suffices
        *)
       let (cIH_opt, tau_i, t) = syn mcid cD (cG, cIH) total_decs i in
       let tau_i = Whnf.cnormCTyp (tau_i, t) in
       let tau_g = Whnf.cnormCTyp ttau in
       let loc = loc_of_exp_syn i in
       ignore (unify_suffices loc cD tau_i (List.map (fun (_, tau, _) -> `exact tau) args) tau_g);
       List.iter
         begin fun (_, tau, p) ->
         dprintf
           begin fun p ->
           p.fmt "[check] [directive] @[<v>suffices\
                  @,argument of type @[%a@]@]"
             P.(fmt_ppr_cmp_typ cD l0) tau
           end;
         proof mcid cD cG cIH total_decs p (tau, Whnf.m_id)
         end
         args

  let syn mcid cD cG (total_decs : total_dec list) ?cIH:(cIH = Syntax.Int.LF.Empty) e =
    let (cIH, tau, ms) = syn mcid cD (cG,cIH) total_decs e in
    (cIH, (tau, ms))

  let check mcid cD cG (total_decs : total_dec list) ?cIH:(cIH = Syntax.Int.LF.Empty) e ttau =
    check mcid cD (cG, cIH) total_decs e ttau

  let thm mcid cD cG total_decs ?cIH:(cIH = Syntax.Int.LF.Empty) t ttau =
    match t with
    | Syntax.Int.Comp.Program e -> check mcid cD cG total_decs ~cIH:cIH e ttau
    | Syntax.Int.Comp.Proof p -> proof mcid cD cG cIH total_decs p ttau

end
