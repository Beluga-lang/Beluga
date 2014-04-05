(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5])

module LF = Lfcheck

module Comp = struct

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

  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type error =
    | IllegalParamTyp of I.mctx * I.dctx * I.typ
    | MismatchChk     of I.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of I.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of I.mctx * gctx * pattern * tclo * tclo
    | CtxFunMismatch  of I.mctx * gctx  * tclo
    | FunMismatch     of I.mctx * gctx  * tclo
    | MLamMismatch    of I.mctx * gctx  * tclo
    | PairMismatch    of I.mctx * gctx  * tclo
    | BoxMismatch     of I.mctx * gctx  * tclo
    | SBoxMismatch    of I.mctx * gctx  * I.dctx  * I.dctx
    | SynMismatch     of I.mctx * tclo (* expected *) * tclo (* inferred *)
    | BoxCtxMismatch  of I.mctx * I.dctx * (I.psi_hat * I.normal)
    | PattMismatch    of (I.mctx * I.dctx * I.normal option * I.tclo) *
                         (I.mctx * I.dctx * I.tclo)
    | IfMismatch      of I.mctx * gctx  * tclo
    | EqMismatch      of I.mctx * tclo (* arg1 *) * tclo (* arg2 *)
    | EqTyp           of I.mctx * tclo
    | MAppMismatch    of I.mctx * (meta_typ * I.msub)
    | AppMismatch     of I.mctx * (meta_typ * I.msub)
    | CtxHatMismatch  of I.mctx * I.dctx (* expected *) * I.psi_hat (* found *) * meta_obj
    | CtxMismatch     of I.mctx * I.dctx (* expected *) * I.dctx (* found *) * meta_obj
    | TypMismatch     of I.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name * string
    | InvalidRecCall

(*  type rec_call = bool *)

  exception Error of Syntax.Loc.t * error

  let string_of_typeVariant = function
    | VariantCross -> "product type"
    | VariantArrow -> "function type"
    | VariantCtxPi -> "context abstraction"
    | VariantPiBox -> "dependent function type"
    | VariantBox   -> "contextual type"

  let _ = Error.register_printer
    (fun (Error (loc, err)) ->
      Error.print_with_location loc (fun ppf ->
        match err with
          | InvalidRecCall ->
            Format.fprintf ppf "Recursive call not structurally smaller."
          | IllegalParamTyp (cD, cPsi, tA) ->
            Format.fprintf ppf
              "Parameter type %a is illegal."
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp (tA, Substitution.LF.id))
          | UnsolvableConstraints (f,cnstrs) ->
            Format.fprintf ppf
            "Unification in type reconstruction encountered constraints because the given signature contains unification problems which fall outside the decideable pattern fragment, i.e. there are meta-variables which are not only applied to a distinct set of bound variables. \n
The constraint \n \n %s \n\n was not solvable. \n \n The program  %s is ill-typed. If you believe the program should type check, then consider making explicit the meta-variables occurring in the non-pattern positions."
              cnstrs (R.render_name f)
          | CtxHatMismatch (cD, cPsi, phat, cM) ->
          let cPhi = Context.hatToDCtx (Whnf.cnorm_psihat phat Whnf.m_id) in
            Error.report_mismatch ppf
              "Type checking encountered ill-typed meta-object. This is a bug in type reconstruction."
              "Expected context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx  cPsi)
              "Given context" (P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl) cPhi;
              Format.fprintf ppf
                "In expression: %a@."
                (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM

          | CtxMismatch (cD, cPsi, cPhi, cM) ->
            Error.report_mismatch ppf
              "Type checking Ill-typed meta-object. This is a bug in type reconstruction."
              "Expected context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx  cPsi)
              "Given context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPhi);
              Format.fprintf ppf
                "In expression: %a@."
                (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM

          | MismatchChk (cD, cG, e, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
            Error.report_mismatch ppf
              "Ill-typed expression."
              "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau');
            Format.fprintf ppf
              "In expression: %a@."
              (P.fmt_ppr_cmp_exp_chk cD cG Pretty.std_lvl) e

          | MismatchSyn (cD, cG, i, variant, theta_tau) ->
            Error.report_mismatch ppf
              "Ill-typed expression."
              "Expected" Format.pp_print_string (string_of_typeVariant variant)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau);
            Format.fprintf ppf
              "In expression: %a@."
              (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i

          | PatIllTyped (cD, cG, pat, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau');
            Format.fprintf ppf
              "In pattern: %a@."
              (P.fmt_ppr_pat_obj cD cG Pretty.std_lvl) pat

          | PattMismatch ((cD, cPsi, pattern, sA) , (cD', cPsi', sA')) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type"
              (P.fmt_ppr_cmp_typ cD' Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, Whnf.normTyp sA', Whnf.normDCtx cPsi'))
              "Inferred type"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, Whnf.normTyp sA, Whnf.normDCtx cPsi))

          | BoxCtxMismatch (cD, cPsi, (phat, tM)) ->
            Format.fprintf ppf
              "Expected: %a\n  in context %a\n  Used in context %a"
              (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) tM
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl) (Context.hatToDCtx phat)

          | CtxFunMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found context abstraction, but expected type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | FunMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found function abstraction, but expected type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | MLamMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found MLam abstraction, but expected type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | BoxMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found box-expression that does not have type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | SBoxMismatch (cD, _cG, cPsi, cPhi) ->
            Format.fprintf ppf
              "Found substitution that does not have type %a[%a]."
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPhi)

          | IfMismatch (cD, _cG, theta_tau) ->
            Error.report_mismatch ppf
              "Type error in guard of if expression."
	      "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) TypBool
	      "Actual type"   (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | PairMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found tuple, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | SynMismatch (cD, theta_tau, theta_tau') ->
            Error.report_mismatch ppf
              "Ill-typed expression."
              "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau')

          | EqMismatch (cD, ttau1, ttau2) ->
            Error.report_mismatch ppf
              "Type mismatch on equality."
              "Type of LHS" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau1)
              "Type of RHS" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau2)

          | EqTyp (cD, ttau) ->
            Error.report_mismatch ppf
              "Equality comparison only possible at base types."
              "Expected type" Format.pp_print_string                "base type"
              "Actual type"   (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau)

          | AppMismatch (cD, (MetaTyp (tP, cPsi), theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, tP, cPsi), theta))

          | MAppMismatch (cD, (MetaTyp (tA, cPsi), theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, tA, cPsi), theta))

          | MAppMismatch (cD, (MetaSubTyp (cPhi, cPsi), theta)) ->
              let cPhi', cPsi'  = Whnf.cnormDCtx (cPhi, theta) , Whnf.cnormDCtx  (cPsi, theta) in
              let cdec = I.SDecl(Id.mk_name (Id.SVarName None), cPhi', cPsi') in
            Format.fprintf ppf
              "Expected contextual substitution object of type %a."
              (P.fmt_ppr_lf_ctyp_decl cD Pretty.std_lvl)
              cdec

          | MAppMismatch (cD, (MetaSchema cid_schema, tau)) ->
            Format.fprintf ppf
              "Expected context of schema %s."
              (R.render_cid_schema cid_schema)

          | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
              Error.report_mismatch ppf
                "Type of destructor did not match the type it was expected to have."
                "Type of destructor" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
                (Whnf.cnormCTyp (tau1, theta1))
                "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
                (Whnf.cnormCTyp (tau2, theta2))))

  type caseType =
    | IndexObj of I.psi_hat * I.normal
    | DataObj

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)


  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

  let rec isRecFun cIH f = match cIH with
    | I.Empty -> false
    | I.Dec(cIH, WfRec (f', _ , _ )) ->
      if f = f' then true
      else isRecFun cIH f


let checkParamTypeValid cD cPsi tA =
  let rec checkParamTypeValid' (cPsi0,n) = match cPsi0 with
  | Syntax.Int.LF.Null -> () (* raise (Error (Syntax.Loc.ghost, IllegalParamTyp  (cD, cPsi, tA))) *)
  | Syntax.Int.LF.CtxVar psi ->
     (* tA is an instance of a schema block *)
      let Syntax.Int.LF.Schema s_elems =
	Schema.get_schema (Context.lookupCtxVarSchema cD psi) in
      begin try
        let _ = LF.checkTypeAgainstSchema (Syntax.Loc.ghost) cD cPsi tA s_elems in ()
        with _ -> raise (Error (Syntax.Loc.ghost, IllegalParamTyp  (cD, cPsi, tA)))
      end

  | Syntax.Int.LF.DDec (cPsi0', Syntax.Int.LF.TypDecl (x, tB)) ->
     (* tA is instance of tB *)
    let tB' = Syntax.Int.LF.TClo(tB, Syntax.Int.LF.Shift (Syntax.Int.LF.NoCtxShift, n)) in
    let ms  = Ctxsub.mctxToMSub cD in
    let tB0 = Whnf.cnormTyp (tB', ms) in
    begin try Unify.unifyTyp cD cPsi (tA, Substitution.LF.id) (tB0, Substitution.LF.id) with
      | _ ->  checkParamTypeValid' (cPsi0', n+1)
    end
  in
  checkParamTypeValid' (cPsi , 1)



  let rec checkMetaObj loc cD cM cTt = match  (cM, cTt) with
  | (MetaCtx (loc, cPsi), (MetaSchema  w, _)) ->
      LF.checkSchema loc cD cPsi (Schema.get_schema w)

  | (MetaObj (loc, phat, tM), (MetaTyp (tA, cPsi), t)) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      if phat = Context.dctxToHat cPsi' then
        LF.check cD cPsi' (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id)
      else
        raise (Error (loc, CtxHatMismatch (cD, cPsi', phat, cM)))

  | (MetaObjAnn (loc, _cPhi, tM), (MetaTyp (tA, cPsi), t)) (* cPhi = cPsi *) ->
      LF.check cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id)

  | (MetaSObj (loc, phat, tM), (MetaSubTyp (tA, cPsi), t)) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      if phat = Context.dctxToHat cPsi' then
        LF.checkSub loc cD cPsi' tM (C.cnormDCtx (tA, t))
      else
        raise (Error (loc, CtxHatMismatch (cD, cPsi', phat, cM)))

  | (MetaSObjAnn (loc, _cPhi, tM), (MetaSubTyp (tA, cPsi), t)) ->
      LF.checkSub loc cD (C.cnormDCtx (cPsi, t)) tM (C.cnormDCtx (tA, t))

  | (MetaParam (loc, _phat, h), (MetaParamTyp (tA, cPsi), t)) ->
      let tA' = LF.inferHead loc cD (C.cnormDCtx (cPsi, t)) h in
      let tA  = C.cnormTyp (tA, t) in
        if Whnf.convTyp (tA, Substitution.LF.id) (tA', Substitution.LF.id) then ()
;

    (* The case for parameter types should be handled separately, for better error messages -bp *)


and checkMetaSpine loc cD mS cKt  = match (mS, cKt) with
  | (MetaNil , (Ctype _ , _ )) -> ()
  | (MetaApp (mO, mS), (PiKind (_, (cdecl, _ ), cK) , t)) ->
      begin match cdecl with
        | I.CDecl (_psi, schema_cid, _ ) ->
            let MetaCtx (_, cPsi) = mO in
            let theta' = I.MDot (I.CObj (cPsi), t) in
              checkMetaObj loc cD mO (MetaSchema schema_cid , t);
              checkMetaSpine loc cD mS (cK, theta')

        | I.MDecl (_u, tA, cPsi) ->
            let MetaObj (loc, psihat, tM) = mO in
              checkMetaObj loc cD mO (MetaTyp (tA, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.MObj(psihat, tM), t))

        | I.PDecl (_u, tA, cPsi) ->
            let MetaParam (loc, psihat, tM) = mO in
              checkMetaObj loc cD mO (MetaParamTyp (tA, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.PObj(psihat, tM), t))

        | I.SDecl (_u, cPhi, cPsi) ->
            let MetaSObj (loc, psihat, tM) = mO in
              checkMetaObj loc cD mO (MetaSubTyp (cPhi, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.SObj(psihat, tM), t))
    end


  let checkCDecl cD cdecl = match cdecl with
    | I.CDecl (_, schema_cid, _ ) ->
        begin try
          let _ = Schema.get_schema schema_cid in ()
        with _ -> raise (Error.Violation "Schema undefined")
        end
    | I.MDecl (_, tA, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)
    | I.PDecl (_, tA, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id);
        checkParamTypeValid cD cPsi tA

    | _ -> ()

  let rec checkKind cD cK = match cK with
    | Ctype _ -> ()
    | PiKind (_, ((I.CDecl _ ) as cdecl, dep), cK) ->
        checkCDecl cD cdecl;
        checkKind (I.Dec(cD, cdecl)) cK
    | PiKind (_, (cdecl,dep), cK) ->
        checkCDecl cD cdecl;
        checkKind (I.Dec(cD, cdecl)) cK

  let rec checkTyp cD tau =  match tau with
    | TypBase (loc, c, mS) ->
        let cK = (CompTyp.get c).CompTyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypCobase (loc, c, mS) ->
        let cK = (CompCotyp.get c).CompCotyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypBox (_ , tA, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)

    | TypSub (_ , cPhi, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkDCtx cD cPhi

    | TypArr (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2

    | TypCross (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2

    | TypPiBox ((cdecl, _), tau') ->
        dprint (fun () -> "[checkCompTyp] " ^
                  P.mctxToString cD ^ " |- " ^
                  P.compTypToString cD tau);
        checkCDecl cD cdecl;
        dprint (fun () -> "[checkCompTyp] " ^
                  P.mctxToString (I.Dec (cD, cdecl)) ^ " |- " ^
                  P.compTypToString (I.Dec (cD, cdecl)) tau');
        checkTyp (I.Dec (cD, cdecl)) tau'

    | TypBool -> ()

;;

let extend_mctx cD (x, (cdecl, dep), t) = match cdecl with
  | I.CDecl(_psi, schema,_ ) ->
      let dep' = match dep with Explicit -> I.No | Implicit -> I.Maybe in
        I.Dec(cD, I.CDecl(x, schema, dep'))
  | I.MDecl(_u, tA, cPsi) ->
      I.Dec(cD, I.MDecl(x, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t)))
  | I.PDecl(_u, tA, cPsi) ->
      I.Dec(cD, I.PDecl(x, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t)))
  | I.SDecl (_s, cPhi, cPsi) ->
      I.Dec(cD, I.SDecl(x, C.cnormDCtx (cPhi, t), C.cnormDCtx (cPsi, t)))

let useIH loc cD cG cIH_opt  e2 = match cIH_opt with
  | None -> None
  | Some cIH ->
  (* We are making a recursive call *)
    let cIH = match cIH with
      | I.Empty -> raise (Error (loc, InvalidRecCall))
      | cIH  -> match e2 with
          | Box (_,cM) -> Total.filter cD cG cIH (M cM)
          | Syn(_ , Var x)  -> Total.filter cD cG cIH (V x)
          | _      -> raise (Error (loc, InvalidRecCall))
    in
    let _ = dprint (fun () -> "[useIH] Partially used IH: " ^ Total.ih_to_string cD cIH) in
  (* We have now partially checked for the recursive call *)
    match cIH with
      | I.Dec(_ , WfRec (_, [], _ )) ->
      (* We have fully used a recursive call
           and we now are finished checking for well-formedness
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

  let rec checkW cD ((cG , cIH) : ctyp_decl I.ctx * ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (_, f, e), (tau, t)) ->
        check cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t))), cIH) e ttau

    | (Fun (_, x, e), (TypArr (tau1, tau2), t)) ->
        check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t))), cIH) e (tau2, t)

    | (Cofun (_, bs), (TypCobase (_, cid, sp), t)) ->
         let f = fun (CopatApp (loc, dest, csp), e') ->
           let ttau' = synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
           in check cD (cG,cIH) e' ttau'
         in let _ = List.map f bs in ()

    | (MLam (_, u, e), (TypPiBox (cdec, tau), t)) ->
        check (extend_mctx cD (u, cdec, t))
          (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (Pair (_, e1, e2), (TypCross (tau1, tau2), t)) ->
        check cD (cG,cIH) e1 (tau1, t);
        check cD (cG,cIH) e2 (tau2, t)

    | (Let (_, i, (x, e)), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
          check cD (cG',cIH) e (tau,t)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        begin match (tau',t') with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cD (cG',cIH) e (tau,t)
          | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
        end

    | (Box (_, MetaObj (_ , _phat, tM)), (TypBox (_, tA, cPsi), t)) ->
        begin try
        let _ = dprint (fun () -> "[comp check ] " ^
	  P.mctxToString cD ^ " ; " ^
	  P.dctxToString cD cPsi ^ " |- " ^
	  P.normalToString cD cPsi (tM, S.LF.id) ^
          " <= " ^ P.typToString cD cPsi (tA, S.LF.id) ) in
            LF.check cD  cPsi (tM, S.LF.id) (tA, S.LF.id)
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Error.Violation ("Free meta-variable " ^ (R.render_name u)))
        end

    | (Case (loc, prag, Ann (Box (_, MetaObj(_, phat, tR)), TypBox (_, tA', cPsi')),
             branches), (tau, t)) ->
        let (tau_sc, projOpt) =  (match tR with
                   | I.Root (_, I.PVar _ , _ ) ->
                       (TypParam (loc, Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi'), None)
                   | I.Root (_, I.Proj (I.PVar _, k ), _ ) ->
                       (TypParam (loc, Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi'), Some k)
                   | _ ->
                       (TypBox (loc, Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi'), None)) in
        let tau_s = TypBox (loc, Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi') in
        let _  = LF.check cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in
        let problem = Coverage.make loc prag cD branches tau_sc in
          (* Coverage.stage problem; *)
          checkBranches (IndexObj (phat, tR)) cD (cG,cIH) branches tau_s (tau, t);
          Coverage.process problem projOpt

    | (Case (loc, prag, i, branches), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        begin match C.cwhnfCTyp (tau',t') with
          | (TypBox (loc', tA, cPsi),  t') ->
              let tau_s = TypBox (loc', C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) in
              let _ = dprint (fun () -> "[check] Case - Scrutinee " ^
                                P.expSynToString cD cG i ^
                                "\n   has type " ^ P.compTypToString cD tau_s)
              in
              let problem = Coverage.make loc prag cD branches tau_s in
              (* Coverage.stage problem; *)
                checkBranches DataObj cD (cG,cIH) branches tau_s (tau,t);
                Coverage.process problem None
          | (tau',t') ->
              let problem = Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) in
              checkBranches DataObj cD (cG,cIH) branches (C.cnormCTyp (tau', t')) (tau,t);
                Coverage.process problem None
        end

    | (Syn (loc, i), (tau, t)) ->
        let (_, tau',t') = syn cD (cG,cIH) i in
        let (tau',t') = Whnf.cwhnfCTyp (tau',t') in
        if C.convCTyp (tau,t)  (tau',t') then
          ()
        else
          raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), (tau',t'))))

    | (If (loc, i, e1, e2), (tau,t)) ->
        let (_flag, tau', t') = syn cD (cG,cIH) i in
        let (tau',t') = C.cwhnfCTyp (tau',t') in
          begin match  (tau',t') with
          | (TypBool , _ ) ->
              (check cD (cG,cIH) e1 (tau,t) ;
               check cD (cG,cIH) e1 (tau,t) )
          | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
        end

    | (Hole (_loc), (_tau, _t)) -> ()

  and check cD (cG, cIH) e (tau, t) =
    let _ =  dprint (fun () -> "[check]  " ^
                       P.expChkToString cD cG e ^
                        " against \n    " ^
                  P.mctxToString cD ^ " |- " ^
                  P.compTypToString cD (Whnf.cnormCTyp (tau, t))) in
    checkW cD (cG, cIH) e (C.cwhnfCTyp (tau, t));

  and syn cD (cG,cIH) e : (gctx option * typ * I.msub) = match e with
    | Var x   ->
      let (f,tau) = lookup cG x in
      if isRecFun cIH f then
        (Some cIH, tau, C.m_id)
      else
        (None, tau, C.m_id)

    | DataConst c ->
        (None,(CompConst.get c).CompConst.typ, C.m_id)
    | DataDest c ->
        (None,(CompDest.get c).CompDest.typ, C.m_id)

    | Const prog ->
        (None,(Comp.get prog).Comp.typ, C.m_id)

    | Apply (loc , e1, e2) ->
        let (cIH_opt , tau1, t1) = syn cD (cG,cIH) e1 in
        let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
        begin match (tau1, t1) with
          | (TypArr (tau2, tau), t) ->
              dprint (fun () -> "[SYN: APPLY ] synthesized type  " ^
                     P.compTypToString cD (Whnf.cnormCTyp (TypArr (tau2, tau), t) ));
              dprint (fun () -> ("[check: APPLY] argument has appropriate type " ^
                                       P.expChkToString cD cG e2));
              dprint (fun () -> "[check: APPLY] cG " ^ P.gctxToString cD cG );
              dprint (fun () -> match cIH_opt with
                | None -> "" | Some ih -> "[APPLY IH] IH = " ^ Total.ih_to_string cD ih);
              check cD (cG,cIH) e2 (tau2, t);
              (useIH loc cD cG cIH_opt e2, tau, t)
          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
        end

    | MApp (loc, e, mC) ->
        let (rec_flag, tau, t) = syn cD (cG,cIH) e in
        let (tau,t) = C.cwhnfCTyp (tau,t) in
        begin match (mC, (rec_flag, tau, t)) with
          | (MetaCtx (loc, cPsi), (None, TypPiBox ((I.CDecl (_ , w, _ ), _ ), tau), t)) ->
              let theta' = I.MDot (I.CObj (cPsi), t) in
              LF.checkSchema loc cD cPsi (Schema.get_schema w);
              (dprint (fun () -> "[check: syn] cPsi = " ^ P.dctxToString cD cPsi );
               dprint (fun () -> "[check: syn] tau1 = " ^
                          P.compTypToString cD (Whnf.cnormCTyp (tau, theta') ))) ;
                 (None, tau, theta')
          | (MetaObj (loc, psihat, tM) , (None, TypPiBox ((I.MDecl (_u, tA, cPsi), _ ), tau), t)) ->
              checkMetaObj loc cD mC (MetaTyp (tA, cPsi), t) ;
              (None, tau, I.MDot(I.MObj (psihat, tM), t))
          | (MetaParam(_, phat, h), (None, TypPiBox ((I.PDecl(_, tA, cPsi), _ ), tau), t)) ->
              let _ =  dprint (fun () -> "[check: inferHead] cPsi = " ^
                                 P.dctxToString cD (C.cnormDCtx (cPsi,t) )) in
              let tB = LF.inferHead loc cD (C.cnormDCtx (cPsi,t)) h in
                if Whnf.convTyp (tB, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) then
                  (None, tau, I.MDot(I.PObj (phat, h), t))
                else
                  raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
          | (MetaSObj(_, phat, s), (None, TypPiBox ((I.SDecl(_, tA, cPsi), _ ), tau), t)) ->
              LF.checkSub loc cD (C.cnormDCtx (cPsi, t)) s (C.cnormDCtx (tA, t));
              (None, tau, I.MDot(I.SObj (phat, s), t))
          | ( _ , (_ , ((TypPiBox ((I.CDecl _ , _ ), _ )) as tau), t) ) ->
              raise (Error (loc, MismatchSyn (cD, cG, e, VariantCtxPi, (tau,t))))
          | (_ , (_ , tau, t)) ->
              raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
        end

    | PairVal (loc, i1, i2) ->
        let (_, tau1,t1) =  syn cD (cG,cIH) i1 in
        let (_, tau2,t2) =  syn cD (cG,cIH) i2 in
        let (tau1,t1)    = C.cwhnfCTyp (tau1, t1) in
        let (tau2,t2)    = C.cwhnfCTyp (tau2, t2) in
          (None, TypCross (TypClo (tau1,t1),
                            TypClo (tau2,t2)), C.m_id)


    | Ann (e, tau) ->
        check cD (cG, cIH) e (tau, C.m_id);
        (None, tau, C.m_id)

    | Equal(loc, i1, i2) ->
         let (_, tau1, t1) = syn cD (cG,cIH) i1 in
         let (_, tau2, t2) = syn cD (cG,cIH) i2 in
           if Whnf.convCTyp (tau1,t1) (tau2,t2) then
             begin match Whnf.cwhnfCTyp (tau1,t1) with
               | (TypBox _ , _ ) ->  (None, TypBool, C.m_id)
               | (TypBool, _ )   ->  (None, TypBool, C.m_id)
               | (tau1,t1)       ->  raise (Error (loc, EqTyp (cD, (tau1,t1))))
             end

           else
             raise (Error(loc, EqMismatch (cD, (tau1,t1), (tau2,t2))))

    | Boolean _  -> (None, TypBool, C.m_id)

  and synObs cD csp ttau1 ttau2 = match (csp, ttau1, ttau2) with
    | (CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) ->
        if Whnf.convCTyp (tau1, theta) (tau', theta') then
          (tau2, theta)
        else
          raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))
    | (CopatApp (loc, dest, csp'), (TypArr (tau1, tau2), theta), (tau', theta')) ->
        if Whnf.convCTyp (tau1, theta) (tau', theta') then
          synObs cD csp' ((CompDest.get dest).CompDest.typ, Whnf.m_id) (tau2, theta)
        else
          raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))

  and checkPattern cD cG pat ttau = match pat with
    | PatEmpty (loc, cPsi) ->
        (match ttau with
          | (TypBox (_, tA, cPhi) , theta) ->
              let _ = dprint (fun () -> "[checkPattern] PatEmpty : \n cD = " ^
                                P.mctxToString cD ^
                                "context of expected  type " ^
                                P.dctxToString cD (Whnf.cnormDCtx (cPhi, theta))
                                ^ "\n context given " ^ P.dctxToString cD cPsi) in
              if C.convDCtx (Whnf.cnormDCtx (cPhi, theta)) cPsi then ()
              else
                raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
          | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
        )

    | PatMetaObj (loc, mO) ->
        (match ttau with
          | (TypBox (_, tA, cPsi) , theta) ->
              checkMetaObj loc cD mO (MetaTyp (tA, cPsi), theta)
          | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
        )
    | PatPair (loc, pat1, pat2) ->
        (match ttau with
           | (TypCross (tau1, tau2), theta) ->
               checkPattern cD cG pat1 (tau1, theta);
               checkPattern cD cG pat2 (tau2, theta)
           | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau))))

    | pat ->
        let (loc, ttau') = synPattern cD cG pat in
        let tau' = Whnf.cnormCTyp ttau' in
        let tau = Whnf.cnormCTyp ttau in
        let ttau' = (tau', Whnf.m_id) in
        let ttau = (tau, Whnf.m_id) in
        let _ = dprint (fun () -> "\n Checking conv: " ^ P.compTypToString cD tau
        ^ "\n == " ^ P.compTypToString cD tau' ^ "\n") in
          if C.convCTyp ttau  ttau' then ()
          else
            raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat = match pat with
    | PatConst (loc, c, pat_spine) ->
        let tau = (CompConst.get c).CompConst.typ in
          (loc, synPatSpine cD cG pat_spine (tau , C.m_id))
    | PatVar (loc, k) -> (loc, (lookup' cG k, C.m_id))
    | PatTrue loc -> (loc, (TypBool, C.m_id))
    | PatFalse loc -> (loc, (TypBool, C.m_id))
    | PatAnn (loc, pat, tau) ->
        checkPattern cD cG pat (tau, C.m_id);
        (loc, (tau, C.m_id))

  and synPatSpine cD cG pat_spine (tau, theta) = match pat_spine with
    | PatNil  -> (tau, theta)
    | PatApp (_loc, pat, pat_spine)  ->
      begin match (tau, theta) with
        | (TypArr (tau1, tau2), theta) ->
          checkPattern cD cG pat (tau1, theta);
          synPatSpine cD cG pat_spine (tau2, theta)
        | (TypPiBox ((cdecl, _), tau), theta) ->
          let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
          synPatSpine cD cG pat_spine (tau, theta')
      end

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (cdecl, theta) = match cdecl with
    | I.MDecl (_, tA, cPsi) ->
        let _ = checkMetaObj loc cD mO (MetaTyp (tA, cPsi), theta) in
          (match mO with
            | MetaObj (_, phat, tM) ->  I.MDot(I.MObj(phat, tM), theta)
            | MetaObjAnn (_, cPsi, tM) -> I.MDot (I.MObj(Context.dctxToHat cPsi, tM), theta)
          )
    | I.PDecl (_, tA, cPsi) ->
        let _ = checkMetaObj loc cD mO (MetaParamTyp (tA, cPsi), theta) in
          (match mO with
            | MetaParam (_, phat, h) ->  I.MDot(I.PObj(phat, h), theta)
          )
    | I.SDecl (_, cPhi, cPsi) ->
        let _ = checkMetaObj loc cD mO (MetaSubTyp (cPhi, cPsi), theta) in
          (match mO with
            | MetaSObj (_, phat, s) ->  I.MDot(I.SObj(phat, s), theta)
            | MetaSObjAnn (_, cPsi, s) -> I.MDot (I.SObj(Context.dctxToHat cPsi, s), theta)
          )
    | I.CDecl (_, w, _ ) ->
        let _ = checkMetaObj loc cD mO (MetaSchema w, theta) in
          (match mO with
            | MetaCtx (_, cPsi) -> I.MDot (I.CObj (cPsi) , theta)
          )
  and checkBranches caseTyp cD (cG, cIH) branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cD (cG,cIH) branch tAbox ttau) branches

  and checkBranch _caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
      | EmptyBranch (loc, cD1', pat, t1) ->
          let _ = dprint (fun () -> "\nCheckBranch - Empty Pattern\n") in
          let _ = dprint (fun () -> "cD1 = " ^ P.mctxToString cD1') in
          let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD) in
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
          let _     = LF.checkMSub  loc cD1' t1 cD in
            checkPattern cD1' I.Empty pat (tau_p, Whnf.m_id)

      | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) ->
          let _ = dprint (fun () -> "\nCheckBranch with normal pattern") in
          let _ = dprint (fun () -> "where scrutinee has type" ^
                            P.compTypToString cD tau_s) in
          let TypBox (_, (I.Atom(_, a, _) as tP) , cPsi) = tau_s in
          (* By invariant: cD1' |- t1 <= cD *)
          let tP1   = Whnf.cnormTyp (tP, t1) in
          let cPsi1 = Whnf.cnormDCtx (cPsi, t1) in
          let cG'   = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in
          let _     = LF.checkMSub loc cD1' t1 cD in
          let _ = dprint (fun () -> "\nChecking refinement substitution :      DONE\n") in
          let _ = dprint (fun () -> "[check] MetaObj " ^ P.metaObjToString cD1'  mO
                            ^ "\n   has type " ^  P.typToString cD1'  cPsi1  (tP1, S.LF.id)
                            ^ "\n   in " ^ P.dctxToString cD1' cPsi1 ) in
          let _     = checkMetaObj loc cD1' mO  (MetaTyp (tP1, cPsi1), C.m_id) in
          let cIH'  = if Total.struct_smaller  mO then Total.wf_rec_calls cD1'
                     else I.Empty in
            check cD1' (cG', Context.append cIH cIH') e1 (tau', Whnf.m_id)

      | Branch (loc, cD1', cG1, pat, t1, e1) ->
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
          let cG'   = Whnf.cnormCtx (cG, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in
          let _     = LF.checkMSub loc  cD1' t1 cD in
          let _ = dprint (fun () -> "\nChecking refinement substitution : DONE\n") in
          let _ = checkPattern cD1' cG1 pat (tau_p, Whnf.m_id) in
            check cD1' ((Context.append cG' cG1), cIH) e1 (tau', Whnf.m_id)


  let rec wf_mctx cD = match cD with
    | I.Empty -> ()
    | I.Dec (cD, cdecl) ->
        (wf_mctx cD ; checkCDecl cD cdecl)


let syn cD cG e =
  let cIH = Syntax.Int.LF.Empty in
  let (_ , tau, t) = syn cD (cG,cIH) e in
    (tau,t)

let check cD cG e ttau =
  let cIH = Syntax.Int.LF.Empty in
    check cD (cG,cIH) e ttau



end

module Sgn = struct

  let rec check_sgn_decls = function
    | [] -> ()

    | Syntax.Int.Sgn.Typ (_a, tK) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkKind cD cPsi tK;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Const (_c, tA) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkTyp cD cPsi (tA, Substitution.LF.id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Schema (_w, schema) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkSchema (Syntax.Loc.ghost) cD cPsi schema;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Rec (f, tau, e) :: decls ->
        let cD = Syntax.Int.LF.Empty in
        let cG = Syntax.Int.LF.Empty in
(*        let _  = Total.initialize f in *)
          Comp.checkTyp cD tau;
          Comp.check cD cG e (tau, Whnf.m_id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Pragma (_a) :: decls ->
        check_sgn_decls decls


 end
