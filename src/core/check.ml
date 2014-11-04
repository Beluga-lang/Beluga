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
    | PattMismatch    of (I.mctx * meta_obj * meta_typ) * 
	                 (I.mctx * meta_typ)
(*    | PattMismatch    of (I.mctx * I.dctx * I.normal option * I.tclo) *
                         (I.mctx * I.dctx * I.tclo) *)
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
    | MissingTotal of Id.cid_prog
    | IllTypedMetaObj of I.mctx * meta_obj * meta_typ 

(*  type rec_call = bool *)

  exception Error of Syntax.Loc.t * error

  let convToParamTyp mT = match mT with
    | MetaTyp (tA, cPsi) -> MetaParamTyp (tA, cPsi)
    | mT -> mT
(*  let matchMetaV mC = match mC with 
    | MetaCtx (_, I.CtxVar _ ) -> true
    | MetaObj (_, phat, I.Root (_ , I.MVar (_ , s), _ )) -> 
	s = S.Shift 0 || (s = S.EmptySub && phat = (None, 0))
    | MetaObjAnn (_, cPsi, I.Root (_ , I.MVar (_ , s), _ )) -> 
	s = S.Shift 0 || (s = S.EmptySub && cPsi = I.Null)
    | MetaParam (_, phat, I.Root (_ , I.PVar (_ , s ), _ )) -> 
	s = S.Shift 0 || (s = S.EmptySub && phat = (None, 0))
    | MetaSubObj (_, phat, I.SVar (_, 0, s)) -> 
	s = S.Shift 0 || (s = S.EmptySub && phat = (None, 0))
    | MetaSubObjAnn (_, cPsi, I.SVar (_, 0, s)) -> 
	s = S.Shift 0 || (s = S.EmptySub && cPsi = I.Null)
    | _ -> false
*)
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
	  | IllTypedMetaObj (cD, cM, mT) -> 
            Format.fprintf ppf
              "Meta object %a does not have type %a."
              (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM
              (P.fmt_ppr_meta_typ cD Pretty.std_lvl) mT
          | MissingTotal prog ->
            Format.fprintf ppf "Function %s not known to be total."
              (R.render_cid_prog prog)
          | InvalidRecCall ->
            Format.fprintf ppf "Recursive call not structurally smaller."
          | IllegalParamTyp (cD, cPsi, tA) ->
            Format.fprintf ppf
              "Parameter type %a is illegal."
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp (tA, Substitution.LF.id))
          | UnsolvableConstraints (f,cnstrs) ->
            Format.fprintf ppf
            "Unification in type reconstruction encountered constraints because the given signature contains unification problems which fall outside the decideable pattern fragment, i.e. there are meta-variables which are not only applied to a distinct set of bound variables.\
\nThe constraint \n \n %s \n\n was not solvable. \n \n The program  %s is ill-typed. If you believe the program should type check, then consider making explicit the meta-variables occurring in the non-pattern positions."
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

          | PattMismatch ((cD, _cM, mT) , (cD', mT')) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type"
              (P.fmt_ppr_cmp_typ cD' Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, mT'))
              "Inferred type"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, mT))

(*          | PattMismatch ((cD, cPsi, pattern, sA) , (cD', cPsi', sA')) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type"
              (P.fmt_ppr_cmp_typ cD' Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, MetaTyp (Whnf.normTyp sA', Whnf.normDCtx cPsi')))
              "Inferred type"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, MetaTyp (Whnf.normTyp sA, Whnf.normDCtx cPsi)))
*)
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
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, MetaTyp(tP, cPsi)), theta))
          | MAppMismatch (cD, (MetaTyp (tA, cPsi), theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, MetaTyp(tA, cPsi)), theta))

          | MAppMismatch (cD, (MetaSubTyp (cPhi, cPsi), theta)) ->
              let cPhi', cPsi'  = Whnf.cnormDCtx (cPhi, theta) , Whnf.cnormDCtx  (cPsi, theta) in
              let cdec = I.Decl(Id.mk_name (Id.SVarName None), I.STyp (cPhi', cPsi', I.Maybe)) in
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
    | IndexObj of meta_obj
    | DataObj
    | IndDataObj
    | IndIndexObj of meta_obj

(*    | IndexObj of I.psi_hat * I.normal
    | DataObj
    | IndDataObj
    | IndIndexObj of I.psi_hat * I.normal
*)
  let is_inductive case_typ = match case_typ with
    | IndDataObj -> true 
    | IndIndexObj mC -> true
    | _ -> false

  let is_indMObj cD (I.Offset x) = match Whnf.mctxLookup cD x with
    | (_, I.MTyp (_, _, I.Inductive)) -> true
    | (_, I.PTyp (_, _, I.Inductive)) -> true
    | (_, I.STyp (_, _, I.Inductive)) -> true
    | (_, I.CTyp ( _, I.Inductive)) -> true
    | (_, _ ) -> false

(*  let ind_to_string case_typ = match case_typ with
    | IndDataObj -> "IndDataObj"
    | IndIndexObj (_ , _ ) -> "IndIndexObj"
    | _ -> "NON-INDUCTIVE"
*)

(*  let is_ind _cD _x  = true 
 match x with
    | I.Offset x, sigma -> 
	let (_, tA, cPsi', dp) = Whnf.mctxMDec cD u in
        let d = match dep with
         | I.Inductive -> true
         | _ -> false in 
         is_id sigma && dep 




*)

  let getLoc cM = match cM with 
    | MetaObj(loc, _, _ ) -> loc
    | MetaObjAnn (loc, _, _ ) -> loc
    | MetaCtx (loc, _ ) -> loc
    | MetaSObj (loc, _, _ ) -> loc
    | MetaSObjAnn (loc, _, _ ) -> loc
    | MetaParam (loc, _, _ ) -> loc


  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)


  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

(*  let rec isRecFun cIH f = match cIH with
    | I.Empty -> false
    | I.Dec(cIH, WfRec (f', _ , _ )) ->
      if f = f' then true
      else isRecFun cIH f
*)

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
    let tB' = Syntax.Int.LF.TClo(tB, Syntax.Int.LF.Shift n) in
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

  | (MetaObj (loc', phat, I.Root (_, h, I.Nil)), (cT, t)) -> 
      checkMetaObj loc cD (MetaParam (loc', phat, h)) (cT, t)

  | (MetaObjAnn (loc', cPhi, I.Root (_, h, I.Nil)), (cT, t)) -> 
      checkMetaObj loc cD (MetaParam (loc', Context.dctxToHat cPhi, h)) (cT, t)

  | _ , _ -> raise (Error (loc, (IllTypedMetaObj (cD, cM, Whnf.cnormMetaTyp cTt))))
;

    (* The case for parameter types should be handled separately, for better error messages -bp *)


and checkMetaSpine loc cD mS cKt  = match (mS, cKt) with
  | (MetaNil , (Ctype _ , _ )) -> ()
  | (MetaApp (mO, mS), (PiKind (_, I.Decl (_u, ctyp), cK) , t)) ->
      begin match ctyp with
        | I.CTyp (schema_cid, _ ) ->
            let MetaCtx (_, cPsi) = mO in
            let theta' = I.MDot (I.CObj (cPsi), t) in
              checkMetaObj loc cD mO (MetaSchema schema_cid , t);
              checkMetaSpine loc cD mS (cK, theta')

        | I.MTyp (tA, cPsi, _) ->
            let MetaObj (loc, psihat, tM) = mO in
              checkMetaObj loc cD mO (MetaTyp (tA, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.MObj(psihat, tM), t))

        | I.PTyp (tA, cPsi, _) ->
            let MetaParam (loc, psihat, tM) = mO in
              checkMetaObj loc cD mO (MetaParamTyp (tA, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.PObj(psihat, tM), t))

        | I.STyp (cPhi, cPsi, _) ->
            let MetaSObj (loc, psihat, tM) = mO in
              checkMetaObj loc cD mO (MetaSubTyp (cPhi, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.SObj(psihat, tM), t))
    end
  
  let checkCLFTyp cD ctyp = match ctyp with
    | I.CTyp (schema_cid, _ ) ->
        begin try
          let _ = Schema.get_schema schema_cid in ()
        with _ -> raise (Error.Violation "Schema undefined")
        end
    | I.MTyp (tA, cPsi, _) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)
    | I.PTyp (tA, cPsi, _) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id);
        checkParamTypeValid cD cPsi tA

    | I.STyp (cPhi, cPsi, _) ->
    	LF.checkDCtx cD cPhi;
    	LF.checkDCtx cD cPsi

  let checkCDecl cD cdecl = match cdecl with
    | I.Decl (_, ctyp) -> checkCLFTyp cD ctyp

  let rec checkKind cD cK = match cK with
    | Ctype _ -> ()
    | PiKind (_, cdecl, cK) ->
        checkCDecl cD cdecl;
        checkKind (I.Dec(cD, cdecl)) cK

  let rec checkTyp cD tau =  match tau with
    | TypBase (loc, c, mS) ->
        let cK = (CompTyp.get c).CompTyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypCobase (loc, c, mS) ->
        let cK = (CompCotyp.get c).CompCotyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypBox (_ , MetaTyp(tA, cPsi)) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)

    | TypBox (_ , MetaSubTyp(cPhi, cPsi)) ->
        LF.checkDCtx cD cPsi;
        LF.checkDCtx cD cPhi

    | TypArr (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2

    | TypCross (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2

    | TypPiBox (cdecl, tau') ->
        dprint (fun () -> "[checkCompTyp] " ^
                  P.mctxToString cD ^ " |- " ^
                  P.compTypToString cD tau);
        checkCDecl cD cdecl;
        dprint (fun () -> "[checkCompTyp] " ^
                  P.mctxToString (I.Dec (cD, cdecl)) ^ " |- " ^
                  P.compTypToString (I.Dec (cD, cdecl)) tau');
        checkTyp (I.Dec (cD, cdecl)) tau'

    | TypBool -> ()
    | TypInd tau -> checkTyp cD tau
;;


(* extend_mctx cD (x, cdecl, t) = cD' 

   if cD mctx 
      cD' |- cU   where cdecl = _ : cU
      cD  |- t : cD
   the 
      cD, x:[t]U  mctx

 *)
let extend_mctx cD (x, cdecl, t) = match cdecl with
  | I.Decl (_u, cU) ->
      I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t)))


let useIH loc cD cG cIH_opt  e2 = match cIH_opt with
  | None -> None
  | Some cIH ->
  (* We are making a recursive call *)
    let cIH = match cIH with
      | I.Empty -> raise (Error (loc, InvalidRecCall))
      | cIH  -> match e2 with
          | Box (_,cM) -> Total.filter cD cG cIH (loc, M cM)
          | Syn(_ , Var (_ , x))  -> Total.filter cD cG cIH (loc, V x)
	  | _i -> Total.filter cD cG cIH (loc, E)
          (* | _      -> raise (Error (loc, InvalidRecCall)) *)
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
    | (Rec (loc, f, e), (tau, t)) ->				
        check cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t))), cIH) e ttau;
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Rec" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->				
        check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t))), cIH) e (tau2, t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Fun" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Cofun (loc, bs), (TypCobase (l, cid, sp), t)) ->				
         let f = fun (CopatApp (loc, dest, csp), e') ->
           let ttau' = synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
           in check cD (cG,cIH) e' ttau'
         in 
	 let _ = List.map f bs in 
           Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Cofun" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->				
        check (extend_mctx cD (u, cdec, t))
          (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))   e (tau, C.mvar_dot1 t);
          Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("MLam" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->
        check cD (cG,cIH) e1 (tau1, t);
        check cD (cG,cIH) e2 (tau2, t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Pair" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Let (loc, i, (x, e)), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
          check cD (cG',cIH) e (tau,t);
          Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Let" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        begin match (tau',t') with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cD (cG',cIH) e (tau,t)
          | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
        end

    | (Box (loc, cM), (TypBox (l, mT), t)) -> (* Offset by 1 *)				
        begin try
	  checkMetaObj loc cD cM (mT, t);
          Typeinfo.Comp.add (getLoc cM) (Typeinfo.Comp.mk_entry cD ttau) 
	    ("Box" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e);
          dprint (fun () -> "loc <> metaLoc " ^ string_of_bool(loc <> (getLoc cM)))
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Error.Violation ("Free meta-variable " ^ (R.render_name u)))
        end
    | (Case (loc, prag, Ann (Box (_, cM), TypBox (_, mT)), branches), (tau, t)) ->
        let (total_pragma, tau_sc, projOpt) =  (match  cM with
                   | MetaObj (_ , _, I.Root (_, I.PVar (x,s) , _ )) | MetaParam (_ , _, I.PVar (x,s) )  ->
		       let order = if !Total.enabled && is_indMObj cD x then IndIndexObj cM  else IndexObj cM in
                       (order, TypBox(loc, convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), None)
                   | MetaObj (_, _, I.Root (_, I.Proj (I.PVar (x,s), k ), _ )) | MetaParam (_, _, I.Proj (I.PVar (x,s), k )) ->
		       let order = if  !Total.enabled && is_indMObj cD x then IndIndexObj cM else IndexObj cM in
                       (order, TypBox (loc, convToParamTyp(Whnf.cnormMetaTyp (mT, C.m_id))), Some k)
		   | MetaObj (_, _, I.Root (_, I.MVar (x,s), _ )) | MetaObjAnn (_, _,I.Root (_, I.MVar (x,s), _ )) -> 
		       let order = if  !Total.enabled && is_indMObj cD x then IndIndexObj cM else IndexObj cM in
                       (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
		   | MetaCtx (_, I.CtxVar (I.CtxOffset k)) -> 
		       let order = if  !Total.enabled && is_indMObj cD (I.Offset k) then IndIndexObj cM else IndexObj cM in
                       (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
		   | _ -> 
		       (IndexObj cM, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)		       ) in
        let _  = checkMetaObj loc cD  cM (convToParamTyp mT, C.m_id)  in
        (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Case 1" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e); *)
        let problem = Coverage.make loc prag cD branches tau_sc in
          (* Coverage.stage problem; *)
          checkBranches total_pragma cD (cG,cIH) branches tau_sc (tau, t);
          Coverage.process problem projOpt

(*    | (Case (loc, prag, Ann (Box (_, MetaObj(_, phat, tR)), TypBox (_, MetaTyp(tA', cPsi'))),
             branches), (tau, t)) ->
        let (total_pragma, tau_sc, projOpt) =  (match  tR with
                   | I.Root (_, I.PVar (x,s) , _ ) ->
		       let order = if !Total.enabled && is_indMObj cD x then IndIndexObj (phat, tR) else IndexObj(phat, tR) in
                       (order, TypBox(loc, MetaParamTyp (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), None)
                   | I.Root (_, I.Proj (I.PVar (x,s), k ), _ ) ->
		       let order = if  !Total.enabled && is_indMObj cD x then IndIndexObj(phat, tR) else IndexObj(phat, tR) in
                       (order, TypBox (loc, MetaParamTyp (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), Some k)
		   | I.Root (_, I.MVar (x,s), _ ) -> 
		       let order = if  !Total.enabled && is_indMObj cD x then IndIndexObj(phat, tR) else IndexObj(phat, tR) in
                       (order, TypBox (loc, MetaTyp(Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), None)
		   | _ -> 
		       (IndexObj (phat, tR), TypBox (loc, MetaTyp(Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), None)		       ) in
        let tau_s = TypBox (loc, MetaTyp(Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')) in
        let _  = LF.check cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in
        (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Case 1" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e); *)
        let problem = Coverage.make loc prag cD branches tau_sc in
          (* Coverage.stage problem; *)
          checkBranches total_pragma cD (cG,cIH) branches tau_s (tau, t);
          Coverage.process problem projOpt
*)
    | (Case (loc, prag, i, branches), (tau, t)) ->
	let chkBranch total_pragma cD (cG, cIH) i branches (tau,t) = 
          let (_ , tau', t') = syn cD (cG,cIH) i in
            begin match C.cwhnfCTyp (tau',t') with
              | (TypBox (loc', mT),  t') ->
		  let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
		  let problem = Coverage.make loc prag cD branches tau_s in
                    checkBranches total_pragma cD (cG,cIH) branches tau_s (tau,t);
                    Coverage.process problem None
              | (tau',t') ->
		  let problem = Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) in
		    checkBranches total_pragma cD (cG,cIH) branches (C.cnormCTyp (tau', t')) (tau,t);
                    Coverage.process problem None
            end
	in 
	  if !Total.enabled then
	    (match i with 
	       | Var (_, x)  ->  
		   let (f,tau') = lookup cG x in
(*		   let _ = print_string ("\nTotality checking enabled - encountered " ^ P.expSynToString cD cG i ^ 
			      " with type " ^ P.compTypToString cD tau' ^ "\n") in*)
		   let ind = match Whnf.cnormCTyp (tau', Whnf.m_id) with 
		     | TypInd _tau -> ((* print_string ("Encountered Var " ^
					 P.expSynToString cD cG i ^ " -	INDUCTIVE\n"); *) true)
		     | _ -> ((* print_string ("Encountered Var " ^ 
					 P.expSynToString cD cG i ^ " -	NON-INDUCTIVE\n");*) false) in 
		   if ind  then
		     ((* print_string " Inductive and Order satisfied\n";*)
		     chkBranch IndDataObj cD (cG,cIH) i branches (tau,t))
		   else 
		     chkBranch DataObj cD (cG,cIH) i branches (tau,t)
	       | _ -> chkBranch DataObj cD (cG,cIH) i branches (tau,t)
	    )
	  else
	    chkBranch DataObj cD (cG,cIH) i branches (tau,t)

    | (Syn (loc, i), (tau, t)) ->
	let _ = dprint (fun () -> "check --> syn") in 
        let (_, tau',t') = syn cD (cG,cIH) i in
        let (tau',t') = Whnf.cwhnfCTyp (tau',t') in
        if C.convCTyp (tau,t)  (tau',t') then
          (Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Syn" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e) ;
          ())
        else
          raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), (tau',t'))))

    | (If (loc, i, e1, e2), (tau,t)) ->
        let (_flag, tau', t') = syn cD (cG,cIH) i in
        let (tau',t') = C.cwhnfCTyp (tau',t') in
          begin match  (tau',t') with
          | (TypBool , _ ) ->
              (check cD (cG,cIH) e1 (tau,t) ;
               check cD (cG,cIH) e1 (tau,t) ;
              Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("If" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e))
          | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
        end

    | (Hole (_loc, _f), (_tau, _t)) -> 
      Typeinfo.Comp.add _loc (Typeinfo.Comp.mk_entry cD ttau) ("Hole" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e);
      ()

  and check cD (cG, cIH) e (tau, t) =
    let _ =  dprint (fun () -> "[check]  " ^
                       P.expChkToString cD cG e ^
                        " against \n    " ^
                  P.mctxToString cD ^ " |- " ^
                  P.compTypToString cD (Whnf.cnormCTyp (tau, t))) in
    checkW cD (cG, cIH) e (C.cwhnfCTyp (tau, t));

  and syn cD (cG,cIH) e : (gctx option * typ * I.msub) = match e with
    | Var (loc, x)   ->
      let (f,tau') = lookup cG x in
      let _ =  Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau', C.m_id))  	       
 	                             ("Var" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e)
      in 
      (* let _ = print_string ("Looking up " ^ P.expSynToString cD cG e ^ 
			      " with type " ^ P.compTypToString cD tau' ^ "\n") in*)
      let tau = match Whnf.cnormCTyp (tau', Whnf.m_id) with 
	| TypInd tau -> tau 
	| _ -> tau' in 
      if Total.exists_total_decl f then
        (Some cIH, tau, C.m_id)
      else
          (None, tau, C.m_id)

    | DataConst (loc, c) ->
        (Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((CompConst.get c).CompConst.typ, C.m_id)) 
	   ("DataConst" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
        (None,(CompConst.get c).CompConst.typ, C.m_id))

    | DataDest (loc, c) ->
	(dprint (fun () -> "DataDest ... ");
        (None,(CompDest.get c).CompDest.typ, C.m_id))

    | Const (loc,prog) ->
	(Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((Comp.get prog).Comp.typ, C.m_id)) 
	   ("Const" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
        if !Total.enabled then
          if (Comp.get prog).Comp.total then
            ((* print_string ("Call to " ^ R.render_cid_prog prog ^
                             " is known to  be total\n"); *)
             (None,(Comp.get prog).Comp.typ, C.m_id))
          else
            raise (Error (loc, MissingTotal prog))
        else
          (None,(Comp.get prog).Comp.typ, C.m_id))

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
              Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, t)) ("Apply" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
              (useIH loc cD cG cIH_opt e2, tau, t)

          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
        end

    | MApp (loc, e, mC) ->
        let (cIH_opt, tau, t) = syn cD (cG,cIH) e in
        let (tau,t) = C.cwhnfCTyp (tau,t) in
        begin match (mC, (tau, t)) with
          | (MetaCtx (loc, cPsi), (TypPiBox ((I.Decl (_ , I.CTyp (w, _) )), tau), t)) ->
              let theta' = I.MDot (I.CObj (cPsi), t) in
              LF.checkSchema loc cD cPsi (Schema.get_schema w);
              (dprint (fun () -> "[check: syn] cPsi = " ^ P.dctxToString cD cPsi );
               dprint (fun () -> "[check: syn] tau1 = " ^
                          P.compTypToString cD (Whnf.cnormCTyp (tau, theta') ))) ;
	      Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, theta')) 
		("MApp 1" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
                 (useIH loc cD cG cIH_opt (Box (loc, mC)) , tau, theta')

          | (MetaObj (loc, psihat, tM) , (TypPiBox ((I.Decl (_u, I.MTyp (tA, cPsi, _ ))), tau), t)) ->
              checkMetaObj loc cD mC (MetaTyp (tA, cPsi), t) ;
	      Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, I.MDot(I.MObj (psihat, tM), t))) 
		("MApp 2" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
              (useIH loc cD cG cIH_opt (Box (loc, mC)), tau, I.MDot(I.MObj (psihat, tM), t))
          | (MetaParam(_, phat, h), (TypPiBox ((I.Decl(_, I.PTyp (tA, cPsi, _))), tau), t)) ->
              let _ =  dprint (fun () -> "[check: inferHead] cPsi = " ^
                                 P.dctxToString cD (C.cnormDCtx (cPsi,t) )) in
              let tB = LF.inferHead loc cD (C.cnormDCtx (cPsi,t)) h in
                if Whnf.convTyp (tB, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) then
                  (Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, I.MDot(I.PObj (phat, h), t))) 
		     ("MApp 3" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
                  (useIH loc cD cG cIH_opt (Box (loc, mC)), tau, I.MDot(I.PObj (phat, h), t)))
                else
                  raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
          | (MetaSObj(loc, phat, s), (TypPiBox ((I.Decl(_, I.STyp (tA, cPsi, _))), tau), t)) ->
              (LF.checkSub loc cD (C.cnormDCtx (cPsi, t)) s (C.cnormDCtx (tA, t));
              Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, I.MDot(I.SObj (phat,s), t))) 
                   ("MApp 4" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
              (useIH loc cD cG cIH_opt (Box (loc, mC)), tau, I.MDot(I.SObj (phat, s), t)))

          | ( _ , ((TypPiBox (I.Decl _ , _ )) as tau, t) ) ->
              raise (Error (loc, MismatchSyn (cD, cG, e, VariantCtxPi, (tau,t))))

          | (_ , ( tau, t)) ->
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
          | (TypBox (_, MetaTyp(tA, cPhi)) , theta) | (TypBox (_, MetaParamTyp (tA, cPhi)), theta) ->
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
          | (TypBox (_, mT) , theta) ->
              checkMetaObj loc cD mO (mT, theta)
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
        | (TypPiBox (cdecl, tau), theta) ->
          let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
          synPatSpine cD cG pat_spine (tau, theta')
      end

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (cdecl, theta) = match cdecl with
    | I.Decl (_, I.MTyp (tA, cPsi, _)) ->
        let _ = checkMetaObj loc cD mO (MetaTyp (tA, cPsi), theta) in
          (match mO with
            | MetaObj (_, phat, tM) ->  I.MDot(I.MObj(phat, tM), theta)
            | MetaObjAnn (_, cPsi, tM) -> I.MDot (I.MObj(Context.dctxToHat cPsi, tM), theta)
          )
    | I.Decl (_, I.PTyp (tA, cPsi, _)) ->
        let _ = checkMetaObj loc cD mO (MetaParamTyp (tA, cPsi), theta) in
          (match mO with
            | MetaParam (_, phat, h) ->  I.MDot(I.PObj(phat, h), theta)
          )
    | I.Decl (_, I.STyp (cPhi, cPsi, _)) ->
        let _ = checkMetaObj loc cD mO (MetaSubTyp (cPhi, cPsi), theta) in
          (match mO with
            | MetaSObj (_, phat, s) ->  I.MDot(I.SObj(phat, s), theta)
            | MetaSObjAnn (_, cPsi, s) -> I.MDot (I.SObj(Context.dctxToHat cPsi, s), theta)
          )
    | I.Decl (_, I.CTyp (w, _ )) ->
        let _ = checkMetaObj loc cD mO (MetaSchema w, theta) in
          (match mO with
            | MetaCtx (_, cPsi) -> I.MDot (I.CObj (cPsi) , theta)
          )
  and checkBranches caseTyp cD (cG, cIH) branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cD (cG,cIH) branch tAbox ttau) branches

  and checkBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
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
          let TypBox (_, mT) = tau_s in
          (* By invariant: cD1' |- t1 <= cD *)
	  let mT1 = Whnf.cnormMetaTyp (mT, t1) in
          let cG'   = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
          let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in          
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in
          let _     = LF.checkMSub loc cD1' t1 cD in
          let _ = dprint (fun () -> "\nChecking refinement substitution :      DONE\n") in
          let _ = dprint (fun () -> "[check] MetaObj " ^ P.metaObjToString cD1'  mO
                            ^ "\n   has type " ^  P.metaTypToString cD1'  mT1 ) in
          let _ = checkMetaObj loc cD1' mO  (mT1, C.m_id) in
	  (* let _ = print_string ("[check] Branch " ^ (ind_to_string caseTyp) ^ "\n") in *)
          let cIH'  = if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (loc', mO)) then
	    ((* print_string "Generate recursive calls .. \n";*)
	     Total.wf_rec_calls cD1' (I.Empty))
                      else I.Empty in
            check cD1' (cG', Context.append cIH cIH') e1 (tau', Whnf.m_id)

      | Branch (loc, cD1', cG1, pat, t1, e1) ->
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
          let cG'   = Whnf.cnormCtx (cG, t1) in
          let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in
          let _     = LF.checkMSub loc  cD1' t1 cD in
          let _ = dprint (fun () -> "\nChecking refinement substitution : DONE\n") in
          let _ = checkPattern cD1' cG1 pat (tau_p, Whnf.m_id) in
          let cIH'  = if is_inductive caseTyp && Total.struct_smaller pat then
                       Total.wf_rec_calls cD1' cG1
                     else I.Empty in
            check cD1' ((Context.append cG' cG1), Context.append cIH cIH') e1 (tau', Whnf.m_id)


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

  module S = Store.Cid

  let rec check_sgn_decls = function
    | [] -> ()

    | Syntax.Int.Sgn.Typ (l, _a, tK):: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkKind cD cPsi tK;
          check_sgn_decls decls;

    | Syntax.Int.Sgn.Const (l, _c, tA)  :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkTyp cD cPsi (tA, Substitution.LF.id);
          check_sgn_decls decls;

    | Syntax.Int.Sgn.Schema (_w, schema) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkSchema (Syntax.Loc.ghost) cD cPsi schema;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Rec (l) :: decls ->
        let cD = Syntax.Int.LF.Empty in
        let cG = Syntax.Int.LF.Empty in
        List.iter (fun (f, tau, e)->
          Comp.checkTyp cD tau;
          Comp.check cD cG e (tau, Whnf.m_id)) l;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Pragma (_a) :: decls ->
        check_sgn_decls decls




end


