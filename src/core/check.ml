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

          | AppMismatch (cD, (I.MTyp (tP, cPsi), theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, I.MTyp (tP, cPsi)), theta))

          | MAppMismatch (cD, (I.MTyp (tA, cPsi), theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, I.MTyp (tA, cPsi)), theta))

          | MAppMismatch (cD, (I.STyp (cPhi, cPsi), theta)) ->
              let cPhi', cPsi'  = Whnf.cnormDCtx (cPhi, theta) , Whnf.cnormDCtx  (cPsi, theta) in
              let cdec = I.Decl(Id.mk_name (Id.SVarName None), I.STyp (cPhi', cPsi'), I.Maybe) in
            Format.fprintf ppf
              "Expected contextual substitution object of type %a."
              (P.fmt_ppr_lf_ctyp_decl cD Pretty.std_lvl)
              cdec

          | MAppMismatch (cD, (I.CTyp cid_schema, tau)) ->
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

  let getLoc cM = match cM with 
    | MetaObj(loc, _, _ ) -> loc
    | MetaCtx (loc, _ ) -> loc

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (_,  tau)), 1) -> tau
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

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
  | (MetaCtx (loc, cPsi), (I.CTyp w, _)) ->
      LF.checkSchema loc cD cPsi (Schema.get_schema w)

  | (MetaObj (loc, phat, I.INorm tM), (I.MTyp (tA, cPsi), t)) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      if phat = Context.dctxToHat cPsi' then
        LF.check cD cPsi' (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id)
      else
        raise (Error (loc, CtxHatMismatch (cD, cPsi', phat, cM)))

  | (MetaObj (loc, phat, I.ISub tM), (I.STyp (tA, cPsi), t)) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      if phat = Context.dctxToHat cPsi' then
        LF.checkSub loc cD cPsi' tM (C.cnormDCtx (tA, t))
      else
        raise (Error (loc, CtxHatMismatch (cD, cPsi', phat, cM)))

  | (MetaObj (loc, _phat, I.IHead h), (I.PTyp (tA, cPsi), t)) ->
      let tA' = LF.inferHead loc cD (C.cnormDCtx (cPsi, t)) h in
      let tA  = C.cnormTyp (tA, t) in
        if Whnf.convTyp (tA, Substitution.LF.id) (tA', Substitution.LF.id) then ()
;

and checkMetaSpine loc cD mS cKt  = match (mS, cKt) with
  | (MetaNil , (Ctype _ , _ )) -> ()
  | (MetaApp (mO, mS), (PiKind (_, I.Decl (_u, ctyp,_), cK) , t)) ->
    let loc = getLoc mO in
    checkMetaObj loc cD mO (ctyp, t);
    checkMetaSpine loc cD mS (cK, I.MDot (metaObjToMFront mO, t))
  
  let checkCLFTyp cD ctyp = match ctyp with
    | I.CTyp schema_cid ->
        begin try
          let _ = Schema.get_schema schema_cid in ()
        with _ -> raise (Error.Violation "Schema undefined")
        end
    | I.MTyp (tA, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)
    | I.PTyp (tA, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id);
        checkParamTypeValid cD cPsi tA

    | I.STyp (cPhi, cPsi) ->
    	LF.checkDCtx cD cPhi;
    	LF.checkDCtx cD cPsi

  let checkCDecl cD cdecl = match cdecl with
    | I.Decl (_, ctyp, _) -> checkCLFTyp cD ctyp

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

    | TypBox (_ , I.MTyp (tA, cPsi)) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)

    | TypBox (_ , I.STyp(cPhi, cPsi)) ->
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

;;

(* extend_mctx cD (x, cdecl, t) = cD' 

   if cD mctx 
      cD' |- cU   where cdecl = _ : cU
      cD  |- t : cD
   the 
      cD, x:[t]U  mctx

 *)
let extend_mctx cD (x, cdecl, t) = match cdecl with
  | I.Decl (_u, cU, dep) ->
      I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t), dep))

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

  let rec checkW cD (cG : ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (loc, f, e), (tau, t)) ->				
        check cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t)))) e ttau;
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Rec" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->				
        check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t)))) e (tau2, t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Fun" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Cofun (loc, bs), (TypCobase (l, cid, sp), t)) ->				
         let f = fun (CopatApp (loc, dest, csp), e') ->
           let ttau' = synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
           in check cD cG e' ttau'
         in let _ = List.map f bs in ();
         Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Cofun" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->				
        check (extend_mctx cD (u, cdec, t))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t);
          Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("MLam" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->			
        check cD cG e1 (tau1, t);
        check cD cG e2 (tau2, t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Pair" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Let (loc, i, (x, e)), (tau, t)) ->				
        let (tau', t') =  C.cwhnfCTyp (syn cD cG i) in
        let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
          check cD cG' e (tau,t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Let" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (LetPair (loc, i, (x, y, e)), (tau, t)) ->				
        begin match C.cwhnfCTyp (syn cD cG i) with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cD cG' e (tau,t);
                (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) "LetPair" *)
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

    | (Case (loc, prag, Ann (Box (_, MetaObj(_, phat, I.INorm tR)),
			     TypBox (_, I.MTyp(tA', cPsi'))),
             branches), (tau, t)) ->				
        let (tau_sc, projOpt) =  (match tR with
                   | I.Root (_, I.PVar _ , _ ) ->
                       (TypBox (loc, I.PTyp(Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), None);                       
                   | I.Root (_, I.Proj (I.PVar _, k ), _ ) ->
                       (TypBox (loc, I.PTyp(Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), Some k);                       
                   | _ ->
                       (TypBox (loc, I.MTyp (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')), None)) in
        let tau_s = TypBox (loc, I.MTyp(Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi')) in
        let _  = LF.check cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in
        (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Case 1" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e); *)
        let problem = Coverage.make loc prag cD branches tau_sc in
          (* Coverage.stage problem; *)
          checkBranches (IndexObj (phat, tR)) cD cG branches tau_s (tau, t);
          Coverage.process problem projOpt

    | (Case (loc, prag, i, branches), (tau, t)) ->				
        begin match C.cwhnfCTyp (syn cD cG i) with
          | (TypBox (loc', mT),  t') ->
              let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
             (*  Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Case 2" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e); *)
              let _ = dprint (fun () -> "[check] Case - Scrutinee " ^
                                P.expSynToString cD cG i ^
                                "\n   has type " ^ P.compTypToString cD tau_s)
              in
              let problem = Coverage.make loc prag cD branches tau_s in
              (* Coverage.stage problem; *)
                checkBranches DataObj cD cG branches tau_s (tau,t);
                Coverage.process problem None
          | (tau',t') ->
              let problem = Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) in
              checkBranches DataObj cD cG branches (C.cnormCTyp (tau', t')) (tau,t);
                Coverage.process problem None
        end

    | (Syn (loc, i), (tau, t)) ->				
        let ttau' = (syn cD cG i) in
        if C.convCTyp (tau,t)  ttau' then
          begin
            Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Syn" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e) ;
            ()
          end
        else
          raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), ttau')))

    | (If (loc, i, e1, e2), (tau,t)) ->				
        begin match C.cwhnfCTyp (syn cD cG i) with
          | (TypBool , _ ) ->
              (check cD cG e1 (tau,t) ;
               check cD cG e1 (tau,t) );
              Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("If" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)
          | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
        end

    | (Hole (_loc, _f), (_tau, _t)) -> 
      Typeinfo.Comp.add _loc (Typeinfo.Comp.mk_entry cD ttau) ("Hole" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e);
      ()

  and check cD cG e (tau, t) =
    let _ =  dprint (fun () -> "[check]  " ^
                       P.expChkToString cD cG e ^
                        " against \n    " ^
                  P.mctxToString cD ^ " |- " ^
                  P.compTypToString cD (Whnf.cnormCTyp (tau, t))) in
    checkW cD cG e (C.cwhnfCTyp (tau, t));

  and syn cD cG e = match e with
    | Var (loc, x)   -> 
      Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (lookup cG x, C.m_id)) ("Var" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
      (lookup cG x, C.m_id)
    | DataConst (loc, c) -> 
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((CompConst.get c).CompConst.typ, C.m_id)) ("DataConst" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
        ((CompConst.get c).CompConst.typ, C.m_id)
    | DataDest (loc, c) -> 
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((CompDest.get c).CompDest.typ, C.m_id)) ("DataDest" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
        ((CompDest.get c).CompDest.typ, C.m_id)

    | Const (loc, prog) -> 
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((Comp.get prog).Comp.typ, C.m_id)) ("Const" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
        ((Comp.get prog).Comp.typ, C.m_id)

    | Apply (loc , e1, e2) ->
        begin match C.cwhnfCTyp (syn cD cG e1) with
          | (TypArr (tau2, tau), t) ->
              dprint (fun () -> "[SYN: APPLY ] synthesized type  " ^
                     P.compTypToString cD (Whnf.cnormCTyp (TypArr (tau2, tau), t) ));
              dprint (fun () -> ("[check: APPLY] argument has appropriate type " ^
                                       P.expChkToString cD cG e2));
              dprint (fun () -> "[check: APPLY] cG " ^ P.gctxToString cD cG );
              check cD cG e2 (tau2, t);
              Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, t)) ("Apply" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
              (tau, t);              
          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
        end

    | MApp (loc, e, mC) ->
        begin match (C.cwhnfCTyp (syn cD cG e)) with
          | (TypPiBox ((I.Decl (_ , ctyp, _)), tau), t) ->
	    checkMetaObj loc cD mC (ctyp, t);
	    (tau, I.MDot(metaObjToMFront mC, t))
          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
        end

    | PairVal (loc, i1, i2) ->
        let (tau1,t1) =  C.cwhnfCTyp (syn cD cG i1) in
        let (tau2,t2) =  C.cwhnfCTyp (syn cD cG i2) in
        (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (TypCross (TypClo (tau1, t1), TypClo (tau2,t2)), C.m_id)); *)
          (TypCross (TypClo (tau1, t1), TypClo (tau2,t2)), C.m_id)


    | Ann (e, tau) ->
        check cD cG e (tau, C.m_id);        
        (tau, C.m_id)

    | Equal(loc, i1, i2) ->
         let ttau1 = syn cD cG i1 in
         let ttau2 = syn cD cG i2 in
           if Whnf.convCTyp ttau1 ttau2 then
             begin match (Whnf.cwhnfCTyp ttau1) with
               | (TypBox _ , _ ) ->  (TypBool, C.m_id)
               | (TypBool, _ )   ->  (TypBool, C.m_id)
               | _               ->  raise (Error (loc, EqTyp (cD, ttau1)))
             end

           else
             raise (Error(loc, EqMismatch (cD, ttau1, ttau2 )))

    | Boolean _  -> (TypBool, C.m_id)

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
          | (TypBox (_, I.MTyp (tA, cPhi)) , theta) ->
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
          | (TypBox (_, I.MTyp(tA, cPsi)) , theta) ->
              checkMetaObj loc cD mO (I.MTyp (tA, cPsi), theta)
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
          if C.convCTyp ttau ttau' then ()
          else
            raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat = match pat with
    | PatConst (loc, c, pat_spine) ->
        let tau = (CompConst.get c).CompConst.typ in
          (loc, synPatSpine cD cG pat_spine (tau , C.m_id))
    | PatVar (loc, k) -> (loc, (lookup cG k, C.m_id))
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

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    checkMetaObj loc cD mO (ctyp, theta);
    I.MDot(metaObjToMFront mO, theta)

  and checkBranches caseTyp cD cG branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cD cG branch tAbox ttau) branches

  and checkBranch _caseTyp cD cG branch tau_s (tau, t) =
    match branch with
      | EmptyBranch (loc, cD1', pat, t1) ->
          let _ = dprint (fun () -> "\nCheckBranch - Empty Pattern\n") in
          let _ = dprint (fun () -> "cD1 = " ^ P.mctxToString cD1') in
          let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD) in
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
          let _     = LF.checkMSub  loc cD1' t1 cD in
            checkPattern cD1' I.Empty pat (tau_p, Whnf.m_id)

      | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) ->
          let _ = dprint (fun () -> "\nCheckBranch with normal pattern\n") in
          let _ = dprint (fun () -> "where scrutinee has type" ^
                            P.compTypToString cD tau_s) in
          let TypBox (_, mT) = tau_s in
          (* By invariant: cD1' |- t1 <= cD *)
	  let mT1 = Whnf.cnormMetaTyp (mT, t1) in
          let cG'   = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in          
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in
          let _     = LF.checkMSub loc cD1' t1 cD in
          let _ = dprint (fun () -> "\nChecking refinement substitution :      DONE\n") in
          let _ = dprint (fun () -> "[check] MetaObj " ^ P.metaObjToString cD1'  mO
                            ^ "\n   has type " ^  P.metaTypToString cD1'  mT1) in
          let _ = checkMetaObj loc cD1' mO  (mT1, C.m_id) in
            check cD1' cG' e1 (tau', Whnf.m_id);
            (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau_s, C.m_id))           *)


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
            check cD1' (Context.append cG' cG1) e1 (tau', Whnf.m_id)
            (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, t)) *)


  let rec wf_mctx cD = match cD with
    | I.Empty -> ()
    | I.Dec (cD, cdecl) ->
        (wf_mctx cD ; checkCDecl cD cdecl)



end

module Sgn = struct

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

