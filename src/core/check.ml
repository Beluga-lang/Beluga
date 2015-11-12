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
    | CtxMismatch     of I.mctx * I.dctx (* expected *) * I.dctx (* found *) * meta_obj
    | TypMismatch     of I.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name * string
    | InvalidRecCall
    | MissingTotal of Id.cid_prog
    (* | IllTypedMetaObj of I.mctx * meta_obj * meta_typ  *)

(*  type rec_call = bool *)

  exception Error of Syntax.Loc.t * error

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
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
            "Unification in type reconstruction encountered constraints because the given signature contains unification problems which fall outside the decideable pattern fragment.\n\nCommon causes are:\n\n- there are meta-variables which are not only applied to a distinct set of bound variables \n- a meta-variable in the program depends on a context, but it must be in fact closed \n\nThe constraint \n \n %s \n\n was not solvable. \n \n The program  %s is considered ill-typed. "
              cnstrs (Id.render_name f)

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

          | AppMismatch (cD, (ctyp, theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, ctyp), theta))

          | MAppMismatch (cD, (ctyp, theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, ctyp), theta))
          (* | Typmismatch (cD, (tau1, theta1), (tau2, theta2)) -> *)
          (*     Error.report_mismatch ppf *)
          (*       "Type of destructor did not match the type it was expected to have." *)
          (*       "Type of destructor" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) *)
          (*       (Whnf.cnormCTyp (tau1, theta1)) *)
          (*       "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) *)
          (*       (Whnf.cnormCTyp (tau2, theta2))) *)
      ))

  type caseType =
    | IndexObj of meta_obj
    | DataObj
    | IndDataObj
    | IndIndexObj of meta_obj

  let is_inductive case_typ = match case_typ with
    | IndDataObj -> true
    | IndIndexObj mC -> true
    | _ -> false

  let is_indMObj cD x = match Whnf.mctxLookupDep cD x with
    | (_, _ , I.Inductive) -> true
    | (_, _ , _) -> false



let mark_ind cD k =
  let rec lookup cD k' =  match cD, k' with
    | I.Dec (cD, I.Decl (u, cdec,dep)), 1 ->
	 I.Dec (cD, I.Decl (u, cdec, I.Inductive))
     | I.Dec (_cD, I.DeclOpt u), 1 ->
	 raise (Error.Violation "Expected declaration to have type")
    | I.Dec (cD, dec), k' -> I.Dec (lookup cD (k' - 1), dec)
    | I.Empty , _  -> raise (Error.Violation ("Meta-variable out of bounds -- looking for " ^ string_of_int k ^ "in context"))
 in
    lookup cD k


  let rec fmv_normal (cD:I.mctx) tM = match tM with
    | I.Root (_, h, tS) -> fmv_spine (fmv_head cD h) tS
    | I.Lam (_, _ , tM) -> fmv_normal cD tM
    | I.LFHole _ -> cD
    | I.Tuple (_, tuple) -> fmv_tuple cD tuple

  and fmv_head (cD:I.mctx) h = match h with
    | I.MVar (I.Offset k, s) | I.PVar (k, s) ->
	fmv_subst  (mark_ind cD k) s
    | I.Proj (h, _ ) -> fmv_head cD h
    | _ -> cD

  and fmv_tuple (cD:I.mctx) tuple = match tuple with
    | I.Last tM -> fmv_normal cD tM
    | I.Cons (tM, tuple) -> fmv_tuple (fmv_normal cD tM) tuple

  and fmv_spine (cD:I.mctx) tS = match tS with
    | I.Nil -> cD
    | I.App (tM, tS) -> fmv_spine (fmv_normal cD tM) tS

  and fmv_hat (cD:I.mctx) phat = match phat with
    | (Some (I.CtxOffset k), _ ) -> mark_ind cD k
    | _ -> I.Empty

  and fmv_dctx (cD:I.mctx) cPsi = match cPsi with
    | I.Null -> cD
    | I.CtxVar (I.CtxOffset k) -> mark_ind cD k
    | I.DDec (cPsi, decl) -> fmv_decl (fmv_dctx cD cPsi) decl

  and fmv_decl (cD:I.mctx) decl = match decl with
    | I.TypDecl (_, tA) -> fmv_typ cD tA
    | _ -> cD

  and fmv_typ (cD:I.mctx) tA = match tA with
    | I.Atom (_, _, tS) -> fmv_spine cD tS
    | I.PiTyp ((decl, _ ) , tA) -> fmv_typ (fmv_decl cD decl) tA
    | I.Sigma trec -> fmv_trec cD trec

  and fmv_trec (cD:I.mctx) trec = match trec with
    | I.SigmaLast (_, tA) -> fmv_typ cD tA
    | I.SigmaElem (_, tA, trec) -> fmv_trec (fmv_typ cD tA) trec

  and fmv_subst (cD:I.mctx) s = match s with
    | I.Dot (f, s) -> fmv_subst (fmv_front cD f) s
    | I.SVar (k, _, s) -> fmv_subst (mark_ind cD k) s
    | _ -> cD

  and fmv_front (cD:I.mctx) f = match f with
    | I.Head h -> fmv_head cD h
    | I.Obj tM -> fmv_normal cD tM
    | I.Undef -> cD

  let fmv_mobj cD cM = match cM with
    | _ , I.CObj (cPsi) -> fmv_dctx cD cPsi
    | _, I.ClObj (phat, I.MObj tM) -> fmv_normal cD tM
    | _, I.ClObj (phat, I.PObj h) -> fmv_head (fmv_hat cD phat) h
    | _, I.ClObj (phat, I.SObj s) ->  fmv_subst (fmv_hat cD phat) s

  let rec fmv cD pat = match pat with
    | PatConst (_ , _ , pat_spine) -> fmv_pat_spine cD pat_spine
    | PatVar (_ , _ ) | PatTrue _ | PatFalse _ -> cD
    | PatPair (_, pat1, pat2) ->  fmv (fmv cD pat1) pat2
    | PatMetaObj (_, cM) -> fmv_mobj cD cM
    | PatAnn (_, pat, _) -> fmv cD pat

  and fmv_pat_spine cD pat_spine = match pat_spine with
    | PatNil -> cD
    | PatApp (_, pat, pat_spine) ->
	fmv_pat_spine  (fmv cD pat) pat_spine

  let mvarsInPatt cD pat =
    fmv cD pat

  let rec id_map_ind cD1' t cD = match t, cD with
    | I.MShift k, I.Empty -> cD1'
    | I.MShift k, cD ->
	if k >= 0 then
	  id_map_ind cD1' (I.MDot (I.MV (k+1), I.MShift (k+1))) cD
	else raise (Error.Violation ("Contextual substitution ill-formed"))

    | I.MDot (I.MV u, ms), I.Dec(cD, I.Decl (_u, mtyp1, dep)) ->
	if Total.is_inductive dep then
	  let cD1' = mark_ind cD1' u in
	    id_map_ind cD1' ms cD
	else
	  id_map_ind cD1' ms cD

    | I.MDot (mf, ms), I.Dec(cD, I.Decl (_u, mtyp1, dep)) ->
	(match mf with
	   | I.ClObj (_, I.MObj(I.Root (_, I.MVar (I.Offset u, I.Shift 0), I.Nil)))
	   | I.ClObj (_, I.MObj(I.Root (_, I.PVar (u, I.Shift 0), I.Nil)))
	   | I.ClObj (_, I.PObj(I.PVar (u, I.Shift 0)))
	   | I.CObj(I.CtxVar (I.CtxOffset u))
	   | I.ClObj (_ , I.SObj (I.SVar (u, 0, I.Shift 0))) ->
	       if Total.is_inductive dep then
		 let cD1' = mark_ind cD1' u in
		   id_map_ind cD1' ms cD
	       else
		 id_map_ind cD1' ms cD
	   | _ -> id_map_ind cD1' ms cD)




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

  let getLoc (loc,cM) = loc


  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

let rec checkParamTypeValid cD cPsi tA =
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

and checkMetaSpine loc cD mS cKt  = match (mS, cKt) with
  | (MetaNil , (Ctype _ , _ )) -> ()
  | (MetaApp (mO, mS), (PiKind (_, I.Decl (_u, ctyp,_), cK) , t)) ->
    let loc = getLoc mO in
    LF.checkMetaObj cD mO (ctyp, t);
    checkMetaSpine loc cD mS (cK, I.MDot (metaObjToMFront mO, t))

  let checkClTyp cD cPsi = function
    | I.MTyp tA ->
        LF.checkTyp  cD cPsi (tA, S.LF.id)
    | I.PTyp tA ->
        LF.checkTyp  cD cPsi (tA, S.LF.id);
        checkParamTypeValid cD cPsi tA
    | I.STyp (_, cPhi) ->
    	LF.checkDCtx cD cPhi
  let checkCLFTyp cD ctyp = match ctyp with
    | I.CTyp (Some schema_cid) ->
        begin try
          let _ = Schema.get_schema schema_cid in ()
        with _ -> raise (Error.Violation "Schema undefined")
        end
    | I.CTyp None -> ()
    | I.ClTyp (tp, cPsi) ->
        LF.checkDCtx cD cPsi;
        checkClTyp cD cPsi tp

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

    | TypBox (_ , ctyp) -> checkCLFTyp cD ctyp

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
  | I.Decl (_u, cU, dep) ->
      I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t), dep))

let rec extract_var i = match i with
  | Var (_, x) -> Some x
  | Apply (_, i, _ ) -> extract_var i
  | MApp (_, i, _ ) -> extract_var i
  | _ -> None

let useIH loc cD cG cIH_opt e2 = match cIH_opt with
  | None -> None
  | Some cIH ->
  (* We are making a recursive call *)
    let cIH = match cIH with
      | I.Empty -> raise (Error (loc, InvalidRecCall))
      | cIH  -> match e2 with
          | Box (_,cM) ->
	      ( dprint (fun () -> "\nCheck whether compatible IH exists\n");
		dprint (fun () -> "cIH " ^ Total.ih_to_string cD cG cIH ^ "\n");
		dprint (fun () -> "Recursive call on " ^ P.metaObjToString cD cM ^ "\n");
	      Total.filter cD cG cIH (loc, M cM))
	  | Syn(_, i) -> (match extract_var i with
			    | Some x -> Total.filter cD cG cIH (loc, V x)
			    | None ->  Total.filter cD cG cIH (loc, E))
          (* | _      -> raise (Error (loc, InvalidRecCall)) *)
    in
    let _ = dprint (fun () -> "[useIH] Partially used IH: " ^ Total.ih_to_string cD cG cIH) in
  (* We have now partially checked for the recursive call *)
    match cIH with
      | I.Dec(_ , WfRec (_, [], _ )) ->
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

  let rec checkW cD ((cG , cIH) : ctyp_decl I.ctx * ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (loc, f, e), (tau, t)) ->
        check cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t))), (Total.shift cIH)) e ttau;
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Rec" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->
        check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t))), (Total.shift cIH)) e (tau2, t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Fun" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Cofun (loc, bs), (TypCobase (l, cid, sp), t)) ->
         let f = fun (CopatApp (loc, dest, csp), e') ->
           let ttau' = synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
           in check cD (cG,cIH) e' ttau'
         in
	 let _ = List.map f bs in
           Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Cofun" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->
	(check (extend_mctx cD (u, cdec, t))
              (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))   e (tau, C.mvar_dot1 t);
          Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("MLam" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e))

    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->
        check cD (cG,cIH) e1 (tau1, t);
        check cD (cG,cIH) e2 (tau2, t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Pair" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (Let (loc, i, (x, e)), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
          check cD (cG', Total.shift cIH) e (tau,t);
          Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Let" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
        let (_ , tau', t') = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        begin match (tau',t') with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cD (cG', (Total.shift (Total.shift cIH))) e (tau,t)
          | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
        end

    | (Box (loc, cM), (TypBox (l, mT), t)) -> (* Offset by 1 *)
        begin try
	  LF.checkMetaObj cD cM (mT, t);
          Typeinfo.Comp.add (getLoc cM) (Typeinfo.Comp.mk_entry cD ttau)
	    ("Box" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e);
          dprint (fun () -> "loc <> metaLoc " ^ string_of_bool(loc <> (getLoc cM)))
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Error.Violation ("Free meta-variable " ^ (Id.render_name u)))
        end
    | (Case (loc, prag, Ann (Box (_, (l,cM)), (TypBox (_, mT) as tau0_sc)), branches), (tau, t)) ->
        let (total_pragma, tau_sc, projOpt) =  (match  cM with
                   | I.ClObj (_ , I.MObj (I.Root (_, I.PVar (x,s) , _ )))
		   | I.ClObj (_ , I.PObj (I.PVar (x,s)))  ->
		       let order = if !Total.enabled && is_indMObj cD x then IndIndexObj (l,cM)  else IndexObj (l,cM) in
                       (order, TypBox(loc, convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), None)
                   | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k ), _ )))
		   | I.ClObj (_, I.PObj (I.Proj (I.PVar (x,s), k))) ->
		       let order = if  !Total.enabled && is_indMObj cD x then IndIndexObj (l,cM) else IndexObj (l,cM) in
                       (order, TypBox (loc, convToParamTyp(Whnf.cnormMetaTyp (mT, C.m_id))), Some k)
		   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x,s), _ ))) ->
		       let order = if  !Total.enabled && is_indMObj cD x then
			 ((* print_string ("\n inductive in " ^ P.metaObjToString cD cM ^ "\n");*) IndIndexObj (l,cM)) else
			   ((* print_string ("\n NOT inductive " ^ P.metaObjToString cD cM ^ "\n in cD = " ^ P.mctxToString cD ^  "\n");*) IndexObj (l,cM)) in
                       (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
		   | I.CObj (I.CtxVar (I.CtxOffset k)) ->
		       let order = if  !Total.enabled && is_indMObj cD k then IndIndexObj (l,cM) else IndexObj (l,cM) in
                       (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
		   | _ ->
		       (IndexObj (l,cM), TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)		       ) in
        let _  = LF.checkMetaObj cD (loc,cM) (mT, C.m_id)  in

        (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Case 1" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e); *)
        let problem = Coverage.make loc prag cD branches tau_sc in
          (* Coverage.stage problem; *)
          checkBranches total_pragma cD (cG,cIH) branches tau0_sc (tau, t);
          Coverage.process problem projOpt

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
		  let tau_s = C.cnormCTyp (tau', t') in
		  let problem = Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) in
		    checkBranches total_pragma cD (cG,cIH) branches tau_s (tau,t);
                    Coverage.process problem None
            end
	in
	  if !Total.enabled then
	    (match i with
	       | Var (_, x)  ->
		   let (f,tau') = lookup cG x in
		    (* let _ = print_string ("\nTotality checking enabled - encountered " ^ P.expSynToString cD cG i ^
			      " with type " ^ P.compTypToString cD tau' ^ "\n") in*)
		   let ind = match Whnf.cnormCTyp (tau', Whnf.m_id) with
		     | TypInd _tau -> ( (*print_string ("Encountered Var " ^
					 P.expSynToString cD cG i ^ " -	INDUCTIVE\n");*)  true)
		     | _ -> ((* print_string ("Encountered Var " ^
					      P.expSynToString cD cG i ^ " -	NON-INDUCTIVE\n");*) false) in
		   if ind then
		     chkBranch IndDataObj cD (cG,cIH) i branches (tau,t)
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
	(Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((Comp.get prog).Comp.typ, C.m_id))  ("Const" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
        if !Total.enabled then
          if (Comp.get prog).Comp.total then
            (None,(Comp.get prog).Comp.typ, C.m_id)
          else
            raise (Error (loc, MissingTotal prog))
        else
          (None,(Comp.get prog).Comp.typ, C.m_id))

    | Apply (loc , e1, e2) ->
        let (cIH_opt , tau1, t1) = syn cD (cG,cIH) e1 in
        let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
        begin match (tau1, t1) with
          | (TypArr (tau2, tau), t) ->
              check cD (cG,cIH) e2 (tau2, t);
              Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau, t)) ("Apply" ^ " " ^ Pretty.Int.DefaultPrinter.expSynToString cD cG e);
              (useIH loc cD cG cIH_opt e2, tau, t)

          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
        end

    | MApp (loc, e, mC) ->
      let (cIH_opt, tau1, t1) = syn cD (cG, cIH) e in
        begin match (C.cwhnfCTyp (tau1,t1)) with
          | (TypPiBox ((I.Decl (_ , ctyp, _)), tau), t) ->
	    LF.checkMetaObj cD mC (ctyp, t);
	    (useIH loc cD cG cIH_opt (Box (loc, mC)), tau, I.MDot(metaObjToMFront mC, t))
          | (tau, t) ->
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
          | (TypBox (_, I.ClTyp (I.MTyp tA, cPhi)) , theta) | (TypBox (_, I.ClTyp (I.PTyp tA, cPhi)), theta) ->
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
          | (TypBox (_, ctyp) , theta) ->
              LF.checkMetaObj cD mO (ctyp, theta)
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

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    LF.checkMetaObj cD mO (ctyp, theta);
    I.MDot(metaObjToMFront mO, theta)

  and checkBranches caseTyp cD cG branches tau_s ttau =
    List.iter (fun branch -> checkBranch caseTyp cD cG branch tau_s ttau) branches

  and checkBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
      | EmptyBranch (loc, cD1', pat, t1) ->
          let _ = dprint (fun () -> "\nCheckBranch - Empty Pattern\n") in
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
            (LF.checkMSub  loc cD1' t1 cD;
            checkPattern cD1' I.Empty pat (tau_p, Whnf.m_id))

      | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) ->
(*         let _ = print_string ("\nCheckBranch with meta-obj pattern : " ^  P.metaObjToString cD1'  mO
				^ "\nwhere scrutinee has type " ^
				P.compTypToString cD tau_s ^ "\n") in *)
          let TypBox (_, mT) = tau_s in
          (* By invariant: cD1' |- t1 <= cD *)
	  let mT1   = Whnf.cnormMetaTyp (mT, t1) in
          let cG'   = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
          let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
          let (cD1',cIH')  = if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (loc', mO)) then
         	               let cD1' = mvarsInPatt cD1' (PatMetaObj(loc', mO)) in
				 (* print_string "Inductive and Structurally smaller\n"; *)
				 (cD1', Total.wf_rec_calls cD1' (I.Empty))
			     else (cD1', I.Empty) in
	  let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD
     	             else cD1' in
	  (* let _ = print_string ("Outer cD = " ^ P.mctxToString cD ^ "\nInner cD' = " ^ P.mctxToString cD1' ^ "\n\n") in *)
            (LF.checkMSub loc cD1' t1 cD;
	     LF.checkMetaObj cD1' mO (mT1, C.m_id);
             check cD1' (cG', Context.append cIH cIH') e1 (tau', Whnf.m_id))

      | Branch (loc, cD1', cG1, pat, t1, e1) ->
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
          let cG'   = Whnf.cnormCtx (cG, t1) in
          let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
(*          let _     = print_string ("\nCheckBranch with general pattern:" ^ P.patternToString  cD1' cG1 pat ^ "\n") in
         let _ = print_string ("\nwhere scrutinee has type" ^
				P.compTypToString cD tau_s ^ "\n") in *)
	  let k     = Context.length cG1 in
	  let cIH0  = Total.shiftIH cIH k in
          let (cD1', cIH')  = if is_inductive caseTyp && Total.struct_smaller pat then
                       let cD1' = mvarsInPatt cD1' pat in (cD1', Total.wf_rec_calls cD1' cG1)
                     else (cD1', I.Empty) in
	  let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD
     	             else cD1' in
	  (* let _ = print_string ("\nOuter cD = " ^ P.mctxToString cD ^ "\nInner cD' = " ^ P.mctxToString cD1' ^ "\nGiven ref. subst. = " ^ P.msubToString cD1' t1 ^ "\n") in *)
          (LF.checkMSub loc  cD1' t1 cD;
           checkPattern cD1' cG1 pat (tau_p, Whnf.m_id);
           check cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') e1 (tau', Whnf.m_id))

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
