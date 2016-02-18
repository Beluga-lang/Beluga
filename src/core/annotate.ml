module P = Pretty.Int.DefaultPrinter
module PE = Pretty.Ext.DefaultPrinter
module R = Store.Cid.DefaultRenderer
(* open Printf *)

(* let loc_ghost = Syntax.Loc.ghost; *)

(* let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5]) *)

(* module LF = struct *)

(*   (\* open Context *\) *)
(*   (\* open Store.Cid *\) *)
(*   open Syntax.Int.LF *)

(*   module Unify = Unify.EmptyTrail *)

(*   (\* type error = *\) *)
(*   (\*   | AnnotError of string *\) *)
(*   (\*   | NothingIsEverWrong *\) *)
(*     (\* | CtxVarMisCheck   of mctx * dctx * tclo * schema *\) *)
(*     (\* | CtxVarMismatch   of mctx * ctx_var * schema *\) *)
(*     (\* | CtxVarDiffer     of mctx * ctx_var * ctx_var *\) *)
(*     (\* | CheckError       of mctx * dctx * nclo * tclo *\) *)
(*     (\* | TupleArity       of mctx * dctx * nclo * trec_clo *\) *)
(*     (\* | SigmaMismatch    of mctx * dctx * trec_clo * trec_clo *\) *)
(*     (\* | KindMismatch     of mctx * dctx * sclo * (kind * sub) *\) *)
(*     (\* | TypMismatch      of mctx * dctx * nclo * tclo * tclo *\) *)
(*     (\* | IllTypedSub      of mctx * dctx * sub * dctx *\) *)
(*     (\* | SpineIllTyped    of int * int *\) *)
(*     (\* | LeftoverFV *\) *)
(*     (\* | ParamVarInst     of mctx * dctx * tclo *\) *)
(*     (\* | CtxHatMismatch   of mctx * dctx (\\* expected *\\) * psi_hat (\\* found *\\) * (Syntax.Loc.t * mfront) *\) *)
(*     (\* | IllTypedMetaObj  of mctx * clobj * dctx * cltyp  *\) *)
(*     (\* | TermWhenVar      of mctx * dctx * normal *\) *)
(*     (\* | SubWhenRen       of mctx * dctx * sub *\) *)

(*   (\* exception Error of Syntax.Loc.t * error *\) *)

(*   (\* let _ = Error.register_printer *\) *)
(*   (\* 	    (fun (Error (loc, err)) -> *\) *)
(*   (\* 	     Error.print_with_location loc (fun ppf -> *\) *)
(*   (\* 					    match err with *\) *)
(*   (\* 					    | AnnotError s -> *\) *)
(*   (\* 					       Format.fprintf ppf "%s" s)) *\) *)

(*   let rec annMetaObj cD (loc, cM) cTt = *)
(*     annMetaObj' cD (loc, cM) cTt *)

(*   and annMetaObj' cD (loc, cM) cTt = (loc, cM) *)

(* end *)

module Comp = struct

  module Unify = Unify.EmptyTrail

  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type error =
    | MismatchChk     of I.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of I.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of I.mctx * gctx * pattern * tclo * tclo
    | PairMismatch    of I.mctx * gctx  * tclo
    | BoxMismatch     of I.mctx * gctx  * tclo
    | IfMismatch      of I.mctx * gctx  * tclo
    | EqMismatch      of I.mctx * tclo (* arg1 *) * tclo (* arg2 *)
    | EqTyp           of I.mctx * tclo
    | TypMismatch     of I.mctx * tclo * tclo
    | InvalidRecCall
    | AnnotError of string
    | MissingTotal of Id.cid_prog

  exception Error of Syntax.Loc.t * error

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT

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
          | BoxMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found box-expression that does not have type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | IfMismatch (cD, _cG, theta_tau) ->
            Error.report_mismatch ppf
              "Type error in guard of if expression."
	      "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) TypBool
	      "Actual type"   (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | PairMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found tuple, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          (* | Typmismatch (cD, (tau1, theta1), (tau2, theta2)) -> *)
          (*     Error.report_mismatch ppf *)
          (*       "Type of destructor did not match the type it was expected to have." *)
          (*       "Type of destructor" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) *)
          (*       (Whnf.cnormCTyp (tau1, theta1)) *)
          (*       "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) *)
          (*       (Whnf.cnormCTyp (tau2, theta2))) *)

	  | AnnotError s ->
	     Format.fprintf ppf "%s" s
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

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

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
			Total.filter cD cG cIH (loc, M cM)
		   | Syn(_, i) -> (match extract_var i with
				   | Some x -> Total.filter cD cG cIH (loc, V x)
				   | None ->  Total.filter cD cG cIH (loc, E))
       (* | _      -> raise (Error (loc, InvalidRecCall)) *)
       in
       (* We have now partially checked for the recursive call *)
       match cIH with
       | I.Dec(_ , WfRec (_, [], _ )) ->
	  (* We have fully used a recursive call and we now are finished checking for
           well-formedness of rec. call. *)
          None
       | I.Empty -> raise (Error (loc, InvalidRecCall))
       | _ -> Some cIH


  let mk_typ_str cD ttau : string option =
    if !Typeinfo.generate_annotations then
      Some (P.subCompTypToString cD ttau)
    else
      None

  let rec ann cD cG e ttau =
    let cIH = I.Empty in
    annotate cD (cG, cIH) e ttau

  (* Use this version of the function to insert debug output *)
  and annotate cD (cG, cIH) e ttau =
    annotate' cD (cG, cIH) e ttau

  and annotate' cD (cG, cIH) e ttau = match (e, ttau) with

    | (Fun (loc, x, e'), (TypArr (tau1, tau2), t)) ->
       let e'' =
	 annotate cD (I.Dec (cG, CTypDecl (x, TypClo (tau1, t))), (Total.shift cIH))
		  e' (tau2, t)
       in
       Annotated.Comp.Fun (loc, x, e'', ttau, mk_typ_str cD ttau)

    | (Cofun (loc', bs), (TypCobase (l, cid, sp), t)) ->
       let f =
    	 fun (CopatApp (ca_loc, dest, csp), e) ->
    	 begin
    	   let (ttau', csp') =
    	     synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
    	   in
    	   let e' = annotate cD (cG, cIH) e ttau' in
    	   (Annotated.Comp.CopatApp (ca_loc, dest, csp'), e')
    	 end
       in
       let bs' = List.map f bs in
       Annotated.Comp.Cofun (loc', bs', ttau, mk_typ_str cD ttau)

    (* This is an implicit MLam *)
    | (MLam (_, u, e'), (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       let e'' =
	 annotate (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  e' (tau, C.mvar_dot1 t)
       in
       e''

    | (MLam (loc, u, e'), (TypPiBox (I.Decl (_, cU, I.No) as cdec, tau), t)) ->
       let e'' =
	 annotate (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  e' (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc, u, e'', ttau, mk_typ_str cD ttau)

    | (MLam (loc, u, e'), (TypPiBox (I.Decl (_, cU, I.Inductive) as cdec, tau), t)) ->
       let e'' =
	 annotate (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  e' (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc, u, e'', ttau, mk_typ_str cD ttau)

    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->
       let e1' = annotate cD (cG, cIH) e1 (tau1, t) in
       let e2' = annotate cD (cG, cIH) e2 (tau2, t) in
       Annotated.Comp.Pair (loc, e1', e2', ttau, mk_typ_str cD ttau)

    | (Let (loc, i, (x, e')), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
       let e'' = annotate cD (cG', Total.shift cIH) e' (tau, t) in
       Annotated.Comp.Let (loc, i', (x, e''), ttau, mk_typ_str cD ttau)

    | (LetPair (loc, i, (x, y, e')), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypCross (tau1, tau2), t') ->
	    let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))),
			     CTypDecl (y, TypClo (tau2, t')))
	    in
	    let e'' =
	      annotate cD (cG', Total.shift (Total.shift cIH)) e' (tau, t)
	    in
	    Annotated.Comp.LetPair (loc, i', (x, y, e''), ttau, mk_typ_str cD ttau)
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
       end

    | (Box (loc, cM), (TypBox (l, mT), t)) ->
       begin
	 try
	   (* TODO LF.annMetaObj *)
	   let cM' = cM (* LF.annMetaObj cD int_cM ext_cM (mT, t) *)
	   in
	   Annotated.Comp.Box (loc, cM', ttau, mk_typ_str cD ttau)
	 with C.FreeMVar (I.FMVar (u, _)) ->
	   raise (Error.Violation ("Free meta-variable " ^ (Id.render_name u)))
       end

    | (Case (loc, prag, Ann (Box (_, (l, cM)), (TypBox (_, mT) as tau0_sc)), branches),
       (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
	 begin
	   match cM with
	   | I.ClObj (_, I.MObj (I.Root (_, I.PVar (x,s), _)))
	   | I.ClObj (_, I.PObj (I.PVar (x, s))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc, convToParamTyp (C.cnormMetaTyp (mT, C.m_id))), None)
	   | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k), _)))
	   | I.ClObj (_, I.PObj (I.Proj (I.PVar (x, s), k))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc, convToParamTyp (C.cnormMetaTyp (mT, C.m_id))), Some k)
	   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x, s), _))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc, C.cnormMetaTyp (mT, C.m_id)), None)
	   | I.CObj (I.CtxVar (I.CtxOffset k)) ->
	      let order = if !Total.enabled && is_indMObj cD k then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc, C.cnormMetaTyp (mT, C.m_id)), None)
	   | _ ->
	      (IndexObj (l, cM), TypBox (loc, C.cnormMetaTyp (mT, C.m_id)), None)
	 end
       in
       (* TODO annMetaObj *)
       (* let _ = () (\* LF.annMetaObj cD (loc, cM) (mT, C.m_id) *\) in *)
       let problem = Coverage.make loc prag cD branches tau_sc in
       let branches' =
	 annBranches total_pragma cD (cG, cIH) branches tau0_sc (tau, t)
       in
       Coverage.process problem projOpt;
       (* TODO What are we doing here? What's the correct substituion? *)
       Annotated.Comp.Case (loc, prag,
		       Annotated.Comp.Ann
			 (Annotated.Comp.Box (loc, (l, cM),
					      (tau0_sc, C.m_id), mk_typ_str cD (tau0_sc, C.m_id)),
			  tau0_sc,
			  (tau0_sc, C.m_id), mk_typ_str cD (tau0_sc, C.m_id)),
		       branches', ttau, mk_typ_str cD ttau)

    | (Case (loc, prag, i, branches), (tau, t)) ->
       let anBranch total_pragma cD (cG, cIH) i branches (tau, t) =
	 let ((_, tau', t'), i') = syn cD (cG, cIH) i in
	 begin
	   match C.cwhnfCTyp (tau', t') with
	   | (TypBox (loc', mT), t') ->
	      let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
	      let problem = Coverage.make loc prag cD branches tau_s in
	      Coverage.process problem None;
	      (i', annBranches total_pragma cD (cG, cIH) branches tau_s (tau, t))
	   | (tau', t') ->
	      let tau_s = C.cnormCTyp (tau', t') in
	      let problem = Coverage.make loc prag cD branches (C.cnormCTyp (tau',t')) in
	      Coverage.process problem None;
	      (i', annBranches total_pragma cD (cG, cIH) branches tau_s (tau, t))
	 end
       in
       if !Total.enabled then
	 begin
	   match i with
	   | Var (loc', x) ->
	      let (f, tau') = lookup cG x in
	      let ind =
		begin
		  match C.cnormCTyp (tau', C.m_id) with
		  | TypInd _tau -> true
		  | _ -> false
		end
	      in
	      if ind then
		let (i', branches') =
		  anBranch IndDataObj cD (cG, cIH) i branches (tau, t)
		in
		Annotated.Comp.Case (loc, prag, i', branches', ttau, mk_typ_str cD ttau)
	      else
		let (i', branches') =
		  anBranch DataObj cD (cG, cIH) i branches (tau, t)
		in
		Annotated.Comp.Case (loc, prag, i', branches', ttau, mk_typ_str cD ttau)
	   | _ ->
	      let (i', branches') =
		anBranch DataObj cD (cG, cIH) i branches (tau, t)
	      in
	      Annotated.Comp.Case (loc, prag, i', branches', ttau, mk_typ_str cD ttau)
	 end
       else
	 let (i', branches') =
	   anBranch DataObj cD (cG, cIH) i branches (tau, t)
	 in
	 Annotated.Comp.Case (loc, prag, i', branches', ttau, mk_typ_str cD ttau)

    | (Syn (loc, i), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       if C.convCTyp (tau, t) (tau', t') then
	 begin
	   Annotated.Comp.Syn (loc, i', ttau, mk_typ_str cD ttau)
	 end
       else
	 raise (Error (loc, MismatchChk (cD, cG, e, (tau, t), (tau', t'))))

    (* TODO *)
    (* Changed to be in line with the actual type checker *)
    (* But note that the checks for e1 and e2 are wrong *)
    | (If (loc, i, e1, e2), (tau, t)) ->
       let ((_flag, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypBool, _) ->
	    let e1' = annotate cD (cG, cIH) e1 (tau, t) in
	    let e2' = annotate cD (cG, cIH) e1 (tau, t) in
	    Annotated.Comp.If (loc, i', e1', e2', ttau, mk_typ_str cD ttau)
	 | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | Hole (loc, f), (tau, t) ->
       Annotated.Comp.Hole (loc, f, ttau, mk_typ_str cD ttau)

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    (* TODO annMetaObj *)
    (* LF.checkMetaObj cD mO (ctyp, theta); *)
    I.MDot(metaObjToMFront mO, theta)

  and synObs cD csp ttau1 ttau2 = match (csp, ttau1, ttau2) with
    | (CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) ->
       if C.convCTyp (tau1, theta) (tau', theta') then
         ((tau2, theta), Annotated.Comp.CopatNil loc)
       else
         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))
    | (CopatApp (loc, dest, csp'), (TypArr (tau1, tau2), theta), (tau', theta')) ->
       if C.convCTyp (tau1, theta) (tau', theta') then
         let ((tau'', theta''), csp'') =
	   synObs cD csp' ((CompDest.get dest).CompDest.typ, Whnf.m_id) (tau2, theta)
	 in
	 ((tau'', theta''), Annotated.Comp.CopatApp (loc, dest, csp''))
       else
         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))

  and syn cD (cG, cIH) i =
    syn' cD (cG, cIH) i

  and syn' cD (cG, cIH) i = match i with
    | Var (loc, x) ->
       let (f, tau') = lookup cG x in
       let tau =
	 match C.cnormCTyp (tau', C.m_id) with
	 | TypInd tau -> tau
	 | _ -> tau'
       in
       if Total.exists_total_decl f then
	 ((Some cIH, tau, C.m_id),
	  Annotated.Comp.Var (loc, x, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))
       else
	 ((None, tau, C.m_id),
	  Annotated.Comp.Var (loc, x, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | DataConst (loc, c) ->
       let tau = (CompConst.get c).CompConst.typ in
       ((None, tau, C.m_id),
	Annotated.Comp.DataConst (loc, c, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | DataDest (loc, c) ->
       let tau = (CompDest.get c).CompDest.typ in
       ((None, tau, C.m_id),
	Annotated.Comp.DataDest (loc, c, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | Const (loc, prog) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	     let tau = (Comp.get prog).Comp.typ in
	     ((None, tau, C.m_id),
	      Annotated.Comp.Const (loc, prog, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	   let tau = (Comp.get prog).Comp.typ in
	   ((None, tau, C.m_id),
	    Annotated.Comp.Const (loc, prog, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | Apply (loc, i', e) ->
       let ((cIH_opt, tau1, t1), i'') = syn cD (cG, cIH) i' in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       begin
	 match (tau1, t1) with
	 | (TypArr (tau2, tau), t) ->
	    let e' = annotate cD (cG, cIH) e (tau2, t) in
	    ((useIH loc cD cG cIH_opt e, tau, t),
	     Annotated.Comp.Apply (loc, i'', e', (tau, t), mk_typ_str cD (tau, t)))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, i', VariantArrow, (tau, t))))
       end

    | MApp (loc, i', mC) ->
       begin
	 let ((cIH_opt, tau1, t1), i'') = syn cD (cG, cIH) i' in
	 begin
	   match (C.cwhnfCTyp (tau1, t1)) with
	   | (TypPiBox (I.Decl (_, ctyp, I.Maybe), tau), t) ->
	      (* This is an implicit argument, so we toss it for the annotated tree *)
	      (* let mC' = mC (\* LF.annMetaObj cD int_mC ext_mC (ctyp, t) *\) in *)
	      let t = I.MDot (metaObjToMFront mC, t) in
	      ((useIH loc cD cG cIH_opt (Box (loc, mC)), tau, t), i'')
	   | (TypPiBox (I.Decl (_, ctyp, _), tau), t) ->
	      let mC' = mC (* LF.annMetaObj cD int_mC ext_mC (ctyp, t) *) in
	      let t = I.MDot (metaObjToMFront mC, t) in
	      ((useIH loc cD cG cIH_opt (Box (loc, mC)), tau, t),
	       Annotated.Comp.MApp (loc, i'', mC', (tau, t), mk_typ_str cD (tau, t)))
	   | (tau, t) ->
	      raise (Error (loc, MismatchSyn (cD, cG, i', VariantPiBox, (tau, t))))
	 end
       end

    | PairVal (loc, i1, i2)->
       let ((_, tau1, t1), i1') = syn cD (cG, cIH) i1 in
       let ((_, tau2, t2), i2') = syn cD (cG, cIH) i2 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       let (tau2, t2) = C.cwhnfCTyp (tau2, t2) in
       let tau = TypCross (TypClo (tau1, t1), TypClo (tau2, t2)) in
       ((None, tau, C.m_id),
	Annotated.Comp.PairVal (loc, i1', i2', (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | Ann (e, tau) ->
       let e' = annotate cD (cG, cIH) e (tau, C.m_id) in
       ((None, tau, C.m_id),
	Annotated.Comp.Ann (e', tau, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | Equal (loc, i1, i2) ->
       let ((_, tau1, t1), i1') = syn cD (cG, cIH) i1 in
       let ((_, tau2, t2), i2') = syn cD (cG, cIH) i2 in
       if C.convCTyp (tau1, t1) (tau2, t2) then
	 begin
	   match C.cwhnfCTyp (tau1, t1) with
	   | (TypBox _, _) ->
	      ((None, TypBool, C.m_id),
	       Annotated.Comp.Equal (loc, i1', i2', (TypBool, C.m_id),
				     mk_typ_str cD (TypBool, C.m_id)))
	   | (TypBool, _) ->
	      ((None, TypBool, C.m_id),
	       Annotated.Comp.Equal (loc, i1', i2', (TypBool, C.m_id),
				     mk_typ_str cD (TypBool, C.m_id)))
	   | (tau1, t1) ->
	      raise (Error (loc, EqTyp (cD, (tau1, t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1, t1), (tau2, t2))))

    | Boolean b ->
       ((None, TypBool, C.m_id),
	Annotated.Comp.Boolean (b, (TypBool, C.m_id), mk_typ_str cD (TypBool, C.m_id)))

  and annBranches caseTyp cD (cG, cIH) branches tau_s ttau =
    List.map (fun branch -> annBranch caseTyp cD (cG, cIH) branch tau_s ttau) branches

  and annBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
    | EmptyBranch (loc, cD1', pat, t1) ->
       let tau_p = C.cnormCTyp (tau_s, t1) in
       let pat' = annPattern cD1' I.Empty pat (tau_p, Whnf.m_id) in
       Annotated.Comp.EmptyBranch (loc, cD1', pat', t1)

    | Branch (loc, cD1', cG, PatMetaObj (l1', mO), t1, e) ->
       (* let TypBox (_, mT) = tau_s in *)
       (* let mT1 = C.cnormMetaTyp (mT, t1) in *)
       let cG' = C.cnormCtx (C.normCtx cG, t1) in
       let cIH = C.cnormCtx (C.normCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (l1', mO)) then
	   let cD1' = mvarsInPatt cD1' (PatMetaObj (l1', mO)) in
	   (cD1', Total.wf_rec_calls cD1' (I.Empty))
	 else
	   (cD1', I.Empty)
       in
       let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD else cD1' in
       (* LF.annMSub loc cD1' t1 cD; *)
       let mO' = mO  (* LF.annMetaObj cD1' int_mO ext_mO (mT1, C.m_id) *) in
       let e' = annotate cD1' (cG', Context.append cIH cIH') e (tau', C.m_id)
       in
       Annotated.Comp.Branch (loc, cD1', cG,
			      Annotated.Comp.PatMetaObj
				(l1', mO', (tau_s, C.m_id), mk_typ_str cD (tau_s, C.m_id))
			      , t1, e')

    | Branch (loc, cD1', cG1, pat, t1, e) ->
       let tau_p = C.cnormCTyp (tau_s, t1) in
       let cG' = C.cnormCtx (cG, t1) in
       let cIH = C.cnormCtx (C.normCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let k = Context.length cG1 in
       let cIH0 = Total.shiftIH cIH k in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller pat then
	   let cD1' = mvarsInPatt cD1' pat in
	   (cD1', Total.wf_rec_calls cD1' cG1)
	 else
	   (cD1', I.Empty)
       in
       let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD else cD1' in
       (* LF.annMSub loc cD1' t1 cD;  *)
       let pat' = annPattern cD1' cG1 pat (tau_p, C.m_id) in
       let e' =
	 annotate cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') e (tau', C.m_id)
       in
       Annotated.Comp.Branch (loc, cD1', cG1, pat', t1, e')

  and annPattern cD cG pat ttau =
    annPattern' cD cG pat ttau

  and annPattern' cD cG pat ttau = match pat with
    | PatEmpty (loc, cPsi) ->
       begin
	 match ttau with
	 | (TypBox (_, I.ClTyp (I.MTyp tA, cPsi)), theta)
	 | (TypBox (_, I.ClTyp (I.PTyp tA, cPsi)), theta) ->
	    if C.convDCtx (C.cnormDCtx (cPsi, theta)) cPsi then
	      begin
		Annotated.Comp.PatEmpty (loc, cPsi, ttau, mk_typ_str cD ttau)
	      end
	    else
	      raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
	 | _ ->
	    raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatMetaObj (loc, mO) ->
       begin
	 match ttau with
	 | (TypBox (_, ctyp), theta) ->
	    let mO' = mO (* LF.annMetaObj cD int_mO ext_mO (ctyp, theta) *) in
	    Annotated.Comp.PatMetaObj (loc, mO', ttau, mk_typ_str cD ttau)
	 | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatPair (loc, pat1, pat2) ->
       begin
	 match ttau with
	 | (TypCross (tau1, tau2), theta) ->
	    let pat1' = annPattern cD cG pat1 (tau1, theta) in
	    let pat2' = annPattern cD cG pat2 (tau2, theta) in
	    Annotated.Comp.PatPair (loc, pat1', pat2', ttau, mk_typ_str cD ttau)
	 | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau)))
       end

    | pat' ->
       let ((loc, ttau'), pat'') = synPattern cD cG pat' in
       let tau' = C.cnormCTyp ttau' in
       let tau = C.cnormCTyp ttau in
       let ttau' = (tau', C.m_id) in
       let ttau = (tau, C.m_id) in
       if C.convCTyp ttau ttau' then
	 pat''
       else
	 raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat =
    synPattern' cD cG pat

  and synPattern' cD cG pat = match pat with
    | PatConst (loc, c, pat_spine) ->
       (* TODO We might not need this now. *)
       (* This function strips away the implicit arguments *)
       (* let rec handle_implicits count pat_spine ttau = *)
       (* 	 begin *)
       (* 	   match count with *)
       (* 	   | 0 -> (tau, pat_spine) *)
       (* 	   | count' -> *)
       (* 	      begin *)
       (* 		match pat_spine with *)
       (* 		(\* | PatNil -> 	(\\* This shouldn't happen, I think *\\) *\) *)
       (* 		| PatApp (_, pat', pat_spine') -> *)
       (* 		   (\* We have to handle the type of the pattern too *\) *)
       (* 		   let ttau' = *)
       (* 		     begin *)
       (* 		       match ttau with *)
       (* 		       | (TypArr (tau1, tau2), theta) -> *)
       (* 			  (tau2, theta) *)
       (* 		       | (TypPiBox (cdecl, tau'), theta) -> *)
       (* 			  let theta' = checkPatAgainstCDecl cD int_pat' (cdecl, theta) in *)
       (* 			  (tau', theta') *)
       (* 		     end *)
       (* 		   in *)
       (* 		   handle_implicits (count' - 1) pat_spine' ttau' *)
       (* 	      end *)
       (* 	 end *)
       (* in *)
       (* let (ttau', pat_spine') = *)
       (* 	 handle_implicits (CompConst.get_implicit_arguments c) pat_spine (tau, C.m_id) *)
       (* in *)
       let tau = (CompConst.get c).CompConst.typ in
       let ttau = (tau, C.m_id) in
       let (ttau', pat_spine') =
	 synPatSpine cD cG pat_spine ttau
       in
       ((loc, ttau'),
	Annotated.Comp.PatConst (loc, c, pat_spine', ttau', mk_typ_str cD ttau'))

    | PatVar (loc, k) ->
       let tau = lookup' cG k in
       ((loc, (tau, C.m_id)),
	Annotated.Comp.PatVar (loc, k, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

    | PatTrue loc ->
       ((loc, (TypBool, C.m_id)),
	Annotated.Comp.PatTrue (loc, (TypBool, C.m_id), mk_typ_str cD (TypBool, C.m_id)))

    | PatFalse loc ->
       ((loc, (TypBool, C.m_id)),
	Annotated.Comp.PatFalse (loc, (TypBool, C.m_id), mk_typ_str cD (TypBool, C.m_id)))

    | PatAnn (loc, pat', tau) ->
       let pat'' = annPattern cD cG pat' (tau, C.m_id) in
       ((loc, (tau, C.m_id)),
	Annotated.Comp.PatAnn (loc, pat'', tau, (tau, C.m_id), mk_typ_str cD (tau, C.m_id)))

  and synPatSpine cD cG pat_spine (tau, theta) =
    synPatSpine' cD cG pat_spine (tau, theta)


  and synPatSpine' cD cG pat_spine (tau, theta) =
    match pat_spine with
    | PatNil ->
       ((tau, theta), Annotated.Comp.PatNil ((tau, theta), mk_typ_str cD (tau, theta)))
    | PatApp (loc, pat, pat_spine') ->
       begin
	 match (tau, theta) with
	 | (TypArr (tau1, tau2), theta) ->
	    let pat' = annPattern cD cG pat (tau1, theta) in
	    let (ttau, pat_spine'') = synPatSpine cD cG pat_spine' (tau2, theta) in
	    (ttau, Annotated.Comp.PatApp (loc, pat', pat_spine'', ttau, mk_typ_str cD ttau))
	 | (TypPiBox ((I.Decl (_, ctyp, I.Maybe)) as cdecl, tau'), theta) ->
	    (* This case is implicit, drop it *)
	    let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
	    (* let tau = TypBox (loc, ctyp) in *)
	    (* let pat' = annPattern cD cG pat (tau, theta) in *)
	    let (ttau, pat_spine'') = synPatSpine cD cG pat_spine' (tau', theta') in
	    (ttau, pat_spine'')
	 | (TypPiBox ((I.Decl (_, ctyp, _)) as cdecl, tau'), theta) ->
	    let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
	    let tau = TypBox (loc, ctyp) in
	    let pat' = annPattern cD cG pat (tau, theta) in
	    let (ttau, pat_spine'') = synPatSpine cD cG pat_spine' (tau', theta') in
	    (ttau, Annotated.Comp.PatApp (loc, pat', pat_spine'', ttau, mk_typ_str cD ttau))
       end
end

module Sgn = struct

end
