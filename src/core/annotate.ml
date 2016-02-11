module P = Pretty.Int.DefaultPrinter
module PE = Pretty.Ext.DefaultPrinter
module R = Store.Cid.DefaultRenderer
open Printf

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5])

module LF = Lfcheck

module Comp = struct

  module Unify = Unify.EmptyTrail

  open Store.Cid
  open Syntax.Int.Comp
  module SE = Syntax.Ext

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


  (* Use this version of the function to insert debug output *)
  let rec ann cD (cG, cIH) int_e ext_e ttau =
    annotate cD (cG, cIH) int_e ext_e ttau

  and annotate cD (cG, cIH) int_e ext_e ttau =
    annotate' cD (cG, cIH) int_e ext_e ttau

  and annotate' cD (cG, cIH) int_e ext_e ttau = match (int_e, ext_e, ttau) with
    (* | (Rec (loc', int_f, int_e'), SE.Comp.Rec (loc, _, ext_e'), (tau, t)) -> *)
    (*	 let int_e'' = *)
    (*	   annotate cD (I.Dec (cG, CTypDecl (int_f, TypClo (tau, t))), (Total.shift cIH)) *)
    (*		    int_e' ext_e' ttau *)
    (*	 in *)
    (*	 Annotated.Comp.Rec (loc', int_f, int_e'', ttau) *)

    | (Fun (loc', int_x, int_e'), SE.Comp.Fun (loc, _, ext_e'), (TypArr (tau1, tau2), t)) ->
       let int_e'' =
	 annotate cD (I.Dec (cG, CTypDecl (int_x, TypClo (tau1, t))), (Total.shift cIH))
		  int_e' ext_e' (tau2, t)
       in
       Annotated.Comp.Fun (loc', int_x, int_e'', ttau, Annotated.ExpTerm)

    (* TODO: Cofuns*)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc', int_u, int_e'', ttau, Annotated.ImpTerm)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.No) as cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc', int_u, int_e'', ttau, Annotated.ExpTerm)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.Inductive) as cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc', int_u, int_e'', ttau, Annotated.ExpTerm)

    (* (\* TODO: Unknown MLams *\) *)
    (* | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'), *)
    (*	 (TypPiBox (cdec, tau), t)) -> *)
    (*	 let int_e'' = *)
    (*	   annotate cD (extend_mctx cD (u, cdec, t)) *)
    (*		    (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1)) *)
    (*		    int_e' ext_e' (tau, C.mvar_dot1 t) *)
    (*	 in *)
    (*	 Annotated.Comp.MLam (loc', int_u, int_e'', ttau, Annotated.ExpTerm) *)

    | (Pair (loc', int_e1, int_e2), SE.Comp.Pair (loc, ext_e1, ext_e2),
       (TypCross (tau1, tau2), t)) ->
       let int_e1' = annotate cD (cG, cIH) int_e1 ext_e1 (tau1, t) in
       let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau2, t) in
       Annotated.Comp.Pair (loc', int_e1', int_e2', ttau, Annotated.ExpTerm)

    | (Let (loc', int_i, (int_x, int_e')), SE.Comp.Let (loc, ext_i, (_, ext_e')),
       (tau, t)) ->
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (int_x, TypClo (tau', t'))) in
       let int_e'' = annotate cD (cG', Total.shift cIH) int_e' ext_e' (tau, t) in
       Annotated.Comp.Let (loc', int_i', (int_x, int_e''), ttau, Annotated.ExpTerm)

    | (LetPair (loc', int_i, (int_x, int_y, int_e')),
       SE.Comp.LetPair (loc, ext_i, (_, _, ext_e')),
       (tau, t)) ->
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypCross (tau1, tau2), t') ->
	    let cG' = I.Dec (I.Dec (cG, CTypDecl (int_x, TypClo (tau1, t'))),
			     CTypDecl (int_y, TypClo (tau2, t')))
	    in
	    let int_e'' =
	      annotate cD (cG', Total.shift (Total.shift cIH)) int_e' ext_e' (tau, t)
	    in
	    Annotated.Comp.LetPair (loc', int_i', (int_x, int_y, int_e''), ttau, Annotated.ExpTerm)
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
       end

    | (Box (loc', int_cM), SE.Comp.Box (loc, ext_cM), (TypBox (l, mT), t)) ->
       begin
	 try
	   (* TODO LF.annMetaObj *)
	   let int_cM' = int_cM (* LF.annMetaObj cD int_cM ext_cM (mT, t) *)
	   in
	   Annotated.Comp.Box (loc, int_cM', ttau, Annotated.ExpTerm)
	 with C.FreeMVar (I.FMVar (u, _)) ->
	   raise (Error.Violation ("Free meta-variable " ^ (Id.render_name u)))
       end

    | (Case (loc', int_prag, Ann (Box (_, (l, cM)), (TypBox (_, mT) as tau0_sc)), int_branches),
       SE.Comp.Case (loc, ext_prag, ext_i, ext_branches),
       (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
	 begin
	   match cM with
	   | I.ClObj (_, I.MObj (I.Root (_, I.PVar (x,s), _)))
	   | I.ClObj (_, I.PObj (I.PVar (x,s ))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc', convToParamTyp (C.cnormMetaTyp (mT, C.m_id))), None)
	   | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k), _)))
	   | I.ClObj (_, I.PObj (I.Proj (I.PVar (x, s), k))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc', convToParamTyp (C.cnormMetaTyp (mT, C.m_id))), Some k)
	   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x, s), _))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc', C.cnormMetaTyp (mT, C.m_id)), None)
	   | I.CObj (I.CtxVar (I.CtxOffset k)) ->
	      let order = if !Total.enabled && is_indMObj cD k then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc', C.cnormMetaTyp (mT, C.m_id)), None)
	   | _ ->
	      (IndexObj (l, cM), TypBox (loc', C.cnormMetaTyp (mT, C.m_id)), None)
	 end
       in
       let _ = () (* LF.annMetaObj cD (loc, cM) (mT, C.m_id) *) in
       let problem = Coverage.make loc int_prag cD int_branches tau_sc in
       let int_branches' =
	 annBranches total_pragma cD (cG, cIH) int_branches ext_branches tau0_sc (tau, t)
       in
       Coverage.process problem projOpt;
       (* TODO What are we doing here? What's the correct substituion? *)
       Annotated.Comp.Case (loc', int_prag,
		       Annotated.Comp.Ann
			 (Annotated.Comp.Box (loc, (l, cM), (tau0_sc, C.m_id), Annotated.ExpTerm),
			  tau0_sc,
			  (tau0_sc, C.m_id),
			  Annotated.ExpTerm),
		       int_branches', ttau, Annotated.ExpTerm)

    | (Case (loc', int_prag, int_i, int_branches),
       SE.Comp.Case (loc, ext_prag, ext_i, ext_branches),
       (tau, t)) ->
       let anBranch total_pragma cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t) =
	 let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
	 begin
	   match C.cwhnfCTyp (tau', t) with
	   | (TypBox (loc'', mT), t') ->
	      let tau_s = TypBox (loc'', C.cnormMetaTyp (mT, t')) in
	      let problem = Coverage.make loc int_prag cD int_branches tau_s in
	      Coverage.process problem None;
	      (int_i',
	       annBranches total_pragma cD (cG, cIH) int_branches ext_branches tau_s (tau,t))
	   | (tau', t') ->
	      let tau_s = C.cnormCTyp (tau', t') in
	      let problem = Coverage.make loc int_prag cD int_branches (C.cnormCTyp (tau',t')) in
	      Coverage.process problem None;
	      (int_i',
	      annBranches total_pragma cD (cG, cIH) int_branches ext_branches tau_s (tau, t))
	 end
       in
       if !Total.enabled then
	 begin
	   match int_i, ext_i with
	   | Var (loc', x), SE.Comp.Var (loc, _) ->
	      let (f, tau') = lookup cG x in
	      let ind =
		match C.cnormCTyp (tau', C.m_id) with
		| TypInd _tau -> true
		| _ -> false
	      in
	      if ind then
		let (int_i', int_branches') =
		  anBranch IndDataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
		in
		Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExpTerm)
	      else
		let (int_i', int_branches') =
		  anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
		in
		Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExpTerm)
	   | _ ->
	      let (int_i', int_branches') =
		anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
	      in
	      Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExpTerm)
	 end
       else
	 let (int_i', int_branches') =
	   anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
	 in
	 Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExpTerm)

    | (Syn (loc', int_i), SE.Comp.Syn (loc, ext_i), (tau, t)) ->
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       if C.convCTyp (tau, t) (tau', t') then
	 Annotated.Comp.Syn (loc', int_i', ttau, Annotated.ExpTerm)
       else
	 raise (Error (loc', MismatchChk (cD, cG, int_e, (tau, t), (tau', t'))))

    | (If (loc', int_i, int_e1, int_e2),
       SE.Comp.If (loc, ext_i, ext_e1, ext_e2),
       (tau, t)) ->
       let ((_flag, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypBool, _) ->
	    let int_e1' = annotate cD (cG, cIH) int_e1 ext_e1 (tau, t) in
	    let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau, t) in
	    Annotated.Comp.If (loc', int_i', int_e1', int_e2', ttau, Annotated.ExpTerm)
	 | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | Hole (loc', f'), SE.Comp.Hole loc, (tau, t) ->
       Annotated.Comp.Hole (loc', f', ttau, Annotated.ExpTerm)

  and syn cD (cG, cIH) int_e ext_e =
    syn' cD (cG, cIH) int_e ext_e

  and syn' cD (cG, cIH) int_e ext_e = match int_e, ext_e with
    | (Var (loc', x), SE.Comp.Var (loc, _)) ->
       let (f, tau') = lookup cG x in
       let tau =
	 match C.cnormCTyp (tau', C.m_id) with
	 | TypInd tau -> tau
	 | _ -> tau'
       in
       if Total.exists_total_decl f then
	 ((Some cIH, tau, C.m_id), Annotated.Comp.Var (loc', x, (tau, C.m_id), Annotated.ExpTerm))
       else
	 ((None, tau, C.m_id), Annotated.Comp.Var (loc', x, (tau, C.m_id), Annotated.ExpTerm))

    (* Possibly has implicit variables *)
    | (DataConst (loc', c), SE.Comp.DataConst (loc, _)) ->
       let tau = (CompConst.get c).CompConst.typ in
       ((None, tau, C.m_id), Annotated.Comp.DataConst (loc', c, (tau, C.m_id), Annotated.ExpTerm))

    | (DataConst (loc', c), SE.Comp.Var (loc, _)) ->
       let tau = (CompConst.get c).CompConst.typ in
       ((None, tau, C.m_id), Annotated.Comp.DataConst (loc', c, (tau, C.m_id), Annotated.ExpTerm))


    (* Possibly has implicit variables *)
    (* DataDest does not exist in external. *)
    (* | (DataDest (loc', c), SE.Comp.DataDest (loc, _)) -> *)
    (*    let tau = (CompDest.get c).CompDest.typ in *)
    (*    ((None, tau, C.m_id), Annotated.Comp.DataDest (loc', c, (tau, C.m_id), Annotated.ExpTerm)) *)

    | (DataDest (loc', c), SE.Comp.Var (loc, _)) ->
       let tau = (CompDest.get c).CompDest.typ in
       ((None, tau, C.m_id), Annotated.Comp.DataDest (loc', c, (tau, C.m_id), Annotated.ExpTerm))

    (* Possibly has implicit variables *)
    | (Const (loc', prog), SE.Comp.Const (loc, _)) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   let tau = (Comp.get prog).Comp.typ in
	   ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id), Annotated.ExpTerm))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 let tau = (Comp.get prog).Comp.typ in
	 ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id), Annotated.ExpTerm))

    | (Const (loc', prog), SE.Comp.Var (loc, _)) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   let tau = (Comp.get prog).Comp.typ in
	   ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id), Annotated.ExpTerm))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 let tau = (Comp.get prog).Comp.typ in
	 ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id), Annotated.ExpTerm))

    | (Apply (loc', int_e1, int_e2), SE.Comp.Apply (loc, ext_e1, ext_e2)) ->
       let ((cIH_opt, tau1, t1), int_e1') = syn cD (cG, cIH) int_e1 ext_e1 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       begin
	 match (tau1, t1) with
	 | (TypArr (tau2, tau), t) ->
	    let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau2, t) in
	    ((useIH loc cD cG cIH_opt int_e2, tau, t),
	     Annotated.Comp.Apply (loc', int_e1', int_e2', (tau, t), Annotated.ExpTerm))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, int_e1, VariantArrow, (tau, t))))
       end

    (* MApp does not exist in external. *)
    (* | (MApp (loc', int_e, int_mC), SE.Comp.MApp (loc, ext_e, ext_mC)) -> *)
    (*    let ((cIH_opt, tau1, t1), int_e') = syn cD (cG, cIH) int_e ext_e in *)
    (*    begin *)
    (* 	 match (C.cwhnfCTyp (tau1, t1)) with *)
    (* 	 | (TypPiBox (I.Decl (_, ctyp, _), tau), t) -> *)
    (* 	    let int_mC' = int_mC (\* LF.annMetaObj cD int_mC ext_mC (ctyp, t); *\) in *)
    (* 	    let t = I.MDot (metaObjToMFront mC, t) in *)
    (* 	    ((useIH loc cD cG cIH_opt (Box (loc, mC)), tau, t), *)
    (* 	     Annotated.Comp.MApp (loc', int_e', int_mC', (tau, t), Annotated.ExpTerm)) *)
    (* 	 | (tau, t) -> *)
    (* 	    raise (Error (loc, MismatchSyn (cD, cG, int_e, VariantPiBox, (tau, t)))) *)
    (*    end *)

    | (MApp (loc', int_e, int_mC), SE.Comp.Apply (loc, ext_i, (SE.Comp.Box (_, ext_mC)))) ->
       let ((cIH_opt, tau1, t1), int_e') = syn cD (cG, cIH) int_e ext_i in
       begin
	 match (C.cwhnfCTyp (tau1, t1)) with
	 | (TypPiBox (I.Decl (_, ctyp, _), tau), t) ->
	    let int_mC' = int_mC (* LF.annMetaObj cD int_mC ext_mC (ctyp, t); *) in
	    let t = I.MDot (metaObjToMFront int_mC, t) in
	    ((useIH loc cD cG cIH_opt (Box (loc, int_mC)), tau, t),
	     Annotated.Comp.MApp (loc', int_e', int_mC', (tau, t), Annotated.ExpTerm))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, int_e, VariantPiBox, (tau, t))))
       end


    | (PairVal (loc', int_i1, int_i2), SE.Comp.PairVal (loc, ext_i1, ext_i2)) ->
       let ((_, tau1, t1), int_i1') = syn cD (cG, cIH) int_i1 ext_i1 in
       let ((_, tau2, t2), int_i2') = syn cD (cG, cIH) int_i2 ext_i2 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       let (tau2, t2) = C.cwhnfCTyp (tau2, t2) in
       let tau = TypCross (TypClo (tau1, t1), TypClo (tau2, t2)) in
       ((None, tau, C.m_id),
	Annotated.Comp.PairVal (loc', int_i1', int_i2', (tau, C.m_id), Annotated.ExpTerm))

    | (Ann (int_e, tau), Ann (loc, ext_e, _)) ->
       let int_e' = annotate cD (cG, cIH) int_e ext_e (tau, C.m_id) in
       ((None, tau, C.m_id), Annotated.Comp.Ann (int_e', tau, (tau, C.m_id), Annotated.ExpTerm))

    | (Equal (loc', int_i1, int_i2), SE.Comp.Equal (loc, ext_i1, ext_i2)) ->
       let ((_, tau1, t1), int_i1') = syn cD (cG, cIH) int_i1 ext_i1 in
       let ((_, tau2, t2), int_i2') = syn cD (cG, cIH) int_i2 ext_i2 in
       if C.convCTyp (tau1, t1) (tau2, t2) then
	 begin
	   match C.cwhnfCTyp (tau1, t1) with
	   | (TypBox _, _) ->
	      ((None, TypBool, C.m_id),
	       Annotated.Comp.Equal (loc', int_i1', int_i2', (TypBool, C.m_id), Annotated.ExpTerm))
	   | (TypBool, _) ->
	      ((None, TypBool, C.m_id),
	       Annotated.Comp.Equal (loc', int_i1', int_i2', (TypBool, C.m_id), Annotated.ExpTerm))
	   | (tau1, t1) ->
	      raise (Error (loc, EqTyp (cD, (tau1, t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1, t1), (tau2, t2))))

    | Boolean b, SE.Comp.Boolean (loc, _) ->
       ((None, TypBool, C.m_id), Annotated.Comp.Boolean (b, (TypBool, C.m_id), Annotated.ExpTerm))

  and annBranches caseTyp cD (cG, cIH) int_branches ext_branches tau_s ttau =
    List.map2
      (fun int_branch ext_branch ->
       annBranch caseTyp cD (cG, cIH) int_branch ext_branch tau_s ttau)
      int_branches ext_branches

  and annBranch caseTyp cD (cG, cIH) int_branch ext_branch tau_s (tau, t) =
    match int_branch, ext_branch with
    (* TODO EmptyBranch *)
    | (Branch (loc', cD1', cG, PatMetaObj (l1', int_mO), t1, int_e),
      SE.Comp.Branch (loc, _, SE.Comp.PatMetaObj (_, ext_mO), ext_e)) ->
       let TypBox (_, mT) = tau_s in
       let _mT1 = C.cnormMetaTyp (mT, t1) in
       let cG' = C.cnormCtx (C.normCtx cG, t1) in
       let cIH = C.cnormCtx (C.normCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (l1', int_mO)) then
	   let cD1' = mvarsInPatt cD1' (PatMetaObj (l1', int_mO)) in
	   (cD1', Total.wf_rec_calls cD1' (I.Empty))
	 else
	   (cD1', I.Empty) in
       let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD else cD1' in
       (* LF.annMSub loc cD1' t1 cD; *)
       let int_mO' = int_mO (* LF.annMetaObj cD1' int_mO ext_mO (mT1, C.m_id) *) in
       let int_e' = annotate cD1' (cG', Context.append cIH cIH') int_e ext_e (tau', C.m_id)
       in
       Annotated.Comp.Branch (loc', cD1', cG, Annotated.Comp.PatMetaObj (l1', int_mO'), t1, int_e')

    | (Branch (loc', cD1', cG1, int_pat, t1, int_e),
      SE.Comp.Branch (loc, _, ext_pat, ext_e)) ->
       let tau_p = C.cnormCTyp (tau_s, t1) in
       let cG' = C.cnormCtx (cG, t1) in
       let cIH = C.cnormCtx (C.cnormCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let k = Context.length cG1 in
       let cIH0 = Total.shiftIH cIH k in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller int_pat then
	   let cD1' = mvarsInPatt cD1' int_pat in (cD1', Total.wf_rec_calls cD1' cG1)
	 else
	   (cD1', I.Empty)
       in
       let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD else cD1' in
       (* LF.annMSub loc cD1' t1 cD;  *)
       let int_pat' = annPattern cD1' cG1 int_pat ext_pat (tau_p, C.m_id) in
       let int_e' =
	 annotate cD1' ((Context.append cG' cG1), Context.append cIH0 cIH')
		  int_e ext_e (tau', C.m_id)
       in
       Annotated.Comp.Branch (loc', cD1' cG1, int_pat', t1, int_e')

  and annPattern cD cG int_pat ext_pat ttau = match int_pat, ext_pat with
    (* TODO PatEmpty *)
    | PatMetaObj (loc', int_mO), SE.Comp.PatMetaObj (loc, ext_mO) ->
       begin
	 match ttau with
	 | (TypBox (_, ctyp), theta) ->
	    let int_mO' = int_mO (* LF.annMetaObj cD int_mO ext_mO (ctyp, theta) *) in
	    Annotated.Comp.PatMetaObj (loc', int_mO', ttau, Annotated.ExpTerm)
	 | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | (PatPair (loc', int_pat1, int_pat2), SE.Comp.PatPair (loc, ext_pat1, ext_pat2)) ->
       begin
	 match ttau with
	 | (TypCross (tau1, tau2), theta) ->
	    let int_pat1' = annPattern cD cG int_pat1 ext_pat1 (tau1, theta) in
	    let int_pat2' = annPattern cG cG int_pat2 ext_pat2 (tau2, theta) in
	 | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau)))
       end
    | int_pat, ext_pat ->
       let ((loc, ttau'), int_pat') = synPattern cD cG int_pat ext_pat in
       let tau' = C.cnormCTyp ttau' in
       let tau = C.cnormCTyp ttau in
       let ttau' = (tau', C.m_id) in
       let ttau = (tau, C.m_id) in
       if C.convCTyp ttau ttau' then
	 int_pat'
       else
	 raise (Error (loc, PatIllTyped (cD, cG, int_pat, ttau, ttau')))

  and synPattern cD cG int_pat ext_pat = match int_pat, ext_pat with
    | (PatConst (loc', int_c, int_pat_spine), SE.Comp.PatConst (loc, ext_c, ext_pat_spine)) ->
       (* Okay, this is a bit complicated *)
       (* First we need to handle the implicit arguments so we can realign the internal *)
       (* and external spines *)
       (* But we also need to rebuild the internal spine so we can create an *)
       (* Annotated spine *)
       let rec handle_implicits count int_pat_spine ext_pat_spine =
	 match count with
	 | 0 -> (int_pat_spine, ext_pat_spine)
	 | m ->
	    begin
	      match int_pat_spine with
	      (* | PatNil -> raise an error here *)
	      | PatApp (loc, int_pat, int_pat_spine') ->
		 handle_implicits (m - 1) int_pat_spine' ext_pat_spine
	    end

end

module Sgn = struct

end
