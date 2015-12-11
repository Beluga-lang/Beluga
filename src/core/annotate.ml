module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5])

module LF = Lfcheck

module Comp = struct

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

  exception Error of Syntax.Loc.t * error

  let extend_mctx cD (x, cdecl, t) = match cdecl with
    | I.Decl (_u, cU, dep) ->
       I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t), dep))

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

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
	lookup cG' (k - 1)

  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

  let rec extract_var i = match i with
    | Var (_, x) -> Some x
    | Apply (_, i, _ ) -> extract_var i
    | MApp (_, i, _ ) -> extract_var i
    | _ -> None

  let mark_ind cD k =
    let rec lookup cD k' =  match cD, k' with
      | I.Dec (cD, I.Decl (u, cdec,dep)), 1 ->
	 I.Dec (cD, I.Decl (u, cdec, I.Inductive))
      | I.Dec (_cD, I.DeclOpt u), 1 ->
	 raise (Error.Violation "Expected declaration to have type")
      | I.Dec (cD, dec), k' -> I.Dec (lookup cD (k' - 1), dec)
      | I.Empty , _  ->
	 raise (Error.Violation
		  ("Meta-variable out of bounds -- looking for " ^ string_of_int k ^ "in context"))
    in
    lookup cD k

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

  and fmv_normal (cD:I.mctx) tM = match tM with
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

  and fmv_mobj cD cM = match cM with
    | _ , I.CObj (cPsi) -> fmv_dctx cD cPsi
    | _, I.ClObj (phat, I.MObj tM) -> fmv_normal cD tM
    | _, I.ClObj (phat, I.PObj h) -> fmv_head (fmv_hat cD phat) h
    | _, I.ClObj (phat, I.SObj s) ->  fmv_subst (fmv_hat cD phat) s

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

  let rec annotate cD ((cG, cIH) : ctyp_decl I.ctx * ctyp_decl I.ctx) e ttau =
    match (e, ttau) with
    | (Rec (loc, f, e), (tau, t)) ->
       let e' =
	 annotate cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t))), (Total.shift cIH)) e ttau
       in
       Annotated.Comp.Rec (loc, f, e', ttau)

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->
       let e' =
	 annotate cD (I.Dec (cG, CTypDecl (x, TypClo (tau1, t))), (Total.shift cIH)) e (tau2, t)
       in
       Annotated.Comp.Fun (loc, x, e', ttau)

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->
       let e' =
	 annotate (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  e (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc, u, e', ttau)

    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->
       let e1' = annotate cD (cG,cIH) e1 (tau1, t) in
       let e2' = annotate cD (cG,cIH) e2 (tau2, t) in
       Annotated.Comp.Pair (loc, e1', e2', ttau)

    | (Let (loc, i, (x, e)), (tau, t)) ->
       let (_, tau', t', i') = syn cD (cG,cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau',t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
       let e' =
	 annotate cD (cG', Total.shift cIH) e (tau, t)
       in
       Annotated.Comp.Let (loc, i', (x, e'), ttau)

    | (LetPair (loc, i, (x, y, e)), (tau, t)) ->
       let (_, tau', t', i') = syn cD (cG,cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau',t') in
       begin
	 match (tau',t') with
	 | (TypCross (tau1, tau2), t') ->
	    let cG' = I.Dec
		       (I.Dec (cG, CTypDecl (x, TypClo (tau1,t'))), CTypDecl (y, TypClo (tau2,t')))
	    in
	    let e' =
	      annotate cD (cG', (Total.shift (Total.shift cIH))) e (tau,t)
	    in
	    Annotated.Comp.LetPair (loc, i', (x, y, e'), ttau)
	 | _ -> raise (Error.Violation "Case scrutinee ot of boxed type")
       end

    | (Box (loc, cM), (TypBox (l, mT), t)) ->
       begin
	 try
	   (* Should produce cM' *)
	   LF.checkMetaObj cD cM (mT, t);
	   Annotated.Comp.Box (loc, cM, ttau)
	 with Whnf.FreeMVar (I.FMVar (u, _)) ->
	   raise (Error.Violation ("Free meta-variable " ^ (Id.render_name u)))
       end

    | (Case (loc, prag, Ann (Box (l1,(l,cM)), (TypBox (l2,mT) as tau0_sc)), branches), (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
	 begin
	   match cM with
	   | I.ClObj (_, I.MObj (I.Root (_, I.PVar (x,s), _)))
	   | I.ClObj (_, I.PObj (I.PVar (x,s))) ->
	      let order =
		if !Total.enabled && is_indMObj cD x then
		  IndIndexObj (l,cM)
		else
		  IndexObj (l,cM)
	      in
	      (order, TypBox (loc, convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), None)
	   | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k), _)))
	   | I.ClObj (_, I.PObj (I.Proj (I.PVar (x,s), k))) ->
	      let order =
		if !Total.enabled && is_indMObj cD x then
		  IndIndexObj (l,cM)
		else
		  IndexObj (l,cM)
	      in
	      (order, TypBox (loc, convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), Some k)
	   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x,s), _))) ->
	      let order =
		if !Total.enabled && is_indMObj cD x then
		  IndIndexObj (l,cM)
		else
		  IndexObj (l,cM)
	      in
	      (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
	   | _ ->
	      (IndexObj (l, cM), TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
	 end
       in
       (* Should produce cM' *)
       LF.checkMetaObj cD (loc, cM) (mT, C.m_id);
       let problem = Coverage.make loc prag cD branches tau_sc in
       let branches' = annotateBranches total_pragma cD (cG,cIH) branches tau0_sc (tau, t) in
       Coverage.process problem projOpt;
       Annotated.Comp.Case (loc, prag,
			    Annotated.Comp.Ann (
				Annotated.Comp.Box (l1,(l,cM), ((TypBox (l2, mT), C.m_id))),
				(TypBox (l2,mT)),
				((TypBox (l2, mT), C.m_id))
			      )
			    , branches', ttau)

    | (Case (loc, prag, i, branches), (tau, t)) ->
       let annBranch total_pragma cD (cG, cIH) i branches (tau, t) =
	 let (_, tau', t', i') = syn cD (cG, cIH) i in
	 begin
	   match C.cwhnfCTyp (tau',t') with
	   | (TypBox (loc', mT), t') ->
	      let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
	      let problem = Coverage.make loc prag cD branches tau_s in
	      let branches' = annotateBranches total_pragma cD (cG,cIH) branches tau_s (tau,t) in
	      Coverage.process problem None;
	      (i', branches')
	   | (tau',t') ->
	      let tau_s = C.cnormCTyp (tau',t') in
	      let problem = Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) in
	      let branches' = annotateBranches total_pragma cD (cG,cIH) branches tau_s (tau,t) in
	      Coverage.process problem None;
	      (i', branches')
	 end
       in
       if !Total.enabled then
	 begin
	   match i with
	   | Var (_, x) ->
	      let (f, tau') = lookup cG x in
	      let ind =
		begin
		  match Whnf.cnormCTyp (tau', Whnf.m_id) with
		  | TypInd _tau -> true
		  | _ -> false
		end
	      in
	      if ind then
		let (i', branches') = annBranch IndDataObj cD (cG,cIH) i branches (tau,t) in
		Annotated.Comp.Case (loc, prag, i', branches', ttau)
	      else
		let (i', branches') = annBranch DataObj cD (cG,cIH) i branches (tau, t) in
		Annotated.Comp.Case (loc, prag, i', branches', ttau)
	   | _ ->
	      let (i', branches') = annBranch DataObj cD (cG,cIH) i branches (tau, t) in
	      Annotated.Comp.Case (loc, prag, i', branches', ttau)
	 end
       else
	 let (i', branches') = annBranch DataObj cD (cG,cIH) i branches (tau,t) in
	 Annotated.Comp.Case (loc, prag, i', branches', ttau)

    | (Syn (loc, i), (tau, t)) ->
       let (_, tau', t', i') = syn cD (cG,cIH) i in
       let (tau',t') = Whnf.cwhnfCTyp (tau',t') in
       if C.convCTyp (tau,t) (tau',t') then
	 Annotated.Comp.Syn (loc, i', ttau)
       else
	 raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), (tau',t'))))

    | (If (loc, i, e1, e2), (tau, t)) ->
       let (_flag, tau', t', i') = syn cD (cG,cIH) i in
       let (tau',t') = C.cwhnfCTyp (tau',t') in
       begin
	 match (tau',t') with
	 | (TypBool, _) ->
	    let e1' = annotate cD (cG,cIH) e1 (tau,t) in
	    let e2' = annotate cD (cG,cIH) e2 (tau,t) in
	    Annotated.Comp.If (loc, i', e1', e2', ttau)
	 | tau_theta' ->
	    raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | (Hole (loc, f), (tau, t)) ->
       Annotated.Comp.Hole (loc, f, ttau)

  and syn cD (cG,cIH) e : (gctx option * typ * I.msub * Annotated.Comp.exp_syn) =
    match e with
    | Var (loc, x) ->
       let (f, tau') = lookup cG x in
       let tau =
	 begin
	   match Whnf.cnormCTyp (tau', Whnf.m_id) with
	   | TypInd tau -> tau
	   | _ -> tau'
	 end
       in
       let ttau = (tau, C.m_id) in
       if Total.exists_total_decl f then
	 (Some cIH, tau, C.m_id, Annotated.Comp.Var (loc, x, ttau))
       else
	 (None, tau, C.m_id, Annotated.Comp.Var (loc, x, ttau))

    | DataConst (loc, c) ->
       let ttau = ((CompConst.get c).CompConst.typ, C.m_id) in
       (None, (CompConst.get c).CompConst.typ, C.m_id,
	Annotated.Comp.DataConst (loc, c, ttau))

    | DataDest (loc, c) ->
       let ttau = ((CompDest.get c).CompDest.typ, C.m_id) in
       (None, (CompDest.get c).CompDest.typ, C.m_id,
	Annotated.Comp.DataDest (loc, c, ttau))

    | Const (loc, prog) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   let ttau = ((Comp.get prog).Comp.typ, C.m_id) in
	   (None, (Comp.get prog).Comp.typ, C.m_id,
	    Annotated.Comp.Const (loc, prog, ttau))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 let ttau = ((Comp.get prog).Comp.typ, C.m_id) in
	 (None, (Comp.get prog).Comp.typ, C.m_id,
	  Annotated.Comp.Const (loc, prog, ttau))

    | Apply (loc, e1, e2) ->
       let (cIH_opt, tau1, t1, e1') = syn cD (cG,cIH) e1 in
       let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
       begin
	 match (tau1, t1) with
	 | (TypArr (tau2, tau), t) ->
	    let e2' = annotate cD (cG, cIH) e2 (tau2, t) in
	    let (cIH_opt') = useIH loc cD cG cIH_opt e2 in
	    let ttau = (tau, t) in
	    (cIH_opt', tau, t, Annotated.Comp.Apply (loc, e1', e2', ttau))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau, t))))
       end

    | MApp (loc, e, mC) ->
       let (cIH_opt, tau1, t1, e') = syn cD (cG, cIH) e in
       begin
	 match (C.cwhnfCTyp (tau1,t1)) with
	 | (TypPiBox ((I.Decl (_, ctyp, _)), tau), t) ->
	    (* Should produce mC' *)
	    LF.checkMetaObj cD mC (ctyp, t);
	    let ttau = (tau, I.MDot (metaObjToMFront mC, t)) in
	    let cIH_opt' = useIH loc cD cG cIH_opt (Box (loc, mC)) in
	    (cIH_opt', tau, I.MDot (metaObjToMFront mC, t),
	     Annotated.Comp.MApp (loc, e', mC, ttau))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
       end

    | PairVal (loc, i1, i2) ->
       let (_,tau1,t1,i1') = syn cD (cG,cIH) i1 in
       let (_,tau2,t2,i2') = syn cD (cG,cIH) i2 in
       let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
       let (tau2,t2) = C.cwhnfCTyp (tau2,t2) in
       let ttau = (TypCross (TypClo (tau1,t1), TypClo (tau2,t2)), C.m_id) in
       (None, TypCross (TypClo (tau1,t1), TypClo (tau2,t2)), C.m_id,
	Annotated.Comp.PairVal (loc, i1', i2', ttau))

    | Ann (e, tau) ->
       let e' = annotate cD (cG, cIH) e (tau, C.m_id) in
       let ttau = (tau, C.m_id) in
       (None, tau, C.m_id, Annotated.Comp.Ann (e', tau, ttau))

    | Equal (loc, i1, i2) ->
       let (_, tau1, t1, i1') = syn cD (cG,cIH) i1 in
       let (_, tau2, t2, i2') = syn cD (cG,cIH) i2 in
       if Whnf.convCTyp (tau1,t1) (tau2,t2) then
	 begin
	   match Whnf.cwhnfCTyp (tau1, t1) with
	   | (TypBox _, _) ->
	      let ttau = (TypBool, C.m_id) in
	      (None,TypBool, C.m_id, Annotated.Comp.Equal (loc, i1', i2', ttau))
	   | (TypBool, _) ->
	      let ttau = (TypBool, C.m_id) in
	      (None, TypBool, C.m_id, Annotated.Comp.Equal (loc, i1', i2', ttau))
	   | (tau1,t1) ->
	      raise (Error (loc, EqTyp (cD, (tau1,t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1,t1), (tau2,t2))))

    | Boolean b ->
       let ttau = (TypBool, C.m_id) in
       (None, TypBool, C.m_id, Annotated.Comp.Boolean (b, ttau))

  and annotateBranches caseTyp cD cG branches tau_s ttau =
    List.map (fun branch -> annotateBranch caseTyp cD cG branch tau_s ttau) branches

  and annotateBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
    | EmptyBranch (loc, cD1', pat, t1) ->
       let tau_p = Whnf.cnormCTyp (tau_s, t1) in
       (LF.checkMSub loc cD1' t1 cD;
	let pat' = annotatePattern cD1' I.Empty pat (tau_p, Whnf.m_id) in
       Annotated.Comp.EmptyBranch (loc, cD1', pat', t1, (tau, t)))

    | Branch (loc, cD1', cG, PatMetaObj (loc', mO), t1, e1) ->
       let TypBox (_, mT) = tau_s in
       let mT1 = Whnf.cnormMetaTyp (mT, t1) in
       let cG' = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
       let cIH = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
       let t'' = Whnf.mcomp t t1 in
       let tau' = Whnf.cnormCTyp (tau, t'') in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (loc', mO)) then
	   let cD1' = mvarsInPatt cD1' (PatMetaObj (loc', mO)) in
	   (cD1', Total.wf_rec_calls cD1' (I.Empty))
	 else
	   (cD1', I.Empty) in
       let cD1' =
	 if !Total.enabled then
	   id_map_ind cD1' t1 cD
	 else
	   cD1'
       in
       (LF.checkMSub loc cD1' t1 cD;
       LF.checkMetaObj cD1' mO (mT1, C.m_id);
       let e1' = annotate cD1' (cG', Context.append cIH cIH') e1 (tau', Whnf.m_id) in
       Annotated.Comp.Branch (loc, cD1', cG,
			      Annotated.Comp.PatMetaObj (loc', mO, (tau_s, Whnf.m_id)),
			      t1, e1', (tau, t)))

    | Branch (loc, cD1', cG1, pat, t1, e1) ->
       let tau_p = Whnf.cnormCTyp (tau_s, t1) in
       let cG' = Whnf.cnormCtx (cG, t1) in
       let cIH = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
       let t'' = Whnf.mcomp t t1 in
       let tau' = Whnf.cnormCTyp (tau, t'') in
       let k = Context.length cG1 in
       let cIH0 = Total.shiftIH cIH k in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller pat then
	   let cD1' = mvarsInPatt cD1' pat in (cD1', Total.wf_rec_calls cD1' cG1)
	 else
	   (cD1', I.Empty)
       in
       let cD1' =
	 if !Total.enabled then
	   id_map_ind cD1' t1 cD
	 else
	   cD1'
       in
       (LF.checkMSub loc cD1' t1 cD;
	let pat' = annotatePattern cD1' cG1 pat (tau_p, Whnf.m_id) in
       let e1' =
	 annotate cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') e1 (tau', Whnf.m_id)
       in
       Annotated.Comp.Branch (loc, cD1', cG1, pat', t1, e1', (tau, t)))

  and annotatePattern cD cG pat ttau =
    match pat with
    | PatEmpty (loc, cPsi) ->
       begin
	 match ttau with
	 | (TypBox (_, I.ClTyp (I.MTyp tA, cPhi)), theta)
	 | (TypBox (_, I.ClTyp (I.PTyp tA, cPhi)), theta) ->
	    if C.convDCtx (Whnf.cnormDCtx (cPhi, theta)) cPsi then
	      Annotated.Comp.PatEmpty (loc, cPsi, ttau)
	    else
	      raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
	 | _ ->
	    raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatMetaObj (loc, mO) ->
       begin
	 match ttau with
	 | (TypBox (_, ctyp), theta) ->
	    (* Should produce mO' *)
	    LF.checkMetaObj cD mO (ctyp, theta);
	    Annotated.Comp.PatMetaObj (loc, mO, ttau)
	 | _ ->
	    raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatPair (loc, pat1, pat2) ->
       begin
	 match ttau with
	 | (TypCross (tau1, tau2), theta) ->
	    let pat1' = annotatePattern cD cG pat1 (tau1, theta) in
	    let pat2' = annotatePattern cD cG pat2 (tau2, theta) in
	    Annotated.Comp.PatPair (loc, pat1', pat2', ttau)
	 | _ ->
	    raise (Error (loc, PairMismatch (cD, cG, ttau)))
       end

    | pat ->
       let (loc, ttau', pat') = synPattern cD cG pat in
       let tau' = Whnf.cnormCTyp ttau' in
       let tau = Whnf.cnormCTyp ttau in
       let ttau' = (tau', Whnf.m_id) in
       let ttau = (tau, Whnf.m_id) in
       if C.convCTyp ttau ttau' then
	 pat'
       else
	 raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat =
    match pat with
    | PatConst (loc, c, pat_spine) ->
       let ttau = ((CompConst.get c).CompConst.typ, C.m_id) in
       let (ttau', pat_spine') = synPatSpine cD cG pat_spine ttau in
       (loc, ttau', Annotated.Comp.PatConst (loc, c, pat_spine', ttau'))
    | PatVar (loc, k) ->
       let ttau = (lookup' cG k, C.m_id) in
       (loc, ttau, Annotated.Comp.PatVar (loc, k, ttau))
    | PatTrue loc ->
       let ttau = (TypBool, C.m_id) in
       (loc, ttau, Annotated.Comp.PatTrue (loc, ttau))
    | PatFalse loc ->
       let ttau = (TypBool, C.m_id) in
       (loc, ttau, Annotated.Comp.PatFalse (loc, ttau))
    | PatAnn (loc, pat, tau) ->
       let ttau = (tau, C.m_id) in
       let pat' = annotatePattern cD cG pat ttau in
       (loc, ttau, Annotated.Comp.PatAnn (loc, pat', tau, ttau))

  and synPatSpine cD cG pat_spine (tau, theta) =
    match pat_spine with
    | PatNil -> ((tau, theta), Annotated.Comp.PatNil (tau, theta))
    | PatApp (loc, pat, pat_spine) ->
       begin
	 match (tau, theta) with
	 | (TypArr (tau1, tau2), theta) ->
	    let pat' = annotatePattern cD cG pat (tau1, theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau2, theta) in
	    (ttau, Annotated.Comp.PatApp (loc, pat', pat_spine', ttau))
	 | (TypPiBox (cdecl, tau), theta) ->
	    let (theta', pat') = checkPatAgainstCDecl cD pat (cdecl, tau, theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau, theta') in
	    (ttau, Annotated.Comp.PatApp (loc, pat', pat_spine', ttau))
       end

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl (_,ctyp,_), tau, theta) =
    LF.checkMetaObj cD mO (ctyp, theta);
    (I.MDot(metaObjToMFront mO, theta), Annotated.Comp.PatMetaObj (loc, mO, (tau, theta)))

end

module Print = struct

  open Format
  open Annotated.Comp

  let std_lvl = 0

  let rec pprint_ann cD cG e = pprint_ann_chk cD cG std_lvl std_formatter e

  and pprint_ann_chk cD cG lvl ppf = function
    | Rec (loc, f, e, ttau) ->
       fprintf ppf "(rec %s : %s) = %a"
	       (Id.render_name f)
	       (P.subCompTypToString cD ttau)
	       (pprint_ann_chk cD cG 0) e
    | Fun (loc, x, e, ttau) ->
       fprintf ppf "(fn %s : %s) => %a"
	       (Id.render_name x)
	       (P.subCompTypToString cD ttau)
	       (pprint_ann_chk cD (Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x)) 0) e
    | MLam (loc, u, e, ttau) ->
       fprintf ppf "(mlam %s : %s) => %a"
	       (Id.render_name u)
	       (P.subCompTypToString cD ttau)
	       (pprint_ann_chk
		  (Syntax.Int.LF.Dec (cD, Syntax.Int.LF.DeclOpt u))
		  (Whnf.cnormCtx (cG, Syntax.Int.LF.MShift 1))
		  0) e
    | Pair (loc, e1, e2, ttau) ->
       fprintf ppf "(<%a,%a> : %s)"
	       (pprint_ann_chk cD cG 0) e1
	       (pprint_ann_chk cD cG 0) e2
	       (P.subCompTypToString cD ttau)
    | Let (loc, i, (x, e), ttau) ->
       fprintf ppf "(let %s = %a in %a : %s)"
	       (Id.render_name x)
	       (pprint_ann_syn cD cG 0) i
	       (pprint_ann_chk cD cG 0) e
	       (P.subCompTypToString cD ttau)
    | LetPair (loc, i, (x, y, e), ttau) ->
       fprintf ppf "(let <%s,%s> = %a in %a : %s)"
	       (Id.render_name x)
	       (Id.render_name y)
	       (pprint_ann_syn cD cG 0) i
	       (pprint_ann_chk cD cG 0) e
	       (P.subCompTypToString cD ttau)
    | Box (loc, cM, ttau) ->
       fprintf ppf "(%s : %s)"
	       (P.metaObjToString cD cM)
	       (P.subCompTypToString cD ttau)
    | Case (loc, prag, i, branches, ttau) ->
       fprintf ppf "(case %a of %a : %s)"
	       (pprint_ann_syn cD cG 0) i
	       (pprint_ann_branches cD cG 0) branches
	       (P.subCompTypToString cD ttau)
    | Syn (loc, i, ttau) ->
       fprintf ppf "(%a : %s)"
	       (pprint_ann_syn cD cG 0) i
	       (P.subCompTypToString cD ttau)
    | If (loc, i, e1, e2, ttau) ->
       fprintf ppf "(if %a then %a else %a : %s)"
	       (pprint_ann_syn cD cG 0) i
	       (pprint_ann_chk cD cG 0) e1
	       (pprint_ann_chk cD cG 0) e2
	       (P.subCompTypToString cD ttau)
    | Hole (loc, f, ttau) ->
       try
	 let x = f () in
	 fprintf ppf "(? %%{ %d }%% : %s)"
		 x
		 (P.subCompTypToString cD ttau)
       with
	 _ -> fprintf ppf " ? "

  and pprint_ann_syn cD cG lvl ppf = function
    | Var (loc, x, ttau) ->
       fprintf ppf "(%s : %s)"
	       (R.render_var cG x)
	       (P.subCompTypToString cD ttau)
    | DataConst (loc, c, ttau) ->
       fprintf ppf "(%s : %s)"
	       (R.render_cid_comp_const c)
	       (P.subCompTypToString cD ttau)
    | DataDest (loc, c, ttau) ->
       fprintf ppf "(%s : %s)"
	       (R.render_cid_comp_dest c)
	       (P.subCompTypToString cD ttau)
    | Const (loc, prog, ttau) ->
       fprintf ppf "(%s : %s)"
	       (R.render_cid_prog prog)
	       (P.subCompTypToString cD ttau)
    | Apply (loc, e1, e2, ttau) ->
       fprintf ppf "(%a %a : %s)"
	      (pprint_ann_syn cD cG 0) e1
	      (pprint_ann_chk cD cG 0) e2
	      (P.subCompTypToString cD ttau)
    | MApp (loc, i, mC, ttau) ->
       fprintf ppf "(%a %s : %s)"
	       (pprint_ann_syn cD cG 0) i
	       (P.metaObjToString cD mC)
	       (P.subCompTypToString cD ttau)
    | PairVal (loc, i1, i2, ttau) ->
       fprintf ppf "((%a, %a) : %s)"
	       (pprint_ann_syn cD cG 0) i1
	       (pprint_ann_syn cD cG 0) i2
	       (P.subCompTypToString cD ttau)
    | Ann (e, tau, ttau) ->
       fprintf ppf "(%a : %s)"
	       (pprint_ann_chk cD cG 0) e
	       (P.subCompTypToString cD ttau)
    | Equal (loc, i1, i2, ttau) ->
       fprintf ppf "(%a == %a : %s)"
	       (pprint_ann_syn cD cG 0) i1
	       (pprint_ann_syn cD cG 0) i2
	       (P.subCompTypToString cD ttau)
    | Boolean (true, ttau) ->
       fprintf ppf "(ttrue : %s)"
	       (P.subCompTypToString cD ttau)
    | Boolean (false, ttau) ->
	 fprintf ppf "(ffalse : %s)"
		 (P.subCompTypToString cD ttau)

  and pprint_ann_branches cD cG lvl ppf = function
    | [] -> ()
    | b :: [] ->
       fprintf ppf "%a"
	       (pprint_ann_branch cD cG 0) b
    | b :: bs ->
       fprintf ppf "%a%a"
	       (pprint_ann_branch cD cG 0) b
	       (pprint_ann_branches cD cG 0) bs

  and pprint_ann_branch cD cG lvl ppf = function
    | EmptyBranch (loc, cD1, pat, t, ttau) ->
       (* fprintf ppf "(%a |- %a :: %a : %s)" *)
       fprintf ppf "(%a : %s)"
	       (* (pprint_ann_branch_prefix 0) cD1 *)
	       (pprint_ann_pat cD1 Syntax.Int.LF.Empty 0) pat
	       (* (pprint_ann_refinement cD1 cD 2) t *)
	       (P.subCompTypToString cD ttau)
    | Branch (_, cD1', _cG, PatMetaObj (_, mO, ttau'), t, e, ttau) ->
       (* fprintf ppf "(%a |- %a :: %a => %a : %s)" *)
       fprintf ppf "(%s => %a : %s)"
	       (P.metaObjToString cD1' mO)
	       (pprint_ann_chk cD1' cG 1) e
	       (P.subCompTypToString cD ttau)
    | Branch (_, cD1', cG', pat, t, e, ttau) ->
       let cG_t = cG in
       let cG_ext = Context.append cG_t cG' in

       fprintf ppf "(%a => %a : %s)"
	       (pprint_ann_pat cD1' cG' 0) pat
	       (pprint_ann_chk cD1' cG_ext 1) e
	       (P.subCompTypToString cD ttau)

  and pprint_ann_pat cD cG lvl ppf = function
    | PatEmpty (loc, cPsi, ttau) ->
       fprintf ppf "([%s |- {}] : %s)"
	       (P.dctxToString cD cPsi)
	       (P.subCompTypToString cD ttau)
    | PatMetaObj (loc, mO, ttau) ->
       fprintf ppf "(%s : %s)"
	       (P.metaObjToString cD mO)
	       (P.subCompTypToString cD ttau)
    | PatConst (loc, c, pat_spine, ttau) ->
       fprintf ppf "(%s %a : %s)"
	       (R.render_cid_comp_const c)
	       (pprint_ann_pat_spine cD cG 2) pat_spine
	       (P.subCompTypToString cD ttau)
    | PatPair (loc, pat1, pat2, ttau) ->
       fprintf ppf "((%a, %a) : %s)"
	       (pprint_ann_pat cD cG 0) pat1
	       (pprint_ann_pat cD cG 0) pat2
	       (P.subCompTypToString cD ttau)
    | PatTrue (loc, ttau) ->
       fprintf ppf "(ttrue : %s)"
	       (P.subCompTypToString cD ttau)
    | PatFalse (loc, ttau) ->
       fprintf ppf "(ffalse : %s)"
	       (P.subCompTypToString cD ttau)
    | PatAnn (loc, pat, tau, ttau) ->
       fprintf ppf "(%a : %s)"
	       (pprint_ann_pat cD cG 0) pat
	       (P.subCompTypToString cD ttau)
    | PatVar (_, offset, ttau) ->
       fprintf ppf "(%s : %s)"
	       (R.render_var cG offset)
	       (P.subCompTypToString cD ttau)

  and pprint_ann_pat_spine cD cG lvl ppf = function
    | PatNil ttau ->
       fprintf ppf "(Nil : %s)"
	       (P.subCompTypToString cD ttau)
    | PatApp (loc, pat, pat_spine, ttau) ->
       fprintf ppf "(%a %a : %s)"
	       (pprint_ann_pat cD cG (lvl + 1)) pat
	       (pprint_ann_pat_spine cD cG lvl) pat_spine
	       (P.subCompTypToString cD ttau)

end
