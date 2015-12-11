module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

module LF = Lfcheck

module Comp = struct

  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  let rec annotate cD ((cG, cIH) : ctyp_decl I.ctx * ctyp_decl I.ctx) e ttau =
    match (e, ttau) with
    | (Rec (loc, f, e), (tau, t)) ->
       let e' =
	 annotate (I.Dec (cG, CTypDecl (f, TypClo (tau,t)))), (Total.shift cIH) e ttau
       in
       Annotated.Comp.Rec (loc, f, e', ttau)

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->
       let e' =
	 annotate (I.Dec (cG, CTypDecl (x, TypClo (tau1, t))), (Total.shift cIH)) e (tau2, t)
       in
       Annotated.Comp.Fun (loc, x, e', ttau)

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->
       let e' =
	 annotate (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  e (tau, C.mvar_dot1 t)
       in
       Annotated.Comp.MLam (loc, x, e', ttau)

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
       Annotated.Comp.Case (loc, prag, Ann (Box (l1,(l,cM)), (TypBox (l2,mT)), branches'), ttau)

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
	      let tau_s = C.cnornCTyp (tau',t') in
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
	 raise (Error (loc, MismatchAnn (cD, cG, e, (tau,t), (tau',t'))))

    | (If (loc, i, e1, e2), (tau, t)) ->
       let (_flag, tau', t', i') = syn cD (cG,cIH) i in
       let (tau',t') = C.cwhnfCTyp (tau',t') in
       begin
	 match (tau',t') with
	 | (TypBool, _) ->
	    let e1' = check cD (cG,cIH) e1 (tau,t) in
	    let e2' = check cD (cG,cIH) e2 (tau,t) in
	    Annotated.Comp.If (loc, i', e1', e2', ttau)
	 | tau_theta' ->
	    raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | (Hole (loc, f), (tau, t)) ->
       Annotated.Comp.Hole (loc, f, ttau)

  and syn cD (cG,cIH) e : (gctx option * typ * I.msub) =
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
       (None, (CompConst.get c).CompConst.typ, C.m_id, Annotated.Comp.DataConst (loc, c, ttau))

    | DataDest (loc, c) ->
       let ttau = ((CompDest.get c).CompDest.typ, C.m_id) in
       (None, (CompDest.get c).CompDest.typ, C.m_id, Annotated.Comp.DataDest (loc, c, ttau))

    | Const (loc, prog) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   let ttau = ((Comp.get prog).Comp.typ, C.m_id) in
	   (None, (Comp.get prog).Comp.typ, C.m_id, Annotated.Comp.Const (loc, prog, ttau))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 let ttau = ((Comp.get prog).Comp.typ, C.m_id) in
	 (None, (Comp.get prog).Comp.typ, C.m_id, Annotated.Comp.Const (loc, prog, ttau))

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
	    raise (Error (loc, MismatchSy (cD, cG, e, VariantPiBox, (tau,t))))
       end

    | PairVal (loc, i1, i2) ->
       let (_,tau1,t1,i1') = syn cD (cG,cIH) i1 in
       let (_,tau2,t2.i2') = syn cD (cG,cIH) i2 in
       let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
       let (tau2,t2) = C.cwhnfCTyp (tau2,t2) in
       let ttau = (TypCross (TypClo (tau1,t1), TypClo (tau2,t2)), C.m_id) in
       (Node, TypCross (TypClo (tau1,t1), TypClo (tau2,t2)), C.m_id,
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
	      raise (Error (loc, EqTyp (cD (tau1,t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1,t1), (tau2,t2))))

    | Boolean b ->
       let ttau = (TypBool, C.m_id) in
       (None, TypBool, C.m_id, Annotated.Comp.Boolean (b, ttau))

  and annotateBranches caseTyp cD cG branches tau_s ttau =
    List.map (fun branch -> checkBranch caseTyp cD cG branch tau_s ttau) branches

  and annotateBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
    | EmptyBranch (loc, cD1', pat, t1) ->
       let tau_p = Whnf.cnormCTyp (tau_s, t1) in
       (LF.checkMSub loc cD1' t1 cD;
       checkPattern cD1' I.Empty pat (tau_p, Whnf.m_id);
       Annotate.Comp.EmptyBranch (loc, cD1', pat, t1, (tau, t)))

    | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) ->
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
       Annotate.Comp.Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1', (tau, t)))

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
	   (cD1' I.Empty)
       in
       let CD1' =
	 if !Total.enabled then
	   id_map_ind cD1' t1 cD
	 else
	   cD1'
       in
       (LF.checkMSub loc cD1' t1 cD;
       checkPattern cD1' cG1 pat (tau_p, Whnf.m_id);
       let e1' =
	 check cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') e1 (tau', Whnf.m_id)
       in
       Annotate.Comp.Branch (loc, cD1', cG1, pat, t1, e1', (tau, t)))

  and annotatePattern cD cG pat ttau =
    match pat with
    | PatEmpty (loc, cPsi) ->
       begin
	 match ttau with
	 | (TypBox (_, I.ClTyp (I.MTyp tA, cPhi)), theta)
	 | (TypBox (_, I.ClTyp (I.PTyp tA, cPhi)), theta) ->
	    if C.convDCtx (Whnf.cnormDCtx (cPhi, theta)) cPsi then
	      Annotate.Comp.PatEmpty (loc, cPsi, ttau)
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
	    Annotate.Comp.PatMetaObj (loc, mO, ttau)
	 | _ ->
	    raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatPair (loc, pat1, pat2) ->
       begin
	 match ttau with
	 | (TypCross (tau1, tau2), theta) ->
	    let pat1' = annotatePattern cD cG pat1 (tau1, theta) in
	    let pat2' = annotatePattern cD cG pat2 (tau2, theta) in
	    Annotate.Comp.PatPair (loc, pat1', pat2', ttau)
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
       (loc, ttau', Annotate.Comp.PatConst (loc, c, pat_spine', ttau'))
    | PatVar (loc, k) ->
       let ttau = (lookup' cG k, C.m_id) in
       (loc, ttau, Annotate.Comp.PatVar (loc, k, ttau))
    | PatTrue loc ->
       let ttau = (TypBool, C.m_id) in
       (loc, ttau, Annotate.Comp.PatTrue (loc, ttau))
    | PatFalse loc ->
       let ttau (TypBool, C.m_id) in
       (loc, ttau, Annotate.Comp.PatFalse (loc, ttau))
    | PatAnn (loc, pat, tau) ->
       let ttau = (tau, C.m_id) in
       let pat' = annotatePattern cD cG pat ttau in
       (loc, ttau, Annotate.Comp.PatAnn (loc, pat', tau, ttau))

  and synPatSpine cD cG pat_spine (tau, theta) =
    match pat_spine with
    | PatNil -> ((tau, theta), Annotate.Comp.PatNil (tau, theta))
    | PatApp (loc, pat, pat_spine) ->
       begin
	 match (tau, theta) with
	 | (TypArr (tau1, tau2), theta) ->
	    let pat' = annotatePattern cD cG pat (tau1, theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau2, theta) in
	    (ttau, Annotate.Comp.PatAnn (loc, pat', pat_spine', ttau))
	 | (TypPiBox (cdecl, tau), theta) ->
	    let (theta', pat') = checkPatAgainstDecl cD pat (cdecl, tau1, theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau, theta') in
	    (ttau, Annotate.Comp.PatAnn (loc, pat', pat_spine', ttau))
       end

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl (_,ctyp,_), tau, theta) =
    LF.checkMetaObj cD mO (ctyp, theta);
    (I.MDot(metaObjToMFront mO, theta), Annotate.Comp.PatMetaObj (loc, mO, (tau, theta)))
end
