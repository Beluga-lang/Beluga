module P = Pretty.Int.DefaultPrinter
module PE = Pretty.Ext.DefaultPrinter

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5])

module LF = Lfcheck

module Comp = struct

  module Unify = Unifty.EmptyTrail

  open Store.Cid
  open Syntax.Int.Comp
  module SE = Syntax.Ext

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf


  module Annotated = Annotated

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
    (*	 Annotated.Rec (loc', int_f, int_e'', ttau) *)

    | (Fun (loc', int_x, int_e'), SE.Comp.Fun (loc, _, ext_e'), (TypArr (tau1, tau2), t)) ->
       let int_e'' =
	 annotate cD (I.Dec (cG, CTypDecl (int_x, TypClo (tau1, t))), (Total.shift cIH))
		  int_e' ext_e' (tau2, t)
       in
       Annotated.Fun (loc', int_x, int_e'', ttau, Annotated.ExpTerm)

    (* TODO: Cofuns*)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       let int_e'' =
	 annotate cD (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Annotated.MLam (loc', int_u, int_e'', ttau, Annotated.ImpTerm)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.No) as cdec, tau), t)) ->
       let int_e'' =
	 annotate cD (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Annotated.MLam (loc', int_u, int_e'', ttau, Annotated.ExpTerm)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.Inductive) as cdec, tau), t)) ->
       let int_e'' =
	 annotate cD (extend_mctx cD (u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Annotated.MLam (loc', int_u, int_e'', ttau, Annotated.ExpTerm)

    (* (\* TODO: Unknown MLams *\) *)
    (* | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'), *)
    (*	 (TypPiBox (cdec, tau), t)) -> *)
    (*	 let int_e'' = *)
    (*	   annotate cD (extend_mctx cD (u, cdec, t)) *)
    (*		    (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1)) *)
    (*		    int_e' ext_e' (tau, C.mvar_dot1 t) *)
    (*	 in *)
    (*	 Annotated.MLam (loc', int_u, int_e'', ttau, Annotated.ExpTerm) *)

    | (Pair (loc', int_e1, int_e2), SES.Comp.Pair (loc, ext_e1, ext_e2),
       (TypCross (tau1, tau2), t)) ->
       let int_e1' = annotate cD (cG, cIH) int_e1 ext_e1 (tau1, t) in
       let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau2, t) in
       Annotated.Pair (loc', int_e1', int_e2', ttau, Annotated.ExpTerm)

    | (Let (loc', int_i, (int_x, int_e')), SE.Comp.Let (loc, ext_i, (_, ext_e')),
       (tau, t)) ->
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
       let int_e'' = annotate cD (cG', Total.shift cIH) int_e' ext_e' (tau, t) in
       Annotated.Let (loc', int_i', (int_x, int_e''), ttau, Annotated.ExpTerm)

    | (LetPair (loc', int_i, (int_x, int_y, int_e')),
       SE.Comp.LetPair (loc, ext_i, (_, _, ext_e')),
       (tau, t)) ->
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypCross (tau1, tau2), t') ->
	    let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))),
			     CTypDecl (y, TypClo (tau2, t')))
	    in
	    let int_e'' =
	      annotate cD (cG', Total.shift (Total.shift cIH)) int_e' ext_e' (tau, t)
	    in
	    Annotated.LetPair (loc', int_i', (int_x, int_y, int_e''), ttau, Annotated.ExpTerm)
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
       end

    | (Box (loc', int_cM), SE.Comp.Box (loc, ext_cM), (TypBox (l, mT), t)) ->
       begin
	 try
	   (* TODO LF.annMetaObj *)
	   let int_cM' = int_cM (* LF.annMetaObj cD int_cM ext_cM (mT, t) *)
	   in
	   Annotated.Box (loc, int_cM', ttau, Annotated.ExpTerm)
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
	      (order, TypBox (loc', convToParamType (C.cnormMetaTyp (mT, C.m_id))), Some k)
	   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x, s), _))) ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox (loc', C.cnorMetaTyp (mT, C.m_id)), None)
	   | I.CObj (I.CtxVar (I.CtxOffset k)) ->
	      let order = if !Total.enabled && is_indMObj cD x then
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
       Annotated.Case (loc', int_prag,
		       Annotated.Ann
			 (Annotated.Box (loc, (l, cM), tau0_sc, Annotated.ExpTerm),
			  tau0_sc,
			  Annotated.ExpTerm),
		       int_branches')

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
	      annBranches total_pragma cD (cG, cIH) int_branches ext_branches tau_s (tau,t)
	   | (tau', t') ->
	      let tau_s = C.cnormCTyp (tau', t') in
	      let problem = Coverage.make loc int_prag cD int_branches (C.cnormCTyp (tau',t')) in
	      Coverage.process problem None;
	      annBranches total_pragma cD (cG, cIH) int_branches ext_branches tau_s (tau, t)
	 end
       in
       if !Total.enabled then
	 begin
	   match int_i, ext_i with
	   | Var (_, x), SE.Comp (loc, _) ->
	      let (f, tau') = lookup cG x in
	      let ind =
		match C.cnormCTyp (tau', C.m_id) with
		| TypInd _tau -> true
		| _ -> false
	      in
	      if ind then
		let int_branches' =
		  anBranch IndDataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
		in
		Annotated.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExtTerm)
	      else
		let int_branches' =
		  anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
		in
		Annotated.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExtTerm)
	   | _ ->
	      let int_branches' =
		anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
	      in
	      Annotated.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExtTerm)
	 end
       else
	 let int_branches' =
	   anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
	 in
	 Annotated.Case (loc', int_prag, int_i', int_branches', ttau, Annotated.ExtTerm)

    | (Syn (loc', int_i), SE.Comp (loc, ext_i), (tau, t)) ->
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       if C.convCTyp (tau, t) (tau', t') then
	 Annotated.Syn (loc', int_i', ttau, Annotated.ExtTerm)
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
	    Annotated.If (loc', int_i', int_e1', int_e2', ttau, Annotated.ExtTerm)
	 | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | Hole (loc', f'), SE.Comp.Hole loc, (tau, t) ->
       Annotated.Hole (loc', f', ttau, Annotated.ExtTerm)

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
	 ((Some cIH, tau, C.m_id), Annotated.Var (loc', x, (tau, C.m_id), Annotated.ExtTerm))
       else
	 ((None, tau, C.m_id), Annotated.Var (loc', x, (tau, C.m_id), Annotated.ExtTerm))

    (* Possibly has implicit variables *)
    | (DataConst (loc', c), SE.Comp.DataConst (loc, _)) ->
       let tau = (CompConst.get c).CompConst.typ in
       ((None, tau, C.m_id), Annotated.DataConst (loc', c, (tau, C.m_id), Annotated.ExtTerm))

    (* Possibly has implicit variables *)
    | (DataDest (loc', c), SE.Comp.DataDest (loc, _)) ->
       let tau = (CompDest.get c).CompDest.typ in
       ((None, tau, C.m_id), Annotated.DataDest (loc', c, (tau, C.m_id), Annotated.ExtTerm))

    (* Possibly has implicit variables *)
    | (Const (loc', prog), SE.Comp.Const (loc, _)) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   let tau = (Comp.get prog).Comp.typ in
	   ((None, tau, C.m_id) Annotated.Const (loc', prog, (tau, C.m_id), Annotated.ExtTerm))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 let tau = (Comp.get prog).Comp.typ in
	 ((None, tau, C.m_id), Annotated.Const (loc', prog, (tau, C.m_id), Annotated.ExtTerm))

    | (Apply (loc', int_e1, int_e2), SE.Comp.Apply (loc, ext_e1, ext_e2)) ->
       let ((cIH_opt, tau1, t1), int_e1') = syn cD (cG, cIH) int_e1 ext_e1 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       begin
	 match (tau1, t1) with
	 | (TypArr (tau2, tau), t) ->
	    let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau2, t) in
	    ((useIH loc cD cG cIH_opt int_e2, tau, t),
	     Annotated.Apply (loc', int_e1', int_e2', (tau, t), Annotated.ExtTerm))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, int_e1, VariantArrow, (tau, t))))
       end

    | (MApp (loc', int_e, int_mC), SE.Comp.MApp (loc, ext_e, ext_mC)) ->
       let ((cIH_opt, tau1, t1), int_e') = syn cD (cG, cIH) int_e ext_e in
       begin
	 match (C.cwhnfCTyp (tau1, t1)) with
	 | (TypPiBox (I.Decl (_, ctyp, _), tau), t) ->
	    let int_mC' = int_mC (* LF.annMetaObj cD int_mC ext_mC (ctyp, t); *) in
	    let t = I.MDot (metaObjToMFront mC, t) in
	    ((useIH loc cD cG cIH_opt (Box (loc, mC)), tau, t),
	     Annotated.MApp (loc', int_e', int_mC', (tau, t), Annotated.ExtTerm))
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
	Annotated.PairVal (loc', int_i1', int_i2', (tau, C.m_id), Annotated.ExtTerm))

    | (Ann (int_e, tau), Ann (loc, ext_e, _)) ->
       let int_e' = annotate cD (cG, cIH) int_e ext_e (tau, C.m_id) in
       ((None, tau, C.m_id), Annotated.Ann (int_e', tau, (tau, C.m_id), Annotated.ExtTerm))

    | (Equal (loc', int_i1, int_i2), SE.Comp.Equal (loc, ext_i1, ext_i2)) ->
       let ((_, tau1, t1), int_i1') = syn cD (cG, cIH) int_i1 ext_i1 in
       let ((_, tau2, t2), int_i2') = syn cD (cG, cIH) int_i2 ext_i2 in
       if C.convCTyp (tau1, t1) (tau2, t2) then
	 begin
	   match C.cwhnfCTyp (tau1, t1) with
	   | (TypBox _, _) ->
	      ((None, TypBool, C.m_id),
	       Annotated.Equal (loc', int_i1', int_i2', (TypBool, C.m_id), Annotated.ExtTerm))
	   | (TypBool, _) ->
	      ((None, TypBool, C.m_id),
	       Annotated.Equal (loc', int_i1', int_i2', (TypBool, C.m_id), Annotated.ExtTerm))
	   | (tau1, t1) ->
	      raise (Error (loc, EqTyp (cD, (tau1, t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1, t1), (tau2, t2))))

    | Boolean b, SE.Comp.Boolean (loc, _) ->
       ((None, TypBool, C.m_id), Annotated.Boolean (b, (TypBool, C.m_id), Annotated.ExtTerm))

end

module Sgn = struct

end
