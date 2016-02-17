module P = Pretty.Int.DefaultPrinter
module PE = Pretty.Ext.DefaultPrinter
module R = Store.Cid.DefaultRenderer
open Printf

let loc_ghost = Syntax.Loc.ghost;

(* let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5]) *)

module LF = struct

  (* open Context *)
  (* open Store.Cid *)
  open Syntax.Int.LF
  module SE = Syntax.Ext

  module Unify = Unify.EmptyTrail

  (* type error = *)
  (*   | AnnotError of string *)
  (*   | NothingIsEverWrong *)
    (* | CtxVarMisCheck   of mctx * dctx * tclo * schema *)
    (* | CtxVarMismatch   of mctx * ctx_var * schema *)
    (* | CtxVarDiffer     of mctx * ctx_var * ctx_var *)
    (* | CheckError       of mctx * dctx * nclo * tclo *)
    (* | TupleArity       of mctx * dctx * nclo * trec_clo *)
    (* | SigmaMismatch    of mctx * dctx * trec_clo * trec_clo *)
    (* | KindMismatch     of mctx * dctx * sclo * (kind * sub) *)
    (* | TypMismatch      of mctx * dctx * nclo * tclo * tclo *)
    (* | IllTypedSub      of mctx * dctx * sub * dctx *)
    (* | SpineIllTyped    of int * int *)
    (* | LeftoverFV *)
    (* | ParamVarInst     of mctx * dctx * tclo *)
    (* | CtxHatMismatch   of mctx * dctx (\* expected *\) * psi_hat (\* found *\) * (Syntax.Loc.t * mfront) *)
    (* | IllTypedMetaObj  of mctx * clobj * dctx * cltyp  *)
    (* | TermWhenVar      of mctx * dctx * normal *)
    (* | SubWhenRen       of mctx * dctx * sub *)

  (* exception Error of Syntax.Loc.t * error *)

  (* let _ = Error.register_printer *)
  (* 	    (fun (Error (loc, err)) -> *)
  (* 	     Error.print_with_location loc (fun ppf -> *)
  (* 					    match err with *)
  (* 					    | AnnotError s -> *)
  (* 					       Format.fprintf ppf "%s" s)) *)

  let rec annMetaObj cD (loc', int_cM) (loc, ext_cM) cTt =
    (* printf "Pairing:\n\t[int_cM] %s\n\t[ext_cM] %s\n" *)
    (* 	  (P.metaObjToString cD (loc', int_cM)) *)
    (* 	  (PE.metaObjToString (Syntax.Ext.LF.Empty) (loc, ext_cM)); *)
    annMetaObj' cD (loc', int_cM) (loc, ext_cM) cTt

  and annMetaObj' cD (loc', int_cM) (loc, ext_cM) cTt =
    match (int_cM, ext_cM, cTt) with
    | CObj _, SE.Comp.CObj _, _ -> (loc', int_cM)
    | ClObj _, SE.Comp.ClObj _, _ -> (loc', int_cM)
    | int_cM', ext_cM', _ -> (loc', int_cM)
       (* raise (Error (loc_ghost, AnnotError ("Unable to pair:\n\t[int_cM'] " ^ P.metaObjToString cD (loc', int_cM') *)
       (* 	      ^ "\n\t[ext_cM'] " ^ PE.metaObjToString (Syntax.Ext.LF.Empty) (loc, ext_cM') *)
       (* 	      ^ "\n\t @ " ^ (Syntax.Loc.to_string loc) *)
       (* 	      ^ "\n"))) *)

end

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


  let rec ann cD cG int_e ext_e ttau =
    let cIH = I.Empty in
    annotate cD (cG, cIH) int_e ext_e ttau

  (* Use this version of the function to insert debug output *)
  and annotate cD (cG, cIH) int_e ext_e ttau =
    (* printf "Ann:\n\t[int_e] %s\n\t[ext_e] %s\n" *)
    (* 	   (P.expChkToString cD cG int_e) *)
    (* 	   (PE.expChkToString (Syntax.Ext.LF.Empty) ext_e); *)
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
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.Fun (loc', int_x, int_e'', ttau)

    | (Cofun (loc', int_bs), SE.Comp.Cofun (loc, ext_bs), (TypCobase (l, cid, sp), t)) ->
       let f =
    	 fun (CopatApp (ca_loc', int_dest, int_csp), int_e)
    	     (SE.Comp.CopatApp (ca_loc, _, ext_csp), ext_e) ->
	 begin
	   let (ttau', int_csp') =
	     synObs cD int_csp ext_csp ((CompDest.get int_dest).CompDest.typ, Whnf.m_id) ttau
	   in
	   let int_e' = annotate cD (cG, cIH) int_e ext_e ttau' in
	   (Annotated.Comp.CopatApp (ca_loc', int_dest, int_csp'), int_e')
	 end
       in
       let int_bs' = List.map2 f int_bs ext_bs in
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.Cofun (loc', int_bs', ttau)

    (* TODO *)
    (* Also hackish, if there's a Fun in the external, just skip over any internal MLam *)
    | (MLam (loc', int_u, int_e'), (SE.Comp.Fun _ as ext_e'), (TypPiBox (cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       int_e''

    (* This is an implicit MLam *)
    | (MLam (loc', int_u, int_e'), ext_e',
       (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       int_e''

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.No) as cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.MLam (loc', int_u, int_e'', ttau)

    | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'),
       (TypPiBox (I.Decl (_, cU, I.Inductive) as cdec, tau), t)) ->
       let int_e'' =
	 annotate (extend_mctx cD (int_u, cdec, t))
		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		  int_e' ext_e' (tau, C.mvar_dot1 t)
       in
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.MLam (loc', int_u, int_e'', ttau)

    (* | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'), *)
    (*    (TypPiBox (I.Decl (_, cU, I.Inductive) as cdec, tau), t)) -> *)
    (*    let int_e'' = *)
    (* 	 annotate (extend_mctx cD (int_u, cdec, t)) *)
    (* 		  (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1)) *)
    (* 		  int_e' ext_e' (tau, C.mvar_dot1 t) *)
    (*    in *)
    (*    Annotated.Comp.MLam (loc', int_u, int_e'', ttau) *)

    (* (\* TODO: Unknown MLams *\) *)
    (* | (MLam (loc', int_u, int_e'), SE.Comp.MLam (loc, _, ext_e'), *)
    (*	 (TypPiBox (cdec, tau), t)) -> *)
    (*	 let int_e'' = *)
    (*	   annotate cD (extend_mctx cD (u, cdec, t)) *)
    (*		    (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1)) *)
    (*		    int_e' ext_e' (tau, C.mvar_dot1 t) *)
    (*	 in *)
    (*	 Annotated.Comp.MLam (loc', int_u, int_e'', ttau) *)

    | (Pair (loc', int_e1, int_e2), SE.Comp.Pair (loc, ext_e1, ext_e2),
       (TypCross (tau1, tau2), t)) ->
       let int_e1' = annotate cD (cG, cIH) int_e1 ext_e1 (tau1, t) in
       let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau2, t) in
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.Pair (loc', int_e1', int_e2', ttau)

    | (Let (loc', int_i, (int_x, int_e')), SE.Comp.Let (loc, ext_i, (_, ext_e')),
       (tau, t)) ->
       let int_i' = strip_mapp_args cD cG int_i in
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i' ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (int_x, TypClo (tau', t'))) in
       let int_e'' = annotate cD (cG', Total.shift cIH) int_e' ext_e' (tau, t) in
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.Let (loc', int_i', (int_x, int_e''), ttau)

    | (LetPair (loc', int_i, (int_x, int_y, int_e')),
       SE.Comp.LetPair (loc, ext_i, (_, _, ext_e')),
       (tau, t)) ->
       let int_i' = strip_mapp_args cD cG int_i in
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i' ext_i in
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
	    Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	    Annotated.Comp.LetPair (loc', int_i', (int_x, int_y, int_e''), ttau)
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
       end

    | (Box (loc', int_cM), SE.Comp.Box (loc, ext_cM), (TypBox (l, mT), t)) ->
       begin
	 try
	   (* TODO LF.annMetaObj *)
	   let int_cM' = (* int_cM *) LF.annMetaObj cD int_cM ext_cM (mT, t)
	   in
	   Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	   Annotated.Comp.Box (loc, int_cM', ttau)
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
	   | I.ClObj (_, I.PObj (I.PVar (x, s))) ->
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
       (* let _ = () (\* LF.annMetaObj cD (loc, cM) (mT, C.m_id) *\) in *)
       let problem = Coverage.make loc int_prag cD int_branches tau_sc in
       let int_branches' =
	 annBranches total_pragma cD (cG, cIH) int_branches ext_branches tau0_sc (tau, t)
       in
       Coverage.process problem projOpt;
       (* TODO What are we doing here? What's the correct substituion? *)
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.Case (loc', int_prag,
		       Annotated.Comp.Ann
			 (Annotated.Comp.Box (loc, (l, cM), (tau0_sc, C.m_id)),
			  tau0_sc,
			  (tau0_sc, C.m_id)),
		       int_branches', ttau)

    | (Case (loc', int_prag, int_i, int_branches),
       SE.Comp.Case (loc, ext_prag, ext_i, ext_branches),
       (tau, t)) ->
       (* let _ = printf "[Case int_i] %s\n" (P.expSynToString cD cG int_i) in *)
       let anBranch total_pragma cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t) =
	 (* let _ = printf "[anBranch int_i] %s\n" (P.expSynToString cD cG int_i) in *)
	 let int_i' = strip_mapp_args cD cG int_i in
	 let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i' ext_i in
	 begin
	   match C.cwhnfCTyp (tau', t') with
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
		begin
		  match C.cnormCTyp (tau', C.m_id) with
		  | TypInd _tau -> true
		  | _ -> false
		end
	      in
	      if ind then
		let (int_i', int_branches') =
		  anBranch IndDataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
		in
		Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
		Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau)
	      else
		let (int_i', int_branches') =
		  anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
		in
		Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
		Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau)
	   | _ ->
	      let (int_i', int_branches') =
		anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
	      in
	      Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	      Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau)
	 end
       else
	 let (int_i', int_branches') =
	   anBranch DataObj cD (cG, cIH) int_i ext_i int_branches ext_branches (tau, t)
	 in
	 Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	 Annotated.Comp.Case (loc', int_prag, int_i', int_branches', ttau)

    | (Syn (loc', int_i), SE.Comp.Syn (loc, ext_i), (tau, t)) ->
       let int_i' = strip_mapp_args cD cG int_i in
       let ((_, tau', t'), int_i') = syn cD (cG, cIH) int_i' ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       if C.convCTyp (tau, t) (tau', t') then
	 begin
	   Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	   Annotated.Comp.Syn (loc', int_i', ttau)
	 end
       else
	 raise (Error (loc', MismatchChk (cD, cG, int_e, (tau, t), (tau', t'))))

    (* Changed to be in line with the actual type checker *)
    | (If (loc', int_i, int_e1, int_e2),
       SE.Comp.If (loc, ext_i, ext_e1, ext_e2),
       (tau, t)) ->
       let int_i' = strip_mapp_args cD cG int_i in
       let ((_flag, tau', t'), int_i') = syn cD (cG, cIH) int_i' ext_i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypBool, _) ->
	    let int_e1' = annotate cD (cG, cIH) int_e1 ext_e1 (tau, t) in
	    let int_e2' = annotate cD (cG, cIH) int_e1 ext_e1 (tau, t) in
	    Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	    Annotated.Comp.If (loc', int_i', int_e1', int_e2', ttau)
	 | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | Hole (loc', f'), SE.Comp.Hole loc, (tau, t) ->
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
       Annotated.Comp.Hole (loc', f', ttau)

    | eInt', eExt', ttau' ->
       raise (Error (loc_ghost, AnnotError
		("Unable to pair chk:"
		 ^ "\n\t [Int] exp_chk: " ^ P.expChkToString cD cG eInt'
		 ^ "\n\t [Int] ttau: " ^ P.subCompTypToString cD ttau'
		 ^ "\n\t [Ext] exp_chk: " ^ PE.expChkToString (Syntax.Ext.LF.Empty) eExt')))


  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    (* LF.checkMetaObj cD mO (ctyp, theta); *)
    I.MDot(metaObjToMFront mO, theta)

  and synObs cD int_csp ext_csp ttau1 ttau2 = match (int_csp, ext_csp, ttau1, ttau2) with
    | (CopatNil loc', SE.Comp.CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) ->
       if C.convCTyp (tau1, theta) (tau', theta') then
         ((tau2, theta), Annotated.Comp.CopatNil loc')
       else
         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))
    | (CopatApp (loc', dest, int_csp'), SE.Comp.CopatApp (loc, _, ext_csp'),
       (TypArr (tau1, tau2), theta), (tau', theta')) ->
       if C.convCTyp (tau1, theta) (tau', theta') then
         let ((tau'', theta''), int_csp'') =
	   synObs cD int_csp' ext_csp' ((CompDest.get dest).CompDest.typ, Whnf.m_id) (tau2, theta)
	 in
	 ((tau'', theta''), Annotated.Comp.CopatApp (loc, dest, int_csp''))
       else
         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))

  and strip_mapp_args cD cG int_i = int_i
    (* (int_i, ext_i) *)
    (* let (int_i', ext_i', _) = strip_mapp_args' cD cG int_i ext_i in (int_i', ext_i') *)
    (* let (int_i', _) = strip_mapp_args' cD cG int_i in int_i' *)

  (* and strip_mapp_args' cD cG i = match i with *)
  (*   | Const (_, prog) -> *)
  (*      (i, implicitCompArg (Comp.get prog).Comp.typ) *)
  (*   | DataConst (_, c) -> *)
  (*      (i, implicitCompArg (CompConst.get c).CompConst.typ) *)
  (*   | Var (_, x) -> *)
  (*      begin *)
  (* 	 match Context.lookup cG x with *)
  (* 	 | None -> (i, []) *)
  (* 	 | Some tau -> (i, implicitCompArg tau) *)
  (*      end *)
  (*   | Apply (loc', int_e1, int_e2) -> *)
  (*      let (int_e1', _) = strip_mapp_args' cD cG int_e1 in *)
  (*      (Apply (loc', int_e1', int_e2), []) *)
  (*   | MApp (loc', int_i1, int_mC) -> *)
  (*      let (int_i1', stripArgs) = strip_mapp_args' cD cG int_i1 in *)
  (*      begin *)
  (* 	 match stripArgs with *)
  (* 	 | false :: sA -> (int_i1', sA) *)
  (* 	 | true :: sA -> (MApp (loc', int_i1', int_mC), sA) *)
  (* 	 | [] -> (int_i1', []) *)
  (*      end *)
  (*   | PairVal (loc', int_i1, int_i2) -> *)
  (*      let (int_i1', _) = strip_mapp_args' cD cG int_i1 in *)
  (*      let (int_i2', _) = strip_mapp_args' cD cG int_i2 in *)
  (*      (PairVal (loc', int_i1', int_i2'), []) *)
  (*   | Equal (loc', int_i1, int_i2) -> *)
  (*      let (int_i1', _) = strip_mapp_args' cD cG int_i1 in *)
  (*      let (int_i2', _) = strip_mapp_args' cD cG int_i2 in *)
  (*      (Equal (loc', int_i1', int_i2'), []) *)
  (*   | _ -> (i, []) *)

  (* and implicitCompArg tau = *)
  (*   match tau with *)
  (*   | TypPiBox ((I.Decl (_, I.ClTyp (I.MTyp _, _), I.Maybe)), tau) -> *)
  (*      false :: (implicitCompArg tau) *)
  (*   | TypPiBox (_, tau) -> *)
  (*      true :: (implicitCompArg tau) *)
  (*   | _ -> [] *)

  and strip_imp_typs tau = tau
    (* match tau with *)
    (* | TypPiBox ((I.Decl (_, I.ClTyp (I.MTyp _, _), I.Maybe)), tau) -> *)
    (*    strip_imp_typs tau *)
    (* | TypPiBox (cdec, tau) -> *)
    (*    TypPiBox (cdec, strip_imp_typs tau) *)
    (* | tau' -> tau' *)

  and syn cD (cG, cIH) int_e ext_e =
    printf "Syn:\n\t[int_i] %s\n\t[ext_i] %s\n"
    	   (P.expSynToString cD cG int_e)
    	   (PE.expSynToString (Syntax.Ext.LF.Empty) ext_e);
    syn' cD (cG, cIH) int_e ext_e

  and syn' cD (cG, cIH) int_e ext_e = match int_e, ext_e with
    | (Var (loc', x), SE.Comp.Var (loc, _)) ->
       let (f, tau') = lookup cG x in
       let tau =
	 match C.cnormCTyp (tau', C.m_id) with
	 | TypInd tau -> tau
	 | _ -> tau'
       in
       let tau = strip_imp_typs tau in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       if Total.exists_total_decl f then
	 ((Some cIH, tau, C.m_id), Annotated.Comp.Var (loc', x, (tau, C.m_id)))
       else
	 ((None, tau, C.m_id), Annotated.Comp.Var (loc', x, (tau, C.m_id)))

    (* Possibly has implicit variables *)
    | (DataConst (loc', c), SE.Comp.DataConst (loc, _)) ->
       let tau = (CompConst.get c).CompConst.typ in
       let tau = strip_imp_typs tau in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((None, tau, C.m_id), Annotated.Comp.DataConst (loc', c, (tau, C.m_id)))

    | (DataConst (loc', c), SE.Comp.Var (loc, _)) ->
       let tau = (CompConst.get c).CompConst.typ in
       let tau = strip_imp_typs tau in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((None, tau, C.m_id), Annotated.Comp.DataConst (loc', c, (tau, C.m_id)))

    | (DataDest (loc', c), SE.Comp.Var (loc, _)) ->
       let tau = (CompDest.get c).CompDest.typ in
       let tau = strip_imp_typs tau in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((None, tau, C.m_id), Annotated.Comp.DataDest (loc', c, (tau, C.m_id)))

    | (DataDest (loc', c), SE.Comp.DataConst (loc, _)) ->
       let tau = (CompDest.get c).CompDest.typ in
       let tau = strip_imp_typs tau in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((None, tau, C.m_id), Annotated.Comp.DataDest (loc', c, (tau, C.m_id)))

    (* Possibly has implicit variables *)
    | (Const (loc', prog), SE.Comp.Const (loc, _)) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   begin
	     let tau = (Comp.get prog).Comp.typ in
	     let tau = strip_imp_typs tau in
	     Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	     ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id)))
	   end
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 begin
	   let tau = (Comp.get prog).Comp.typ in
	   let tau = strip_imp_typs tau in
	   Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	   ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id)))
	 end

    | (Const (loc', prog), SE.Comp.Var (loc, _)) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   begin
	     let tau = (Comp.get prog).Comp.typ in
	     let tau = strip_imp_typs tau in
	     Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	     ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id)))
	   end
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 begin
	   let tau = (Comp.get prog).Comp.typ in
	   let tau = strip_imp_typs tau in
	   Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	   ((None, tau, C.m_id), Annotated.Comp.Const (loc', prog, (tau, C.m_id)))
	 end

    | (Apply (loc', int_e1, int_e2), SE.Comp.Apply (loc, ext_e1, ext_e2)) ->
       let ((cIH_opt, tau1, t1), int_e1') = syn cD (cG, cIH) int_e1 ext_e1 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       begin
	 match (tau1, t1) with
	 | (TypArr (tau2, tau), t) ->
	    let int_e2' = annotate cD (cG, cIH) int_e2 ext_e2 (tau2, t) in
	    Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	    ((useIH loc' cD cG cIH_opt int_e2, tau, t),
	     Annotated.Comp.Apply (loc', int_e1', int_e2', (tau, t)))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, int_e1, VariantArrow, (tau, t))))
       end

    | (MApp (loc', int_e, int_mC), SE.Comp.Apply (loc, ext_i, (SE.Comp.Box (_, ext_mC)))) ->
       (* printf "[MApp 1]\n\t[int_i] %s\n\t[ext_i] %s\n" *)
       	   (* (P.expSynToString cD cG int_e) *)
       	   (* (PE.expSynToString (Syntax.Ext.LF.Empty) ext_i); *)
       begin
	 try
	   let ((cIH_opt, tau1, t1), int_e') = syn cD (cG, cIH) int_e ext_i in
	   begin
	     match (C.cwhnfCTyp (tau1, t1)) with
	     | (TypPiBox (I.Decl (_, ctyp, _), tau), t) ->
		let int_mC' = (* int_mC *) LF.annMetaObj cD int_mC ext_mC (ctyp, t) in
		let t = I.MDot (metaObjToMFront int_mC, t) in
		Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
		((useIH loc' cD cG cIH_opt (Box (loc', int_mC)), tau, t),
		 Annotated.Comp.MApp (loc', int_e', int_mC', (tau, t)))
	     | (tau, t) ->
		raise (Error (loc', MismatchSyn (cD, cG, int_e, VariantPiBox, (tau, t))))
	   end
	 (* If there's an error, then we strip the MApp and recurse again with Apply *)
	 with Error _ ->
	      let ((cIH_opt, tau1, t1), int_e') = syn cD (cG, cIH) int_e ext_e in
	      begin
		match (C.cwhnfCTyp (tau1, t1)) with
		| (TypPiBox (I.Decl (_, ctyp, _), tau), t) ->
		   let int_mC' = (* int_mC *) LF.annMetaObj cD int_mC ext_mC (ctyp, t) in
		   let t = I.MDot (metaObjToMFront int_mC, t) in
		   Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
		   ((useIH loc' cD cG cIH_opt (Box (loc', int_mC)), tau, t),
		    Annotated.Comp.MApp (loc', int_e', int_mC', (tau, t)))
		| (tau, t) ->
		   raise (Error (loc', MismatchSyn (cD, cG, int_e, VariantPiBox, (tau, t))))
	      end
       end

    | (PairVal (loc', int_i1, int_i2), SE.Comp.PairVal (loc, ext_i1, ext_i2)) ->
       let ((_, tau1, t1), int_i1') = syn cD (cG, cIH) int_i1 ext_i1 in
       let ((_, tau2, t2), int_i2') = syn cD (cG, cIH) int_i2 ext_i2 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       let (tau2, t2) = C.cwhnfCTyp (tau2, t2) in
       let tau = TypCross (TypClo (tau1, t1), TypClo (tau2, t2)) in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((None, tau, C.m_id),
	Annotated.Comp.PairVal (loc', int_i1', int_i2', (tau, C.m_id)))

    | (Ann (int_e, tau), SE.Comp.Ann (loc, ext_e, _)) ->
       let int_e' = annotate cD (cG, cIH) int_e ext_e (tau, C.m_id) in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((None, tau, C.m_id), Annotated.Comp.Ann (int_e', tau, (tau, C.m_id)))

    | (Ann (Box (loc', int_mO), tau), SE.Comp.BoxVal (loc, ext_mO)) ->
       begin
	 try
	   let ttau = (tau, C.m_id) in
	   let int_mO' = (* int_mO *) LF.annMetaObj cD int_mO ext_mO ttau in
	   Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	   ((None, tau, C.m_id),
	    Annotated.Comp.Ann (Annotated.Comp.Box (loc', int_mO', ttau), tau, ttau))
	 with C.FreeMVar (I.FMVar (u, _)) ->
	   raise (Error.Violation ("Free meta-variable" ^ (Id.render_name u)))
       end
       (* ((None, tau, C.m_id), Annotated.Comp.Ann (int_e', tau, (tau, C.m_id))) *)

    | (Equal (loc', int_i1, int_i2), SE.Comp.Equal (loc, ext_i1, ext_i2)) ->
       let ((_, tau1, t1), int_i1') = syn cD (cG, cIH) int_i1 ext_i1 in
       let ((_, tau2, t2), int_i2') = syn cD (cG, cIH) int_i2 ext_i2 in
       if C.convCTyp (tau1, t1) (tau2, t2) then
	 begin
	   match C.cwhnfCTyp (tau1, t1) with
	   | (TypBox _, _) ->
	      Typeinfo.Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
	      ((None, TypBool, C.m_id),
	       Annotated.Comp.Equal (loc', int_i1', int_i2', (TypBool, C.m_id)))
	   | (TypBool, _) ->
	      Typeinfo.Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
	      ((None, TypBool, C.m_id),
	       Annotated.Comp.Equal (loc', int_i1', int_i2', (TypBool, C.m_id)))
	   | (tau1, t1) ->
	      raise (Error (loc, EqTyp (cD, (tau1, t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1, t1), (tau2, t2))))

    | Boolean b, SE.Comp.Boolean (loc, _) ->
       Typeinfo.Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
       ((None, TypBool, C.m_id), Annotated.Comp.Boolean (b, (TypBool, C.m_id)))

    | eInt', eExt' ->
       raise (Error (loc_ghost, AnnotError
		("Unable to pair syn:"
		 ^ "\n\t [Int] exp_syn: " ^ P.expSynToString cD cG eInt'
		 ^ "\n\t [Ext] exp_syn: " ^ PE.expSynToString (Syntax.Ext.LF.Empty) eExt')))


  and annBranches caseTyp cD (cG, cIH) int_branches ext_branches tau_s ttau =
    List.map2
      (fun int_branch ext_branch ->
       annBranch caseTyp cD (cG, cIH) int_branch ext_branch tau_s ttau)
      int_branches ext_branches

  and annBranch caseTyp cD (cG, cIH) int_branch ext_branch tau_s (tau, t) =
    match int_branch, ext_branch with
    | EmptyBranch (loc', cD1', int_pat, t1), SE.Comp.EmptyBranch (loc, _, ext_pat) ->
       let tau_p = C.cnormCTyp (tau_s, t1) in
       let int_pat' = annPattern cD1' I.Empty int_pat ext_pat (tau_p, Whnf.m_id) in
       Annotated.Comp.EmptyBranch (loc', cD1', int_pat', t1)

    | (Branch (loc', cD1', cG, PatMetaObj (l1', int_mO), t1, int_e),
      SE.Comp.Branch (loc, _, SE.Comp.PatMetaObj (_, ext_mO), ext_e)) ->
       let TypBox (_, mT) = tau_s in
       let mT1 = C.cnormMetaTyp (mT, t1) in
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
       let cD1' = if !Total.enabled then
		    id_map_ind cD1' t1 cD
		  else
		    cD1' in
       (* LF.annMSub loc cD1' t1 cD; *)
       let int_mO' = (* int_mO *) LF.annMetaObj cD1' int_mO ext_mO (mT1, C.m_id) in
       let int_e' = annotate cD1' (cG', Context.append cIH cIH') int_e ext_e (tau', C.m_id)
       in
       Annotated.Comp.Branch (loc', cD1', cG,
			      Annotated.Comp.PatMetaObj (l1', int_mO', (tau_s, C.m_id))
			      , t1, int_e')

    | (Branch (loc', cD1', cG1, int_pat, t1, int_e),
      SE.Comp.Branch (loc, _, ext_pat, ext_e)) ->
       (* printf "[Branch] %s\n" (P.branchToString cD cG int_branch); *)
       let tau_p = C.cnormCTyp (tau_s, t1) in
       let cG' = C.cnormCtx (cG, t1) in
       let cIH = C.cnormCtx (C.normCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let k = Context.length cG1 in
       let cIH0 = Total.shiftIH cIH k in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller int_pat then
	   let cD1' = mvarsInPatt cD1' int_pat in
	   (cD1', Total.wf_rec_calls cD1' cG1)
	 else
	   (cD1', I.Empty)
       in
       let cD1' = if !Total.enabled then
		    id_map_ind cD1' t1 cD
		  else
		    cD1' in
       (* LF.annMSub loc cD1' t1 cD;  *)
       let int_pat' = annPattern cD1' cG1 int_pat ext_pat (tau_p, C.m_id) in
       let int_e' =
	 annotate cD1' ((Context.append cG' cG1), Context.append cIH0 cIH')
		  int_e ext_e (tau', C.m_id)
       in
       Annotated.Comp.Branch (loc', cD1', cG1, int_pat', t1, int_e')

  and annPattern cD cG int_pat ext_pat ttau =
    (* printf "Annotating patterns:\n\t[int_pat] %s\n\t[ext_pat] %s \n\t[with Type] %s\n" *)
    (* 	   (P.patternToString cD cG int_pat) *)
    (* 	   (PE.patternToString Syntax.Ext.LF.Empty ext_pat) *)
    (* 	   (P.subCompTypToString cD ttau); *)
    annPattern' cD cG int_pat ext_pat ttau

  and annPattern' cD cG int_pat ext_pat ttau = match int_pat, ext_pat with
    (* TODO Find out how empty patterns are produced *)
    | PatEmpty (loc', cPsi), _ ->
       begin
	 match ttau with
	 | (TypBox (_, I.ClTyp (I.MTyp tA, cPsi)), theta)
	 | (TypBox (_, I.ClTyp (I.PTyp tA, cPsi)), theta) ->
	    if C.convDCtx (C.cnormDCtx (cPsi, theta)) cPsi then
	      begin
		Typeinfo.Annot.add loc' (P.subCompTypToString cD ttau);
		Annotated.Comp.PatEmpty (loc', cPsi, ttau)
	      end
	    else
	      raise (Error (loc', BoxMismatch (cD, I.Empty, ttau)))
	 | _ ->
	    raise (Error (loc', BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatMetaObj (loc', int_mO), SE.Comp.PatMetaObj (loc, ext_mO) ->
       begin
	 match ttau with
	 | (TypBox (_, ctyp), theta) ->
	    let int_mO' = (* int_mO *) LF.annMetaObj cD int_mO ext_mO (ctyp, theta) in
	    Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	    Annotated.Comp.PatMetaObj (loc', int_mO', ttau)
	 | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    (* | PatMetaObj (loc', int_mO), SE.Comp.PatAnn (loc, SE.Comp.PatMetaObj (_, ext_mO), _) -> *)
    (*    begin *)
    (* 	 match ttau with *)
    (* 	 | (TypBox (_, ctyp), theta) -> *)
    (* 	    let int_mO' = int_mO (\* LF.annMetaObj cD int_mO ext_mO (ctyp, theta) *\) in *)
    (* 	    Annotated.Comp.PatMetaObj (loc', int_mO', ttau) *)
    (* 	 | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau))) *)
    (*    end *)

    | (PatPair (loc', int_pat1, int_pat2), SE.Comp.PatPair (loc, ext_pat1, ext_pat2)) ->
       begin
	 match ttau with
	 | (TypCross (tau1, tau2), theta) ->
	    let int_pat1' = annPattern cD cG int_pat1 ext_pat1 (tau1, theta) in
	    let int_pat2' = annPattern cD cG int_pat2 ext_pat2 (tau2, theta) in
	    Typeinfo.Annot.add loc (P.subCompTypToString cD ttau);
	    Annotated.Comp.PatPair (loc', int_pat1', int_pat2', ttau)
	 | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau)))
       end

    | int_pat, SE.Comp.PatAnn (_, ext_pat, _) ->
       annPattern cD cG int_pat ext_pat ttau

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

  and synPattern cD cG int_pat ext_pat =
    (* printf "Building pattern types:\n\t[int_pat] %s\n\t[ext_pat] %s\n" *)
    (* 	   (P.patternToString cD cG int_pat) *)
    (* 	   (PE.patternToString Syntax.Ext.LF.Empty ext_pat); *)
    synPattern' cD cG int_pat ext_pat

  and synPattern' cD cG int_pat ext_pat = match int_pat, ext_pat with
    | (PatConst (loc', int_c, int_pat_spine), SE.Comp.PatConst (loc, ext_c, ext_pat_spine)) ->
       let tau = (CompConst.get int_c).CompConst.typ in
       let rec int_spineLen pat_sp = match pat_sp with
	 | PatNil -> 0
	 | PatApp (_, _, pat_sp') -> 1 + int_spineLen pat_sp'
       in
       let rec ext_spineLen pat_sp = match pat_sp with
	 | SE.Comp.PatNil _ -> 0
	 | SE.Comp.PatApp (_, _, pat_sp') -> 1 + ext_spineLen pat_sp'
       in
       let rec handle_implicits count int_pat_spine ext_pat_spine ttau =
	 (* This is kind of hackish, but I don't know what else to do. *)
	 (* If the spines are the same length, then don't worry about implicits *)
	 if int_spineLen int_pat_spine = ext_spineLen ext_pat_spine then
	   (int_pat_spine, ext_pat_spine, ttau)
	 else
	   begin
	     match count with
	     | 0 -> (int_pat_spine, ext_pat_spine, ttau)
	     | count' ->
		begin
		  match int_pat_spine, ext_pat_spine with
		  (* | PatNil, _ -> 	(\* This shouldn't happen, I think *\) *)
		  | PatApp (_, int_pat', int_pat_spine'), ext_pat_spine ->
		     (* We have to handle the type of the pattern too *)
		     let ttau' =
		       begin
			 match ttau with
			 | (TypArr (tau1, tau2), theta) ->
			    (tau2, theta)
			 | (TypPiBox (cdecl, tau'), theta) ->
			    let theta' = checkPatAgainstCDecl cD int_pat' (cdecl, theta) in
			    (tau', theta')
		       end
		     in
		     handle_implicits (count' - 1) int_pat_spine' ext_pat_spine ttau'
		end
	   end
       in
       let (int_pat_spine', ext_pat_spine', ttau') =
	 handle_implicits (CompConst.get_implicit_arguments int_c)
			  int_pat_spine ext_pat_spine (tau, C.m_id)
       in
       let (ttau'', int_pat_spine'') =
	 synPatSpine cD cG int_pat_spine' ext_pat_spine' ttau'
       in
       Typeinfo.Annot.add loc (P.subCompTypToString cD ttau'');
       ((loc', ttau''), Annotated.Comp.PatConst (loc', int_c, int_pat_spine'', ttau''))

    (* | PatVar (loc', k), SE.Comp.PatAnn (loc, SE.Comp.PatVar (_, _), _) -> *)
    (*    let tau = lookup' cG k in *)
    (*    ((loc', (tau, C.m_id)), Annotated.Comp.PatVar (loc', k, (tau, C.m_id))) *)

    | PatVar (loc', k), SE.Comp.PatVar (loc, _) ->
       let tau = lookup' cG k in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((loc', (tau, C.m_id)), Annotated.Comp.PatVar (loc', k, (tau, C.m_id)))

    | PatTrue loc', SE.Comp.PatTrue loc ->
       Typeinfo.Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
       ((loc', (TypBool, C.m_id)), Annotated.Comp.PatTrue (loc', (TypBool, C.m_id)))

    | PatFalse loc', SE.Comp.PatFalse loc ->
       Typeinfo.Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
       ((loc', (TypBool, C.m_id)), Annotated.Comp.PatFalse (loc', (TypBool, C.m_id)))

    | PatAnn (loc', int_pat', tau), SE.Comp.PatAnn (loc, ext_pat', _) ->
       let int_pat'' = annPattern cD cG int_pat' ext_pat' (tau, C.m_id) in
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
       ((loc', (tau, C.m_id)), Annotated.Comp.PatAnn (loc', int_pat'', tau, (tau, C.m_id)))

    | PatAnn (loc', int_pat', tau), ext_pat' ->
       let int_pat'' = annPattern cD cG int_pat' ext_pat' (tau, C.m_id) in
       ((loc', (tau, C.m_id)), Annotated.Comp.PatAnn (loc', int_pat'', tau, (tau, C.m_id)))

    | (patInt', patExt') ->
       raise (Error (loc_ghost, AnnotError ("Unable to pair pat:\n"
			  ^ "\n\t [Int] pat: " ^ P.patternToString cD cG patInt'
			  ^ "\n\t [Ext] pat: " ^ PE.patternToString Syntax.Ext.LF.Empty patExt')))

  and synPatSpine cD cG int_pat_spine ext_pat_spine (tau, theta) =
    (* printf "Working with pattern spine:\n\t[int_pat_spine] %s\n\t[tau] %s\n\t[ext_pat_spine] %s\n" *)
    (* 	   (P.patSpineToString cD cG int_pat_spine) *)
    (* 	   (P.subCompTypToString cD (tau, theta)) *)
    (* 	   (PE.patSpineToString (Syntax.Ext.LF.Empty) ext_pat_spine); *)
    synPatSpine' cD cG int_pat_spine ext_pat_spine (tau, theta)


  and synPatSpine' cD cG int_pat_spine ext_pat_spine (tau, theta) =
    match int_pat_spine, ext_pat_spine with
    | (PatNil, SE.Comp.PatNil loc) ->
       Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, theta));
       ((tau, theta), Annotated.Comp.PatNil (tau, theta))
    | (PatApp (loc', int_pat', int_pat_spine'), SE.Comp.PatApp (loc, ext_pat', ext_pat_spine')) ->
       begin
	 match (tau, theta) with
	 | (TypArr (tau1, tau2), theta) ->
	    let int_pat'' = annPattern cD cG int_pat' ext_pat' (tau1, theta) in
	    let (ttau, int_pat_spine'') =
	      synPatSpine cD cG int_pat_spine' ext_pat_spine' (tau2, theta)
	    in
	    Typeinfo.Annot.add loc (P.subCompTypToString cD (tau1, theta));
	    (ttau, Annotated.Comp.PatApp (loc', int_pat'', int_pat_spine'', ttau))
	 | (TypPiBox ((I.Decl (_, ctyp, _)) as cdecl, tau'), theta) ->
	    let theta' = checkPatAgainstCDecl cD int_pat' (cdecl, theta) in
	    let tau = TypBox (loc', ctyp) in
	    let int_pat'' = annPattern cD cG int_pat' ext_pat' (tau, theta) in
	    let (ttau, int_pat_spine'') =
	      synPatSpine cD cG int_pat_spine' ext_pat_spine' (tau', theta')
	    in
	    Typeinfo.Annot.add loc (P.subCompTypToString cD (tau, theta));
	    (ttau, Annotated.Comp.PatApp (loc', int_pat'', int_pat_spine'', ttau))
       end

end

module Sgn = struct

end
