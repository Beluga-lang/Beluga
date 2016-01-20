module Loc = Syntax.Int.Loc
module P = Pretty.Int.DefaultPrinter
module PE = Pretty.Ext.DefaultPrinter
module R = Store.Cid.DefaultRenderer
open Lexing
open Printf

let generate_annotations = ref true;

exception AnnotError of string

let _ = Error.register_printer
	  (fun (AnnotError s) ->
	  Error.print (fun ppf -> Format.fprintf ppf "AnnotError: %s" s))

module Annot = struct
  open Syntax.Int

  (* Type Annotation Store *)

  type entry = {
    typ : string
  }

  let mk_entry (t : string) : entry =
  {
    typ = ExtString.String.map (fun c -> if c <> '\n' then c else ' ') t
  }

  let store     = Hashtbl.create 0
  let add (l : Loc.t) (t : string) =
		  Hashtbl.replace store l (mk_entry t)
  let get       = Hashtbl.find store
  let to_string (e : entry) = e.typ
  let clear ()  = Hashtbl.clear store

  (* Printing functions *)

  let output_int (pp : out_channel) (i : int) : unit = output_string pp (string_of_int i)

  let rec print_annot (pp : out_channel) (name : string) : unit =
  begin
    let sorted =
    let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) store [] in
      List.sort (fun (key1,_) (key2,_) -> compare key1 key2) l in
    let f = print_one pp name in
    ignore (List.iter f sorted);
    close_out pp
  end

  and print_one (pp : out_channel) (name : string) (typtup : Loc.t * entry) : unit =
    begin
      let (loc, entry) = typtup in
      let tp = entry.typ in
      print_location pp loc name;
      output_string pp "\ntype(\n     ";
      output_string pp tp;
      output_string pp "\n)\n"
    end

  and print_location (pp : out_channel) (loc : Loc.t) (name : string) : unit =
    begin
      let start_pos = Loc.start_pos loc in
      let end_pos = Loc.stop_pos loc in
      print_position pp start_pos name;
      output_char pp ' ';
      print_position pp end_pos name
    end

  and print_position (pp : out_channel) (pos : position) (name : string) : unit =
    begin
      output_string pp "\"";
      output_string pp (String.escaped name);
      output_string pp "\" ";
      output_int pp pos.pos_lnum;
      output_char pp ' ';
      output_int pp pos.pos_bol;
      output_char pp ' ';
      output_int pp (pos.pos_cnum + 1)
    end

end

module LF = struct

end

module Comp = struct
  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  module SELF = Syntax.Ext.LF
  module SEComp = Syntax.Ext.Comp

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

  let rec annotate cD cG eInt eExt ttau =
    let cIH = Syntax.Int.LF.Empty in
    annotate_comp_exp_chk cD (cG, cIH) eInt eExt ttau

  and annotate_comp_exp_chk cD (cG, cIH) eInt eExt (tau, t) =
    (* printf "[annotate] expChk: %s\n" (P.expChkToString cD cG eInt); *)
    annotate_comp_exp_chk' cD (cG, cIH) eInt eExt (C.cwhnfCTyp (tau, t))

  and annotate_comp_exp_chk' cD (cG, cIH) eInt eExt ttau = match (eInt, eExt, ttau) with
    | (Rec (loc, f, eInt'), eExt', (tau, t)) ->
       annotate_comp_exp_chk
	 cD (I.Dec (cG, CTypDecl (f, TypClo (tau, t))), (Total.shift cIH)) eInt' eExt' ttau

    | (Fun (_, x, eInt'), SEComp.Fun (loc, _, eExt'), (TypArr (tau1, tau2), t)) ->
       annotate_comp_exp_chk
	 cD (I.Dec (cG, CTypDecl (x, TypClo (tau1, t))), (Total.shift cIH)) eInt' eExt' (tau2, t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (Cofun (_, bs1), SEComp.Cofun (loc, bs2), (TypCobase (l, cid, sp), t)) ->
       let f = fun (CopatApp (_, dest1, csp1), eInt') (SEComp.CopatApp (loc', _, _), eExt') ->
	 (let ttau' = synObs cD csp1 ((CompDest.get dest1).CompDest.typ, Whnf.m_id) ttau in
	 annotate_comp_exp_chk cD (cG, cIH) eInt' eExt' ttau';
	 Annot.add loc' (P.subCompTypToString cD ttau'))
       in
       List.iter2 f bs1 bs2;
       Annot.add loc (P.subCompTypToString cD ttau)

    (* Implicit MLam, does not have a node in the external syntax tree *)
    | (MLam (_, u, eInt'), SEComp.MLam (loc, _, eExt'), (TypPiBox (I.Decl (_, cU, I.No) as cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (MLam (_, u, eInt'), SEComp.MLam (loc, _, eExt'), (TypPiBox (I.Decl (_, cU, I.Inductive) as cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (MLam (_, u, eInt'), eExt', (TypPiBox (cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t)

    | (Pair (_, eInt1, eInt2), SEComp.Pair (loc, eExt1, eExt2), (TypCross (tau1, tau2), t)) ->
       annotate_comp_exp_chk cD (cG, cIH) eInt1 eExt1 (tau1, t);
       annotate_comp_exp_chk cD (cG, cIH) eInt2 eExt2 (tau2, t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (Let (_, iInt, (x, eInt')), SEComp.Let (loc, iExt, (_, eExt')), (tau, t)) ->
       let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) iInt iExt in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
       annotate_comp_exp_chk cD (cG', Total.shift cIH) eInt' eExt' (tau, t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (LetPair (_, iInt, (x, y, eInt')), SEComp.LetPair (loc, iExt, (_, _, eExt')), (tau, t)) ->
       let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) iInt iExt in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypCross (tau1, tau2), t') ->
	    let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t')))
			    , CTypDecl (y, TypClo (tau2, t')))
	    in
	    annotate_comp_exp_chk cD (cG', (Total.shift (Total.shift cIH))) eInt' eExt' (tau,t)
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
       end

    | (Box (_, cMInt), SEComp.Box (loc, cMExt), (TypBox (l, mT), t)) ->
       begin
	 (* try *)
	   (* LF.annotate_meta_obj cD cMInt (mT, t); *)
	   Annot.add loc (P.subCompTypToString cD ttau)
	 (* with Whnf.FreeMVar (I.FMVar (u, _)) -> *)
	 (* raise (Error.Violation "(Free meta-variable " ^ Id.render_name u)) *)
       end

    | (Case (_, prag, Ann (Box (_, (l, cM)), (TypBox (l', mT) as tau0_sc)), branchesInt),
       SEComp.Case (loc, _, SEComp.BoxVal (_, m0), branchesExt),
       (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
    	 begin
    	   match cM with
    	   | I.ClObj (_, I.MObj (I.Root (_, I.PVar (x, s), _)))
    	   | I.ClObj (_, I.PObj (I.PVar (x, s))) ->
    	      let order = if !Total.enabled && is_indMObj cD x then
    			    IndIndexObj (l,cM)
    			  else
    			    IndexObj (l,cM)
    	      in
    	      (order, TypBox (l', convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), None)
    	   | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k), _)))
    	   | I.ClObj (_, I.PObj (I.Proj (I.PVar (x,s), k))) ->
    	      let order = if !Total.enabled && is_indMObj cD x then
    			    IndIndexObj (l,cM)
    			  else
    			    IndexObj (l,cM)
    	      in
    	      (order, TypBox (l', convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), Some k)
    	   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x, s), _))) ->
    	      let order = if !Total.enabled && is_indMObj cD x then
    			    IndIndexObj (l,cM)
    			  else
    			    IndexObj (l,cM)
    	      in
    	      (order, TypBox (l', Whnf.cnormMetaTyp (mT, C.m_id)), None)
    	   | I.CObj (I.CtxVar (I.CtxOffset k)) ->
    	      let order = if !Total.enabled && is_indMObj cD k then
    			    IndIndexObj (l,cM)
    			  else
    			    IndexObj (l,cM)
    	      in
    	      (order, TypBox (l', Whnf.cnormMetaTyp (mT, C.m_id)), None)
    	 end
       in
       (* LF.annotate_meta_obj cD (loc, cM), (mT, C.m_id); *)
       let problem = Coverage.make loc prag cD branchesInt tau_sc in
       annotate_branches total_pragma cD (cG, cIH) branchesInt branchesExt tau0_sc (tau, t);
       Annot.add loc (P.subCompTypToString cD ttau);
       Coverage.process problem projOpt

    | (Case (_, prag, iInt, branchesInt), SEComp.Case (loc, _, iExt, branchesExt), (tau, t)) ->
       let annBranch total_pragma cD (cG, cIH) iInt iExt branchesInt branchesExt (tau, t) =
    	 let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) iInt iExt in
    	 begin
    	   match C.cwhnfCTyp (tau', t') with
    	   | (TypBox (loc', mT), t') ->
    	      let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
    	      let problem = Coverage.make loc prag cD branchesInt tau_s in
    	      annotate_branches total_pragma cD (cG, cIH)
                 branchesInt branchesExt tau_s (tau,t);
    	      Annot.add loc (P.subCompTypToString cD ttau);
    	      Coverage.process problem None
    	   | (tau', t') ->
    	      let tau_s = C.cnormCTyp (tau', t') in
    	      let problem = Coverage.make loc prag cD branchesInt (Whnf.cnormCTyp (tau', t')) in
    	      annotate_branches total_pragma cD (cG, cIH)
    	         branchesInt branchesExt tau_s (tau,t);
    	      Annot.add loc (P.subCompTypToString cD ttau);
    	      Coverage.process problem None
    	 end
       in
       if !Total.enabled then
    	 begin
    	   match (iInt, iExt) with
    	   | Var (_, x), SEComp.Var (_, _) ->
    	      let (f, tau') = lookup cG x in
    	      let ind =
    		begin
    		  match Whnf.cnormCTyp (tau', Whnf.m_id) with
    		  | TypInd _tau -> true
    		  | _ -> false
    		end
    	      in
    	      if ind then
    		annBranch IndDataObj cD (cG, cIH) iInt iExt branchesInt branchesExt (tau,t)
    	      else
    		annBranch DataObj cD (cG, cIH) iInt iExt branchesInt branchesExt (tau,t)
    	   | _ ->
    	      annBranch DataObj cD (cG, cIH) iInt iExt branchesInt branchesExt (tau,t)
    	 end
       else
    	 annBranch DataObj cD (cG, cIH) iInt iExt branchesInt branchesExt (tau, t)

    | (Syn (_, iInt), SEComp.Syn (loc, iExt), (tau, t)) ->
       let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) iInt iExt in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       if C.convCTyp (tau, t) (tau', t') then
	 Annot.add loc (P.subCompTypToString cD ttau)
       else
	 raise (Error (loc, MismatchChk (cD, cG, eInt, (tau,t), (tau', t'))))

    | (If (_, iInt, eInt1, eInt2), SEComp.If (loc, iExt, eExt1, eExt2), (tau, t)) ->
       let (_flag, tau', t') = annotate_comp_exp_syn cD (cG, cIH) iInt iExt in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypBool, _) ->
	    begin
	      annotate_comp_exp_chk cD (cG, cIH) eInt1 eExt1 (tau, t);
	      annotate_comp_exp_chk cD (cG, cIH) eInt2 eExt2 (tau, t);
	      Annot.add loc (P.subCompTypToString cD ttau)
	    end
	 | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | (Hole (_, f), SEComp.Hole loc, (tau, t)) ->
       Annot.add loc (P.subCompTypToString cD ttau)

    | eInt', eExt', _ ->
       let (_, str) = render_ext_exp_chk eExt' in
       raise (AnnotError
		("Unable to pair chk:\n\t" ^ render_int_exp_chk eInt'
		 ^ "\n\t\tand\n\t" ^ str
		 ^ "\n\t [Int] exp_chk: " ^ P.expChkToString cD cG eInt'
		 ^ " : " ^ P.subCompTypToString cD ttau
		 ^ "\n\t [Ext] exp_chk: " ^ PE.expChkToString (Syntax.Ext.LF.Empty) eExt'))

    and annotate_branches caseTyp cD cG branchesInt branchesExt tau_s ttau =
      List.iter2
	(fun branchInt branchExt -> annotate_branch caseTyp cD cG branchInt branchExt tau_s ttau)
	branchesInt branchesExt

    and annotate_branch caseTyp cD (cG, cIH) branchInt branchExt tau_s (tau, t) =
      match (branchInt, branchExt) with
      (* | (EmptyBranch (_, cD1', pat1, t1), SEComp.EmptyBranch (loc, _, pat2)) -> *)
      (* 	 let _tau_p = C.cnormCTyp (tau_s, t1) in *)
      (* 	 (\* LF.checkMSub loc cD1' t1 cD; *\) *)
      (* 	 (\* annotate_pattern cD1' I.Empty pat1 pat2 (tau_p, C.m_id) *\) *)
      (* 	 () *)

      | (EmptyBranch (_, cD1', pat1, t1),
	 SEComp.EmptyBranch (loc, cD,
			     SEComp.PatMetaObj (_,
						(_, SEComp.ClObj (cPsi, SEComp.MObj
									  (SELF.PatEmpty _)))))) ->
	 let tau_p = C.cnormCTyp (tau_s, t1) in
	 (* LF.checkMSub loc cD1' t1 cD *)
	 ()

      | (Branch (_, cD1', _cG, PatMetaObj (l1', mO), t1, eInt'),
	SEComp.Branch (loc, _, SEComp.PatMetaObj (_, _), eExt')) ->
	 let TypBox (_, mT) = tau_s in
	 let _mT1 = C.cnormMetaTyp (mT, t1) in
	 let cG' = C.cnormCtx (C.normCtx cG, t1) in
	 let cIH = C.cnormCtx (C.normCtx cIH, t1) in
	 let t'' = C.mcomp t t1 in
	 let tau' = C.cnormCTyp (tau, t'') in
	 let (cD1', cIH') =
	   if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (l1', mO)) then
	     let cD1' = mvarsInPatt cD1' (PatMetaObj (l1', mO)) in
	     (cD1', Total.wf_rec_calls cD1' (I.Empty))
	   else (cD1', I.Empty) in
	 let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD else cD1' in
	 (* LF.checkMSub loc cD1' t1 cD; *)
	 (* LF.checkMetaObj cD1' mO (mT1, C.m_id); *)
	 annotate_comp_exp_chk
	   cD1' (cG', Context.append cIH cIH') eInt' eExt' (tau', C.m_id)

      | (Branch (_, cD1', cG1, patInt, t1, eInt'),
	SEComp.Branch (loc, _, patExt, eExt')) ->
	 let tau_p = C.cnormCTyp (tau_s, t1) in
	 let cG' = C.cnormCtx (cG, t1) in
	 let cIH = C.cnormCtx (C.normCtx cIH, t1) in
	 let t'' = C.mcomp t t1 in
	 let tau' = C.cnormCTyp (tau, t'') in
	 let k = Context.length cG1 in
	 let cIH0 = Total.shiftIH cIH k in
	 let (cD1', cIH') =
	   if is_inductive caseTyp && Total.struct_smaller patInt then
	     let cD1' = mvarsInPatt cD1' patInt in (cD1', Total.wf_rec_calls cD1' cG1)
	   else (cD1', I.Empty)
	 in
	 let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD else cD1' in
	 (* LF.checkMSub loc cD1' t1 cD; *)
	 annotate_pattern cD1' cG1 patInt patExt (tau_p, C.m_id);
	 annotate_comp_exp_chk
	   cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') eInt' eExt' (tau', C.m_id)
      | _ ->
	 raise (AnnotError "Incompatible branch.")

    and annotate_pattern cD cG patInt patExt ttau = match patInt, patExt with
      | (PatMetaObj (_, mO), SEComp.PatMetaObj (loc, _)) ->
	 begin
	   match ttau with
	   | (TypBox (_, ctyp), theta) ->
	      Annot.add loc (P.subCompTypToString cD ttau);
	      (* LF.checkMetaObj cD mO (ctyp, theta) *)
	   | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
	 end

      | (PatMetaObj (_, mO), SEComp.PatAnn (_, SEComp.PatMetaObj (loc, _), _)) ->
	 begin
	   match ttau with
	   | (TypBox (_, ctyp), theta) ->
	      Annot.add loc (P.subCompTypToString cD ttau);
	   | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
	 end

      | (PatPair (_, patInt1, patInt2), SEComp.PatPair (loc, patExt1, patExt2)) ->
	 begin
	   match ttau with
	   | (TypCross (tau1, tau2), theta) ->
	      annotate_pattern cD cG patInt1 patExt1 (tau1, theta);
	      annotate_pattern cD cG patInt2 patExt2 (tau2, theta)
	   | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau)))
	 end

      | ((PatVar _) as patInt', (SEComp.PatAnn (loc, ((SEComp.PatVar _) as patExt'), _))) ->
	 let (loc', ttau') = synPattern cD cG patInt' patExt' in
	 let tau' = C.cnormCTyp ttau' in
	 let tau = C.cnormCTyp ttau in
	 let ttau' = (tau', C.m_id) in
	 let ttau = (tau, C.m_id) in
	 if C.convCTyp ttau ttau' then
	   ()
	 else
	   raise (Error (loc', PatIllTyped (cD, cG, patInt', ttau, ttau')))

      | patInt', patExt' ->
	 let (loc, ttau') = synPattern cD cG patInt' patExt' in
	 let tau' = C.cnormCTyp ttau' in
	 let tau = C.cnormCTyp ttau in
	 let ttau' = (tau', C.m_id) in
	 let ttau = (tau, C.m_id) in
	 if C.convCTyp ttau ttau' then ()
	 else
	   raise (Error (loc, PatIllTyped (cD, cG, patInt', ttau, ttau')))

    and synPattern cD cG patInt patExt = match (patInt, patExt) with
      | (PatConst (_, cInt, pat_spineInt), SEComp.PatConst (loc, cExt, pat_spineExt)) ->
	 let tau = (CompConst.get cInt).CompConst.typ in
	 Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	 (loc, synPatSpine cD cG pat_spineInt pat_spineExt (tau, C.m_id))
      | (PatVar (_, kInt), SEComp.PatVar (loc, kExt)) ->
	 let tau = lookup' cG kInt in
	 Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	 (loc, (tau, C.m_id))
      | (PatTrue _, SEComp.PatTrue loc) ->
	 Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
	 (loc, (TypBool, C.m_id))
      | (PatFalse _, SEComp.PatFalse loc) ->
	 Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
	 (loc, (TypBool, C.m_id))
      | (PatAnn (_, patInt', tau), SEComp.PatAnn (loc, patExt', _)) ->
	 Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	 annotate_pattern cD cG patInt' patExt' (tau, C.m_id);
	 (loc, (tau, C.m_id))
      | (PatAnn (loc, patInt', tau), patExt') ->
	 annotate_pattern cD cG patInt' patExt' (tau, C.m_id);
	 (loc, (tau, C.m_id))
      | (patInt', patExt') ->
	 raise (AnnotError ("Unable to pair pat:\n\t" ^ render_int_pat patInt'
			    ^ "\n\tand\n\t" ^ render_ext_pat patExt'))

    and render_int_pat pat = match pat with
      | PatEmpty (loc, _) -> "(PatEmpty at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatMetaObj (loc, _) -> "(PatMetaObj at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatConst (loc, _, _) -> "(PatConst at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatFVar   (loc, _) -> "(PatFVar at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatVar   (loc, _) -> "(PatVar at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatPair  (loc, _, _) -> "(PatPair at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatTrue  loc -> "(PatTrue at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatFalse loc -> "(PatFalse at " ^ Syntax.Loc.to_string loc ^ ")"
      | PatAnn   (loc, _, _) -> "(PatAnn at " ^ Syntax.Loc.to_string loc ^ ")"

    and render_ext_pat pat = match pat with
      | SEComp.PatMetaObj (loc, _) -> "(PatMetaObj at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatConst (loc, _, _) -> "(PatConst at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatVar   (loc, _) -> "(PatVar at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatPair  (loc, _, _) -> "(PatPair at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatTrue  loc -> "(PatTrue at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatFalse loc -> "(PatFalse at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatAnn   (loc, _, _) -> "(PatAnn at " ^ Syntax.Loc.to_string loc ^ ")"

    and synPatSpine cD cG pat_spineInt pat_spineExt (tau, theta) =
      match (pat_spineInt, pat_spineExt) with
      | (PatNil, SEComp.PatNil loc) ->
	 Annot.add loc (P.subCompTypToString cD (tau, theta));
	 (tau, theta)

      | (PatApp (_, patInt, pat_spineInt'), SEComp.PatNil loc) ->
	 begin
	   match (tau, theta) with
	   | (TypArr (tau1, tau2), theta) ->
	      Annot.add loc (P.subCompTypToString cD (tau, theta));
	      synPatSpine cD cG pat_spineInt' pat_spineExt (tau2, theta)
	   | (TypPiBox (cdecl, tau'), theta) ->
	      let theta' = checkPatAgainstCDecl cD patInt (cdecl, theta) in
	      Annot.add loc (P.subCompTypToString cD (tau, theta));
	      synPatSpine cD cG pat_spineInt' pat_spineExt (tau', theta')
	 end
      	 (* begin *)
      	 (*   match (tau) with *)
	 (*   | TypBase _ -> raise (AnnotError "TypBase") *)
	 (*   | TypCobase _ -> raise (AnnotError "TypCobase") *)
	 (*   | TypDef _ -> raise (AnnotError "TypDef") *)
	 (*   | TypBox _ -> raise (AnnotError "TypBox") *)
	 (*   | TypArr _ -> raise (AnnotError "TypArr") *)
	 (*   | TypCross _ -> raise (AnnotError "TypCross") *)
	 (*   | TypPiBox _ -> raise (AnnotError "TypPiBox") *)
	 (*   | TypClo _ -> raise (AnnotError "TypClo") *)
	 (*   | TypBool -> raise (AnnotError "TypBool") *)
	 (*   | TypInd _ -> raise (AnnotError "TypInd") *)
      	 (* end *)

      | (PatApp (_, patInt, pat_spineInt'), SEComp.PatApp (loc, patExt, pat_spineExt')) ->
	 begin
	   match (tau, theta) with
	   | (TypArr (tau1, tau2), theta) ->
	      annotate_pattern cD cG patInt patExt (tau1, theta);
	      Annot.add loc (P.subCompTypToString cD (tau, theta));
	      synPatSpine cD cG pat_spineInt' pat_spineExt' (tau2, theta)
	   | (TypPiBox (cdecl, tau'), theta) ->
	      let theta' = checkPatAgainstCDecl cD patInt (cdecl, theta) in
	      Annot.add loc (P.subCompTypToString cD (tau, theta));
	      synPatSpine cD cG pat_spineInt' pat_spineExt' (tau', theta')
	 end
      | (pat_spineInt', pat_spineExt') ->
	 raise (AnnotError ("Unable to pair: Int: "
			    ^ render_int_pat_spine pat_spineInt'
			    ^ " with Ext: "
			    ^ render_ext_pat_spine pat_spineExt'
	 ^ "\n\t [Int] pat_spine: " ^ P.patSpineToString cD cG pat_spineInt'
	 ^ "\n\t [Ext] pat_spine: " ^ PE.patSpineToString (Syntax.Ext.LF.Empty) pat_spineExt'))


    and render_int_pat_spine pat_spine = match pat_spine with
	| PatNil -> "(PatNil)"
	| PatApp _ -> "(PatApp)"

    and render_ext_pat_spine pat_spine = match pat_spine with
      | SEComp.PatNil loc -> "(PatNil at " ^ Syntax.Loc.to_string loc ^ ")"
      | SEComp.PatApp (loc, _, _) -> "(PatApp at " ^ Syntax.Loc.to_string loc ^ ")"

    and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
      (* LF.checkMetaObj cD mO (ctyp, theta); *)
      I.MDot(metaObjToMFront mO, theta)

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

    and annotate_comp_exp_syn cD (cG, cIH) eInt eExt =
      (* printf "[annotate] expSyn : %s\n" (P.expSynToString cD cG eInt); *)
      annotate_comp_exp_syn' cD (cG, cIH) eInt eExt

    and annotate_comp_exp_syn' cD (cG, cIH) eInt eExt = match (eInt, eExt) with
      | (Var (_, x), SEComp.Var (loc, n)) ->
	 let (f, tau') = lookup cG x in
	 let tau =
	   match C.cnormCTyp (tau', C.m_id) with
	   | TypInd tau -> tau
	   | _ -> tau'
	 in
	 Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	 if Total.exists_total_decl f then
	   (Some cIH, tau, C.m_id)
	 else
	   (None, tau, C.m_id)

      | (DataConst (_, c), SEComp.DataConst (loc, _)) ->
	 let tau = (CompConst.get c).CompConst.typ in
	 Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	 (None, (CompConst.get c).CompConst.typ, C.m_id)

      | (Const (_, prog), SEComp.Const (loc, _)) ->
	 let tau = (Comp.get prog).Comp.typ in
	 if !Total.enabled then
	   if (Comp.get prog).Comp.total then
	     begin
	       Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
               (None, tau, C.m_id)
	     end
	   else
	     raise (Error (loc, MissingTotal prog))
	 else
	   begin
	     Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	     (None, tau, C.m_id)
	   end

      | (Const (_, prog), SEComp.Var (loc, _)) ->
	 let tau = (Comp.get prog).Comp.typ in
	 if !Total.enabled then
	   if (Comp.get prog).Comp.total then
	     begin
	       Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
               (None, tau, C.m_id)
	     end
	   else
	     raise (Error (loc, MissingTotal prog))
	 else
	   begin
	     Annot.add loc (P.subCompTypToString cD (tau, C.m_id));
	     (None, tau, C.m_id)
	   end

      | (Apply (_, eInt1, eInt2), SEComp.Apply (loc, eExt1, eExt2)) ->
	 let (cIH_opt, tau1, t1) = annotate_comp_exp_syn cD (cG, cIH) eInt1 eExt1 in
	 let (tau1, t1) = C.cwhnfCTyp (tau1,t1) in
	 begin
	   match (tau1, t1) with
	   | (TypArr (tau2, tau), t) ->
	      Annot.add loc (P.subCompTypToString cD (tau1, t1));
	      annotate_comp_exp_chk cD (cG, cIH) eInt2 eExt2 (tau2, t);
	      (useIH loc cD cG cIH_opt eInt2, tau, t)
	   | (tau, t) ->
	      raise (Error (loc, MismatchSyn (cD, cG, eInt1, VariantArrow, (tau, t))))
	 end

      | (MApp (loc', iInt', mCInt), SEComp.Apply (loc, iExt', (SEComp.Box (_, mCExt)))) ->
	 let (cIH_opt, tau1, t1) = annotate_comp_exp_syn cD (cG, cIH) iInt' iExt' in
	 begin
	   match (C.cwhnfCTyp (tau1, t1)) with
	   | (TypPiBox ((I.Decl (_, ctyp, _)), tau), t) ->
	      (* printf "Comparing int: %s with ext: %s\n" *)
	      (* 	     (P.metaObjToString cD mCInt) *)
	      (* 	     (PE.metaObjToString (Syntax.Ext.LF.Empty) mCExt); *)
	      (* LF.checkMetaObj cD mC (ctyp, t) *)
	      (useIH loc' cD cG cIH_opt (Box (loc', mCInt)), tau, I.MDot (metaObjToMFront mCInt, t))
	   | (tau, t) ->
	      raise (Error (loc', MismatchSyn (cD, cG, iInt', VariantPiBox, (tau, t))))
	 end

      | (MApp (loc, eInt', mC), eExt') ->
	 let (cIH_opt, tau1, t1) = annotate_comp_exp_syn cD (cG, cIH) eInt' eExt' in
	 begin
	   match (C.cwhnfCTyp (tau1, t1)) with
	   | (TypPiBox ((I.Decl (_, _ctyp, _)), tau), t) ->
	      (* LF.checkMetaObj cD mC (ctyp, t) *)
	      Annot.add loc (P.subCompTypToString cD (tau1, t1));
	      (useIH loc cD cG cIH_opt (Box (loc, mC)), tau, I.MDot (metaObjToMFront mC, t))
	   | (tau, t) ->
	      raise (Error (loc, MismatchSyn (cD, cG, eInt', VariantPiBox, (tau, t))))
	 end

      | PairVal (_, iInt1, iInt2), SEComp.PairVal (loc, iExt1, iExt2) ->
         let (_, tau1,t1) =  annotate_comp_exp_syn cD (cG,cIH) iInt1 iExt1 in
         let (_, tau2,t2) =  annotate_comp_exp_syn cD (cG,cIH) iInt2 iExt2 in
         let (tau1,t1)    = C.cwhnfCTyp (tau1, t1) in
         let (tau2,t2)    = C.cwhnfCTyp (tau2, t2) in
	 Annot.add loc (P.subCompTypToString cD (TypCross (TypClo (tau1,t1),
                          TypClo (tau2,t2)), C.m_id));
         (None, TypCross (TypClo (tau1,t1),
                          TypClo (tau2,t2)), C.m_id)

      | (Ann (eInt', tau), SEComp.Ann (loc, eExt', _)) ->
	 annotate_comp_exp_chk cD (cG, cIH) eInt' eExt' (tau, C.m_id);
	 (None, tau, C.m_id)

      (* | Ann (eInt', tau), SEComp.BoxVal (loc, mO) -> *)
      (* 	 annotate_comp_exp_chk cD (cG, cIH) eInt' (SEComp.Box (loc, mO)); *)
      (* 	 (None, tau, C.m_id) *)

      | (Equal (_, iInt1, iInt2), SEComp.Equal (loc, iExt1, iExt2)) ->
	 let (_, tau1, t1) = annotate_comp_exp_syn cD (cG, cIH) iInt1 iExt1 in
	 let (_, tau2, t2) = annotate_comp_exp_syn cD (cG, cIH) iInt2 iExt2 in
	 if C.convCTyp (tau1, t1) (tau2, t2) then
	   begin match C.cwhnfCTyp (tau1, t1) with
		 | (TypBox _, _) ->
		    Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
		    (None, TypBool, C.m_id)
		 | (TypBool, _) ->
		    Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
		    (None, TypBool, C.m_id)
		 | (tau1, t1) -> raise (Error (loc, EqTyp (cD, (tau1, t1))))
	   end
	 else
	   raise (Error (loc, EqMismatch (cD, (tau1, t1), (tau2, t2))))

      | (Boolean _, SEComp.Boolean (loc, _))  ->
	 Annot.add loc (P.subCompTypToString cD (TypBool, C.m_id));
	 (None, TypBool, C.m_id)

      | eInt', eExt' ->
	 let (_, str) = render_ext_exp_syn eExt' in
	 raise (AnnotError
		  ("Unable to pair syn:\n\t" ^ render_int_exp_syn eInt'
		   ^ "\n\t\tand\n\t" ^ str
		 ^ "\n\t [Int] exp_syn: " ^ P.expSynToString cD cG eInt'
		 ^ "\n\t [Ext] exp_syn: " ^ PE.expSynToString (Syntax.Ext.LF.Empty) eExt'))

  and render_ext_exp_chk e = match e with
    | SEComp.Syn (loc, _) -> (loc, "(Syn at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Fun (loc, x, _) ->
       (loc, "(Fun " ^ Id.render_name x ^ " at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Cofun (loc, _) -> (loc, "(Cofun at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.MLam (loc, u, _) ->
       (loc, "(MLam " ^ Id.render_name u ^ " at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Pair (loc, _, _) -> (loc, "(Pair at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.LetPair (loc, _, _) -> (loc, "(LetPair at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Let (loc, _, _) -> (loc, "(Let at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Box (loc, _) -> (loc, "(Box at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Case (loc, _, _, _) -> (loc, "(Case at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.If (loc, _, _, _) -> (loc, "(If at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Hole loc -> (loc, "(Hole at " ^ Syntax.Loc.to_string loc ^ ")")

  and render_ext_exp_syn e = match e with
    | SEComp.Var (loc, n) ->
       (loc, "(Var " ^ Id.render_name n ^ " at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.DataConst (loc, n) ->
       (loc, "(DataConst " ^ Id.render_name n ^ " at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Const (loc, n) ->
       (loc, "(Const " ^ Id.render_name n ^ " at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Apply (loc, _, _) -> (loc, "(Apply at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.BoxVal (loc, _) -> (loc, "(BoxVal at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.PairVal (loc, _, _) -> (loc, "(PairVal at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Ann (loc, _, _) -> (loc, "(Ann at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Equal (loc, _, _) -> (loc, "(Equal at " ^ Syntax.Loc.to_string loc ^ ")")
    | SEComp.Boolean (loc, _) -> (loc, "(Boolean at " ^ Syntax.Loc.to_string loc ^ ")")

  and render_int_exp_chk e = match e with
    | Syn (loc, _) -> "(Syn at " ^ Syntax.Loc.to_string loc ^ ")"
    | Rec (loc, x, _) ->
       "(Rec " ^ Id.render_name x ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | Fun (loc, x, _) ->
       "(Fun " ^ Id.render_name x ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | Cofun (loc, _) -> "(Cofun at " ^ Syntax.Loc.to_string loc ^ ")"
    | MLam (loc, u, _) ->
       "(MLam " ^ Id.render_name u ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | Pair (loc, _, _) -> "(Pair at " ^ Syntax.Loc.to_string loc ^ ")"
    | LetPair (loc, _, _) -> "(LetPair at " ^ Syntax.Loc.to_string loc ^ ")"
    | Let (loc, _, _) -> "(Let at " ^ Syntax.Loc.to_string loc ^ ")"
    | Box (loc, _) -> "(Box at " ^ Syntax.Loc.to_string loc ^ ")"
    | Case (loc, _, _, _) -> "(Case at " ^ Syntax.Loc.to_string loc ^ ")"
    | If (loc, _, _, _) -> "(If at " ^ Syntax.Loc.to_string loc ^ ")"
    | Hole (loc, _) -> "(Hole at " ^ Syntax.Loc.to_string loc ^ ")"

  and render_int_exp_syn e = match e with
    | Var (loc, _) -> "(Var at " ^ Syntax.Loc.to_string loc ^ ")"
    | DataConst (loc, _) -> "(DataConst at " ^ Syntax.Loc.to_string loc ^ ")"
    | DataDest (loc, _) -> "(DataDest at " ^ Syntax.Loc.to_string loc ^ ")"
    | Const (loc, _) -> "(Const at " ^ Syntax.Loc.to_string loc ^ ")"
    | Apply (loc, _, _) -> "(Apply at " ^ Syntax.Loc.to_string loc ^ ")"
    | MApp (loc, _, _) -> "(MApp at " ^ Syntax.Loc.to_string loc ^ ")"
    | PairVal (loc, _, _) -> "(PairVal at " ^ Syntax.Loc.to_string loc ^ ")"
    | Ann (_, _) -> "(Ann at unknown location)"
    | Equal (loc, _, _) -> "(Equal at " ^ Syntax.Loc.to_string loc ^ ")"
    | Boolean _ -> "(Boolean at unknown location)"

end

module Sgn = struct
  open Syntax.Int

  let annotate_sgn_typ loc tK =
    let tK_str = P.kindToString LF.Null (tK, LF.EmptySub) in
    Annot.add loc tK_str

  let annotate_sgn_const loc tA =
    let tA_str = P.typToString LF.Empty LF.Null (tA, LF.EmptySub) in
    Annot.add loc tA_str

end

let clear_all () : unit = Annot.clear()

let print_annot (name : string) : unit =
  let pp = open_out ((fun n -> String.sub n 0 (String.rindex n '.')) name ^ ".annot") in
  Annot.print_annot pp name

let type_of_position (line : int) (col : int) : Syntax.Loc.t option * string =
  let sorted =
    let cmp l1 l2 = (Loc.start_off l1) - (Loc.start_off l2) in
    let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) Annot.store [] in
      List.sort (fun (key1,_) (key2,_) -> cmp key1 key2) l in
  let contains_pos (l, x) : bool = begin
    let start_c = ((Loc.start_off l) - (Loc.start_bol l)) in
    let end_c = ((Loc.stop_off l) - (Loc.stop_bol l)) in
    let start_l = Loc.start_line l in
    let end_l = Loc.stop_line l in
    if (start_l = line) && (end_l = line) then
      (start_c <= col) && (col <= end_c)
    else if (start_l = line) && (line < end_l) then
      start_c <= col
    else if (start_l < line) && (line < end_l) then true
    else if (start_l < line) && (line = end_l) then
      col <= end_c
    else false
    end
  in
  match List.fold_left (fun acc x -> if contains_pos x then (Some x) else acc) None sorted with
  | Some (loc, s) -> (Some loc, (s.Annot.typ ^ ";\n"))
  | None -> (None, "No type information found for point: (" ^ (string_of_int line) ^ ", " ^ (string_of_int col)^ ");\n")
