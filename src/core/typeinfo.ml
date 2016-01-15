module Loc = Syntax.Int.Loc
module P = Pretty.Int.DefaultPrinter
open Lexing

let generate_annotations = ref false;

exception AnnotError of string

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

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT

  type caseType =
    | IndexObj of meta_obj
    | DataObj
    | IndDataObj
    | IndIndexObj of meta_obj

  let is_indMObj cD x = match Whnf.mctxLookupDep cD x with
    | (_, _ , I.Inductive) -> true
    | (_, _ , _) -> false

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let extend_mctx cD (x, cdecl, t) = match cdecl with
    | I.Decl (_u, cU, dep) ->
       I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t), dep))

  let rec annotate_comp_exp_chk cD (cG, cIH) eInt eExt ttau = match (eInt, eExt, ttau) with
    | (Rec (_, f, eInt'), eExt', (tau, t)) ->
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
    | (MLam (_, u, eInt'), eExt', (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t)

    | (MLam (_, u, eInt'), SEComp.MLam (loc, _, eExt'), (TypPiBox (cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t);
       Annot.add loc (P.subCompTypToString cD ttau)

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

    | (Case (_, prag, Ann (Box (_, (l, cM)), (TypBox (l', mT) as _tau0_sc)), branchesInt),
       SEComp.Case (loc, _, SEComp.Ann (_, SEComp.Box (_, _), (SEComp.TypBox _)), branchesExt),
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
       (* annotate_branches total_pragma cD (cG, cIH) branchesInt branchesExt tau0_sc (tau, t); *)
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
	      (* annotate_branches total_pragma cD (cG, cIH)
                 branchesInt branchesExt tau_s (tau,t); *)
	      Annot.add loc (P.subCompTypToString cD ttau);
	      Coverage.process problem None
	   | (tau', t') ->
	      let _tau_s = C.cnormCTyp (tau', t') in
	      let problem = Coverage.make loc prag cD branchesInt (Whnf.cnormCTyp (tau', t')) in
	      (* annotate_branches total_pragma cD (cG, cIH)
	         branchesInt branchesExt tau_s (tau,t); *)
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
       raise (AnnotError
		("Unable to pair chk:\n\t" ^ render_int_exp_chk eInt'
		 ^ "\n\t\tand\n\t" ^ render_ext_exp_chk eExt'))

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

  and annotate_comp_exp_syn cD (cG, cIH) eInt eExt = match (eInt, eExt) with
    | (Var (_, x), SEComp.Var (loc, _)) ->
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
    | eInt', eExt' ->
       raise (AnnotError
		("Unable to pair syn:\n\t" ^ render_int_exp_syn eInt'
		 ^ "\n\t\tand\n\t" ^ render_ext_exp_syn eExt'))

  and render_ext_exp_chk e = match e with
    | SEComp.Syn (loc, _) -> "(Syn at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Fun (loc, x, _) ->
       "(Fun " ^ Id.render_name x ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Cofun (loc, _) -> "(Cofun at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.MLam (loc, u, _) ->
       "(MLam " ^ Id.render_name u ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Pair (loc, _, _) -> "(Pair at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.LetPair (loc, _, _) -> "(LetPair at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Let (loc, _, _) -> "(Let at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Box (loc, _) -> "(Box at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Case (loc, _, _, _) -> "(Case at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.If (loc, _, _, _) -> "(If at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Hole loc -> "(Hole at " ^ Syntax.Loc.to_string loc ^ ")"

  and render_ext_exp_syn e = match e with
    | SEComp.Var (loc, n) -> "(Var " ^ Id.render_name n ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.DataConst (loc, n) ->
       "(DataConst " ^ Id.render_name n ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Const (loc, n) ->
       "(Const " ^ Id.render_name n ^ " at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Apply (loc, _, _) -> "(Apply at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.BoxVal (loc, _) -> "(BoxVal at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.PairVal (loc, _, _) -> "(PairVal at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Ann (loc, _, _) -> "(Ann at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Equal (loc, _, _) -> "(Equal at " ^ Syntax.Loc.to_string loc ^ ")"
    | SEComp.Boolean (loc, _) -> "(Boolean at " ^ Syntax.Loc.to_string loc ^ ")"

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
