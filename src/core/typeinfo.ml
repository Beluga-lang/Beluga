module Loc = Syntax.Int.Loc
module P = Pretty.Int.DefaultPrinter
open Lexing

let generate_annotations = ref false;



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
  open Syntax.Int

end

module Comp = struct
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  module SELF = Syntax.Ext.LF
  module SEComp = Syntax.Ext.Comp

  let annotate_comp_exp_chk cD (cG, cIH) eInt eExt ttau = match (eInt, eExt, ttau) with
    | (Rec (_, f, eInt'), eExt', (tau, t)) ->
       annotate_comp_exp_chk
	 cD (I.Dec (cG, CTypDecl (f, TypClo (tau, t))), (Total.shift cIH)) eExt' eInt' ttau

    | (Fun (_, x, eInt'), SEComp.Fun (loc, _, eExt'), (TypArr (tau1, tau2), t)) ->
       annotate_comp_exp_chk
	 cD (I.Dec (cG, CTypDecl (x, TypClo (tau1, t))), (Total.shift cIH)) eExt' eInt' (tau2, t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (Cofun (_, bs1), SEComp.Cofun (loc, bs2), (TypCobase (l, cid, sp), t)) ->
       let f = fun (CopatApp (_, dest1, csp1), eInt') (SEComp.CopatApp (loc', _, _), eExt') ->
	 (let ttau' = synObs cD csp1 ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau in
	 annotate_comp_exp_chk cD (cG, cIH) eInt' eExt' ttau';
	 Annot.add loc' (P.subCompTypToString cD ttau'))
       in
       List.iter2 f bs1 bs2;
       Annot.add loc (P.subCompTypToString cD ttau)

    |

module Comp = struct
  open Syntax.Int
  module SynE = Syntax.Ext

  (* e : Syntax.Int.Comp.exp_chk, e' : Syntax.Ext.Comp.exp_chk *)
  (* Syntax.Int is open *)
  let annotate_comp_exp_chk cD (cG, cIH) e1 e2 ttau = match (e1, e2, ttau) with
    | (Comp.Rec (_, f, e1'), e2', (tau, t)) ->
       annotate_comp_exp_chk
	 cD (LF.Dec (cG, Comp.CTypDecl (f, Comp.TypClo (tau, t))), (Total.shift cIH))
	 e1' e2' ttau

    | (Comp.Fun (_, x, e1'), SynE.Comp.Fun (loc, _, e2'), (TypArr (tau1, tau2), t)) ->
       annotate_comp_exp_chk
	 cD (LF.Dec (cG, Comp.CTypDecl (x, Comp.TypClo (tau1, t))), (Total.shift cIH))
	 e1' e2' (tau2, t);
       Annot.add loc (mk_entry (P.subCompTypToString cD ttau))

    | (Comp.Cofun (_, bs1), SynE.Comp.Cofun (loc, bs2), (Comp.TypCobase (_, cid, sp), t)) ->
       let f = fun (Comp.CopatApp (_, dest1, csp1, e1')
		   , SynE.Comp.CopatApp (_, dest2, csp1, e2')) ->
	 let ttau' = synObs cD csp1 ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
	 in annotate_comp_exp_chk cD (cG, cIH) e1' e2' ttau'
       in
       List.iter f bs;
       Annot.add loc (mk_entry (P.subCompTypToString cD ttau))

    | (Comp.MLam (_, u1, e1'), e2', (Comp.TypPiBox(LF.Decl (_,cU,Int.LF.Maybe) as cdec,tau),t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u1, cdec, t))
	 (C.cnormCtx (cG, LF.MShift 1), C.cnormCtx (cIH, LF.MShift 1))
	 e1' e2' (tau, C.mvar_dot1 t)

    | (Comp.MLam (_, u1, e1'), SynE.Comp.MLam (loc, u2, e2'), (Comp.TypPiBox(cdec,tau),t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u1, cdec, t))
	 (C.cnormCtx (cG, LF.MShift 1), C.cnormCtx (cIH, LF.MShift 1))
	 e1' e2' (tau, C.mvar_dot1 t);
       Annot.add loc (mk_entry (P.subCompTypToString cD ttau))

    | (Comp.Pair(_,e1a,e1b), SynE.Comp.Pair(loc,e2a,e2b), (Comp.TypCross (tau1, tau2), t)) ->
       annotate_comp_exp_chk cD (cG, cIH) e1a e2a (tau1, t);
       annotate_comp_exp_chk cD (cG, cIH) e1b e2b (tau2, t);
       Annot.add loc (mk_entry (P.subCompTypToString cD ttau))

    | (Comp.Let (_, i1, (x1, e1')), SynE.Comp.Let (loc, i2, (x2, e2')), (tau, t)) ->
       let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) i1 in
       let (tau', t') = C.whnfCTyp (tau', t') in
       let cG' = LF.Dec (cG, Comp.CTypDecl (x1, Comp.TypClo (tau', t'))) in
       annotate_comp_exp_chk cD (cG', Total.shift cIH) e1' e2' (tau, t);
       Annot.add loc (mk_entry (P.subCompTypToString cD ttau))

    | (Comp.LetPair (_,i1,(x1,y1,e1')), SynE.Comp.LetPair (loc,i2,(x2,y2,e2')), (tau, t)) ->
       let (_, tau', t') = syn cD (cG, cIH) i1 in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (Comp.TypCross (tau1, tau2), t') ->
	    let cG' = LF.Dec (LF.Dec (cG, Comp.CTypDecl (x1, Comp.TypClo (tau1, t'))),
			      Comp.CTypDecl (y1, Comp.TypClo (tau2, t')))
	    in
	    annotate_comp_exp_chk cD (cG', (Total.shift (Total.shift cIH))) e1' e2' (tau, t);
	    Annot.add loc (mk_entry (P.subCompTypToString cD ttau))
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type.")
       end

    | (Comp.Box (_, cM1), SynE.Comp.Box (loc, cM2), (Comp.TypBox (l, mT), t)) ->
       begin
	 try
	   (* LF.annotateMetaObj cD cM1 (mT, t); *)
	   Annot.add loc (mk_entry (P.subCompTypToString cD ttau))
	 with Whnf.FreeMVar (LF.FMVar (u, _)) ->
	   raise (Error.Violation ("Free meta-variable " ^ (Id.render_name u)))
       end

    | (Comp.Case (_, prag1,
		  Comp.Ann (Comp.Box (_, (l1,cM1)), (Comp.TypBox (_, mT1) as tau0_sc)), branches1),
       SynE.Comp.Case (loc, prag2, SynE.Comp.Ann (SynE.Comp.Box (_, (l2, cM2)),
			    (Syntax.Ext.Comp.TypBox (_, mT2) as tau0_sc)), branches2),
       (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
	 begin
	   match cM1 with
	   | Comp.ClObj (_, Comp.MObj (Comp.Root (_, Comp.PVar (x,s), _)))
	   | Comp.ClObj (_, Comp.PObj (Comp.PVar (x,s))) ->
	      let order =
		if !Total.enabled && is_ind_MObj cD x then
		  Ind

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

end

module Sgn = struct
  open Syntax.Int
  let annotate_sgn_typ loc tK =
    let tK_str = P.kindToString LF.Null (tK, LF.EmptySub) in
    Annot.add loc (mk_entry tK_str)

  let annotate_sgn_const loc tA =
    let tA_str = P.typToString LF.Empty LF.Null (tA, LF.EmptySub) in
    Annot.add loc (mk_entry tA_str)

end

let clear_all () : unit =
    LF.clear (); Comp.clear (); Annot.clear()

let print_annot (name : string) : unit =
  let pp = open_out ((fun n -> String.sub n 0 (String.rindex n '.')) name ^ ".annot") in
  Annot.print_annot pp name

let type_of_position (line : int) (col : int) : string =
  let sorted =
    let cmp l1 l2 = (Loc.start_off l1) - (Loc.start_off l2) in
    let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) Annot.store [] in
      List.sort (fun (key1,_) (key2,_) -> cmp key1 key2) l in
  (* let f (l, _) = print_string ((string_of_int (Loc.start_off l)) ^ ", " ^ (string_of_int (Loc.stop_off l)) ^ "\n") in
  let _ = List.iter f sorted in *)
  let contains_pos (l, x) : bool = begin
    let start_c = ((Loc.start_off l) - (Loc.start_bol l)) in
    let end_c = ((Loc.stop_off l) - (Loc.stop_bol l)) in
    let start_l = Loc.start_line l in
    let end_l = Loc.stop_line l in
    (* let _ = Format.printf "(%d, %d), (%d, %d), %s\n" (Loc.start_line l) start_c (Loc.stop_line l) end_c x.Annot.typ in *)
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
  | Some (_, s) -> (s.Annot.typ ^ ";\n")
  | None -> ("No type information found for point: (" ^ (string_of_int line) ^ ", " ^ (string_of_int col)^ ");\n")
