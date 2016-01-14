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

    (* Implicit MLam, does not have a node in the external syntax tree *)
    | (MLam (_, u, eInt'), eExt', (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, LF.MShift 1), C.cnormCtx (cIH, LF.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t)

    | (MLam (_, u, eInt'), SEComp.MLam (loc, _, eExt'), (TypPiBox (cdec, tau), t)) ->
       annotate_comp_exp_chk
	 (extend_mctx cD (u, cdec, t))
	 (C.cnormCtx (cG, LF.MShift 1), C.cnormCtx (cIH, LF.MShift 1))
	 eInt' eExt' (tau, C.mvar_dot1 t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (Pair (_, eInt1, eInt2), SEComp.Pair (loc, eExt1, eExt2), (TypCross (tau1, tau2), t)) ->
       annotate_comp_exp_chk cD (cG, cIH) eInt1 eExt1 tau1;
       annotate_comp_exp_chk cD (cG, cIH) eInt2 eExt2 tau2;
       Annot.add loc (P.subCompTypToString cD ttau)

    | (Let (_, i, (x, eInt')), SEComp.Let (loc, _, (_, eExt')), (tau, t)) ->
       let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
       annotate_comp_exp_chk cD (cG', Total.shift cIH) eInt' eExt' (tau, t);
       Annot.add loc (P.subCompTypToString cD ttau)

    | (LetPair (_, i, (x, y, eInt')), SEComp.LetPair (loc, _, (_, _, eExt')), (tau, t)) ->
       let (_, tau', t') = annotate_comp_exp_syn cD (cG, cIH) i in
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
