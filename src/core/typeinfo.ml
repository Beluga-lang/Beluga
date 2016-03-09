module Loc = Syntax.Int.Loc
module P = Pretty.Int.DefaultPrinter
module PE = Pretty.Ext.DefaultPrinter
open Lexing
open Printf

(* exception AnnotError of string *)

let generate_annotations = ref true;

module Annot = struct
  open Syntax.Int
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

  module Ann = Annotated
  module Ext = Syntax.Ext

  (* let _ = Error.register_printer *)
  (*	    (fun (AnnotError s) -> Error.print (fun ppf -> Format.fprintf ppf "[AnnotError] %s" s)) *)

  let add_entry loc str =
    match str with
    | None -> Annot.add loc ("No type information found.")
    | Some str' ->
       (* print_string ("Trying to add " ^ str' ^ " to loc: " ^ Syntax.Loc.to_string loc ^ "\n"); *)
       Annot.add loc str'

  let rec annotate_meta_obj ext_mO ann_mO =
    match ext_mO, ann_mO with
    | (Ext.Comp.CObj _, Ann.LF.CObj _) -> ()
    | (Ext.Comp.ClObj (_, ext_clobj), Ann.LF.ClObj (_, ann_clobj)) ->
       annotate_clobj ext_clobj ann_clobj

  and annotate_clobj ext_clobj ann_clobj =
    match ext_clobj, ann_clobj with
    | (Ext.Comp.MObj ext_tM, Ann.LF.MObj ann_tM) ->
       annotate ext_tM ann_tM
    | (Ext.Comp.MObj ext_tM, _) -> ()
    | (Ext.Comp.SObj _, Ann.LF.SObj _) -> ()

  and annotate ext_tM ann_tM =
    let ann_tM_str =
      match ann_tM with
      | Ann.LF.Lam (_, _, _, nstr, _, _) -> nstr
      | Ann.LF.Root (_, _, _, nstr, _, _) -> nstr
      | Ann.LF.Tuple (_, _, nstr, _, _) -> nstr
      | Ann.LF.LFHole (_, nstr, _, _) -> nstr
    in
    let ann_tM_str =
      match ann_tM_str with
      | None -> ""
      | Some str -> str
    in
    let ext_tM_str = PE.normalToString (Ext.LF.Empty) (Ext.LF.Null) ext_tM
    in
    let loc =
      match ext_tM with
      | Ext.LF.Lam (loc, _, _) -> loc
      | Ext.LF.Root (loc, _, _) -> loc
      | Ext.LF.Tuple (loc, _) -> loc
      | Ext.LF.LFHole loc -> loc
      | Ext.LF.Ann (loc, _, _) -> loc
      | Ext.LF.TList (loc, _) -> loc
    in
    let loc = Syntax.Loc.to_string loc in
    print_string (sprintf "Matching:\n\t[ext] %s\n\t[ann] %s\nat loc: %s\n"
    			  ext_tM_str ann_tM_str loc);
    annotate' ext_tM ann_tM

  and annotate' ext_tM ann_tM =
    match ext_tM, ann_tM with
    | Ext.LF.Lam (loc, n, ext_tM'), Ann.LF.Lam (_, _, ann_tM',_ , _, tstr) ->
       add_entry loc tstr;
       annotate ext_tM' ann_tM'
    | Ext.LF.Root (loc, h, tS), Ann.LF.Lam (_, _, ann_tM', _, _, tstr) ->
       annotate ext_tM ann_tM'
    | Ext.LF.Root _, Ann.LF.Root _ ->
       print_string ("Going to syn.\n");
       syn ext_tM ann_tM
    | Ext.LF.Tuple (loc, ext_tuple), Ann.LF.Tuple (_, ann_tuple, _, _, tstr) ->
       add_entry loc tstr;
       annotate_tuple ext_tuple ann_tuple
    | Ext.LF.LFHole loc, Ann.LF.LFHole (_, _, _, tstr) ->
       add_entry loc tstr
    | Ext.LF.Ann (loc, ext_tM', _), ann_tM' ->
       annotate ext_tM' ann_tM'
    | Ext.LF.TList (loc, tMs), ann_tM' ->
       (* In practice, ann_tM' should always be Root *)
       let ext_tM' = Index.shunting_yard tMs in
       annotate ext_tM' ann_tM'
  (* Never happens? *)
    (* | Ext.LF.NTyp (loc, _) -> *)
    (* | Ext.LF.PatEmpty loc -> () *)

  and annotate_tuple ext_tuple ann_tuple =
    match ext_tuple, ann_tuple with
    | Ext.LF.Last ext_tM, Ann.LF.Last ann_tM ->
       annotate ext_tM ann_tM
    | Ext.LF.Cons (ext_tM, ext_tuple), Ann.LF.Cons (ann_tM, ann_tuple) ->
       annotate ext_tM ann_tM;
       annotate_tuple ext_tuple ann_tuple

  and syn (Ext.LF.Root (loc, ext_h, ext_tS)) (Ann.LF.Root (_, ann_h, ann_tS, nstr, _, tstr)) =
    let Some str = nstr in
    print_string ("Here, we have: " ^ str ^ "\n");
    let rec syn ext_tS ann_tS =
      match ext_tS, ann_tS with
      | Ext.LF.Nil, Ann.LF.Nil -> ()
      | Ext.LF.App (_, ext_tM, ext_tS'), Ann.LF.App (ann_tM, ann_tS', str) ->
	 print_string (sprintf "Matching:\n\t[ext spine] %s\n\t[ann spine] %s\n"
	 		 (PE.spineToString (Ext.LF.Empty) (Ext.LF.Null) ext_tS)
	 		 str
	 	      );
	 annotate ext_tM ann_tM;
	 syn ext_tS' ann_tS'
      (* | _, _ -> ()    (\* TODO: See why spines don't always line up *\) *)
    in
    add_entry loc tstr;
    print_string "We're in syn (ext)!\n";
    syn ext_tS ann_tS;
    print_string "Done with syn\n";

end

module Comp = struct
  module Ann = Annotated
  module Ext = Syntax.Ext

  let add_entry loc str =
    match str with
    | None -> Annot.add loc ("No type information found.")
    | Some str' ->
       (* print_string ("Trying to add " ^ str' ^ " to loc: " ^ Syntax.Loc.to_string loc ^ "\n"); *)
       Annot.add loc str'

  let rec annotate_comp_exp_chk ext_e ann_e =
    ann_chk ext_e ann_e

  and ann_chk ext_e ann_e =
    print_string (sprintf "[annotate exp_chk] %s\n"
		 (PE.expChkToString (Ext.LF.Empty) ext_e));
    ann_chk' ext_e ann_e

  and ann_chk' ext_e ann_e =
    match (ext_e, ann_e) with
    | (Ext.Comp.Fun (loc, _, ext_e'), Ann.Comp.Fun (_, _, ann_e', _, tstr)) ->
       ann_chk ext_e' ann_e';
       add_entry loc tstr

    (* TODO Look into this, we shouldn't have any implicit MLams *)
    | (((Ext.Comp.Fun _) as ext_e'), Ann.Comp.MLam (_, _, ann_e', _, tstr)) ->
       ann_chk ext_e' ann_e'

    | (Ext.Comp.MLam (loc, _, ext_e'), Ann.Comp.MLam (_, _, ann_e', _, tstr)) ->
       ann_chk ext_e' ann_e';
       add_entry loc tstr

    | (Ext.Comp.Cofun (loc, ext_bs), Ann.Comp.Cofun (_, ann_bs, _, tstr)) ->
       (* TODO Check out cofuns *)
       (* let f = (fun (ext_csp, ext_e') *)
       (*		    (int_csp, ann_e') -> ann_chk ext_e' ann_e') *)
       (* in *)
       (* List.iter2 f ext_bs ann_bs; *)
       add_entry loc tstr

    | (Ext.Comp.Pair (loc, ext_e1, ext_e2), Ann.Comp.Pair (_, ann_e1, ann_e2, _, tstr)) ->
       ann_chk ext_e1 ann_e1;
       ann_chk ext_e2 ann_e2;
       add_entry loc tstr

    | (Ext.Comp.Let (loc, ext_i, (_, ext_e')), Ann.Comp.Let (_, ann_i, (_, ann_e'), _, tstr)) ->
       ann_syn ext_i ann_i;
       ann_chk ext_e' ann_e';
       add_entry loc tstr

    | (Ext.Comp.LetPair (loc, ext_i, (_,_, ext_e')),
       Ann.Comp.LetPair (_, ann_i, (_,_, ann_e'), _, tstr)) ->
       ann_syn ext_i ann_i;
       ann_chk ext_e' ann_e';
       add_entry loc tstr

    | (Ext.Comp.Box (loc, (_, ext_mO)), Ann.Comp.Box (_, (_, ann_mO), _, tstr)) ->
       LF.annotate_meta_obj ext_mO ann_mO;
       add_entry loc tstr

    | (Ext.Comp.Case (loc, _, ext_i, ext_branches),
       Ann.Comp.Case (_, _, ann_i, ann_branches, _, tstr)) ->
       ann_syn ext_i ann_i;
       annotate_branches ext_branches ann_branches;
       add_entry loc tstr

    | (Ext.Comp.Syn (loc, ext_i), Ann.Comp.Syn (_, ann_i, _, tstr)) ->
       ann_syn ext_i ann_i;
       add_entry loc tstr

    | (Ext.Comp.If (loc, ext_i, ext_e1, ext_e2),
       Ann.Comp.If (_, ann_i, ann_e1, ann_e2, _, tstr)) ->
       ann_syn ext_i ann_i;
       ann_chk ext_e1 ann_e1;
       ann_chk ext_e2 ann_e2;
       add_entry loc tstr

    | (Ext.Comp.Hole loc, Ann.Comp.Hole (_, _, _, tstr)) ->
       add_entry loc tstr

  and ann_syn ext_i ann_i =
    print_string (sprintf "[annotate exp_syn] %s\n"
		 (PE.expSynToString (Ext.LF.Empty) ext_i));
    ann_syn' ext_i ann_i
  and ann_syn' ext_i ann_i =
    match (ext_i, ann_i) with
    | (Ext.Comp.Var (loc, _), Ann.Comp.Var (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.Var (loc, _), Ann.Comp.Const (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.Var (loc, _), Ann.Comp.DataConst (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.Var (loc, _), Ann.Comp.DataDest (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.DataConst (loc, _), Ann.Comp.DataConst (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.DataConst (loc, _), Ann.Comp.DataDest (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.Apply (loc, ext_i, ext_e), Ann.Comp.Apply (_, ann_i, ann_e, _, tstr)) ->
       add_entry loc tstr;
       ann_syn ext_i ann_i;
       ann_chk ext_e ann_e

    | (Ext.Comp.Apply (loc, ext_i, Ext.Comp.Box (_, (_, ext_mC))),
       Ann.Comp.MApp (_, ann_i, (_, ann_mC), _, tstr)) ->
       add_entry loc tstr;
       ann_syn ext_i ann_i;
       LF.annotate_meta_obj ext_mC ann_mC;

    | (Ext.Comp.PairVal (loc, ext_i1, ext_i2), Ann.Comp.PairVal (_, ann_i1, ann_i2, _, tstr)) ->
       ann_syn ext_i1 ann_i1;
       ann_syn ext_i2 ann_i2;
       add_entry loc tstr

    | (Ext.Comp.BoxVal (loc, ext_mO), Ann.Comp.Ann (ann_e, _, _, tstr)) ->
       ann_chk (Ext.Comp.Box (loc, ext_mO)) ann_e

    | (Ext.Comp.Ann (loc, ext_e, _), Ann.Comp.Ann (ann_e, _, _, tstr)) ->
       ann_chk ext_e ann_e;
       add_entry loc tstr

    | (Ext.Comp.Equal (loc, ext_i1, ext_i2), Ann.Comp.Equal (_, ann_i1, ann_i2, _, tstr)) ->
       ann_syn ext_i1 ann_i1;
       ann_syn ext_i2 ann_i2;
       add_entry loc tstr

    | (Ext.Comp.Boolean _, Ann.Comp.Boolean _) -> ()

  and annotate_branches ext_branches ann_branches =
    List.iter2 (fun ext_branch ann_branch -> annotate_branch ext_branch ann_branch)
	       ext_branches ann_branches

  and annotate_branch ext_branch ann_branch =
    match (ext_branch, ann_branch) with
    | (Ext.Comp.EmptyBranch (_, _,
			     Ext.Comp.PatMetaObj (
				 loc',
				 (_l, Ext.Comp.ClObj (cPsi, Ext.Comp.MObj (Ext.LF.PatEmpty _))))
			    ),
       Ann.Comp.EmptyBranch (_, _, Ann.Comp.PatEmpty (_, _, _, tstr), _)) ->
       add_entry loc' tstr

    | (Ext.Comp.EmptyBranch (_, _, ext_pat), Ann.Comp.EmptyBranch (_, _, ann_pat, _)) ->
       annotate_pattern ext_pat ann_pat

    | (Ext.Comp.Branch (_, _, ext_pat, ext_e), Ann.Comp.Branch (_, _, _, ann_pat, _, ann_e)) ->
       annotate_pattern ext_pat ann_pat;
       ann_chk ext_e ann_e

  and annotate_pattern ext_pat ann_pat =
    print_string (sprintf "[annotate pattern] %s\n"
		 (PE.patternToString (Ext.LF.Empty) ext_pat));
    annotate_pattern' ext_pat ann_pat
  and annotate_pattern' ext_pat ann_pat =
    match (ext_pat, ann_pat) with
    | (Ext.Comp.PatMetaObj (loc, (l, ext_mO)), Ann.Comp.PatMetaObj (_, (_, ann_mO), _, tstr)) ->
       (* print_string ("[annotate_pattern] PatMetaObj: " ^ PE.metaObjToString (Ext.LF.Empty) (l, ext_mO) ^ "\n"); *)
       LF.annotate_meta_obj ext_mO ann_mO;
       add_entry loc tstr

    | (Ext.Comp.PatConst (loc, _, ext_pat_spine),
       Ann.Comp.PatConst (_, _, ann_pat_spine, _, tstr)) ->
       annotate_pat_spine ext_pat_spine ann_pat_spine;
       add_entry loc tstr

    | (Ext.Comp.PatPair (loc, ext_pat1, ext_pat2),
      Ann.Comp.PatPair (_, ann_pat1, ann_pat2, _, tstr)) ->
       annotate_pattern ext_pat1 ann_pat1;
       annotate_pattern ext_pat2 ann_pat2;
       add_entry loc tstr

    | (Ext.Comp.PatVar (loc, _), Ann.Comp.PatVar (_, _, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.PatTrue loc, Ann.Comp.PatTrue (_, _, tstr)) ->
       add_entry loc tstr

    | (Ext.Comp.PatFalse loc, Ann.Comp.PatFalse (_, _, tstr)) ->
       add_entry loc tstr

    | (((Ext.Comp.PatMetaObj _) as ext_pat), Ann.Comp.PatAnn (_, ann_pat, _, _, tstr)) ->
       annotate_pattern ext_pat ann_pat

    | (Ext.Comp.PatAnn (loc, ext_pat, _), Ann.Comp.PatAnn (_, ann_pat, _, _, tstr)) ->
       annotate_pattern ext_pat ann_pat;
       add_entry loc tstr

    | (Ext.Comp.PatAnn (loc, ext_pat, _), ann_pat) ->
       annotate_pattern ext_pat ann_pat

  and annotate_pat_spine ext_pat_spine ann_pat_spine =
    match (ext_pat_spine, ann_pat_spine) with
    | (Ext.Comp.PatNil loc, Ann.Comp.PatNil (_, tstr)) ->
       add_entry loc tstr
    | (Ext.Comp.PatApp (loc, ext_pat, ext_pat_spine'),
      Ann.Comp.PatApp (_, ann_pat, ann_pat_spine', _, tstr)) ->
       annotate_pattern ext_pat ann_pat;
       annotate_pat_spine ext_pat_spine' ann_pat_spine';
       add_entry loc tstr

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
