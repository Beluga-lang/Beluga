module Loc = Syntax.Int.Loc
module P = Pretty.Int.DefaultPrinter
open Lexing

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

module Comp = struct
  module Ann = Annotated
  module Ext = Syntax.Ext

  let add_entry loc str =
    match str with
    | None -> Annot.add loc ("No type information found.")
    | Some str' -> Annot.add loc str'

  let rec annotate_comp_exp_chk ext_e ann_e =
    ann_chk ext_e ann_e

  and ann_chk ext_e ann_e =
    match ext_e, ann_e with
    | (Ext.Comp.Fun (loc, _, ext_e'), Ann.Comp.Fun (_, _, ann_e', _, tstr)) ->
       ann_chk ext_e' ann_e';
       add_entry loc tstr

    | (Ext.Comp.MLam (loc, _, ext_e'), Ann.Comp.MLam (_, _, ann_e', _, tstr)) ->
       ann_chk ext_e' ann_e';
       add_entry loc tstr

    | (Ext.Comp.Cofun (loc, ext_bs), Ann.Comp.Cofun (_, ann_bs, _, tstr)) ->
       let f = (fun (Ext.Comp.CopatApp (loc, _, _), ext_e')
		    (Ann.Comp.CopatApp (_, _, _), ann_e') -> ann_chk ext_e' ann_e')
       in
       List.iter2 f ext_bs ann_bs;
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
       ann_chk ext_e'ann_e';
       add_entry loc tstr

    | (Ext.Comp.Box (loc, _), Ann.Comp.Box (_, _, _, tstr)) ->
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
