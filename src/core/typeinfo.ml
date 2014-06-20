module Loc = Syntax.Int.Loc
module P = Pretty.Int.DefaultPrinter
open Lexing

let generate_annotations = ref false;

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
  let add (l : Loc.t) (e : entry) = 
                  (* dprint (fun () -> "[TypeInfo.Annot] Entry of " ^ e.typ ^ " added at: \n" ^ Syntax.Loc.to_string l ^ "\n");  *)
                  Hashtbl.replace store l e
  let get       = Hashtbl.find store
  let to_string (e : entry) = e.typ
  let clear ()  = Hashtbl.clear store

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
  type entry = {
    ctx : LF.mctx;
    psi : LF.dctx;
    tc : LF.tclo
  }

  let mk_entry (c : LF.mctx) (p : LF.dctx) (t : LF.tclo) : entry =
  {
    ctx = c;
    psi = p;
    tc = t
  }

  let store         = Hashtbl.create 0  
  let add (l : Loc.t) (e : entry) (s : string) = 
    if l <> Loc.ghost
      then begin                                      
        (* dprint (fun () -> "[TypeInfo.LF] Entry of " ^ P.typToString e.ctx e.psi e.tc ^ " added at: \n" ^ Syntax.Loc.to_string l ^ "\n"); *)
        Annot.add l (Annot.mk_entry ((* s ^ " :: " ^ *) P.typToString e.ctx e.psi e.tc));
        Hashtbl.add store l e
      end else ()

  let get           = Hashtbl.find store
  let clear ()      = Hashtbl.clear store

end

module Comp = struct
  open Syntax.Int
  type entry = {
    ctx : LF.mctx;
    tc: Comp.tclo
  }

  let mk_entry (c : LF.mctx) (t : Comp.tclo) : entry = 
  {
    ctx = c;
    tc = t
  }

  let store         = Hashtbl.create 0
  let add (l : Loc.t) (e : entry) (s : string) = if l <> Loc.ghost
                                    then   
                                      begin
                                      (* dprint (fun () -> "[TypeInfo.Comp] Entry of " ^ P.subCompTypToString e.ctx e.tc ^ " added at: \n" ^ Syntax.Loc.to_string l ^ "\n"); *)
                                      Annot.add l (Annot.mk_entry ((* s ^ " :: " ^  *)P.subCompTypToString e.ctx e.tc)) ; 
                                      Hashtbl.add store l e
                                      end
                                    else
                                      ()
  let get           = Hashtbl.find store
  let clear ()      = Hashtbl.clear store

end

module Sgn = struct
  open Syntax.Int
  type typ_or_kind = Typ of LF.typ | Kind of LF.kind

  type entry = {
    sgn : typ_or_kind
  }

  let mk_entry (decl : typ_or_kind) : entry =
    {sgn = decl}

  let store = Hashtbl.create 0

  let add : Loc.t -> entry -> string -> unit = 
    fun l e _ -> if l <> Loc.ghost then begin
      let s = match e.sgn with
      | Typ t -> P.typToString LF.Empty LF.Null (t, LF.EmptySub)
      | Kind k -> P.kindToString LF.Null (k, LF.EmptySub)
      in
      Annot.add l (Annot.mk_entry s);
      Hashtbl.add store l e
    end

  let get : Loc.t -> entry = Hashtbl.find store

  let clear : unit -> unit = fun () -> Hashtbl.clear store

end

let clear_all () : unit =
    LF.clear (); Comp.clear (); Annot.clear()

let print_annot (name : string) : unit =
  let pp = open_out ((fun n -> String.sub n 0 (String.rindex n '.')) name ^ ".annot") in
  Annot.print_annot pp name

let type_of_position (pos : int) : string =
  let sorted =
    let cmp l1 l2 = (Loc.start_off l1) - (Loc.start_off l2) in
    let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) Annot.store [] in
      List.sort (fun (key1,_) (key2,_) -> cmp key1 key2) l in
  let f (l, _) = print_string ((string_of_int (Loc.start_off l)) ^ ", " ^ (string_of_int (Loc.stop_off l)) ^ "\n") in
  let _ = List.iter f sorted in
  let contains_pos (l, _) =
    (Loc.start_off l <= pos) && (pos <= Loc.stop_off l) in(* 
  let _ = print_string (string_of_int (List.length sorted)) in *)
  match List.fold_left (fun acc x -> if contains_pos x then (Some x) else acc) None sorted with
  | Some (_, s) -> (s.Annot.typ ^ "\n")
  | None -> ("No type information found for point: " ^ (string_of_int pos) ^ "\n")

