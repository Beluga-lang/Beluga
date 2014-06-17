module Loc = Syntax.Int.Loc
open Lexing

let generate_annotations = ref false;

module Annot = struct
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
                  Hashtbl.add store l e
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
  type entry = {
    ctx : Syntax.Int.LF.mctx;
    psi : Syntax.Int.LF.dctx;
    tc : Syntax.Int.LF.tclo
  }

  let mk_entry (c : Syntax.Int.LF.mctx) (p : Syntax.Int.LF.dctx) (t : Syntax.Int.LF.tclo) : entry =
  {
    ctx = c;
    psi = p;
    tc = t
  }

  let store         = Hashtbl.create 0  
  let add (l : Loc.t) (e : entry) (s : string) = if l <> Loc.ghost
                                    then        
                                      begin                                      
                                      (* dprint (fun () -> "[TypeInfo.LF] Entry of " ^ Pretty.Int.DefaultPrinter.typToString e.ctx e.psi e.tc ^ " added at: \n" ^ Syntax.Loc.to_string l ^ "\n"); *)
                                      Annot.add l (Annot.mk_entry (s ^ " :: " ^ Pretty.Int.DefaultPrinter.typToString e.ctx e.psi e.tc));
                                      Hashtbl.add store l e
                                      end
                                    else
                                      ()
  let get           = Hashtbl.find store
  let clear ()      = Hashtbl.clear store

end

module Comp = struct
  type entry = {
    ctx : Syntax.Int.LF.mctx;
    tc: Syntax.Int.Comp.tclo;
  }

  let mk_entry (c : Syntax.Int.LF.mctx) (t : Syntax.Int.Comp.tclo) : entry = 
  {
    ctx = c;
    tc = t
  }

  let store         = Hashtbl.create 0
  let add (l : Loc.t) (e : entry) (s : string) = if l <> Loc.ghost
                                    then   
                                      begin
                                      (* dprint (fun () -> "[TypeInfo.Comp] Entry of " ^ Pretty.Int.DefaultPrinter.subCompTypToString e.ctx e.tc ^ " added at: \n" ^ Syntax.Loc.to_string l ^ "\n"); *)
                                      Annot.add l (Annot.mk_entry (s ^ " :: " ^ Pretty.Int.DefaultPrinter.subCompTypToString e.ctx e.tc)) ; 
                                      Hashtbl.add store l e
                                      end
                                    else
                                      ()
  let get           = Hashtbl.find store
  let clear ()      = Hashtbl.clear store

end

let clear_all () : unit =
    LF.clear (); Comp.clear ()

let print_annot (name : string) : unit =
  let pp = open_out ((fun n -> String.sub n 0 (String.rindex n '.')) name ^ ".annot") in
  Annot.print_annot pp name
