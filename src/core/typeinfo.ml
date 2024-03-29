open Support.Equality
open Support
open Beluga_syntax
module P = Prettyint.DefaultPrinter

let generate_annotations = ref false

module Annot = struct
  type entry = { typ : string }

  let store = Hashtbl.create 0

  let mk_entry (t : string) : entry =
    let typ =
      String.map
        (function
          | '\n' -> ' '
          | c -> c)
        t
    in
    { typ }

  let add (l : Location.t) (e : entry) =
    (* dprint (fun () -> "[TypeInfo.Annot] Entry of " ^ e.typ ^ " added at: \n" ^ Location.to_string l ^ "\n");  *)
    Hashtbl.replace store l e
  let get = Hashtbl.find store
  let clear () = Hashtbl.clear store
  let to_string (e : entry) = e.typ

  let output_int pp i = output_string pp (string_of_int i)

  let print_position (pp : out_channel) (pos : Position.t) (name : string) : unit =
    output_string pp "\"";
    output_string pp (String.escaped name);
    output_string pp "\" ";
    output_int pp (Position.line pos);
    output_char pp ' ';
    output_int pp (Position.beginning_of_line pos);
    output_char pp ' ';
    output_int pp (Position.column pos)

  let print_location (pp : out_channel) (loc : Location.t) (name : string) : unit =
    let start_pos = Location.start_position loc in
    let end_pos = Location.stop_position loc in
    print_position pp start_pos name;
    output_char pp ' ';
    print_position pp end_pos name

  let print_one (pp : out_channel) (name : string) (typtup : Location.t * entry) : unit =
    let (loc, entry) = typtup in
    let tp = entry.typ in
    print_location pp loc name;
    output_string pp "\ntype(\n     ";
    output_string pp tp;
    output_string pp "\n)\n"

  let print_annot out_channel (name : string) : unit =
    let sorted =
      let cmp l1 l2 = Location.start_offset l1 - Location.start_offset l2 in
      let l = Hashtbl.fold (fun k v acc -> (k, v) :: acc) store [] in
      List.sort (fun (key1, _) (key2, _) -> cmp key1 key2) l
    in
    let f = print_one out_channel name in
    List.iter f sorted
end

module LF = struct
  open Synint

  type entry =
    { ctx : LF.mctx
    ; psi : LF.dctx
    ; tc : LF.tclo
    }

  let store = Hashtbl.create 0
  let mk_entry (c : LF.mctx) (p : LF.dctx) (t : LF.tclo) : entry =
    { ctx = c
    ; psi = p
    ; tc = t
    }

  let add (l : Location.t) (e : entry) (_ : string) =
    if Bool.not (Location.is_ghost l)
    then
      begin
        (* dprint (fun () -> "[TypeInfo.LF] Entry of " ^ P.typToString e.ctx e.psi e.tc ^ " added at: \n" ^ Location.to_string l ^ "\n"); *)
        Format.stringify (P.fmt_ppr_lf_typ e.ctx e.psi P.l0) (Whnf.normTyp e.tc)
        |> Annot.mk_entry
        |> Annot.add l;
        Hashtbl.add store l e
      end
  let get = Hashtbl.find store
  let clear () = Hashtbl.clear store
end

module Comp = struct
  open Synint

  type entry =
    { ctx : LF.mctx
    ; tc: Comp.tclo
    }

  let store = Hashtbl.create 0
  let mk_entry (c : LF.mctx) (t : Comp.tclo) : entry =
    { ctx = c
    ; tc = t
    }

  let add (l : Location.t) (e : entry) (_ : string) =
    if Bool.not (Location.is_ghost l)
    then
      begin
        (* dprint (fun () -> "[TypeInfo.Comp] Entry of " ^ P.subCompTypToString e.ctx e.tc ^ " added at: \n" ^ Location.to_string l ^ "\n"); *)
        Format.stringify (P.fmt_ppr_cmp_typ e.ctx P.l0) (Whnf.cnormCTyp e.tc)
        |> Annot.mk_entry
        |> Annot.add l;
        Hashtbl.add store l e
      end
  let get = Hashtbl.find store
  let clear () = Hashtbl.clear store
end

module Sgn = struct
  open Synint

  type typ_or_kind = Typ of LF.typ | Kind of LF.kind

  type entry =
    { sgn : typ_or_kind
    }

  let store = Hashtbl.create 0
  let mk_entry (decl : typ_or_kind) : entry =
    { sgn = decl
    }

  let add (l : Location.t) (e : entry) (_ : string) : unit =
    if Bool.not (Location.is_ghost l)
    then
      begin
        begin
          match e.sgn with
          | Typ t ->
             Format.stringify (P.fmt_ppr_lf_typ LF.Empty LF.Null P.l0) t
          | Kind k ->
             Format.stringify (P.fmt_ppr_lf_kind LF.Null P.l0) k
        end
        |> Annot.mk_entry
        |> Annot.add l;
        Hashtbl.add store l e
      end
  let get : Location.t -> entry = Hashtbl.find store
  let clear () : unit = Hashtbl.clear store
end

let clear_all () : unit =
  LF.clear ();
  Comp.clear ();
  Annot.clear ()

let print_annot (name : string) : unit =
  let output_filename = (Filename.remove_extension name) ^ ".annot" in
  Out_channel.with_open_bin
    output_filename
    (fun out_channel -> Annot.print_annot out_channel name)

let type_of_position (line : int) (col : int) : string =
  let sorted =
    let cmp l1 l2 = Location.start_offset l1 - Location.start_offset l2 in
    let l = Hashtbl.fold (fun k v acc -> (k, v) :: acc) Annot.store [] in
    List.sort (fun (key1, _) (key2, _) -> cmp key1 key2) l
  in
  (* let f (l, _) = print_string ((string_of_int (Location.start_off l)) ^ ", " ^ (string_of_int (Location.stop_off l)) ^ "\n") in
  List.iter f sorted; *)
  let contains_pos (l, x) : bool =
    let start_c = Location.start_offset l - Location.start_bol l in
    let end_c = Location.stop_offset l - Location.stop_bol l in
    let start_l = Location.start_line l in
    let end_l = Location.stop_line l in
    (* Format.printf "(%d, %d), (%d, %d), %s\n" (Location.start_line l) start_c (Location.stop_line l) end_c x.Annot.typ; *)
    if (start_l = line) && (end_l = line)
    then (start_c <= col) && (col <= end_c)
    else if (start_l = line) && (line < end_l)
    then start_c <= col
    else if (start_l < line) && (line < end_l)
    then true
    else if (start_l < line) && (line = end_l)
    then col <= end_c
    else false
  in
  match List.fold_left (fun acc x -> if contains_pos x then Some x else acc) None sorted with
  | Some (_, s) -> s.Annot.typ ^ ";\n"
  | None ->
     Format.asprintf "No type information found for point: (%d, %d);@\n"
       line
       col
