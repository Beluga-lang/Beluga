(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Frontend



let main () =
  let file_name = Sys.argv.(1) in
  let sgn       = Parser.parse_file ~name:file_name Parser.p_sgn_eoi in
    List.map Pretty.Ext.ppr_sgn_decl sgn

let _ = main ()
