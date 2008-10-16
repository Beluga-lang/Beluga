(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Core.Common
open Frontend


(* Grammar.Loc.Exc_located (loc, exc) -> *)
(*         Format.printf "%s\n" (Printexc.to_string exc) *)
(*       ; Grammar.Loc.print Format.std_formatter loc *)
(*       ; assert false (\* needed for type-checking *\) *)

let main () =
  let file_name     = Sys.argv.(1) in
  let sgn           = Parser.parse_file ~name:file_name Parser.p_sgn_eoi in
  let rec print_sgn = function
    | []            -> ()
    | (decl::decls) ->
          Pretty.Ext.ppr_sgn_decl decl
        ; print_sgn decls
  in
    match sgn with
      | (InL exc)   ->
          begin match exc with
            | Parser.Grammar.Loc.Exc_located (loc, exc) ->
                  Format.fprintf Format.std_formatter "%s\n" (Printexc.to_string exc)
                ; Parser.Grammar.Loc.print Format.std_formatter loc
                ; Format.fprintf Format.std_formatter "\n"
                ; ()
            | _ ->
                  Format.fprintf Format.std_formatter "Uncaught Exception\n"
          end
      | (InR decls) ->
          print_sgn decls

let _ = main ()
