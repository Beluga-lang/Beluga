(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Core
open Format
open Frontend



(* The following is an example of how to use the Frontend module *)
let main () =
  if Array.length Sys.argv < 2
  then
    fprintf std_formatter "Usage: %s <file-1.lf> ... <file-n.lf>\n" Sys.argv.(0)
  else
    let per_file file_name =
      let sgn           = Parser.parse_file ~name:file_name Parser.p_sgn_eoi in
      let rec print_sgn = function
        | []            -> ()
        | (decl::decls) ->
              Pretty.Ext.ppr_sgn_decl decl
            ; print_sgn decls
      in
        (* matching against `(exn, 'a) either` which is just a sum type *)
        match sgn with
          (* If we have a parse failure, print out some messages *)
          | (Common.InL exn)   ->
              begin match exn with
                | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
                      fprintf std_formatter "Parse Error: \n\t%s\n\nLocation:\n\t" exn
                    ; Parser.Grammar.Loc.print std_formatter loc
                    ; fprintf std_formatter "\n"
                    ; ()
                | exn ->
                      fprintf std_formatter "Uncaught Exception: %s\n" (Printexc.to_string exn)
              end
          (* If we succeed, pretty print the resulting AST *)
          | (Common.InR decls) ->
                fprintf std_formatter "## Pretty Printing: %s ##\n\n" file_name
              ; print_sgn decls
              ; fprintf std_formatter "\n"
    in
      (* Iterate the process for each file given on the commandline *)
      Array.iter per_file (Array.sub Sys.argv 1 (Array.length Sys.argv -1))

let _ = main ()
