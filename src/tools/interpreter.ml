(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
    @author Darin Morrison
*)

open Core
open Format
open Frontend



(* The following is an example of how to use the Core and Frontend modules *)
let main () =
  if Array.length Sys.argv < 2
  then
    fprintf std_formatter "Usage: %s <file-1.lf> ... <file-n.lf>\n" Sys.argv.(0)
  else
    let per_file file_name =
      let rec sgn = Parser.parse_file ~name:file_name Parser.p_sgn_eoi
      and print_sgn printer = function
        | []            -> ()
        | decl :: decls ->
              printer decl
            ; print_sgn printer decls
      in
        (* matching against `(exn, 'a) either` which is just a sum type *)
        match sgn with
          (* If we have a parse failure, print some messages *)
          | Common.InL exn   ->
              begin match exn with
                | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
                      fprintf std_formatter "Parse Error: \n\t%s\n\nLocation:\n\t" exn
                    ; Parser.Grammar.Loc.print std_formatter loc
                    ; fprintf std_formatter "\n"
                    ; ()
                | exn' ->
                      fprintf std_formatter "Uncaught Exception: %s\n" (Printexc.to_string exn')
              end

          (* If we succeed, pretty-print the resulting AST *)
          | Common.InR decls ->
                fprintf std_formatter   "## Pretty Printing External Syntax: %s ##\n" file_name
              ; print_sgn Pretty.Ext.ppr_sgn_decl decls

              ; fprintf std_formatter "\n## Pretty Printing Internal Syntax: %s ##\n" file_name
              ; let internal_decls = List.map Reconstruct.internalize_sgn_decl decls in
                    print_sgn Pretty.Int.ppr_sgn_decl internal_decls
                  ; try
                        Check.check_sgn_decls internal_decls
                      ; fprintf std_formatter "\n####\n\n"
                    with
                      | Check.Error msg ->
                          fprintf std_formatter "## Typechecking failed:\n\t%s\n" msg


    in
      (* Iterate the process for each file given on the commandline *)
      Array.iter per_file (Array.sub Sys.argv 1 (Array.length Sys.argv -1))

let _ = main ()
