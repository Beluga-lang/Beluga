(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
    @author Darin Morrison
*)

open Core
open Format
open Frontend

(* FIXME: make sure we're sequencing the printing properly by using appropriate print_newline () -dwm *)


(* The following is an example of how to use the Core and Frontend modules *)
let main () =
  if Array.length Sys.argv < 2
  then
    fprintf std_formatter "Usage: %s <file-1.lf> ... <file-n.lf>\n" Sys.argv.(0)
  else
    let per_file file_name =
      let rec sgn           = Parser.parse_file ~name:file_name Parser.p_sgn_eoi
      and ppf               = std_formatter
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
                      fprintf ppf "Parse Error: \n\t%s\n\nLocation:\n\t" exn
                    ; Parser.Grammar.Loc.print ppf loc
                    ; fprintf ppf "\n"
                    ; ()
                | exn' ->
                      fprintf ppf "Uncaught Exception: %s\n" (Printexc.to_string exn')
              end

          (* If we succeed, pretty-print the resulting AST *)
          | Common.InR decls ->
                fprintf ppf "## Pretty Printing External Syntax: %s ##\n" file_name
              ; print_sgn Pretty.Ext.DefaultPrinter.ppr_sgn_decl decls

              ; fprintf ppf "\n## Pretty Printing Internal Syntax: %s ##\n" file_name
              ; let internal_decls = List.map Reconstruct.internalize_sgn_decl decls in
                    print_sgn Pretty.Int.DefaultPrinter.ppr_sgn_decl internal_decls
                  ; try
                        fprintf ppf "\n## Checking Kinds and Types ##\n"
                      ; print_newline ()
                      ; Check.check_sgn_decls internal_decls
                      ; fprintf ppf "\n## Checking Successful! ##\n\n"
                      (* finally, cleanup for the next file *)
                      ; Store.clear ()
                  with
                    | Whnf.Error  err ->
                        fprintf
                          ppf
                          "\n!! Error during Weak-Head Normalization !!\n\n%a\n\n"
                          Pretty.Error.DefaultPrinter.Whnf.fmt_ppr err

                    | Check.Error err ->
                        fprintf
                          ppf
                          "\n!! Error during Type-Checking !!\n\n%a\n\n"
                          Pretty.Error.DefaultPrinter.Check.fmt_ppr err

    in
      (* Iterate the process for each file given on the commandline *)
      Array.iter per_file (Array.sub Sys.argv 1 (Array.length Sys.argv -1))

let _ = main ()
