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
    let per_file errors file_name =
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
             (begin match exn with
                | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
                      fprintf ppf "Parse Error: \n\t%s\n\nLocation:\n\t" exn
                    ; Parser.Grammar.Loc.print ppf loc
                    ; fprintf ppf "\n"
                    ; ()
                | exn' ->
                      fprintf ppf "Uncaught Exception: %s\n" (Printexc.to_string exn')
              end
            ; errors + 1)

          (* If we succeed, pretty-print the resulting AST *)
          | Common.InR decls ->
                fprintf ppf "## Pretty Printing External Syntax: %s ##\n" file_name
              ; print_sgn Pretty.Ext.DefaultPrinter.ppr_sgn_decl decls

              ; fprintf ppf "\n## Pretty Printing Internal Syntax: %s ##\n" file_name
              ; fprintf ppf "\n## Type Reconstruction ##\n"
              ; let internal_decls = List.map Reconstruct.recSgnDecl decls in
                    print_sgn Pretty.Int.DefaultPrinter.ppr_sgn_decl internal_decls
                  ; try
                        fprintf ppf "\n## Double Checking ##"
                      ; print_newline ()
                      ; Check.LF.check_sgn_decls internal_decls
                      ; fprintf ppf "\n## Double Checking Successful! ##\n\n"
                      (* clean up for the next file *)
                      ; Store.clear ()
                      ; errors
                  with
                    | Whnf.Error  err ->
                        fprintf
                          ppf
                          "\n!! Error during Weak-Head Normalization !!\n\n%s\n\n"
                          err
                          (* Pretty.Error.DefaultPrinter.Whnf.fmt_ppr err *)
                      ; errors + 1

                    | Check.LF.Error err ->
                        fprintf
                          ppf
                          "\n!! Error during Type-Checking !!\n\n%s\n\n"
                          err
                          (* Pretty.Error.DefaultPrinter.Check.fmt_ppr err; *)
                      ; errors + 1

    (* Iterate the process for each file given on the command line *)
    in let file_count = Array.length Sys.argv - 1
    in let error_count = Array.fold_left
                           per_file
                           0  (*number of errors*)
                           (Array.sub Sys.argv 1 file_count)

    in let plural count what suffix =
        string_of_int count
      ^ " "
      ^ (if count = 1 then
           what
         else
           what ^ suffix)

    in let status_code = if error_count = 0 then 0 else 1
       and message = if file_count = 1 && error_count = 0 then
                       ""
                     else "#### " ^
                       (if file_count <= 1 then "" 
                        else plural file_count "file" "s" ^ ", ")
                     ^ plural error_count "error" "s"
                     ^ "\n"
    in
        print_string message
      ; exit status_code

let _ = main ()
