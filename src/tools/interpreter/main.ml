(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Core
open Frontend
open Printf

(* The following is an example of how to use the Core and Frontend modules *)
let main () =
  if Array.length Sys.argv < 2
  then
    printf "Usage: %s <file-1.lf> ... <file-n.lf>\n" Sys.argv.(0)
  else
    let per_file errors file_name =
      let rec print_sgn printer = function
        | []            -> ()
        | decl :: decls ->
              printer decl
            ; print_sgn printer decls
      in
        try
          let sgn = Parser.parse_file ~name:file_name Parser.sgn_eoi in
              printf "## Pretty Printing External Syntax: %s ##\n" file_name
            ; print_sgn Pretty.Ext.DefaultPrinter.ppr_sgn_decl sgn

            ; printf "\n## Pretty Printing Internal Syntax: %s ##\n" file_name
            ; printf "\n## Type Reconstruction ##\n"
            ; let int_decls = List.map Reconstruct.recSgnDecl sgn in
                print_sgn Pretty.Int.DefaultPrinter.ppr_sgn_decl int_decls
              ; try
                (* Double Checking is done after reconstruction 

                  printf "\n## Double Checking ##"
                ; print_newline ()
                ; Check.Sgn.check_sgn_decls int_decls
                ; printf "\n## Double Checking Successful! ##\n\n" *)
                  (* clean up for the next file *)
                  Store.clear () 
                ; errors
                with
                  | Whnf.Error err ->
                      Format.fprintf
                        Format.std_formatter
                        "\n!! Error during Weak-Head Normalization !!\n\n%a\n\n@?"
                        Pretty.Error.DefaultPrinter.Whnf.fmt_ppr err
                      ; print_newline ()
                      ; errors + 1

                  | Check.LF.Error err ->
                       printf "\n!! Error during Type-Checking !!\n\n%s\n\n" err
                     ; print_newline ()
                        (* Format.fprintf
                          Format.std_formatter
                          "\n!! Error during Type-Checking !!\n\n%a\n\n@?"
                           Pretty.Error.DefaultPrinter.Check.fmt_ppr err; *)
                     ; errors + 1
        with
          | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
                printf "Parse Error: \n\t%s\nLocation:\n\t" exn
              ; Parser.Grammar.Loc.print Format.std_formatter loc
              ; Format.fprintf Format.std_formatter "@?"
              ; print_newline ()
              ; print_newline ()
              ; errors + 1


    (* Iterate the process for each file given on the command line *)
    in let file_count  = Array.length Sys.argv - 1
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
