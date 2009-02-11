(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Core
open Frontend
open Printf

(* The following is an example of how to use the Core and Frontend modules *)

let usage () =
  let options = "    -d      turn all debugging off (default)\n"
              ^ "    +d      turn all debugging on\n"
  in
    fprintf stderr
      "Usage: %s [options] spec1 ... spec-n\nspec ::= file | @file (file that should fail)\noptions:\n%s"
      Sys.argv.(0)   options
  ; exit 2

(* We should be using a library for this *)
let process_option = function
  | "+d" -> Debug.showAll ()
  | "-d" -> Debug.showNone ()
  | _ -> usage ()

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      let first = String.get arg 0 in
        if first = '-' or first = '+' then
         (process_option arg; process_options rest)
        else  (* reached end of options: return this and remaining arguments *)
          arg :: rest

(* File specification. *)
type spec =
  | Positive   (* "filename": should be processed with no errors *)
  | Negative   (* "@filename": should yield errors *)
  (* "Negative" is too broad; should distinguish type errors from internal failures, at least! *)

let process_name name =
  let rest = String.sub name 1 (String.length name - 1) in
    if String.get name 0 = '@' then
      (Negative, rest)
(* else if String.get name 0 = ...... then
      (......, rest)
*)
    else
      (Positive, name)

let is_cfg file_name =
  Filename.check_suffix file_name ".cfg"

let rec accum_lines input =
  try
    let res = input_line input in Printf.printf "%s\n" res; res :: accum_lines input
  with
    | End_of_file -> []

let rec process_lines parent_dir = function
  | []      -> []
  | x :: [] -> (true, parent_dir ^ x) :: []
  | x :: xs -> let ((s, x') :: xs') = process_lines parent_dir xs in (false, parent_dir ^ x) :: (s, x') :: xs'

let rec process_files = function
  | []                    -> []
  | f :: fs when is_cfg f ->
      let cfg =
        if String.get f 0 = '@' then
          open_in (String.sub f 1 (String.length f - 1))
        else
          open_in f in
      let lines = accum_lines cfg in
        List.append (process_lines (Filename.dirname f ^ "/") lines) (process_files fs)
  | f :: fs               -> (true, f) :: process_files fs

let main () =
  if Array.length Sys.argv < 2 then
    usage ()
  else
    let per_file (errors, unsound, incomplete) (should_reset_state, file_name) =
      let (spec, file_name) = process_name file_name in
      let return actual = match (spec, actual) with
        | (Positive, Positive) -> (errors, unsound, incomplete)
        | (Positive, Negative) -> (errors + 1, unsound, incomplete + 1)
        | (Negative, Positive) -> (errors, unsound + 1, incomplete)
        | (Negative, Negative) -> (errors + 1, unsound, incomplete)
      in
      let rec print_sgn printer = function
        | []            -> ()
        | decl :: decls ->
            printer decl;
            print_sgn printer decls
      in
      let printOptionalLocation locOpt = match locOpt with
        | None     -> Format.fprintf Format.std_formatter "<unknown location>"
        | Some loc -> Parser.Grammar.Loc.print Format.std_formatter loc
      in
        try
          let sgn = Parser.parse_file ~name:file_name Parser.sgn_eoi in
              printf "## Pretty Printing External Syntax: %s ##\n" file_name
            ; print_sgn Pretty.Ext.DefaultPrinter.ppr_sgn_decl sgn

            ; printf "\n## Type Reconstruction: %s ##\n" file_name

            ; let int_decls = List.map Reconstruct.recSgnDecl sgn in
                print_sgn Pretty.Int.DefaultPrinter.ppr_sgn_decl int_decls
              ; try
                (* Double Checking is done after reconstruction 

                  printf "\n## Double Checking ##"
                ; print_newline ()
                ; Check.Sgn.check_sgn_decls int_decls
                ; printf "\n## Double Checking Successful! ##\n\n" *)
                  (* clean up for the next file *)
                  if should_reset_state then
                    Store.clear ()
                  else
                    ()
                ; return Positive
                with
                  | Whnf.Error err ->
                      Format.fprintf
                        Format.std_formatter
                        "\n!! Error during weak-head normalization !!\n\n%a\n@?\n"
                        Pretty.Error.DefaultPrinter.fmt_ppr err;
                      return Negative

                  | Check.LF.Error (locOpt, err) ->
                      printOptionalLocation locOpt;
                      Format.fprintf Format.std_formatter ":\n";
                      Format.fprintf
                        Format.std_formatter
                        "Error (Type-Checking): %a@?"
                        Pretty.Error.DefaultPrinter.fmt_ppr err;
                      print_newline ();
                      return Negative

                  | Check.LF.Violation msg ->
                      printf "\n!! Error during typechecking !!\n\n%s\n\n" msg;
                      return Negative

        with
          | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
              Parser.Grammar.Loc.print Format.std_formatter loc;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf Format.std_formatter "Parse Error: %s" exn;
              Format.fprintf Format.std_formatter "@?";
              print_newline ();
              return Negative

          | Reconstruct.Error (locOpt, err) ->
              printOptionalLocation locOpt;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf
                Format.std_formatter
                "Error (Reconstruction): %a@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              return Negative

          | Reconstruct.Violation err_string ->
              Format.fprintf
                Format.std_formatter
                (* TODO print location as "filename:line1.col1-line2-col2" *)
                "Error (\"Violation\") (Reconstruction): %s\n@?"
                err_string;
              print_newline ();
              return Negative

          | Check.Comp.Err err ->
              (* Parser.Grammar.Loc.print Format.std_formatter loc; *)
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf
                Format.std_formatter
                "Error (Checking): %a@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              return Negative

          | Context.Error err ->
              Format.fprintf
                Format.std_formatter
                "Error (Context): %a\n@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              return Negative

    (* Iterate the process for each file given on the command line *)
    in
    let args   = List.tl (Array.to_list Sys.argv) in
    let files  = process_options args in
    let files' = process_files files in
    let file_count = List.length files' in
    let (error_count, unsound_count, incomplete_count) = List.fold_left per_file
                         (0, 0, 0) (* initial number of: errors, unsounds, incompletes *)
                         files' in
    let plural count what suffix =
      string_of_int count ^ " "
      ^ (if count = 1 then
           what
         else
           what ^ suffix) in

    let status_code = if unsound_count + incomplete_count = 0 then 0 else 1
    and message     = 
      let full =
        let sound = unsound_count = 0
        and complete = incomplete_count = 0 in
       (if sound && complete then "#      OK!"
        else (if sound then "" else "####    " ^ plural unsound_count "erroneously accepted (unsound)" "" ^ (if complete then "" else ", "))
          ^(if complete then "" else "####    " ^ plural incomplete_count "erroneously rejected (incomplete)" ""))
        ^ "\n"
      in match (file_count, error_count, unsound_count + incomplete_count) with
         | (1, 0, 0) -> ""
         | (1, 1, 1) -> "\n#### 1 error\n"
         | (_, _, _) -> "\n#### " ^ plural file_count "file" "s" ^ ":\n" ^ full
    in
      print_string message;
      exit status_code

let _ = main ()
