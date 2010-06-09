(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Core
(* open Frontend *)
open Printf

let usage () =
  let options =
          "    -d            turn all debugging printing off (default)\n"
        ^ "    +d            turn all debugging printing on\n"
        ^ "    -s=natural    print substitutions in a \"natural\" style (default)\n"
        ^ "    -s=debruijn   print substitutions in deBruijn-ish style (when debugging Beluga)\n"
        ^ "    +implicit     print implicit arguments (default -- for now)\n"
        ^ "    -implicit     don't print implicit arguments\n"
        ^ "    -t            turn timing off (default)\n"
        ^ "    +t            print timing information\n"
        ^ "    +tfile        print timing information to file \"time.txt\"\n"
        ^ "    -coverage     turn off coverage checker (default, since coverage checker is incomplete)\n"
        ^ "    +coverage     turn on coverage checker (experimental)\n"
        ^ "    +warncover    turn on coverage checker (experimental), but give warnings only\n"
        ^ "    +printSubord  print subordination relation (experimental)\n"
        ^ "    -width nnn    set output width to nnn (default 86; minimum 40)\n"
  in
    fprintf stderr
      "Usage: %s [options] spec1 ... spec-n\nspec ::= file | @file (file that should fail)\noptions:\n%s"
      Sys.argv.(0)   options
  ; exit 2

module PC = Pretty.Control

let process_option' arg rest = begin let f = function
  (* these strings must be lowercase *)
  | "+d" -> (Debug.showAll (); rest)
  | "-d" -> (Debug.showNone (); rest)
  | "-s=natural" -> (PC.substitutionStyle := PC.Natural; rest)
  | "-s=debruijn" -> (PC.substitutionStyle := PC.DeBruijn; rest)
  | "+implicit" -> (PC.printImplicit := true; rest)
  | "-implicit" -> (PC.printImplicit := false; rest)
  | "+t" -> (Monitor.on := true; rest)
  | "+tfile" -> (Monitor.onf := true; rest)
  | "-t" -> (Monitor.on := false;
             Monitor.onf := false;
             rest)
  | "+coverage" -> (Coverage.enableCoverage := true; rest)
  | "+warncover" -> (Coverage.enableCoverage := true; Coverage.warningOnly := true; rest)
  | "-coverage" -> (Coverage.enableCoverage := false; rest)
  | "+printsubord" -> (Subord.dump := true; rest)
  | "-width" -> (match rest with [] -> (print_string "-width needs an argument\n"; exit 2)
                               | arg::rest -> (try let width = int_of_string arg in
                                                 Format.set_margin (max 40 width);
                                                 rest
                                               with Failure "int_of_string" ->
                                                      print_string "-width needs a numeric argument\n"; exit 2))
  | _ -> usage ()
in (* print_string (">>>> " ^ arg ^ "\n"); *)
  f arg
end

let process_option string rest =
  if String.length string < 4 then
    process_option' string rest
  else
    (* preserve case of first 2 characters; lowercase following *)
    let first_part = String.sub string 0 2
    and second_part = String.lowercase (String.sub string 2 (String.length string - 2)) in
      process_option' (first_part ^ second_part) rest

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      let first = String.get arg 0 in
        if first = '-' or first = '+' then
          process_options (process_option arg rest)
        else  (* reached end of options: return this and remaining arguments *)
          arg :: rest

(* File specification. *)
type spec =
  | Positive   (* "filename": should be processed with no errors *)
  | Negative   (* "@filename": should yield errors *)
  (* "Negative" is too broad; should distinguish type errors from internal failures, at least! *)

type session =
  | Session of string list

exception SessionFatal of spec

let process_name name =
  let rest = String.sub name 1 (String.length name - 1) in
    if String.get name 0 = '@' then
      (print_string ("\nNOTE: %not is usually preferred over \"@\"\n\n")
      ; (Negative, rest))
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
  | [x]    -> [parent_dir ^ x]
  | x :: xs -> let x' :: xs' = process_lines parent_dir xs in (parent_dir ^ x) :: x' :: xs'

let rec process_files = function
  | []                    -> []
  | f :: fs when is_cfg f ->
      let filename =
        if String.get f 0 = '@'
        then String.sub f 1 (String.length f - 1)
        else f in
      let cfg = open_in filename in
      let lines = accum_lines cfg in
        close_in cfg
        ; (Session (process_lines (Filename.dirname f ^ "/") lines))
       :: (process_files fs)
  | f :: fs               -> (Session [f]) :: process_files fs

let main () =
  if Array.length Sys.argv < 2 then
    usage ()
  else
    let per_file (errors, unsound, incomplete) file_name =
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
      let abort_session () = raise (SessionFatal spec)
      in
        try
          (* Subord.clearMemoTable();   (* obsolete *) *)
          let sgn = Parser.parse_file ~name:file_name Parser.sgn_eoi in
            (* printf "## Pretty Printing External Syntax: %s ##\n" file_name;
            print_sgn Pretty.Ext.DefaultPrinter.ppr_sgn_decl sgn;  *)
            printf "\n## Type Reconstruction: %s ##\n" file_name;

(*            let int_decls = List.map Reconstruct.recSgnDecl sgn in *)
            let _int_decls = Reconstruct.recSgnDecls sgn in
              (* print_sgn Pretty.Int.DefaultPrinter.ppr_sgn_decl int_decls; *)
              printf "\n## Type Reconstruction done: %s  ##\n" file_name;
              let _ = Coverage.force
                (function
                  | Coverage.Success -> ()
                  | Coverage.Failure messageFn ->
                      if !Coverage.warningOnly then
                        Error.addInformation ("WARNING: Cases didn't cover: " ^ messageFn())
                      else
                        raise (Coverage.NoCover messageFn)
                ) in
                if !Subord.dump then Subord.dump_subord();
                return Positive
        with
          | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
              Parser.Grammar.Loc.print Format.std_formatter loc;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf Format.std_formatter "Parse Error: %s" exn;
              Format.fprintf Format.std_formatter "@?";
              print_newline ();
              abort_session ()

          | Reconstruct.Error (locOpt, err) ->
              printOptionalLocation locOpt;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf
                Format.std_formatter
                "\nError (Reconstruction): %a@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              abort_session ()

          | Reconstruct.Violation str ->
              Format.fprintf
                Format.std_formatter
                "Error (\"Violation\") (Reconstruction): %s\n@?"
                str;
              print_newline ();
              abort_session ()


          | Check.LF.Error (locOpt, err) ->
              printOptionalLocation locOpt;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf
                Format.std_formatter
                "\nError (Type-checking): %a@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              abort_session ()

          | Check.Comp.Error (locOpt, err) ->
             (* Parser.Grammar.Loc.print Format.std_formatter loc; *)
              printOptionalLocation locOpt;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf
                Format.std_formatter
                "\nError (Checking): %a@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              abort_session ()

          | Check.LF.Violation str ->
              printf "Error (\"Violation\") (Checking): %s\n" str;
              abort_session ()

          | Context.Error err ->
              Format.fprintf
                Format.std_formatter
                "Error (Context): %a\n@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              abort_session ()

          | Whnf.Error (locOpt, err) ->
              printOptionalLocation locOpt;
              Format.fprintf
                Format.std_formatter
                "\nError (Whnf): %a\n@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              abort_session ()

          | Abstract.Error str ->
              printf "Error (Abstraction): %s\n" str;
              abort_session ()

          | Coverage.NoCover strFn ->
              printf "Error (Coverage): %sn" (strFn());
              abort_session ()


    in
    let per_session (errors, unsound, incomplete) (Session file_names) =
      let return spec actual = match (spec, actual) with
        | (Positive, Positive) -> (errors, unsound, incomplete)
        | (Positive, Negative) -> (errors + 1, unsound, incomplete + 1)
        | (Negative, Positive) -> (errors, unsound + 1, incomplete)
        | (Negative, Negative) -> (errors + 1, unsound, incomplete)
      in
        Store.clear ()
      ; Coverage.clear ()
      ; Gensym.reset ()
      ; try List.fold_left per_file (errors, unsound, incomplete) file_names
        with SessionFatal spec -> return spec Negative

    in
      (* Iterate the process for each file given on the command line *)
    let args   = List.tl (Array.to_list Sys.argv) in
    let files  = process_options args in
    let sessions = process_files files in
    let session_count = List.length sessions in
    let (error_count, unsound_count, incomplete_count) = List.fold_left per_session
      (0, 0, 0) (* initial number of: errors, unsounds, incompletes *)
                         sessions in
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
          (if sound && complete
           then ( let _ = if (!Monitor.on || !Monitor.onf) then
                    Monitor.print_timer ();
                  in "#      OK!"
                )            

           else (if sound then "" else "####    " ^ plural unsound_count "erroneously accepted (unsound)" "" ^ (if complete then "" else ", "))
          ^(if complete then "" else "####    " ^ plural incomplete_count "erroneously rejected (incomplete)" ""))
          ^ "\n"

      in match (session_count, error_count, unsound_count + incomplete_count) with
         | (1, 0, 0) -> ""
         | (1, 1, 1) -> "\n#### 1 error\n"
         | (_, _, _) -> "\n#### " ^ plural session_count "session" "s" ^ ":\n" ^ full
    in
      print_string message;
      printf "%s" (Error.getInformation());
      exit status_code

let _ = Format.set_margin 86
let _ = main ()
