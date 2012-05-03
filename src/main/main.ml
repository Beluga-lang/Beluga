(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Core
(* open Frontend *)
open Printf
open Marshal

let usage () =
  let options =
          "    -d            turn all debugging printing off (default)\n"
        ^ "    +d            turn all debugging printing on\n"
        ^ "    +ext          print external syntax before reconstruction\n"
        ^ "    -s=natural    print substitutions in a \"natural\" style (default)\n"
        ^ "    -s=debruijn   print substitutions in deBruijn-ish style (when debugging Beluga)\n"
        ^ "    +implicit     print implicit arguments (default -- for now)\n"
        ^ "    -implicit     don't print implicit arguments\n"
        ^ "    -t            turn timing off (default)\n"
        ^ "    +t            print timing information\n"
        ^ "    +tfile        print timing information to file \"time.txt\"\n"
        ^ "    -coverage     turn off coverage checker (default, since coverage checker is incomplete)\n"
        ^ "    +coverage     turn on coverage checker (experimental)\n"
        ^ "    +covdepth nn  \"extra\" depth for coverage checker\n"
        ^ "    +warncover    turn on coverage checker (experimental), but give warnings only\n"
        ^ "    +printSubord  print subordination relations (experimental)\n"
        ^ "    -width nnn    set output width to nnn (default 86; minimum 40)\n"
        ^ "    -logic        turn on logic programming engine\n"
  in
  fprintf stderr
    "Usage: %s [options] file.(bel|cfg)\noptions:\n%s"
    Sys.argv.(0) options;
  exit 2

let usasy = ref false
let externall = ref false

module PC = Pretty.Control

let process_option' arg rest = begin let f = function
  (* these strings must be lowercase *)
  | "+d" -> (Debug.showAll (); Printexc.record_backtrace true; rest)
  | "-d" -> (Debug.showNone (); Printexc.record_backtrace false; rest)
  | "+ext" -> (externall := true; rest)
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
  | "-logic" -> (Logic.Options.enableLogic := true ; rest)
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

type session =
  | Session of string list

exception SessionFatal

let is_cfg file_name =
  Filename.check_suffix file_name ".cfg"

let is_sasy file_name =
  (if Filename.check_suffix file_name ".sbel" then usasy := true else () )

let rec accum_lines input =
  try
    let res = input_line input in res :: accum_lines input
  with
    | End_of_file -> []

let rec trim_comment str = 
  let len = String.length str in
  match str with
  | "" -> ""
  | s when s.[0] = ' '       -> trim_comment (String.sub s 1 (len - 1))
  | s when s.[0] = '\t'      -> trim_comment (String.sub s 1 (len - 1))
  | s when s.[0] = '%'       -> ""
  | s when s.[len - 1] = ' ' -> trim_comment (String.sub s 0 (len - 1))
  | s -> s

let filter_lines files = 
  let files' = List.map trim_comment files in
  List.filter (fun s -> String.length s != 0) files'

let process_cfg_file file_name = 
  let cfg = open_in file_name in
  let lines = accum_lines cfg in
  close_in cfg
  ; let dir = Filename.dirname file_name ^ "/" in
    Session (List.map (fun x -> dir ^ x) (filter_lines lines))

let rec process_file_argument f =
  if is_cfg f
  then process_cfg_file f
  else Session [f]
(*
let rec process_files = function
  | []                    -> []
  | f :: fs when is_cfg f ->
    process_cfg_file f
    :: (process_files fs)
  | f :: fs               -> (Session [f]) :: process_files fs

*)
let rec printL lsgn =
  match lsgn with
    | [] -> ()
    | h::t -> Ext_print.Ext.DefaultPrinter.ppr_sgn_decl h; printL t

let main () =
  (*let args   = List.tl (Array.to_list Sys.argv) in*)
  (*let files  = process_options args in*)
  (*let sessions = process_file_argument files in*)
  (*let session_count = List.length sessions in*)
  if Array.length Sys.argv < 2 then
    usage ()
  else
    let per_file file_name =
      let rec print_sgn printer = function
        | []            -> ()
        | decl :: decls ->
            printer decl;
            print_sgn printer decls
      in
      let abort_session () = raise SessionFatal
      in
        try
          (* Subord.clearMemoTable();   (* obsolete *) *)

         (* let args   = List.tl (Array.to_list Sys.argv) in
          let files  = process_options args in 
          let args   = List.tl (Array.to_list Sys.argv) in
          let files  = process_options args in*)
         (* let asasy   = List.tl (Array.to_list Sys.argv) in
          process_sasy asasy;*) 
            is_sasy file_name;
            if !usasy then
            let sgn = Sparser.parse_file ~name:file_name Sparser.section_eoi in
            (* printf "## Pretty Printing External Syntax: %s ##\n" file_name;
            print_sgn Pretty.Ext.DefaultPrinter.ppr_sgn_decl sgn;  *)
            printf "\n## Sasybel Type Reconstruction: %s ##\n" file_name;
        
            let tSgn = Transform.sectionDecls sgn in
            printL tSgn;
            let _int_decls = Recsgn.recSgnDecls tSgn in
              printf "\n## Type Reconstruction done: %s  ##\n" file_name;
              let _ = Coverage.force
                (function
                  | Coverage.Success -> 
                     ()
                  | Coverage.Failure message ->
                      if !Coverage.warningOnly then
                        Error.addInformation ("WARNING: Cases didn't cover: " ^ message)
                      else
                        raise (Coverage.Error (Syntax.Loc.ghost, Coverage.NoCover message))
                )  in
               (* if !Coverage.enableCoverage then 
                  (printf "\n## Coverage checking done: %s  ##\n" file_name )
                else ();
                if !Subord.dump then (Subord.dump_subord() (* ;
                                      Subord.dump_typesubord() *) );
            
                return Positive*)
              begin
                if !Coverage.enableCoverage then 
                  (if !Debug.chatter = 0 then () else
                      printf "\n## Coverage checking done: %s  ##\n" file_name )
                else ();
                if !Subord.dump then (Subord.dump_subord() (* ;
                                      Subord.dump_typesubord() *) );
                print_newline () ;
                Logic.runLogic ()
              end


           else 
           let sgn = Parser.parse_file ~name:file_name Parser.sgn_eoi in

            if !externall then (printf "\n## Pretty-printing of the external syntax : ##\n"; printL sgn;) else ();

            if !Debug.chatter = 0 then () else
              printf "\n## Type Reconstruction: %s ##\n" file_name;  

(*            let int_decls = List.map Recsgn.recSgnDecl sgn in *)
            let _int_decls = Recsgn.recSgnDecls sgn in

              if !Debug.chatter = 0 then () else
              printf "\n## Type Reconstruction done: %s  ##\n" file_name;
              let _ = Coverage.force
                (function
                  | Coverage.Success -> 
                     ()
                  | Coverage.Failure message ->
                      if !Coverage.warningOnly then
                        Error.addInformation ("WARNING: Cases didn't cover: " ^ message)
                      else
                        raise (Coverage.Error (Syntax.Loc.ghost, Coverage.NoCover message))
                ) in 
              begin
                if !Coverage.enableCoverage then 
                  (if !Debug.chatter = 0 then () else
                      printf "\n## Coverage checking done: %s  ##\n" file_name )
                else ();
                if !Subord.dump then (Subord.dump_subord() (* ;
                                      Subord.dump_typesubord() *) );

                print_newline () ;
                Logic.runLogic ()
              end

(*
        with
          | Parser.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
              Parser.Grammar.Loc.print Format.std_formatter loc;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf Format.std_formatter "Parse Error: %s" exn;
              Format.fprintf Format.std_formatter "@?";
              print_newline ();
              abort_session ()

          | ParserRelease.Grammar.Loc.Exc_located (loc, Stream.Error exn) ->
              ParserRelease.Grammar.Loc.print Format.std_formatter loc;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf Format.std_formatter "Parse Error: %s" exn;
              Format.fprintf Format.std_formatter "@?";
              print_newline ();
              abort_session ()

          | Error.Error (locOpt, err) ->
              printOptionalLocation locOpt;
              Format.fprintf Format.std_formatter ":\n";
              Format.fprintf
                Format.std_formatter
                "\nError (Reconstruction): %a@?"
                Pretty.Error.DefaultPrinter.fmt_ppr err;
              print_newline ();
              abort_session ()

          | Error.Violation str ->
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
              printf "Error (Coverage): %s" (strFn());
              abort_session ()

          | exn ->
              printf "%s\n" (Printexc.to_string exn);
              abort_session ()

*)
        with e ->
          Debug.print (Debug.toFlags [0]) (fun () -> "\nBacktrace:\n" ^ Printexc.get_backtrace () ^ "\n");
          output_string stderr (Printexc.to_string e);
          abort_session ()
    in

    let args   = List.tl (Array.to_list Sys.argv) in
    let files = process_options args in
    let status_code =
      match files with
        | [file] ->
          begin
            try
              let Session file_names = process_file_argument file in
              List.iter per_file file_names; 0
            with SessionFatal -> 1
          end
        | _ ->
          printf "Wrong number of command line arguments.\n";
          2
    in
    printf "%s" (Error.getInformation());
    exit status_code

let _ = Format.set_margin 80
let _ = main ()
