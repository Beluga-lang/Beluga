(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Printf

let bailout msg =
  fprintf stderr "%s\n" msg;
  exit 2

let usage () =
  let options =
          "    -d            turn all debugging printing off (default)\n"
        ^ "    +d            turn all debugging printing on\n"
        ^ "    +ext          print external syntax before reconstruction\n"
        ^ "    -s=natural    print substitutions in a \"natural\" style (default)\n"
        ^ "    -s=debruijn   print substitutions in deBruijn-ish style (when debugging Beluga)\n"
        ^ "    +implicit     print implicit arguments\n"
        ^ "    -implicit     don't print implicit arguments (default)\n"
        ^ "    -t            turn timing off (default)\n"
        ^ "    +t            print timing information\n"
        ^ "    +tfile        print timing information to file \"time.txt\"\n"
        ^ "    -coverage     turn off coverage checker (default, since coverage checker is incomplete)\n"
        ^ "    +coverage     turn on coverage checker (experimental)\n"
        ^ "    +covdepth nn  \"extra\" depth for coverage checker\n"
        ^ "    +warncover    turn on coverage checker (experimental), but give warnings only\n"
        ^ "    +printSubord  print subordination relations (experimental)\n"
        ^ "    +print        turn printing on (default)\n"
        ^ "    -print        turn printing off\n"
        ^ "    -width nnn    set output width to nnn (default 86; minimum 40)\n"
        ^ "    +logic        turn on logic programming engine\n"
        ^ "    +test         Make output suitable for test harness. Implies -print\n"
        ^ "    +strengthen   Perform metavariable strengthening automatically.\n"
        ^ "    -strengthen   Turn off metavariable strengthening.\n"
        ^ "    +realNames    Print holes using real names (default)\n"
        ^ "    -realNames    Print holes using freshly generated names\n"
        ^ "    +annot        Generate a .annot file for use in emacs\n"
        ^ "    +locs         Output location information (for testing)\n"
  in
  fprintf stderr "Beluga version %s\n" Version.beluga_version;
  fprintf stderr
    "Usage: %s [options] file.(bel|cfg)\noptions:\n%s"
    Sys.argv.(0) options;
  exit 2

let externall = ref false

module PC = Pretty.Control

let process_option arg rest = match arg with
  (* these strings must be lowercase *)
  | "+d" ->Debug.showAll (); Printexc.record_backtrace true; rest
  | "-d" -> Debug.showNone (); Printexc.record_backtrace false; rest
  | "+ext" -> externall := true; rest
  | "-s=natural" -> PC.substitutionStyle := PC.Natural; rest
  | "-s=debruijn" -> PC.substitutionStyle := PC.DeBruijn; rest
  | "+implicit" -> PC.printImplicit := true; rest
  | "-implicit" -> PC.printImplicit := false; rest
  | "+t" -> Monitor.on := true; rest
  | "+tfile" -> Monitor.onf := true; rest
  | "-t" -> Monitor.on := false; Monitor.onf := false; rest
  | "+coverage" -> Coverage.enableCoverage := true; rest
  | "+warncover" -> Coverage.enableCoverage := true; Coverage.warningOnly := true; rest
  | "-coverage" -> Coverage.enableCoverage := false; rest
  | "+printsubord" -> Subord.dump := true; rest
  | "+print" -> rest
  | "-print" -> Debug.chatter := 0; rest
  | "-width" ->
    begin match rest with
      | [] -> bailout "-width needs an argument"
      | arg::rest ->
        try
          let width = int_of_string arg in
          Format.set_margin (max 40 width);
          rest
        with Failure "int_of_string" ->
          bailout "-width needs a numeric argument"
    end
  | "+logic" -> Logic.Options.enableLogic := true ; rest
  | "+test" -> Error.Options.print_loc := false; Debug.chatter := 0; rest
  | "+strengthen" -> Lfrecon.strengthen := true; rest
  | "-strengthen" -> Lfrecon.strengthen := false; rest
  | "+realNames" -> Store.Cid.NamedHoles.usingRealNames := true; rest
  | "-realNames" -> Store.Cid.NamedHoles.usingRealNames := false; rest
  | "+annot"      -> Typeinfo.generate_annotations := true; rest
  | "+locs"       -> Locs.gen_loc_info := true; rest
  | _ -> usage ()

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      let first = String.get arg 0 in
        if first = '-' || first = '+' then
          process_options (process_option arg rest)
        else  (* reached end of options: return this and remaining arguments *)
          arg :: rest

type session =
  | Session of string list

exception SessionFatal

let is_cfg file_name =
  Filename.check_suffix file_name ".cfg"

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

let process_file_argument f =
  if is_cfg f
  then process_cfg_file f
  else Session [f]

let main () =
  if Array.length Sys.argv < 2 then
    usage ()
  else
    let per_file file_name =
      let abort_session () = raise SessionFatal in
      try
        let sgn = Parser.parse_file ~name:file_name Parser.sgn in
        (* If the file starts with an %opts pragma then process it now. *)
        let sgn = match sgn with
          | Synext.Sgn.Pragma (_, Synext.Sgn.OptsPrag opts) :: sgn ->
            ignore (process_options opts); sgn
          | _ -> sgn in
        if !externall then begin
          if !Debug.chatter != 0 then
            printf "\n## Pretty-printing of the external syntax : ##\n";
          List.iter Pretty.Ext.DefaultPrinter.ppr_sgn_decl sgn
        end;
        if !Debug.chatter != 0 then
          printf "\n## Type Reconstruction: %s ##\n" file_name;
        Recsgn.recSgnDecls sgn;
        if !Debug.chatter != 0 then
          printf "\n## Type Reconstruction done: %s  ##\n" file_name;
          ignore (Coverage.force
                  (function
                    | Coverage.Success -> ()
                    | Coverage.Failure message ->
                      if !Coverage.warningOnly then
                        Error.addInformation ("WARNING: Cases didn't cover: " ^ message)
                      else
                        raise (Coverage.Error (Syntax.Loc.ghost, Coverage.NoCover message))));

          if !Coverage.enableCoverage then
            (if !Debug.chatter != 0 then
                printf "\n## Coverage checking done: %s  ##\n" file_name);
          if !Subord.dump then begin
            Subord.dump_subord();
            (* Subord.dump_typesubord() *)
          end;
          print_newline ();
          Logic.runLogic ();
          if not (Holes.none ()) && !Debug.chatter != 0 then begin
            printf "\n## Holes: %s  ##" file_name;
            Holes.printAll ()
          end;
          if not (Lfholes.none ()) && !Debug.chatter != 0 then begin
            printf "\n\n## LF Holes: %s  ##" file_name;
            Lfholes.printAll ()
          end;
          if !Typeinfo.generate_annotations then
            Typeinfo.print_annot file_name;
          if !Locs.gen_loc_info then begin
            List.iter Loctesting.store_locs sgn;
            Locs.print_loc_info file_name end;
          print_newline();
          if !Monitor.on || !Monitor.onf then
            Monitor.print_timer ()
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
        | _ -> bailout "Wrong number of command line arguments."
    in
    printf "%s" (Error.getInformation());
    exit status_code

let _ = Format.set_margin 80
let _ = main ()
