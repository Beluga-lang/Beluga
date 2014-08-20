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
          "    +d                    Turn all debugging printing on - note that in interactive mode\n"
        ^ "                              debugging information is piped to '"^ !Debug.filename ^ ".out" ^ "'\n"
        ^ "    +ext                  Print external syntax before reconstruction\n"
        ^ "    -s=debruijn           Print substitutions in deBruijn-ish style (when debugging Beluga)\n"
        ^ "    +implicit             Print implicit arguments\n"
        ^ "    +t                    Print timing information\n"
        ^ "    +tfile                Print timing information to file \"time.txt\"\n"
        ^ "    +printSubord          Print subordination relations (experimental)\n"
        ^ "    -print                Turn printing off\n"
        ^ "    -width nnn            Set output width to nnn (default 86; minimum 40)\n"
        ^ "    -logic                Turn off logic programming engine\n"
        ^ "    +test                 Make output suitable for test harness. Implies -print\n"
        ^ "    +realNames         Print holes using real names\n"
        ^ "    +html              Generate an html page of the source code using default CSS\n"
        ^ "    +htmltest          Run HTML mode on file, but do not create final HTML page\n"
        ^ "    -css               Generate the html of the source code without CSS or <body> tags -- for inserting HTML into a webpage\n"
        ^ "    +cssfile [file]    Specify css file to link to from generated HTML page\n"
        ^ "    +annot                Generate a .annot file for use in emacs\n"
        ^ "    +locs                 Output location information (for testing)\n"
        ^ "    -I [beli-options]     Invoke interactive (Beli) mode with option path to interactive mode (default is bin/beli) \n"
        ^ "                          beli-options: \n"
        ^ "                              -emacs        mode used to interact with emacs (not recommended in command line)\n"
        ^ "                              -readLine     disabe readline support using rlwrap \n"
        ^ "    +n                    Print line numbers\n"
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
  | "+ext" -> externall := true; rest
  | "-s=debruijn" -> PC.substitutionStyle := PC.DeBruijn; rest
  | "+implicit" -> PC.printImplicit := true; rest
  | "+t" -> Monitor.on := true; rest
  | "+tfile" -> Monitor.onf := true; rest
  | "+printsubord" -> Subord.dump := true; rest
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
  | "-logic" -> Logic.Options.enableLogic := false ; rest
  | "+test" -> Error.Options.print_loc := false; Debug.chatter := 0; rest
  | "+realNames" -> Store.Cid.NamedHoles.usingRealNames := true; rest
  | _ when (String.lowercase arg = "+htmltest") -> Html.genHtml := true; Html.filename := "/dev/null"; rest
  | "+html" | "+HTML" -> Html.genHtml := true; rest
  | "-css"  | "-CSS"  -> Html.css := Html.NoCSS; rest
  | _ when (String.lowercase arg = "+cssfile") -> 
      begin match rest with
      | arg::rest when arg.[0] <> '-' && arg.[0] <> '+' ->
          Html.css := Html.File arg; rest
      | _ -> bailout "-cssfile requires an argument"
      end
  | "+annot"      -> Typeinfo.generate_annotations := true; rest
  | "+locs"       -> Locs.gen_loc_info := true; rest
  | "-I" -> begin
      try Beli.run rest
      with Beli.Invalid_Arg -> usage () end
  | "+n" | "+N"  -> Pretty.setup_linenums (); rest
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
        (* If the file starts with a global pragma then process it now. *)
        let rec extract_global_pragmas = function
          | Synext.Sgn.GlobalPragma(_, Synext.Sgn.NoStrengthen) :: t -> begin Lfrecon.strengthen := false; extract_global_pragmas t end
          | Synext.Sgn.GlobalPragma(_, Synext.Sgn.Coverage(opt))::t -> begin 
            Coverage.enableCoverage := true;
            begin match opt with | `Warn -> Coverage.warningOnly := true | `Error -> () end;
            extract_global_pragmas t end
          | l -> l in
        let sgn = extract_global_pragmas sgn in
        if !externall then begin
          if !Debug.chatter != 0 then
            printf "\n## Pretty-printing of the external syntax : ##\n";
          List.iter Pretty.Ext.DefaultPrinter.ppr_sgn_decl sgn
        end;
        if !Debug.chatter <> 0 then
          printf "\n## Type Reconstruction: %s ##\n" file_name;
        let sgn' = Recsgn.recSgnDecls sgn in
        let _ = Store.Modules.reset () in
        let _ = Pretty.line_num := 1 in
        if !Debug.chatter <> 0 then
          List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn';
        Pretty.printing_nums := false;
        if !Debug.chatter <> 0 then
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
            Monitor.print_timer () ;
          if !Html.genHtml then begin
            if !Html.filename <> "/dev/null" then
              let l = String.length file_name in 
              Html.filename := ((String.sub file_name 0 (l-3)) ^ "html");
            Html.generatePage () 
          end;
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
