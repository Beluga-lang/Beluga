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
        ^ "    +print                Turn printing on\n"
        ^ "    -width nnn            Set output width to nnn (default 86; minimum 40)\n"
        ^ "    -logic                Turn off logic programming engine\n"
        ^ "    +test                 Make output suitable for test harness. Implies -print\n"
        ^ "    +realNames         Print holes using real names\n"
        ^ "    +html              Generate an html page of the source code using default CSS\n"
        ^ "    +htmltest          Run HTML mode on file, but do not create final HTML page\n"
        ^ "    +sexp              Dump the elaborated code using S-expressions\n"
        ^ "    -css               Generate the html of the source code without CSS or <body> tags -- for inserting HTML into a webpage\n"
        ^ "    +cssfile [file]    Specify css file to link to from generated HTML page\n"
        ^ "    +annot                Generate a .annot file for use in emacs\n"
        ^ "    +locs                 Output location information (for testing)\n"
        ^ "    -I [beli-options]     Invoke interactive (Beli) mode with option path to interactive mode (default is bin/beli) \n"
        ^ "                          beli-options: \n"
        ^ "                              -emacs        mode used to interact with emacs (not recommended in command line)\n"
        ^ "                              -readLine     disabe readline support using rlwrap \n"
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
  | "+printSubord" -> Subord.dump := true; rest
  | "-print" -> Debug.chatter := 0; rest
  | "+print" -> Debug.chatter := 2; rest
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
  | "+test" -> Error.Options.print_loc := false; Debug.chatter := 0; Sexp.testing := true ; rest
  | "+realNames" -> Store.Cid.NamedHoles.usingRealNames := true; rest
  | _ when (String.lowercase arg = "+htmltest") -> Html.genHtml := true; Html.filename := "/dev/null"; rest
  | "+html" | "+HTML" -> Html.genHtml := true; rest
  | "+sexp" -> Sexp.enabled := true ; rest
  | "-css"  | "-CSS"  -> Html.css := Html.NoCSS; rest
  | _ when (String.lowercase arg = "+cssfile") ->
      begin match rest with
      | arg::rest when arg.[0] <> '-' && arg.[0] <> '+' ->
          Html.css := Html.File arg; rest
      | _ -> bailout "-cssfile requires an argument"
      end
  | "+annot"      -> Typeinfo.generate_annotations := true; rest
  | "-I" -> begin
      try Beli.run rest
      with Beli.Invalid_Arg -> usage () end
  | _ -> usage ()

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      let first = String.get arg 0 in
        if first = '-' || first = '+' then
          process_options (process_option arg rest)
        else  (* reached end of options: return this and remaining arguments *)
          arg :: rest

exception SessionFatal

open Cfg

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
        let sgn', leftoverVars = Recsgn.recSgnDecls sgn in
        let _ = Store.Modules.reset () in
        if !Debug.chatter > 1 then begin
          List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn' end
        else
          ();

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
          print_newline () ;
          Logic.runLogic ();
          if not (Holes.none ()) && !Debug.chatter != 0 then begin
            printf "\n## Holes: %s  ##" file_name;
            Holes.printAll ()
          end;
          if not (Lfholes.none ()) && !Debug.chatter != 0 then begin
            printf "\n\n## LF Holes: %s  ##" file_name;
            Lfholes.printAll ()
          end;
          begin match leftoverVars with
            | None -> ()
            | Some vars ->
              if !Debug.chatter != 0 then begin
                printf "\n## Left over variables ##" ;
                Recsgn.print_leftoverVars vars
              end ;
              raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
          end ;
          if !Typeinfo.generate_annotations then
            Typeinfo.print_annot file_name;
          (* print_newline(); *)
          if !Monitor.on || !Monitor.onf then
            Monitor.print_timer () ;
          if !Html.genHtml then begin
            Html.generatePage file_name
          end;
          (* If requested, dump the elaborated program as S-expressions *)
          if !Sexp.enabled then
            begin
              let sexp_file_name = file_name ^ ".sexp" in
              let oc = open_out sexp_file_name in
              Sexp.Printer.sexp_sgn_decls (Format.formatter_of_out_channel oc) sgn' ;
              flush oc ; close_out oc ;
              if !Sexp.testing == false then
                printf "\n## Dumped AST to: %s ##\n" sexp_file_name
            end
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
              List.iter per_file (process_file_argument file) ; 0
            with SessionFatal -> 1
          end
        | _ -> bailout "Wrong number of command line arguments."
    in
    printf "%s" (Error.getInformation());
    exit status_code

let _ = Format.set_margin 80
let _ = main ()
