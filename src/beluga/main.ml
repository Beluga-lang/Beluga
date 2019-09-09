(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Beluga
open Printf
module P = Parser

let dprintf, _, _ = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

let bailout msg =
  fprintf stderr "%s\n" msg;
  exit 2

let usage () =
  let options =
          "    +d                    Turn all debugging printing on - note that in interactive mode\n"
        ^ "                              debugging information is piped to 'debug.out'\n"
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
  in
  fprintf stderr "Beluga version %s\n" (Version.get ());
  fprintf stderr
    "Usage: %s [options] file.(bel|cfg)\noptions:\n%s"
    Sys.argv.(0) options;
  exit 2

let externall = ref false

module PC = Printer.Control

let process_option arg rest =
  let with_arg_for arg k =
    match rest with
    | [] -> bailout (arg ^ " requires an argument")
    | a :: rest -> k a rest
  in
  match arg with
  (* these strings must be lowercase *)
  | "+d" -> Debug.enable (); Printexc.record_backtrace true; rest
  | "+ext" -> externall := true; rest
  | "-s=debruijn" -> PC.substitutionStyle := PC.DeBruijn; rest
  | "+implicit" -> PC.printImplicit := true; rest
  | "+t" -> Monitor.on := true; rest
  | "+tfile" -> Monitor.onf := true; rest
  | "+printSubord" -> Subord.dump := true; rest
  | "-print" -> Debug.chatter := 0; rest
  | "+print" -> Debug.chatter := 2; rest
  | "-width" ->
     with_arg_for "-width"
       begin fun arg rest ->
       let width =
         try int_of_string arg
         with Failure _ -> bailout "-width requires a numeric argument"
       in
       Format.set_margin (max 40 width);
       rest
       end
  | "-logic" -> Logic.Options.enableLogic := false ; rest
  | "+test" -> Error.Options.print_loc := false; Debug.chatter := 0; Sexp.testing := true ; rest
  | "+realNames" -> Store.Cid.NamedHoles.usingRealNames := true; rest
  | "+htmltest" -> Html.genHtml := true; Html.filename := "/dev/null"; rest 
  | "+html" | "+HTML" -> Html.genHtml := true; rest
  | "+sexp" -> Sexp.enabled := true ; rest
  | "-css"  | "-CSS"  -> Html.css := Html.NoCSS; rest
  | "+cssfile" -> 
     with_arg_for "+cssfile"
       (fun arg rest -> Html.css := Html.File arg; rest)
  | "+annot"      -> Typeinfo.generate_annotations := true; rest
  | "-I" ->
     begin
       try Beli.run rest
       with Beli.Invalid_Arg -> usage ()
     end
  | _ ->
     usage ()

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      let first = String.get arg 0 in
        if first = '-' || first = '+' then
          process_options (process_option arg rest)
        else  (* reached end of options: return this and remaining arguments *)
          arg :: rest

exception SessionFatal

let per_file file_name =
  let chatter f = if !Debug.chatter <> 0 then f () in
  let abort_session () = raise SessionFatal in
  try
    let sgn =
      Parser.(Runparser.parse_file file_name (only sgn) |> extract)
    in
    (* If the file starts with a global pragma then process it now. *)
    let sgn = Recsgn.apply_global_pragmas sgn in
    if !externall then
      begin
        chatter
          (fun _ -> printf "\n## Pretty-printing of the external syntax : ##\n");
        let module P = Pretty.Ext.DefaultPrinter in
        P.fmt_ppr_sgn Format.std_formatter sgn
      end;
    chatter (fun _ -> printf "\n## Type Reconstruction: %s ##\n" file_name);
    let sgn', leftoverVars = Recsgn.recSgnDecls sgn in
    let _ = Store.Modules.reset () in
    if !Debug.chatter > 1 then
      begin
        let module P = Pretty.Int.DefaultPrinter in
        List.iter (P.fmt_ppr_sgn_decl Format.std_formatter) sgn'
      end;
    
    if !Debug.chatter <> 0 then
      printf "\n## Type Reconstruction done: %s  ##\n" file_name;
    
    Coverage.iter
      begin function
        | Coverage.Success -> ()
        | Coverage.Failure message ->
           if !Coverage.warningOnly then
             Error.addInformation ("WARNING: Cases didn't cover: " ^ message)
           else
             raise (Coverage.Error (Syntax.Loc.ghost, Coverage.NoCover message))
      end;
    
    if !Coverage.enableCoverage && !Debug.chatter <> 0 then
      printf "\n## Coverage checking done: %s  ##\n" file_name;
    
    if !Subord.dump then begin
        Subord.dump_subord();
        (* Subord.dump_typesubord() *)
      end;
    print_newline () ;
    Logic.runLogic ();
    if not (Holes.none ()) && !Debug.chatter != 0 then
      begin
        let open Format in
        fprintf std_formatter
          "@[<v>## Holes: %s  ##@,@[<v>%a@]@]@."
          file_name
          (pp_print_list Holes.print) (Holes.list ());
      end;
    begin match leftoverVars with
    | None -> ()
    | Some vars ->
      let open Format in
      if !Debug.chatter <> 0 then
        fprintf std_formatter "@[<v>## Leftover variables: %s  ##@,  @[%a@]@]@."
          file_name
          Recsgn.fmt_ppr_leftover_vars vars;
      raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
    end;
    if !Typeinfo.generate_annotations then
      Typeinfo.print_annot file_name;
    print_newline();
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
    dprintf
      (fun p ->
        p.fmt "Backtrace: %s" (Printexc.get_backtrace ()));
    output_string stderr (Printexc.to_string e);
    abort_session ()

let main () =
  let args   = List.tl (Array.to_list Sys.argv) in
  let files = process_options args in
  Debug.init None;
  let status_code =
    match files with
    | [file] ->
       begin
         try
           List.iter per_file (Cfg.process_file_argument file) ; 0
         with SessionFatal -> 1
       end
    | _ -> bailout "Wrong number of command line arguments."
  in
  printf "%s" (Error.getInformation ());
  exit status_code

let _ =
  Format.set_margin 80;
  if Array.length Sys.argv < 2 then
    usage ()
  else
    main ()
