(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Core / Frontend Driver

    @author Joshua Dunfield
*)

open Beluga
open Printf
module P = Parser
module F = Support.Misc.Function

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
        ^ "    +html              Generate an html page of the source code using default CSS\n"
        ^ "    +htmltest          Run HTML mode on file, but do not create final HTML page\n"
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
  | "+d" -> Debug.enable (); rest
  | "+ext" -> Options.Testing.print_external_syntax := true; rest
  | "-s=debruijn" -> PC.substitutionStyle := PC.DeBruijn; rest
  | "+implicit" -> PC.printImplicit := true; rest
  | "+t" -> Monitor.on := true; rest
  | "+tfile" -> Monitor.onf := true; rest
  | "+printSubord" -> Subord.dump := true; rest
  | "+test" | "-print" -> Chatter.level := 0; rest
  | "+print" -> Chatter.level := 2; rest
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
  | "+htmltest" ->
     Html.generate := true;
     Html.filename := None;
     rest
  | "+html" | "+HTML" -> Html.generate := true; rest
  | "-css"  | "-CSS"  -> Html.css := `none; rest
  | "+cssfile" ->
     with_arg_for "+cssfile"
       begin fun arg rest ->
       Html.css := `file arg;
       rest
       end
  | "+annot" ->
     Typeinfo.generate_annotations := true;
     rest
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

let main () =
  let args   = List.tl (Array.to_list Sys.argv) in
  let files = process_options args in
  Debug.init None;
  begin match files with
  | [file] ->
     let _ = Load.load Format.std_formatter file in
     ()
  | _ -> bailout "Wrong number of command line arguments."
  end;
  printf "%s" (Error.getInformation ())

let _ =
  Format.set_margin 80;
  if Array.length Sys.argv < 2 then
    usage ()
  else
    try
      main ()
    with
    | e ->
       prerr_string (Printexc.to_string e);
       exit 1
