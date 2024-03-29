(** Core / Frontend Driver

    @author Joshua Dunfield *)

open Support
open Beluga
module F = Fun

let bailout msg =
  Format.fprintf Format.err_formatter "%s@." msg;
  exit 2

let usage () =
  let options =
          "    +d                    Turn all debugging printing on - note that in interactive mode\n"
        ^ "                              debugging information is piped to 'debug.out'\n"
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
        ^ "    +html                 Generate an HTML page of the source Beluga code\n"
        ^ "    +annot                Generate a .annot file for use in emacs\n"
        ^ "    -I [beli-options]     Invoke interactive (Beli) mode with an optional path to a Beluga signature to load\n"
        ^ "                          beli-options: \n"
        ^ "                              -emacs        mode used to interact with emacs (not recommended in command line)\n"
  in
  Format.fprintf Format.err_formatter "Beluga version %s\n" (Version.get ());
  Format.fprintf Format.err_formatter
    "Usage: %s [options] file.(bel|cfg)\noptions:\n%s"
    Sys.argv.(0) options;
  exit 2

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
  | "-s=debruijn" -> PC.substitutionStyle := PC.DeBruijn; rest
  | "+implicit" -> PC.printImplicit := true; rest
  | "+t" -> Monitor.on := true; rest
  | "+tfile" -> Monitor.onf := true; rest
  | "+printSubord" -> Subord.dump := true; rest
  | "+test" -> Chatter.level := 0; Syncom.Error.disable_colored_output (); rest
  | "-print" -> Chatter.level := 0; rest
  | "+print" -> Chatter.level := 2; rest
  | "+html" -> Options.Html.enabled := true; rest
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
  | "+annot" ->
     Typeinfo.generate_annotations := true;
     rest
  | "-I" ->
     begin
       try Beli.run rest
       with Beli.Invalid_argument -> usage ()
     end
  | _ ->
     usage ()

let is_option argument =
  let first = String.get argument 0 in
  first = '-' || first = '+'

let rec process_options = function
  | [] -> []
  | arg :: rest ->
      if is_option arg then process_options (process_option arg rest)
      else
        (* reached end of options: return this and remaining arguments *)
        arg :: rest

let main () =
  let args = List.tl (Array.to_list Sys.argv) in
  let files = process_options args in
  Debug.init Option.none;
  (match files with
  | [ file ] ->
      ignore (Load.load_fresh file)
  | _ -> bailout "Wrong number of command line arguments.");
  Format.fprintf Format.std_formatter "%s@?" (Beluga.Coverage.get_information ())

let () =
  Format.set_margin 80;
  if Array.length Sys.argv <= 1 then usage ()
  else
    try main () with
    | e ->
        prerr_string (Printexc.to_string e);
        exit 1
