open Core
open Format

module Options = struct
  let readline = ref true
  let emacs = ref false
  let debug = ref false
  let interrupt_count = ref 0
end

let whale ppf = fprintf ppf
";,,,,,,,,,,,,,,,,,'+++++++++++:,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,,,,:#'........```.,'#+;,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,,,+'..............````.'#',,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,,+,...................```.'+;,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,+:........................``,+',,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,+.............................,+;,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,+................................:++,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,#...................................'++;,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,#......................................,'+++;,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,#...........................................,;++++':,,,,,,,,,`@\n\
;,,,,,,,,,,#..................................................,;+++#+'::`@\n\
;,,,,,,,,,,#......................................................```.,;`@\n\
;,,,,,,,,,,+..........................................................`` @\n\
;,,,,,,,,,,#............................................................@\n\
;,,,,,,,,,,+............................................................@\n\
;,,,,,,,,,#.............................................................@\n\
;,,,,,,,,+''#######+;...................#'.............................@\n\
;,,,,,,,,#,..........+#,................##'.............................@\n\
;,,,,,,,,#.............;#'..............................................@\n\
;,,,,,,,,:'...............'+##+'........................................@\n\
;,,,,,,,,,+,............................................................@\n\
;,,,,,,,,,,#............................................................@\n\
;,,``,,,,,,::....,,...........`.`........`........`.......``.......``...@\n\
;`....`,,,.....`........`...``...``..``....`..``....`...`....`...`....`.@\n\
``````````````;;.`````````````.;;```````````````````````````````````````@\n\
``````````````;;.`````````````.;;```````````````````````````````````````@\n\
``````````````;;..:.````.::```.;;``,,``,,```,:`.,.``,::,````````````````@\n\
``````````````;;;;;;:``;;;;;.`.;;`.;;``;;``;;;;;;.`:;;;;;```````````````@\n\
``````````````;;;``;;`,;:``;;``;;`.;;``;;``;;``;;.`````;;```````````````@\n\
``````````````;;.``;;`;;;;;;;``;;`.;;``;;`.;;``;;.`.;;;;;.``````````````@\n\
``````````````;;,``;;`;;.``````;;`.;;``;;`.;;``;;.`;;``;;.``````````````@\n\
``````````````;;;.;;;`:;;``.:``;;``;;,;;;``;;;;;;.`;;`.;;.``````````````@\n\
``````````````;;;;;;```;;;;;;``;;``:;;;;;``.;;;;;.`;;;;;;.``````````````@\n\
%s`;;@\n\
%s;;;;;,@\n" 
("                                              ")
("                                           ")




let bailout msg =
  fprintf Format.err_formatter "%s\n" msg;
  exit 2

let usage () =
  let options =
      "    -help         this usage message\n"
    ^ "    (+|-)readline (enable|disable) readline support (requires rlwrap installed)\n"
    ^ "    -emacs        mode used to interact with emacs (not recommended in command line)\n"
    ^ "    +d            Pipe debugging information into '"^ !Debug.filename ^ ".out" ^ "'\n"
  in
    fprintf Format.err_formatter
      "Usage: %s [options]\noptions:\n%s"
      Sys.argv.(0) options;
    exit 2

let process_option arg rest = match arg with
  | "-help" -> usage ()
  | "+readline" -> Options.readline := true; rest
  | "-readline" -> Options.readline := false; rest
  | "-emacs" -> Options.emacs := true; Debug.chatter := 0; rest
  | "+d" -> Options.debug := true; Debug.pipeDebug := true; Debug.showAll (); Printexc.record_backtrace true; rest
  | _ -> usage ()

let rec process_options = function
  | [] -> []
  | arg :: rest ->
    let first = String.get arg 0 in
    if first = '-' || first = '+' then
      process_options (process_option arg rest)
    else
      (* reached end of options: return this and remaining arguments *)
      arg :: rest

let init_repl ppf =
  fprintf ppf "        Beluga (interactive) version %s@.@." Version.beluga_version;
  if not !Options.emacs then whale ppf;
  Sys.catch_break true

let rec loop ppf =
  begin
    try
      if !Options.emacs then ()
      else fprintf ppf "# ";
      pp_print_flush ppf ();
      let input = read_line () in
        match Command.is_command input with
          | `Cmd cmd ->
            Command.do_command ppf cmd
          | `Input input ->
              let sgn = Parser.parse_string ~name:"<interactive>" ~input:input Parser.sgn in
              let sgn' = Recsgn.recSgnDecls sgn in
              if !Debug.chatter <> 0 then
                List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn'
    with
      | End_of_file -> exit 0
      | Sys.Break -> 
          if !Options.interrupt_count = 2 then begin fprintf ppf "@\n@."; exit 0 end else begin
          incr Options.interrupt_count;
          fprintf ppf "Interrupted (press %d more times to quit).@." (3 - !Options.interrupt_count) end
      | err ->
        output_string stderr (Printexc.to_string err);
        flush stderr
  end;
  loop ppf

let main () =
  let ppf = Format.std_formatter in
  let files = process_options (List.tl (Array.to_list Sys.argv)) in
  

  (* If readline wrapper exists, replace current process with a call
     to it and ask it to run us, wrapped. Line editing is then
     available. Otherwise don't bother. *)
  if !Options.readline && (not !Options.emacs) then begin
    try
      let args = if !Options.debug then ("+d"::files) else files in
      Unix.execvp "ledit" (Array.append [| "ledit"; Sys.executable_name; "-readline" |] (Array.of_list args))
    with Unix.Unix_error _ -> ()
  end;

  if List.length files = 1 then
    try
      let arg = List.hd files in
      let sgn = Parser.parse_file ~name:arg Parser.sgn in
      let sgn' = Recsgn.recSgnDecls sgn in
        if !Debug.chatter <> 0 then
          List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn';
      fprintf ppf "The file has been successfully loaded.\n"
    with
    |Failure _ -> fprintf ppf "Please provide the file name\n" ;
  else begin if List.length files > 1 then fprintf ppf "Please supply only 1 file" end;

  if !Options.debug && Sys.file_exists (!Debug.filename ^ ".out") then begin
    let x = ref 1 in
    while Sys.file_exists (!Debug.filename ^ "(" ^ (string_of_int !x) ^ ").out") do
      incr x
    done ;
    Debug.filename := (!Debug.filename ^ "(" ^ (string_of_int !x) ^ ")") ;
  end;

  init_repl ppf;
  Command.print_usage ppf ;
  loop ppf

let _ = Format.set_margin 80
let _ = main ()
