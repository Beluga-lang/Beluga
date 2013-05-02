open Core
open Format
open ExtString.String

module Options = struct
  let readline = ref true
  let emacs = ref false
end

let bailout msg =
  fprintf Format.err_formatter "%s\n" msg;
  exit 2

let usage () =
  let options =
      "    -help         this usage message\n"
    ^ "    (+|-)readline (enable|disable) readline support (requires rlwrap installed)\n"
    ^ "    -emacs        mode used to interact with emacs (not recommended in command line)"
  in
    fprintf Format.err_formatter
      "Usage: %s [options]\noptions:\n%s"
      Sys.argv.(0) options;
    exit 2

let cmd_usage ppf =
  let options =
      "    chatteron           Turn on the chatter\n"
    ^ "    chatteroff          Turn off the chatter\n"
    ^ "    load filename       Load the file \"filename\" into the interpreter\n"
    ^ "    printhole i         Print all the information of the i-th hole\n"
    ^ "    lochole i           Print the location of the i-th hole\n"
    ^ "    countholes          Print the total number of holes\n"
    ^ "    printfun funname    Print the specified function\n"
  in
    fprintf ppf
      "Usage: %%: [command]\ncommand:\n%s"
      options

let process_option arg rest = match arg with
  | "-help" -> usage ()
  | "+readline" -> Options.readline := true; rest
  | "-readline" -> Options.readline := false; rest
  | "-emacs" -> Options.emacs := true; Debug.chatter := 0; rest
  | _ -> usage ()

let rec process_options = function
  | [] -> []
  | arg :: rest ->
    let first = String.get arg 0 in
    if first = '-' or first = '+' then
      process_options (process_option arg rest)
    else
      (* reached end of options: return this and remaining arguments *)
      arg :: rest

let init_repl ppf =
  fprintf ppf "        Beluga (interactive) version %s@.@." Version.beluga_version;
  Sys.catch_break true

let is_command (str:string) =
  let str' = strip str in
  let l = String.length str' in
    if l > 1 && String.sub str' 0 2 = "%:" then
      let (_, cmd) = ExtString.String.split str' ":" in
        `Cmd (strip cmd)
    else
      `Input str

let do_command ppf str =
  begin
    match str with
      | "countholes" -> Holes.printNumHoles ()
      | "chatteron" -> Debug.chatter :=1; fprintf ppf "\nThe chatter is on now.\n"
      | "chatteroff" -> Debug.chatter :=0; fprintf ppf "\nThe chatter is off now.\n"
      | _ ->
        try
          let (cmd, arg) = split str " " in
          match cmd with
            | "load" ->
              let sgn = Parser.parse_file ~name:arg Parser.sgn in
              Recsgn.recSgnDecls sgn;
              fprintf ppf "\nThe file has been successfully loaded.\n"
            | "printhole" ->
	      if not (Holes.none ()) then Holes.printOneHole (to_int arg)
	      else fprintf ppf "\nThere is no hole at all!!\n"
            | "lochole" -> 
	      if not (Holes.none ()) then Holes.printHolePos (to_int arg) 
	      else fprintf ppf "\nThere is no hole at all!!\n"
            | _ -> fprintf ppf "Invalid command.@.\n"; cmd_usage ppf
        with
          | ExtString.Invalid_string -> fprintf ppf "Invalid command.@.\n"; cmd_usage ppf
  end

let rec loop ppf =
  begin
    try
      if !Options.emacs then ()
      else fprintf ppf "# ";
      pp_print_flush ppf ();
      let input = read_line () in
        match is_command input with
          | `Cmd cmd ->
              do_command ppf cmd
          | `Input input ->
              let sgn = Parser.parse_string ~name:"<interactive>" ~input:input Parser.sgn in
                Recsgn.recSgnDecls sgn
    with
      | End_of_file -> exit 0
      | Sys.Break -> fprintf ppf "Interrupted.@."
      | err ->
        output_string stderr (Printexc.to_string err);
        flush stderr
  end;
  loop ppf

let main () =
  let ppf = Format.std_formatter in
  let args = process_options (List.tl (Array.to_list Sys.argv)) in
  if args <> [] then usage ();

  (* If readline wrapper exists, replace current process with a call
     to it and ask it to run us, wrapped. Line editing is then
     available. Otherwise don't bother. *)
  if !Options.readline then begin
    try
      Unix.execvp "rlwrap" [| "rlwrap"; Sys.executable_name; "-readline" |]
    with Unix.Unix_error _ -> ()
  end;

  init_repl ppf;
  loop ppf

let _ = Format.set_margin 80
let _ = main ()
