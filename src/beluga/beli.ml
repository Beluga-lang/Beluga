open Format
  
module Options = struct
	let readline = ref false
  let ledit = ref true
	let emacs = ref false
	let interrupt_count = ref 0
end

exception Invalid_Arg

let process_option arg rest = match arg with
  | "+readline" -> Options.readline := true; Options.ledit := false; rest
  | "-ledit"    -> Options.ledit := false; rest
  | "-emacs" -> Options.emacs := true; Typeinfo.generate_annotations := true;
		Debug.chatter := 0; rest
  | _ -> raise Invalid_Arg

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
  if not !Options.emacs then Interactive.whale ();
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
              let sgn'= begin match Recsgn.recSgnDecls sgn with
		| sgn', None -> sgn'
		| _, Some _ ->
		  raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
	      end
	      in
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

let run args =
  let ppf = Format.std_formatter in
  let files = process_options args in
  let _ = Debug.pipeDebug := true in

  (* If readline wrapper exists, replace current process with a call
     to it and ask it to run us, wrapped. Line editing is then
     available. Otherwise don't bother. *)
  if !Options.ledit && (not !Options.emacs) then begin
    try
      let (_,pre, post) = Array.fold_right 
        (fun x (f, pre, post) -> 
            if f then (f, x::pre, post)
            else if x = "-I" then (true, pre, post) 
            else (false, pre, x::post)) Sys.argv (false, [], []) in
      let args = "ledit" :: (pre @ ("-I"::"-ledit"::post)) in
      Unix.execvp "ledit" (Array.of_list args)
    with Unix.Unix_error _ -> ()
  end else if !Options.readline && (not !Options.emacs) then begin
    try
      let (_,pre, post) = Array.fold_right 
        (fun x (f, pre, post) -> 
            if f then (f, x::pre, post)
            else if x = "-I" then (true, pre, post) 
            else (false, pre, x::post)) Sys.argv (false, [], []) in
      let args = "rlwrap" :: (pre @ ("-I"::"-ledit"::post)) in
      Unix.execvp "rlwrap" (Array.of_list args)
    with Unix.Unix_error _ -> ()
  end;

  if List.length files = 1 then
    try
      let arg = List.hd files in
      let sgn = Parser.parse_file ~name:arg Parser.sgn in
      let sgn' = begin match Recsgn.recSgnDecls sgn with
	| sgn', None -> sgn'
	| _, Some _ ->
	  raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
      end 
      in
        if !Debug.chatter <> 0 then
          List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn';
      fprintf ppf "The file has been successfully loaded.\n"
    with
    |Failure _ -> fprintf ppf "Please provide the file name\n" ;
  else begin if List.length files > 1 then fprintf ppf "Please supply only 1 file" end;

  if !Debug.pipeDebug && Sys.file_exists (!Debug.filename ^ ".out") then begin
    let x = ref 1 in
    while Sys.file_exists (!Debug.filename ^ "(" ^ (string_of_int !x) ^ ").out") do
      incr x
    done ;
    Debug.filename := (!Debug.filename ^ "(" ^ (string_of_int !x) ^ ")") ;
  end;

  init_repl ppf;
  Command.print_usage ppf ;
  loop ppf
