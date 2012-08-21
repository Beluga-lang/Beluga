open Core
open Format

module Options = struct
  let readline = ref true
end

let bailout msg =
  fprintf Format.err_formatter "%s\n" msg;
  exit 2

let usage () =
  let options =
      "    -help         this usage message\n"
    ^ "    (+|-)readline (enable|disable) readline support (requires rlwrap installed)\n"
  in
  fprintf Format.err_formatter
    "Usage: %s [options]\noptions:\n%s"
    Sys.argv.(0) options;
  exit 2

let process_option arg rest = match arg with
  | "-help" -> usage ()
  | "+readline" -> Options.readline := true; rest
  | "-readline" -> Options.readline := false; rest
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

let rec loop ppf =
  begin
    try
      fprintf ppf "# ";
      pp_print_flush ppf ();
      let input = read_line () in
      let sgn = Parser.parse_string ~name:"<interactive>" ~input:input Parser.sgn_eoi in
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
