open Support

module B = Beluga

module PC = B.Printer.Control

module Error = struct
  type t =
    | OptparserError of Optparser.Builder.opt_parser_error
    | InvalidIncomplete
    | InvalidStop
    | DanglingArguments
      of string list

  exception E of t
  let throw e = raise (E e)

  open Format
  let format_error ppf = function
    | OptparserError e ->
       let open Optparser.Builder in
       begin match e with
       | MissingMandatory name ->
          fprintf ppf "Mandatory option %s is missing.@."
            name
       | InvalidArgLength (name, exp, act) ->
          fprintf ppf "Option %s requires %d arguments. Got %d.@."
            name
            exp
            act
       | ArgReaderFailure name ->
          fprintf ppf "%s"
            name
       | NotAnOption name ->
          fprintf ppf "%s is not an option"
            name
       end
    | InvalidIncomplete ->
       fprintf ppf "--incomplete can be specified only after --test@."
    | InvalidStop ->
       fprintf ppf "%a@."
         pp_print_string "--stop can only be specified with --test and without --incomplete"
    | DanglingArguments args ->
       fprintf ppf "Unexpected remaining command-line arguments:@,  @[%a@]@."
         (pp_print_list ~pp_sep: Fmt.comma
            (fun ppf -> fprintf ppf "%s"))
         args
end

(* Register error formatting. *)
let _ =
  let open Error in
  B.Error.register_printer'
    begin fun e ->
    match e with
    | E e ->
       Some (B.Error.print (fun ppf -> format_error ppf e))
    | _ -> None
    end

type test_kind = [ `incomplete | `complete ]
type test_file = string * test_kind

(** The command-line options specified to Harpoon. *)
type ('a, 'b) t =
  { path : 'a (* the path of the signature file to load, could be a cfg *)
  ; all_paths : 'b (* the list of paths resolved from the signature file to load *)
  ; test_file : test_file option (* the harpoon test file to load *)
  ; test_start : int option (* the first line from which the harpoon test file is considered as input *)
  ; test_stop : [ `stop | `go_on ] (* whether to stop a test script if there's an error *)
  ; load_holes : bool
  ; save_back : bool
  }

type elaborated_t =
  (string, string list) t
type valid_t =
  (string, unit) t
type parsed_t =
  (string, unit) t

let options_spec : valid_t Optparser.Builder.t =
  let handle_debug () =
    B.Debug.enable ();
    Printexc.record_backtrace true
  in
  let handle_implicit () =
    PC.printImplicit := true
  in
  let handle_help pp_print_help =
    let usage_string =
      Printf.sprintf "Usage: %s <mandatory options> <other options>"
        Sys.argv.(0)
    in
    Format.eprintf "%a"
      (pp_print_help usage_string) ();
    exit 1
  in
  let open Optparser.Builder in
  begin fun path test_opt test_kind test_start test_stop no_load_holes no_save_back ->
  let test_file =
    match test_opt with
    | Some test -> Some (test, test_kind)
    | None when test_kind = `incomplete ->
       Error.(throw InvalidIncomplete)
    | None -> None
  in
  { path
  ; all_paths = ()
  ; test_file
  ; test_start
  ; test_stop
  ; load_holes = not no_load_holes
  ; save_back = not no_save_back
  }
  end
  <$ string_opt1
       [ OptSpec.long_name "sig"
       ; OptSpec.meta_vars ["path"]
       ; OptSpec.help_msg
           "specify the input signature"
       ]
  <& opt1 (fun s -> Maybe.pure (Maybe.pure s))
       [ OptSpec.long_name "test"
       ; OptSpec.meta_vars ["path"]
       ; OptSpec.optional None
       ; OptSpec.help_msg
           ("specify the test input file that is used as "
            ^ "a test input instead of stdin user input"
           )
       ]
  <& (switch_opt
        [ OptSpec.long_name "incomplete"
        ; OptSpec.help_msg
            ("mark the test input file as incomplete so that stdin user "
             ^ "input is followed after the test input "
             ^ "(valid only when --test option is provided)"
            )
        ]
      $> fun b -> if b then `incomplete else `complete
     )
  <& opt1 (fun s -> Option.map Maybe.pure (int_of_string_opt s))
       [ OptSpec.long_name "test-start"
       ; OptSpec.meta_vars ["number"]
       ; OptSpec.optional None
       ; OptSpec.help_msg
           "specify the first line of test file considered as test input"
       ]
  <& (switch_opt
        [ OptSpec.long_name "stop"
        ]
      $> fun b -> if b then `go_on else `stop
     )
  <& switch_opt
       [ OptSpec.long_name "no-load-holes"
       ]
  <& switch_opt
       [ OptSpec.long_name "no-save-back"
       ]
  <! impure_opt handle_debug
       [ OptSpec.long_name "debug"
       ; OptSpec.help_msg
           "use debugging mode (writes to debug.out in CWD)"
       ]
  <! impure_opt handle_implicit
       [ OptSpec.long_name "implicit"
       ; OptSpec.help_msg "print implicit variables"
       ]
  <! help_opt handle_help
       [ OptSpec.long_name "help"
       ; OptSpec.short_name 'h'
       ; OptSpec.help_msg "print this message"
       ]
  <! rest_args
       begin function
         | [] -> ()
         | rest -> Error.(throw (DanglingArguments rest))
       end

(** Parses argument list and
    returns parsed result and leftover arguments.
 *)
let parse_arguments args : parsed_t =
  match Optparser.Builder.parse options_spec args with
  | Ok options -> options
  | Error e -> Error.(throw (OptparserError e))

(** Checks whether partial options have all mandatory options or not,
    and lift its type to valid_options
 *)
let validate (o : parsed_t) : valid_t =
  if o.test_stop = `stop then
    begin match o.test_file with
    | None ->
       Error.(throw InvalidStop)
    | Some (f, `incomplete) ->
       Error.(throw InvalidStop)
    | _ -> ()
    end;
  o

(** Loads the specified signature and elaborates the theorem.
    Returns also the path of the last file loaded.
    (This is where Harpoon will store proofs.)
 *)
let elaborate (o : valid_t) : elaborated_t =
  let open B in
  let ppf = Format.std_formatter in
  let all_paths = Load.load ppf o.path in
  { o with all_paths }
