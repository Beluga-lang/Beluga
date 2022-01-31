open Support

module B = Beluga

module PC = B.Printer.Control

module Error = struct
  type t =
    | OptparserError of Optparser.OptSpec.error
    | InvalidIncomplete
    | InvalidStop
    | DanglingArguments
      of string list

  exception E of t
  let throw e = raise (E e)

  open Format
  let format_error ppf = function
    | OptparserError e ->
       let open Optparser.OptSpec in
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

(** The `stop and `go_on flag control what happens in the presence of errors.
    In particular, the `stop flag will cause Harpoon to exit as soon
    as an error in encountered instead of continuing to process
    commands which may not make sense anymore.
    This is especially important when running tests.
 *)
type interaction_mode = [ `stop | `go_on ]

(** Controls the behaviour of saving sessions back to the signature
    when they are completed. *)
type save_mode = [ `save_back | `no_save_back ]

type test_kind = [ `incomplete | `complete ]
type test_file = string * test_kind

(** The command-line options specified to Harpoon. *)
type ('a, 'b) t =
  { path : 'a (* the path of the signature file to load, could be a cfg *)
  ; all_paths : 'b (* the list of paths resolved from the signature file to load *)
  ; test_file : test_file option (* the harpoon test file to load *)
  ; test_start : int option (* the first line from which the harpoon test file is considered as input *)
  ; test_stop : interaction_mode (* whether to stop a test script if there's an error *)
  ; load_holes : bool
  ; save_back : save_mode
  }

type parsed_t =
  (string, unit) t
type elaborated_t =
  (string, string list) t

let options_spec : parsed_t Optparser.OptSpec.t =
  let handle_debug () =
    Debug.enable ();
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
  let open Optparser in
  let open OptSpec in
  begin fun path test_opt test_kind test_start test_stop no_load_holes save_back ->
  let test_file =
    match test_opt, test_kind, test_stop with
    | None, `incomplete, _ ->
       Error.(throw InvalidIncomplete)
    | None, _, `stop ->
       Error.(throw InvalidStop)
    | Some _, `incomplete, `stop ->
       Error.(throw InvalidStop)
    | _ -> Option.map (fun test -> (test, test_kind)) test_opt
  in
  { path
  ; all_paths = ()
  ; test_file
  ; test_start
  ; test_stop
  ; load_holes = not no_load_holes
  ; save_back
  }
  end
  <$ string_opt1
       [ OptInfo.Unchecked.long_name "sig"
       ; OptInfo.Unchecked.meta_vars [ "path" ]
       ; OptInfo.Unchecked.help_msg "specify the input signature"
       ]
  <& opt1
       (fun s -> Option.some (Option.some s))
       [ OptInfo.Unchecked.long_name "test"
       ; OptInfo.Unchecked.meta_vars [ "path" ]
       ; OptInfo.Unchecked.optional None
       ; OptInfo.Unchecked.help_msg
           ( "specify the test input file that is used as "
           ^ "a test input instead of stdin user input" )
       ]
  <& ( switch_opt
         [ OptInfo.Unchecked.long_name "incomplete"
         ; OptInfo.Unchecked.help_msg
             ( "mark the test input file as incomplete so that stdin user "
             ^ "input is followed after the test input "
             ^ "(valid only when --test option is provided)" )
        ]
     $> fun b -> if b then `incomplete else `complete )
  <& opt1
       (fun s -> Option.map Option.some (int_of_string_opt s))
       [ OptInfo.Unchecked.long_name "test-start"
       ; OptInfo.Unchecked.meta_vars [ "number" ]
       ; OptInfo.Unchecked.optional None
       ; OptInfo.Unchecked.help_msg
           "specify the first line of test file considered as test input"
       ]
  <& ( switch_opt [ OptInfo.Unchecked.long_name "stop" ]
     $> fun b -> if b then `stop else `go_on )
  <& switch_opt [ OptInfo.Unchecked.long_name "no-load-holes" ]
  <& ( switch_opt [ OptInfo.Unchecked.long_name "no-save-back" ]
     $> fun b -> if b then `no_save_back else `save_back )
  <! impure_opt0
       handle_debug
       [ OptInfo.Unchecked.long_name "debug"
       ; OptInfo.Unchecked.help_msg
           "use debugging mode (writes to debug.out in CWD)"
       ]
  <! impure_opt0
       handle_implicit
       [ OptInfo.Unchecked.long_name "implicit"
       ; OptInfo.Unchecked.help_msg "print implicit variables"
       ]
  <! help_opt0
       handle_help
       [ OptInfo.Unchecked.long_name "help"
       ; OptInfo.Unchecked.short_name 'h'
       ; OptInfo.Unchecked.help_msg "print this message"
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
  match Optparser.Parser.parse options_spec args with
  | Ok options -> options
  | Error e -> Error.(throw (OptparserError e))

(** Loads the specified signature and elaborates the theorem.
    Returns also the path of the last file loaded.
    (This is where Harpoon will store proofs.)
 *)
let elaborate (o : parsed_t) : elaborated_t =
  let open B in
  let ppf = Format.std_formatter in
  let all_paths = Load.load ppf o.path in
  { o with all_paths }
