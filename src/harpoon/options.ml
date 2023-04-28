open Support
module B = Beluga
module PC = B.Printer.Control

module Error = struct
  type t =
    | OptparserError of Optparser.Error.t
    | InvalidIncomplete
    | InvalidStop
    | DanglingArguments of string list

  exception E of t

  let throw e = raise (E e)

  let error_printer = function
    | OptparserError e -> (
        match e with
        | `Missing_mandatory_option { Optparser.Error.Option.option_name; _ }
          ->
            Format.dprintf "Mandatory option %s is missing." option_name
        | `Invalid_arguments_length
            { Optparser.Error.Argument.option_name
            ; expected_argument_count = exp
            ; actual_argument_count = act
            } ->
            Format.dprintf "Option %s requires %d arguments. Got %d."
              option_name exp act
        | `Argument_reader_failure { Optparser.Error.Option.option_name; _ }
          ->
            Format.dprintf "%s" option_name
        | `Not_an_option { Optparser.Error.Option.option_name; _ } ->
            Format.dprintf "%s is not an option" option_name)
    | InvalidIncomplete ->
        Format.dprintf "--incomplete can be specified only after --test"
    | InvalidStop ->
        Format.dprintf
          "--stop can only be specified with --test and without --incomplete"
    | DanglingArguments args ->
        Format.dprintf
          "Unexpected remaining command-line arguments:@,  @[%a@]@\n"
          (Format.pp_print_list ~pp_sep:Format.comma Format.pp_print_string)
          args

  let () =
    Beluga_syntax.Error.register_exception_printer (function
      | E e -> error_printer e
      | exn -> Beluga_syntax.Error.raise_unsupported_exception_printing exn)
end

type interaction_mode =
  [ `stop
  | `go_on
  ]

type save_mode =
  [ `save_back
  | `no_save_back
  ]

type test_kind =
  [ `incomplete
  | `complete
  ]

type test_file =
  { filename : string
  ; kind : test_kind
  }

type t =
  { path : string
  ; test_file : test_file option
  ; test_start : int option
  ; test_stop : interaction_mode
  ; load_holes : bool
  ; save_back : save_mode
  }

let options_spec : t Optparser.options_specification =
  let handle_debug () =
    Debug.enable ();
    Printexc.record_backtrace true
  in
  let handle_implicit () = PC.printImplicit := true in
  let handle_help pp_print_help =
    let usage_string =
      Printf.sprintf "Usage: %s <mandatory options> <other options>"
        Sys.argv.(0)
    in
    Format.eprintf "%a" (pp_print_help usage_string) ();
    exit 1
  in
  let module E = Error in
  let open Optparser in
  (fun path test_opt test_kind test_start test_stop no_load_holes save_back ->
    let test_file =
      match (test_opt, test_kind, test_stop) with
      | Option.None, `incomplete, _ -> E.(throw InvalidIncomplete)
      | Option.None, _, `stop -> E.(throw InvalidStop)
      | Option.Some _, `incomplete, `stop -> E.(throw InvalidStop)
      | _ ->
          Option.map
            (fun test -> { filename = test; kind = test_kind })
            test_opt
    in
    { path
    ; test_file
    ; test_start
    ; test_stop
    ; load_holes = Bool.not no_load_holes
    ; save_back
    })
  <$ string_opt1
       [ long_name "sig"
       ; meta_variables [ "path" ]
       ; help_message "specify the input signature"
       ]
  <& opt1
       (fun s -> Option.some (Option.some s))
       [ long_name "test"
       ; meta_variables [ "path" ]
       ; optional None
       ; help_message
           ("specify the test input file that is used as "
          ^ "a test input instead of stdin user input")
       ]
  <& ( switch_opt
         [ long_name "incomplete"
         ; help_message
             ("mark the test input file as incomplete so that stdin user "
            ^ "input is followed after the test input "
            ^ "(valid only when --test option is provided)")
         ]
     $> fun b -> if b then `incomplete else `complete )
  <& opt1
       (fun s -> Option.map Option.some (int_of_string_opt s))
       [ long_name "test-start"
       ; meta_variables [ "number" ]
       ; optional None
       ; help_message
           "specify the first line of test file considered as test input"
       ]
  <& (switch_opt [ long_name "stop" ] $> fun b -> if b then `stop else `go_on)
  <& switch_opt [ long_name "no-load-holes" ]
  <& ( switch_opt [ long_name "no-save-back" ] $> fun b ->
       if b then `no_save_back else `save_back )
  <! impure_opt0 handle_debug
       [ long_name "debug"
       ; help_message "use debugging mode (writes to debug.out in CWD)"
       ]
  <! impure_opt0 handle_implicit
       [ long_name "implicit"; help_message "print implicit variables" ]
  <! help_opt0 handle_help
       [ long_name "help"
       ; short_name 'h'
       ; help_message "print this message"
       ]
  <! rest_args (function
       | [] -> ()
       | rest -> E.(throw (DanglingArguments rest)))

(** Parses argument list and returns parsed result and leftover arguments. *)
let parse_arguments args : t =
  match Optparser.parse options_spec args with
  | Result.Ok x -> x
  | Result.Error e -> Error.throw (Error.OptparserError e)
