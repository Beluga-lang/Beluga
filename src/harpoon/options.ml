open Support

module B = Beluga

module PC = B.Printer.Control

module Error = struct
  type t =
    | ArgParseLengthMismatch
      of string (* option name *)
         * int (* expected number of arguments *)
         * int (* actual number of arguments *)
    | MissingMandatoryOption
      of string (* option name *)
         * string (* hint *)
    | InvalidIncomplete
    | InvalidStop
    | DanglingArguments
      of string list

  exception E of t
  let throw e = raise (E e)

  open Format
  let format_error ppf = function
    | ArgParseLengthMismatch (name, exp, act) ->
       fprintf ppf "Option %s requires %d arguments. Got %d.@."
         name
         exp
         act
    | MissingMandatoryOption (name, hint) ->
       fprintf ppf "Mandatory option %s is missing.@,(It %s.)@."
         name
         hint
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
  }

type elaborated_t =
  (string, string list) t
type valid_t =
  (string, unit) t
type partial_t =
  (string option, unit) t

let initial_t : partial_t =
  { path = None
  ; all_paths = ()
  ; test_file = None
  ; test_start = None
  ; test_stop = `go_on
  }

(** TODO
    Generate this from options if possible.
    (by ppx or something)
 *)
let usage () : unit =
  let usageString : (_, out_channel, unit) format =
    ""
    ^^ "Usage: %s <mandatory options> <other options>\n"
    ^^ "\n"
    ^^ "Mandatory options:\n"
    ^^ "  --sig path             specify the input signature\n"
    ^^ "\n"
    ^^ "Other options:\n"
    ^^ "  --test path            specify the test input file that is used as\n"
    ^^ "                         a test input instead of stdin user input\n"
    ^^ "  --incomplete           mark the test input file as incomplete so that\n"
    ^^ "                         stdin user input is followed after the test input\n"
    ^^ "                         (valid only when --test option is provided)\n"
    ^^ "  --test-start number    specify the first line of test file considered\n"
    ^^ "                         as test input\n"
    ^^ "  --debug                use debugging mode (writes to debug.out in CWD)\n"
    ^^ "  --implicit             print implicit variables\n"
    ^^ "  --help                 print this message\n"
    ^^ "\n"
  in
  Printf.eprintf usageString
    Sys.argv.(0)

let forbid_dangling_arguments = function
  | [] -> ()
  | rest -> Error.(throw (DanglingArguments rest))

(** Parses argument list and
    returns parsed result and leftover arguments.
 *)
let parse_arguments args : partial_t =
  (** Gets exactly the first `n` elements from a list.
      If the list contains fewer than `n` elements, the length of the
      list is returned on the Left.
   *)
  let rec take_exactly n =
    let open Either in
    function
    | xs when n <= 0 -> Right ([], xs)
    | x :: xs ->
       bimap
         (fun k -> k + 1)
         (Pair.lmap (fun xs -> x :: xs))
         (take_exactly (n-1) xs)
    | [] -> Left 0
  in
  let rec parse_from options =
    function
    | [] -> [], options
    | arg :: rest ->
       let with_args_for a n k =
         let open Either in
         match take_exactly n rest with
         | Left k ->
            let open Error in
            throw (ArgParseLengthMismatch (a, n, k))
         | Right (args, rest) -> k args rest
       in
       let parse_the_rest_with k x rest =
         parse_from (k x) rest
       in
       let parse_the_rest () =
         parse_the_rest_with (Misc.id) options rest
       in
       match arg with
       | "--debug" ->
          B.Debug.enable ();
          Printexc.record_backtrace true;
          parse_the_rest ()
       | "--implicit" ->
          PC.printImplicit := true;
          parse_the_rest ()
       | "--sig" ->
          with_args_for "--sig" 1
            (parse_the_rest_with
               (fun [path] ->
                 { options with path = Some path }))
       | "--test" ->
          with_args_for "--test" 1
            (parse_the_rest_with
               (fun [test_path] ->
                 { options with test_file = Some (test_path, `complete) }))
       | "--stop" ->
          parse_from { options with test_stop = `stop } rest
       | "--incomplete" ->
          begin match options.test_file with
          | None -> Error.(throw InvalidIncomplete)
          | Some (f, k) ->
             parse_from { options with test_file = Some (f, `incomplete) } rest
          end
       | "--test-start" ->
          with_args_for "--test-start" 1
            (parse_the_rest_with
               (fun [test_start] ->
                 { options with test_start = Some (int_of_string test_start) }))
       | "--help" ->
          usage ();
          exit 1
       | _ ->
          rest, options
  in
  let rest, options = parse_from initial_t args in
  forbid_dangling_arguments rest;
  options

(** Checks whether partial options have all mandatory options or not,
    and lift its type to valid_options
 *)
let validate (o : partial_t) : valid_t =
  let check opt_name hint =
    function
    | None -> Error.(throw (MissingMandatoryOption (opt_name, hint)))
    | Some x -> x
  in
  if o.test_stop = `stop then
    begin match o.test_file with
    | None ->
       Error.(throw InvalidStop)
    | Some (f, `incomplete) ->
       Error.(throw InvalidStop)
    | _ -> ()
    end;

  { o with
    path =
      check
        "--sig"
        "specifies the input signature"
        o.path
  }

(** Loads the specified signature and elaborates the theorem.
    Returns also the path of the last file loaded.
    (This is where Harpoon will store proofs.)
 *)
let elaborate (o : valid_t) : elaborated_t =
  let open B in
  let forbid_leftover_vars path = function
    | None -> ()
    | Some vars ->
       let open Format in
       if !Debug.chatter <> 0 then
         fprintf std_formatter "@[<v>## Leftover variables: %s  ##@,  @[%a@]@]@."
           path
           Recsgn.fmt_ppr_leftover_vars vars;
       raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
  in
  let load_file path =
    let sgn, leftover_vars =
      Parser.(Runparser.parse_file path (only sgn) |> extract)
      |> Recsgn.apply_global_pragmas
      |> Recsgn.recSgnDecls
    in
    Store.Modules.reset ();
    forbid_leftover_vars path leftover_vars
  in
  let all_paths = Cfg.process_file_argument o.path in
  List.iter load_file all_paths;
  { o with all_paths }
