(** Harpoon

@author Jacob Thomas Errington

Harpoon is an interactive mode for Beluga that uses a small set of
tactics for elaborating proofs.
The syntax of Harpoon proofs is defined in Syntax.Ext.Comp; it is a
part of the computation language.

This module defines the datatypes for Harpoon syntax and operations
for transforming it.

A Harpoon script is a sequence of statements, of which there are two kinds:
1. Commands: these generally manipulate the context in some way,
   e.g. by invoking an IH or a lemma, unboxing an expression to a
   metavariable, etc.
2. Directives: these are proof tactics, which allow for more
   complex formulas to be proven by breaking them apart.
   e.g. intros & split

Harpoon proofs end in two ways:
1. With QED, when the goal has been established.
2. With Incomplete, when the proof still needs work. Incomplete proofs
   are called _subgoals_, since they are typically introduced by using
   tactics.

Tactics (may) solve the current goal at the expense of introducing one
or more subgoals that need to be solved. For example, when focusing on
a subgoal of function type, the `intros` tactic will solve it by
introducing an Incomplete hypothetical derivation that will need to be
solved.

Here is an example (partial) proof.

```
proof modus_ponens : {A : [ |- tp]} {B : [ |- tp]}
                     [ |- nd A ] -> [ |- nd (imp A B) ] -> [ |- nd B ] =
  intros
  { A : [ |- tp ], B : [ |- tp ]
  | a : [ |- nd A], ab : [ |- nd (imp A B) ];
    ?
  };
```
 *)

open Support

module B = Beluga

module E = B.Syntax.Ext
module I = B.Syntax.Int

module PC = B.Printer.Control

(** Defines error type and formatting. *)
module Error = struct
  type t =
    | ArgParseLengthMismatch
      of string (* option name *)
         * int (* expected number of arguments *)
         * int (* actual number of arguments *)
    | MissingMandatoryOption
      of string (* option name *)
         * string (* hint *)
    | DanglingArguments
      of string list
    | OrderTooComplicated
    | OrderDoesntMatch
    | InvalidIncomplete

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
    | DanglingArguments args ->
       fprintf ppf "Unexpected remaining command-line arguments:@,  @[%a@]@."
         (pp_print_list ~pp_sep: Fmt.comma
            (fun ppf -> fprintf ppf "%s"))
         args
    | OrderTooComplicated ->
       fprintf ppf "Induction order too complicated@."
    | OrderDoesntMatch ->
       fprintf ppf "Induction order doesn't match theorem statement.@."
    | InvalidIncomplete ->
       fprintf ppf "--incomplete can be specified only after --test"
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

(** The command-line options specified to Harpoon. *)
type ('a, 'b) options =
  { path : 'a (* the path of the signature file to load, could be a cfg *)
  ; all_paths : 'b (* the list of paths resolved from the signature file to load *)
  ; test_file : (string * test_kind) option (* the harpoon test file to load *)
  ; test_start : int option (* the first line from which the harpoon test file is considered as input *)
  }

type elaborated_options =
  (string, string list) options
type valid_options =
  (string, unit) options
type partial_options =
  (string option, unit) options

let initial_options : partial_options =
  { path = None
  ; all_paths = ()
  ; test_file = None
  ; test_start = None
  }

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

module Validate :
sig
  val options : partial_options -> valid_options
end = struct
  let check opt_name hint =
    function
    | None -> Error.(throw (MissingMandatoryOption (opt_name, hint)))
    | Some x -> x

  (** Checks that mandatory options are specified, throwing exceptions
      if they're missing. *)
  let options (o : partial_options) : valid_options =
    { o with
      path =
        check
          "--sig"
          "specifies the input signature"
          o.path
    }
end

module Elab :
sig
  val options : valid_options -> elaborated_options
end = struct
  let forbid_leftover_vars path = function
    | None -> ()
    | Some vars ->
       let open B in
       let open Format in
       if !Debug.chatter <> 0 then
         fprintf std_formatter "@[<v>## Leftover variables: %s  ##@,  @[%a@]@]@."
           path
           Recsgn.fmt_ppr_leftover_vars vars;
       raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))

  let load_file path =
    let open B in
    let sgn, leftover_vars =
      Parser.(Runparser.parse_file path (only sgn) |> extract)
      |> Recsgn.apply_global_pragmas
      |> Recsgn.recSgnDecls
    in
    Store.Modules.reset ();
    forbid_leftover_vars path leftover_vars

  (** Loads the specified signature and elaborates the theorem.
      Returns also the path of the last file loaded.
      (This is where Harpoon will store proofs.)
   *)
  let options (o : valid_options) : elaborated_options =
    let all_paths = B.Cfg.process_file_argument o.path in
    List.iter load_file all_paths;
    { o with all_paths }
end

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

let sanitize_statement_string (stmt : string) : string =
  let length = String.length stmt in
  match stmt.[0], stmt.[length - 1] with
  | '"', '"' -> String.sub stmt 1 (length - 2)
  | '\'', '\'' -> String.sub stmt 1 (length - 2)
  | _ -> stmt

let rec parse_arguments options : string list -> string list * partial_options =
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
       parse_arguments (k x) rest
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
     | "--incomplete" ->
        begin match options.test_file with
        | None -> Error.(throw InvalidIncomplete)
        | Some (f, k) ->
           parse_arguments { options with test_file = Some (f, `incomplete) } rest
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

let forbid_dangling_arguments = function
  | [] -> ()
  | rest -> Error.(throw (DanglingArguments rest))

(**
   Module for user interface
   TODO: Extract this module as a file
         (It may also need to extract option parsing functions/types)
 *)
module Prompt : sig
  type t = string -> string option -> unit -> string option

  val make_prompt : (string * test_kind) option -> int option -> t
end = struct
  type t = string -> string option -> unit -> string option

  let stdin_prompt msg history_file () =
    let open Maybe in
    LNoise.linenoise msg
    $> fun str ->
       match history_file with
       | None -> str
       | Some path ->
          let _ = LNoise.history_load ~filename:path in
          let _ = LNoise.history_add str in
          let _ = LNoise.history_save ~filename:path in
          str

  let make_file_prompt path (k : test_kind) (test_start : int option) =
    let h = open_in path in
    let g =
      let open GenMisc in
      of_in_channel_lines h
      |> iter_through (fun x -> print_string (x ^ "\n"))
    in
    begin
      match test_start with
      | None -> ()
      | Some ln -> GenMisc.drop_lines g (ln - 1)
    end;
    match k with
    | `incomplete ->
       fun msg history_file ->
       GenMisc.sequence [g; stdin_prompt msg history_file]
    | `complete ->
       fun _ _ -> g

  let make_prompt test_file test_start : t =
    match test_file with
    | None -> stdin_prompt
    | Some (path, k) -> make_file_prompt path k test_start
end

let realMain () =
  B.Debug.init (Some "debug.out");
  let (arg0 :: args) = Array.to_list Sys.argv in
  let rest, options = parse_arguments initial_options args in
  forbid_dangling_arguments rest;
  let options = options |> Validate.options |> Elab.options in
  Prover.start_toplevel
    (Prompt.make_prompt options.test_file options.test_start)
    Format.std_formatter

let main () =
  try
    realMain ()
  with
  | e -> print_string (Printexc.to_string e)

let _ =
  main ()
