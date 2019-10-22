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
type ('a, 'b, 'c, 'd, 'e) options =
  { path : 'a (* the path of the signature file to load, could be a cfg *)
  ; all_paths : 'b (* the list of paths resolved from the signature file to load *)
  ; theorem_name : 'c (* the name of the theorem to prove *)
  ; theorem : 'd (* the statement of the theorem to prove *)
  ; order : 'e (* the induction order for the theorem *)
  ; test_file : (string * test_kind) option (* the harpoon test file to load *)
  }

type elaborated_options =
  (string, string list, string, I.Comp.typ, I.Comp.order option) options
type valid_options =
  (string, unit, string, E.Comp.typ, E.Comp.numeric_order option) options
type partial_options =
  (string option, unit, string option, E.Comp.typ option, E.Comp.numeric_order option) options

let initial_options : partial_options =
  { path = None
  ; all_paths = ()
  ; theorem_name = None
  ; theorem = None
  ; order = None
  ; test_file = None
  }

let usage () : unit =
  let usageString : (_, out_channel, unit) format =
    ""
    ^^ "Usage: %s <mandatory options> <other options>\n"
    ^^ "\n"
    ^^ "Mandatory options:\n"
    ^^ "  --sig file             specify the input signature\n"
    ^^ "  --name 'theorem name'  specify the name of the theorem to prove\n"
    ^^ "  --theorem 'theorem'    specify the statement of the theorem to prove\n"
    ^^ "\n"
    ^^ "Other options:\n"
    ^^ "  --order number         specify the induction order of the theorem\n"
    ^^ "                         for the totality checker\n"
    ^^ "  --debug                use debugging mode\n"
    ^^ "  --implicit             print implicit variables\n"
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
    ; theorem_name =
        check
          "--name"
          "specifies the name of the theorem to prove"
          o.theorem_name
    ; theorem =
        check
          "--theorem"
          "specifies the statement of the theorem to prove"
          o.theorem
    ; order =
        o.order
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

  let elaborate_theorem (thm : E.Comp.typ) : I.Comp.typ * int =
    let open B in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    thm |> Index.comptyp |> Reconstruct.comptyp |> Abstract.comptyp

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
    (* Now that the signature has been loaded, we can elaborate the
       statement of the theorem. *)
    let theorem, k = elaborate_theorem o.theorem in
    let order =
      Maybe.map
        begin fun x ->
        E.Comp.map_order (fun n -> n + k) x
        |> B.Order.of_numeric_order
        end
        o.order
    in
    let theorem =
      match order with
      | None -> theorem
      | Some order ->
         match B.Order.list_of_order order with
         | None ->
            let open Error in
            throw OrderTooComplicated
         | Some order ->
            match B.Total.annotate theorem order with
            | None ->
               let open Error in
               throw OrderDoesntMatch
            | Some theorem ->
               theorem
    in
    { o with
      theorem
    ; order
    ; all_paths
    }
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
  let beluga_parse name input entry =
    let open B in
    Runparser.parse_string ("<" ^ name ^ "'s argument>") input (Parser.only entry)
    |> Parser.extract
  in
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
     | "--name" ->
        with_args_for "--name" 1
          (parse_the_rest_with
             (fun [name] ->
               { options with theorem_name = Some name}))
     | "--theorem" ->
        with_args_for "--theorem" 1
          (parse_the_rest_with
             (fun [stmt] ->
               let stmt = sanitize_statement_string stmt in
               let theorem = beluga_parse "--theorem" stmt B.Parser.cmp_typ in
               { options with theorem = Some theorem }))
     | "--sig" ->
        with_args_for "--sig" 1
          (parse_the_rest_with
             (fun [path] ->
               { options with path = Some path }))
     | "--order" ->
        with_args_for "--order" 1
          (parse_the_rest_with
             (fun [order] ->
               let order = beluga_parse "--order" order B.Parser.numeric_total_order in
               { options with order = Some order }))
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
     | "--help" ->
        usage ();
        exit 1
     | _ ->
        rest, options

let forbid_dangling_arguments = function
  | [] -> ()
  | rest -> Error.(throw (DanglingArguments rest))

let main () =
  B.Debug.init (Some "debug.out");
  let (arg0 :: args) = Array.to_list Sys.argv in
  let rest, options = parse_arguments initial_options args in
  forbid_dangling_arguments rest;
  let options = options |> Validate.options |> Elab.options in
  let input_source =
    let stdin = Misc.Gen.of_in_channel_lines stdin in
    match options.test_file with
    | None -> stdin
    | Some (path, k) ->
       let h = open_in path in
       let g = Misc.Gen.of_in_channel_lines h in
       match k with
       | `incomplete ->
          Misc.Gen.sequence [g; stdin]
       | `complete -> g
  in
  Prover.start_toplevel
    input_source
    Format.std_formatter
    (B.Id.(mk_name (SomeString options.theorem_name)))
    (options.theorem, I.LF.MShift 0)
    options.order

let _ = main ()
