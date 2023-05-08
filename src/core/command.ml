(** Top level functions invoked by the interactive mode.

    Each interactive mode command corresponds with a {!command} record in
    this file. Available commands are added to a registry at the bottom of
    this file. *)

open Support.Equality
open Support
open Beluga_syntax.Syncom
open Synint
open Beluga_parser
module P = Prettyint.DefaultPrinter

[@@@warning "+A-4-44"]

exception Duplicate_command_name of String.t

exception Unknown_command of String.t

exception Line_parse_error

exception Column_parse_error

exception No_load_to_redo

(** The exception variant signaling a recoverable failure to executing a
    command in the interpreter. If this exception is raised during the
    evaluation of a command, then the command has failed, but the interpreter
    is not in an invalid state.

    For instance, if a command requires that we parse an integer, and the
    input token is not a valid integer, then the command has failed, but the
    interpreter should not crash. *)
exception Command_execution_error of exn

let () =
  Error.register_exception_printer (function
    | Duplicate_command_name command_name ->
        Format.dprintf
          "There is already a registered command with name \"%s\"."
          command_name
    | Unknown_command name ->
        Format.dprintf "Unrecognized command with name \"%s\"." name
    | Line_parse_error -> Format.dprintf "Failed to parse the line number."
    | Column_parse_error ->
        Format.dprintf "Failed to parse the column number."
    | No_load_to_redo -> Format.dprintf "No load command to repeat."
    | Command_execution_error cause ->
        let cause_printer = Error.find_printer cause in
        Format.dprintf "@[<v>- Failed to execute command.@,%t@]"
          cause_printer
    | cause -> Error.raise_unsupported_exception_printing cause)

let raise_command_execution_error cause =
  Error.re_raise (Command_execution_error cause)

(** [run_safe f] evaluates [f ()], and if that raises an exception [exn],
    then [Command_execution_error exn] is raised instead. *)
let run_safe f =
  try f () with
  | cause -> raise_command_execution_error cause

module type INTERPRETER_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  type command

  val make_command :
       name:String.t
    -> usage:String.t
    -> description:String.t
    -> run:(state -> input:String.t -> Unit.t)
    -> command

  val command_usage : command -> String.t

  val command_description : command -> String.t

  val run_command : state -> command -> input:String.t -> Unit.t

  val register_command : state -> command -> Unit.t

  val find_command : state -> name:String.t -> command

  val iter_commands : state -> (command -> Unit.t) -> Unit.t

  val fprintf : state -> ('a, Format.formatter, Unit.t) format -> 'a

  val read_comp_expression_and_infer_type :
    state -> ?location:Location.t -> String.t -> Comp.exp * Comp.typ

  val read_checked_query :
       state
    -> ?location:Location.t
    -> String.t
    -> Int.t Option.t
       * Int.t Option.t
       * Identifier.t Option.t
       * (LF.typ * Int.t)

  val read_line_number : state -> ?location:Location.t -> String.t -> Int.t

  val read_column_number : state -> ?location:Location.t -> String.t -> Int.t

  val read_identifier :
    state -> ?location:Location.t -> String.t -> Identifier.t
    [@@warning "-32"]

  val read_qualified_identifier :
    state -> ?location:Location.t -> String.t -> Qualified_identifier.t

  (** [index_of_lf_type_constant state identifier] is the constant ID of
      [identifier] in [state] if it is bound to an LF type-level constant. If
      [identifier] is bound to any other entry, then an exception is raised. *)
  val index_of_lf_type_constant :
    state -> Qualified_identifier.t -> Id.cid_typ

  val index_of_comp_program : state -> Qualified_identifier.t -> Id.cid_prog

  val index_of_comp_type_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typ

  val maximum_lf_hole_solutions : state -> Int.t

  val maximum_lf_hole_search_depth : state -> Int.t

  val load : state -> filename:String.t -> Synint.Sgn.sgn

  val reload : state -> Synint.Sgn.sgn
end

module Make_interpreter_state
    (Disambiguation_state : Beluga_parser.DISAMBIGUATION_STATE)
    (Disambiguation : Beluga_parser.DISAMBIGUATION
                        with type state = Disambiguation_state.state)
    (Indexing_state : Index_state.INDEXING_STATE)
    (Indexer : Index.INDEXER with type state = Indexing_state.state)
    (Signature_reconstruction_state : Recsgn_state
                                      .SIGNATURE_RECONSTRUCTION_STATE)
    (Signature_reconstruction : Recsgn.SIGNATURE_RECONSTRUCTION
                                  with type state =
                                    Signature_reconstruction_state.state) =
struct
  module Parser_state =
    Parser_combinator.Make_persistent_state (Located_token)
  module Parser = Beluga_parser.Make (Parser_state) (Disambiguation_state)
  module Load_state =
    Load.Make_load_state (Disambiguation_state) (Disambiguation)
      (Signature_reconstruction_state)
      (Signature_reconstruction)
  module Load = Load.Make_load (Load_state)

  type state =
    { ppf : Format.formatter
          (** The pretty-printing state for outputting strings. *)
    ; commands : command String.Hashtbl.t
          (** The map of registered commands by command name. *)
    ; disambiguation_state : Disambiguation_state.state
          (** The disambiguation state for parsing new expressions. *)
    ; index_state : Indexing_state.state
          (** The indexing state for indexing new expressions. *)
    ; signature_reconstruction_state : Signature_reconstruction_state.state
          (** The signature reconstruction state to reconstruct loaded
              signatures. *)
    ; mutable maximum_lf_hole_solutions : Int.t
          (** The maximum number of solutions to search for LF holes. *)
    ; mutable maximum_lf_hole_search_depth : Int.t
          (** The maximum depth of the search for solutions to LF holes. *)
    ; load_state : Load_state.state
    ; mutable last_load : String.t Option.t
          (** The latest Beluga signature configuration file to have been
              loaded. *)
    }
  [@@warning "-69"]

  and command =
    { name : String.t  (** The command's name. *)
    ; usage : String.t
          (** An example usage of the command to show its syntax. *)
    ; description : String.t
          (** The command's help message, which describes how to use the
              command. *)
    ; run : state -> input:String.t -> Unit.t
          (** The command's stateful runner function for executing it for a
              given input. *)
    }

  let create_state ppf disambiguation_state index_state
      signature_reconstruction_state =
    let load_state =
      Load_state.create_state disambiguation_state
        signature_reconstruction_state
    in
    { ppf
    ; commands = String.Hashtbl.create 20
    ; disambiguation_state
    ; index_state
    ; signature_reconstruction_state
    ; maximum_lf_hole_solutions = 10 (* Arbitrary value *)
    ; maximum_lf_hole_search_depth = 100 (* Arbitrary value *)
    ; load_state
    ; last_load = Option.none
    }

  include (
    Imperative_state.Make (struct
      type nonrec state = state
    end) :
      Imperative_state.IMPERATIVE_STATE with type state := state)

  let make_command ~name ~usage ~description ~run =
    { name; usage; description; run }

  let command_usage command = command.usage

  let command_description command = command.description

  let run_command state command ~input = command.run state ~input

  let is_command state command_name =
    String.Hashtbl.mem state.commands command_name

  let register_command state command =
    if is_command state command.name then
      Error.raise (Duplicate_command_name command.name)
    else String.Hashtbl.add state.commands command.name command

  let find_command state ~name =
    match String.Hashtbl.find_opt state.commands name with
    | Option.Some command -> command
    | Option.None -> raise_command_execution_error (Unknown_command name)

  let iter_commands state f =
    String.Hashtbl.iter
      (fun _command_name command -> f command)
      state.commands

  let fprintf state fmt = Format.fprintf state.ppf (fmt ^^ "@.")

  let comp_expression_parser = Parser.Parsing.(only comp_expression)

  let comp_expression_disambiguator state exp =
    Parser.Disambiguation.(
      with_bindings_checkpoint state (fun state ->
          disambiguate_comp_expression state exp))

  let read_comp_expression_and_infer_type state ?(location = Location.ghost)
      input =
    let apx_exp =
      run_safe (fun () ->
          let token_sequence =
            Lexer.lex_string ~initial_location:location input
          in
          let parsing_state =
            Parser_state.initial ~initial_location:location token_sequence
          in
          let parser_state =
            Parser.make_state ~parser_state:parsing_state
              ~disambiguation_state:state.disambiguation_state
          in
          let exp =
            Parser.eval
              (Parser.parse_and_disambiguate ~parser:comp_expression_parser
                 ~disambiguator:comp_expression_disambiguator)
              parser_state
          in
          let apx_exp =
            Indexing_state.with_bindings_checkpoint state.index_state
              (fun state -> Indexer.index_comp_expression state exp)
          in
          apx_exp)
    in
    (* FIXME: The following elaboration steps need checkpoints to rollback to
       in case of failure *)
    let exp, ttau = Reconstruct.elExp' LF.Empty LF.Empty apx_exp in
    let tau = Whnf.cnormCTyp ttau in
    (exp, tau)

  let query_parser =
    Parser.Parsing.(
      let bound =
        alt (star $> fun () -> Option.none) (integer $> Option.some)
        |> labelled "search bound"
      in
      let expected_arguments = bound
      and maximum_tries = bound in
      only
        (seq4 expected_arguments maximum_tries
           (maybe (identifier <& colon))
           lf_typ))

  let query_disambiguator state
      (expected_arguments, maximum_tries, identifier_opt, typ) =
    Parser.Disambiguation.(
      with_bindings_checkpoint state (fun state ->
          let typ' = disambiguate_lf_typ state typ in
          (expected_arguments, maximum_tries, identifier_opt, typ')))

  let read_query state ?(location = Location.ghost) input =
    run_safe (fun () ->
        let token_sequence =
          Lexer.lex_string ~initial_location:location input
        in
        let parsing_state =
          Parser_state.initial ~initial_location:location token_sequence
        in
        let parser_state =
          Parser.make_state ~parser_state:parsing_state
            ~disambiguation_state:state.disambiguation_state
        in
        Parser.eval
          (Parser.parse_and_disambiguate ~parser:query_parser
             ~disambiguator:query_disambiguator)
          parser_state)

  let read_checked_query state ?(location = Location.ghost) input =
    let expected, tries, identifier, apxT =
      run_safe (fun () ->
          let expected, tries, identifier, extT =
            read_query state ~location input
          in
          let apxT =
            Indexing_state.with_bindings_checkpoint state.index_state
              (fun state -> Indexer.index_open_lf_typ state extT)
          in
          (expected, tries, identifier, apxT))
    in
    (* FIXME: The following reconstruction steps need checkpoints to rollback
       to in case of failure *)
    Store.FVar.clear ();
    let tA = Reconstruct.typ Lfrecon.Pi apxT in
    Reconstruct.solve_fvarCnstr Lfrecon.Pi;
    Unify.StdTrail.forceGlobalCnstr ();
    let tA', i = Abstract.typ tA in
    Reconstruct.reset_fvarCnstr ();
    Unify.StdTrail.resetGlobalCnstrs ();
    Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', Substitution.LF.id);
    (expected, tries, identifier, (tA', i))

  let parse_int ~on_error token =
    match int_of_string_opt token with
    | Option.None -> on_error ()
    | Option.Some line -> line

  let parse_line_number =
    parse_int ~on_error:(fun () -> Error.raise Line_parse_error)

  let parse_column_number =
    parse_int ~on_error:(fun () -> Error.raise Column_parse_error)

  let read_line_number _state ?location:_ input =
    run_safe (fun () -> parse_line_number input)

  let read_column_number _state ?location:_ input =
    run_safe (fun () -> parse_column_number input)

  let read_identifier _state ?(location = Location.ghost) input =
    run_safe (fun () ->
        let token_sequence =
          Lexer.lex_string ~initial_location:location input
        in
        let parsing_state =
          Parser_state.initial ~initial_location:location token_sequence
        in
        Parser.Parsing.eval_exn
          Parser.Parsing.(only identifier)
          parsing_state)

  let read_qualified_identifier _state ?(location = Location.ghost) input =
    run_safe (fun () ->
        let token_sequence =
          Lexer.lex_string ~initial_location:location input
        in
        let parsing_state =
          Parser_state.initial ~initial_location:location token_sequence
        in
        Parser.Parsing.eval_exn
          Parser.Parsing.(only qualified_identifier)
          parsing_state)

  let index_of_lf_type_constant state identifier =
    run_safe (fun () ->
        Indexing_state.index_of_lf_type_constant state.index_state identifier)

  let index_of_comp_program state identifier =
    run_safe (fun () ->
        Indexing_state.index_of_comp_program state.index_state identifier)

  let index_of_comp_type_constant state identifier =
    run_safe (fun () ->
        Indexing_state.index_of_comp_type_constant state.index_state
          identifier)

  let maximum_lf_hole_solutions state = state.maximum_lf_hole_solutions

  let maximum_lf_hole_search_depth state = state.maximum_lf_hole_search_depth

  let load state ~filename =
    let _all_paths, sgn = Load.load state.load_state filename in
    state.last_load <- Option.some filename;
    sgn

  let reload state =
    match state.last_load with
    | Option.None -> raise_command_execution_error No_load_to_redo
    | Option.Some filename -> load state ~filename
end

module Make_interpreter (State : INTERPRETER_STATE) = struct
  include State

  (* The built-in commands *)

  (** Used to define command bodies requiring a certain number of arguments.

      This function checks the length of the argument list against the given
      number, and in case of success runs the given command body function. *)
  let command_with_arguments n f state ~input =
    let arguments =
      match String.split_on_char ' ' input with
      | [ "" ] (* [input = ""] *) -> []
      | arguments -> arguments
    in
    let n' = List.length arguments in
    if n = n' then f state arguments
    else
      fprintf state "- Command requires %d arguments, but %d were given;" n
        n'

  let command0 f =
    command_with_arguments 0 (fun [@warning "-8"] state [] -> f state)

  let command1 f =
    command_with_arguments 1 (fun [@warning "-8"] state [ a ] -> f state a)

  let command2 f =
    command_with_arguments 2 (fun [@warning "-8"] state [ a1; a2 ] ->
        f state a1 a2)

  let countholes =
    make_command ~name:"countholes" ~usage:"countholes"
      ~description:"Print the total number of holes"
      ~run:(command0 (fun state -> fprintf state "%d;" (Holes.count ())))

  let chatteron =
    make_command ~name:"chatteron" ~usage:"chatteron"
      ~description:"Turn on the chatter"
      ~run:
        (command0 (fun state ->
             Chatter.level := 1;
             fprintf state "The chatter is on now;"))

  let chatteroff =
    make_command ~name:"chatteroff" ~usage:"chatteroff"
      ~description:"Turn off the chatter"
      ~run:
        (command0 (fun state ->
             Chatter.level := 0;
             fprintf state "The chatter is off now;"))

  let types =
    make_command ~name:"types" ~usage:"types"
      ~description:"Print out all types currently defined"
      ~run:
        (command0 (fun state ->
             let entrylist =
               List.map Pair.snd (Store.Cid.Typ.current_entries ())
             in
             let dctx = Synint.LF.Null in
             fprintf state "@[<v>%a@];"
               (Format.pp_print_list ~pp_sep:Format.pp_print_cut
                  (fun state x ->
                    Format.fprintf state "%a : %a" Name.pp
                      x.Store.Cid.Typ.Entry.name
                      (P.fmt_ppr_lf_kind dctx P.l0)
                      x.Store.Cid.Typ.Entry.kind))
               entrylist))

  let reset =
    make_command ~name:"reset" ~usage:"reset" ~description:"Reset the store."
      ~run:
        (command0 (fun state ->
             Store.clear ();
             Typeinfo.clear_all ();
             Holes.clear ();
             fprintf state "Reset successful;"))

  let clearholes =
    make_command ~name:"clearholes" ~usage:"clearholes"
      ~description:"Clear all computation level holes."
      ~run:(command0 (fun _state -> Holes.clear ()))

  let reload =
    make_command ~name:"reload" ~usage:"reload"
      ~description:
        "Clear the interpreter state and repeat the last load command."
      ~run:(command0 (fun state -> ignore (reload state : Synint.Sgn.sgn)))

  let load =
    make_command ~name:"load" ~usage:"load FILE"
      ~description:"Clear the interpreter state and loads the file."
      ~run:
        (command1 (fun state filename ->
             ignore (load state ~filename : Synint.Sgn.sgn);
             fprintf state "The file %s has been successfully loaded;"
               filename))

  (** Parses the given hole lookup strategy string, and retrieves a hole
      using that strategy.

      If the string is invalid, or the lookup fails, an error is displayed.
      Otherwise, the given function is executed with the hole identifier and
      information. *)
  let with_hole_from_strategy_string state (strat : string)
      (f : HoleId.t * Holes.some_hole -> unit) : unit =
    match Holes.parse_lookup_strategy strat with
    | Option.None ->
        fprintf state "- Failed to parse hole identifier `%s';" strat
    | Option.Some s -> (
        match Holes.get s with
        | Option.Some id_and_hole -> f id_and_hole
        | Option.None ->
            fprintf state "- No such hole %s;"
              (Holes.string_of_lookup_strategy s))

  let requiring_hole_satisfies (check : Holes.some_hole -> bool)
      (on_error : HoleId.t * Holes.some_hole -> unit)
      (f : HoleId.t * Holes.some_hole -> unit)
      (p : HoleId.t * Holes.some_hole) : unit =
    let g =
      match p with
      | _, h when check h -> f
      | _ -> on_error
    in
    g p

  (** Requires that an list of checks on the hole pass before invoking the
      continuation [f]. *)
  let rec require checks f p =
    match checks with
    | [] -> f p
    | (check, on_error) :: checks ->
        requiring_hole_satisfies check on_error (require checks f) p

  let string_of_id_hole (i, h) = HoleId.string_of_name_or_id (h.Holes.name, i)

  let check_is_unsolved state =
    ( Holes.is_unsolved
    , fun (id, Holes.Exists (_, h)) ->
        fprintf state "- Hole %s is already solved;"
          (string_of_id_hole (id, h)) )

  let requiring_computation_hole state
      (f : HoleId.t * Holes.comp_hole_info Holes.hole -> unit)
      (p : HoleId.t * Holes.some_hole) : unit =
    let open Holes in
    require
      [ check_is_unsolved state ]
      (fun (id, Exists (w, h)) ->
        match w with
        | CompInfo -> f (id, h)
        | _ ->
            fprintf state "- Hole %s is not a computational hole;"
              (string_of_id_hole (id, h)))
      p

  let requiring_lf_hole state
      (f : HoleId.t * Holes.lf_hole_info Holes.hole -> unit)
      (p : HoleId.t * Holes.some_hole) : unit =
    let open Holes in
    require
      [ check_is_unsolved state ]
      (fun (id, Exists (w, h)) ->
        match w with
        | LFInfo -> f (id, h)
        | _ ->
            fprintf state "- Hole %s is not an LF hole;"
              (string_of_id_hole (id, h)))
      p

  let printhole =
    make_command ~name:"printhole" ~usage:"printhole N"
      ~description:
        "Print out all the information of the i-th hole passed as a \
         parameter."
      ~run:
        (command1 (fun state s ->
             with_hole_from_strategy_string state s
               (fprintf state "%a;" Interactive.fmt_ppr_hole)))

  let lochole =
    make_command ~name:"lochole" ~usage:"lochole N"
      ~description:
        "Print out the location information of the N-th hole passed as a \
         parameter."
      ~run:
        (command1 (fun state s ->
             with_hole_from_strategy_string state s
               (fun (_, Holes.Exists (_, { Holes.location; _ })) ->
                 let file_name = Location.filename location in
                 let start_line = Location.start_line location in
                 let start_bol = Location.start_bol location in
                 let start_off = Location.start_offset location in
                 let stop_line = Location.stop_line location in
                 let stop_bol = Location.stop_bol location in
                 let stop_off = Location.stop_offset location in
                 fprintf state "(\"%s\" %d %d %d %d %d %d);" file_name
                   start_line start_bol start_off stop_line stop_bol stop_off)))

  let solvelfhole =
    make_command ~name:"solve-lf-hole" ~usage:"solve-lf-hole N"
      ~description:"Use logic programming to solve an LF hole."
      ~run:
        (command1 (fun state name ->
             with_hole_from_strategy_string state name
               (requiring_lf_hole state (fun (_i, h) ->
                    let Holes.
                          { cD; info = { lfGoal = lfTyp, _; cPsi; _ }; _ } =
                      h
                    in
                    let lfTyp', i = Abstract.typ lfTyp in
                    (* Not too sure what I'm doing here. *)
                    Logic.prepare ();
                    let query, _skinnyTyp, _querySub, _instMVars =
                      Logic.Convert.typToQuery cD cPsi (lfTyp', i)
                    in
                    (* Count the solutions that are found so we only emit a
                       maximum number of them. Raise the "Done" exception to
                       stop the search. *)
                    let maximum_lf_hole_solutions =
                      maximum_lf_hole_solutions state
                    in
                    let maximum_lf_hole_search_depth =
                      maximum_lf_hole_search_depth state
                    in
                    (try
                       let solutions_found = ref 0 in
                       Logic.Solver.solve cD cPsi query
                         (fun (ctx, norm) ->
                           fprintf state "%a@\n"
                             (P.fmt_ppr_lf_normal cD ctx P.l0)
                             norm;
                           incr solutions_found;
                           if !solutions_found = maximum_lf_hole_solutions
                           then raise Logic.Frontend.Done)
                         (Option.some maximum_lf_hole_search_depth)
                     with
                    | Logic.Frontend.Done -> ()
                    | e -> Error.re_raise e);
                    fprintf state ";"))))

  let constructors =
    make_command ~name:"constructors" ~usage:"constructors IDENTIFIER"
      ~description:
        "Print all constructors of a given type passed as a parameter."
      ~run:
        (command1 (fun state arg ->
             let name = read_qualified_identifier state arg in
             let cid = index_of_lf_type_constant state name in
             let entry = Store.Cid.Typ.get cid in
             let termlist =
               List.map Store.Cid.Term.get
                 !(entry.Store.Cid.Typ.Entry.constructors)
             in
             fprintf state "@[<v>%a@]@\n;"
               (Format.pp_print_list ~pp_sep:Format.pp_print_cut
                  (fun state x ->
                    Format.fprintf state "%a : [%d] %a" Name.pp
                      x.Store.Cid.Term.Entry.name
                      x.Store.Cid.Term.Entry.implicit_arguments
                      (P.fmt_ppr_lf_typ LF.Empty LF.Null P.l0)
                      x.Store.Cid.Term.Entry.typ))
               termlist))

  let print_helpme state =
    iter_commands state (fun command ->
        let usage = command_usage command in
        let description = command_description command in
        fprintf state "%%:%30s\t %s" usage description)

  let helpme =
    make_command ~name:"help" ~usage:"help"
      ~description:"List all available commands with a short description."
      ~run:(command0 print_helpme)

  (** Actually does a split on a variable in a hole.

      Requires that the hole is a computation hole. *)
  let do_split state (hi : HoleId.t * Holes.comp_hole_info Holes.hole)
      (var : string) : unit =
    match Interactive.split var hi with
    | Option.None -> fprintf state "- No variable %s found;" var
    | Option.Some exp ->
        let _, h = hi in
        let { Holes.cG; _ } = h.Holes.info in
        Printer.with_normal true (fun () ->
            fprintf state "%a;" (P.fmt_ppr_cmp_exp h.Holes.cD cG P.l0) exp)

  let split =
    make_command ~name:"split" ~usage:"split H V"
      ~description:
        "Try to split on variable V in hole H (specified by name or number)."
      ~run:
        (command2 (fun state strat_s var ->
             with_hole_from_strategy_string state strat_s
               (requiring_computation_hole state (fun hi ->
                    do_split state hi var))))

  let intro =
    make_command ~name:"intro" ~usage:"intro N"
      ~description:"Try to introduce variables in the N-th hole."
      ~run:
        (command1 (fun state strat ->
             with_hole_from_strategy_string state strat
               (requiring_computation_hole state (fun (_, h) ->
                    let exp = Interactive.intro h in
                    let Holes.{ cD; info = { Holes.cG; _ }; _ } = h in
                    Printer.with_normal true (fun () ->
                        fprintf state "%a;"
                          (P.fmt_ppr_cmp_exp cD cG P.l0)
                          exp)))))

  let compconst =
    make_command ~name:"constructors-comp"
      ~usage:"constructors-comp IDENTIFIER"
      ~description:
        "Print all constructors of a given computational datatype passed as \
         a parameter."
      ~run:
        (command1 (fun state arg ->
             let name = read_qualified_identifier state arg in
             try
               let cid = index_of_comp_type_constant state name in
               let entry = Store.Cid.CompTyp.get cid in
               let termlist =
                 List.map Store.Cid.CompConst.get
                   !(entry.Store.Cid.CompTyp.Entry.constructors)
               in
               fprintf state "@[<v>%a@]@\n;"
                 (Format.pp_print_list ~pp_sep:Format.pp_print_cut
                    (fun state x ->
                      Format.fprintf state "%s : [%d] %a"
                        (Name.string_of_name x.Store.Cid.CompConst.Entry.name)
                        x.Store.Cid.CompConst.Entry.implicit_arguments
                        (P.fmt_ppr_cmp_typ LF.Empty P.l0)
                        x.Store.Cid.CompConst.Entry.typ))
                 termlist
             with
             | Not_found -> fprintf state "- The type %s does not exist;" arg))

  let function_signature =
    make_command ~name:"fsig" ~usage:"fsig IDENTIFIER"
      ~description:
        "Print the signature of the function if such a function is \
         currently defined."
      ~run:
        (command1 (fun state arg ->
             try
               let name = read_qualified_identifier state arg in
               let cid = index_of_comp_program state name in
               let entry = Store.Cid.Comp.get cid in
               fprintf state "%a : %a;" Name.pp
                 entry.Store.Cid.Comp.Entry.name
                 (P.fmt_ppr_cmp_typ LF.Empty P.l0)
                 entry.Store.Cid.Comp.Entry.typ
             with
             | Not_found -> fprintf state "- The function does not exist;"))

  let printfun =
    make_command ~name:"fdef" ~usage:"fdef IDENTIFIER"
      ~description:"Print the type of the function with the given name."
      ~run:
        (command1 (fun state arg ->
             try
               let name = read_qualified_identifier state arg in
               let cid = index_of_comp_program state name in
               let entry = Store.Cid.Comp.get cid in
               match entry.Store.Cid.Comp.Entry.prog with
               | Option.Some (Synint.Comp.ThmValue (_cid, body, _ms, _env))
                 ->
                   let identifier = Qualified_identifier.name name in
                   let typ = entry.Store.Cid.Comp.Entry.typ in
                   fprintf state "%a@\n" P.fmt_ppr_theorem
                     (identifier, body, typ)
               | _ -> fprintf state "- %s is not a function.;" arg
             with
             | Not_found ->
                 fprintf state "- The function %s does not exist;" arg))

  let read_comp_expression_and_print_type state input =
    let location = Beluga_syntax.Location.initial "<interactive>" in
    let exp, tau =
      read_comp_expression_and_infer_type state ~location input
    in
    fprintf state "%a : %a@\n"
      (P.fmt_ppr_cmp_exp LF.Empty LF.Empty P.l0)
      exp
      (P.fmt_ppr_cmp_typ LF.Empty P.l0)
      tau

  let print_type =
    make_command ~name:"type" ~usage:"print EXP"
      ~description:
        "Print the type of the input computation-level expression."
      ~run:(command1 read_comp_expression_and_print_type)

  let quit =
    make_command ~name:"quit" ~usage:"quit"
      ~description:"Exit interactive mode" ~run:(fun state ~input:_ ->
        fprintf state "Bye bye;";
        exit 0)

  let query =
    make_command ~name:"query" ~usage:"query EXPECTED TRIES TYP"
      ~description:"Query solutions to a given type."
      ~run:(fun state ~input ->
        try
          let location = Location.initial "<query>" in
          let expected, tries, identifier, (tA', i) =
            read_checked_query state ~location input
          in
          let name_opt = Option.map Name.make_from_identifier identifier in
          Logic.storeQuery name_opt (tA', i) Synint.LF.Empty expected tries;
          Logic.runLogic ();
          fprintf state ";"
        with
        | e -> fprintf state "- Error in query : %s;" (Printexc.to_string e))

  let get_type =
    make_command ~name:"get-type" ~usage:"get-type LINE COLUMN"
      ~description:"Get the type at a location (for use in emacs)."
      ~run:
        (command2 (fun state line_token column_token ->
             let line = read_line_number state line_token in
             let column = read_column_number state column_token in
             let typ = Typeinfo.type_of_position line column in
             fprintf state "%s;" typ))

  let lookup_hole =
    make_command ~name:"lookuphole" ~usage:"lookuphole N"
      ~description:"Look up a hole's number by its name."
      ~run:
        (command1 (fun state strat ->
             with_hole_from_strategy_string state strat (fun (i, _) ->
                 fprintf state "%s;" (HoleId.string_of_hole_id i))))

  let parse_command input =
    let trimmed_input = String.trim input in
    let l = String.length trimmed_input in
    if l >= 2 && String.equal (String.sub trimmed_input 0 2) "%:" then
      let command_token = String.sub trimmed_input 2 (l - 2) in
      let command, arguments_input =
        match String.index_from_opt command_token 0 ' ' with
        | Option.None -> (command_token, "")
        | Option.Some i ->
            let command = String.sub command_token 0 i in
            let arguments_input =
              String.sub command_token
                (i + 1 (* Discard [' '] *))
                (String.length command_token - i - 1)
            in
            (command, arguments_input)
      in
      `Command (command, arguments_input)
    else if l > 0 then `Input trimmed_input
    else `Empty

  let do_command state input =
    match parse_command input with
    | `Input input -> (
        try read_comp_expression_and_print_type state input with
        | Command_execution_error _ as e ->
            fprintf state "%s" (Printexc.to_string e)
        | e ->
            fprintf state "- Unhandled exception: %s;" (Printexc.to_string e)
        )
    | `Command (command, arguments_input) -> (
        let command = find_command state ~name:command in
        try run_command state command ~input:arguments_input with
        | Command_execution_error _ as e ->
            fprintf state "%s" (Printexc.to_string e)
        | e ->
            fprintf state "- Unhandled exception: %s;" (Printexc.to_string e)
        )
    | `Empty -> ()

  let print_usage state =
    fprintf state "Usage: \n";
    print_helpme state

  let commands =
    [ helpme
    ; chatteroff
    ; chatteron
    ; load
    ; reload
    ; clearholes
    ; countholes
    ; lochole
    ; printhole
    ; types
    ; constructors
    ; split
    ; intro
    ; compconst
    ; function_signature
    ; printfun
    ; query
    ; get_type
    ; reset
    ; quit
    ; lookup_hole
    ; solvelfhole
    ; print_type
    ]

  let register_commands state = List.iter (register_command state) commands
end

module Interpreter_state =
  Make_interpreter_state
    (Parser.Disambiguation_state)
    (Parser.Disambiguation)
    (Index_state.Indexing_state)
    (Index.Indexer)
    (Recsgn_state.Signature_reconstruction_state)
    (Recsgn.Signature_reconstruction)
module Interpreter = Make_interpreter (Interpreter_state)

let create_initial_state () =
  let disambiguation_state =
    Parser.Disambiguation_state.create_initial_state ()
  in
  let indexing_state = Index_state.Indexing_state.create_initial_state () in
  let signature_reconstruction_state =
    Recsgn_state.Signature_reconstruction_state.create_initial_state
      indexing_state
  in
  let state =
    Interpreter_state.create_state Format.std_formatter disambiguation_state
      indexing_state signature_reconstruction_state
  in
  Interpreter.register_commands state;
  state

type state = Interpreter.state

let fprintf = Interpreter.fprintf

let print_usage = Interpreter.print_usage

let interpret_command state ~input = Interpreter.do_command state input

let load state ~filename = Interpreter_state.load state ~filename
