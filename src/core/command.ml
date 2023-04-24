(** Top level functions invoked by the interactive mode.

    Each interactive mode command corresponds with a {!command} record in
    this file. Available commands are added to a registry at the bottom of
    this file. *)

open Support.Equality
open Support
open Beluga_syntax
open Beluga_parser
module P = Prettyint.DefaultPrinter
open Syntax.Int

[@@@warning "-A-4-44"] (* FIXME: *)

exception Duplicate_command_name of String.t

exception Line_parse_error

exception Column_parse_error

(** The exception variant signaling a recoverable failure to executing a
    command in the interpreter. If this exception is raised during the
    evaluation of a command, then the command has failed, but the interpreter
    is not in an invalid state. *)
exception Command_execution_error of exn

let () =
  Error.register_exception_printer (function
    | Duplicate_command_name command_name ->
        Format.dprintf
          "There is already a registered command with name \"%s\"."
          command_name
    | Line_parse_error -> Format.dprintf "Failed to parse the line number."
    | Column_parse_error ->
        Format.dprintf "Failed to parse the column number."
    | Command_execution_error cause ->
        let cause_printer = Error.find_printer cause in
        Format.dprintf "@[<v>- Failed to execute command.@,%t@]"
          cause_printer
    | cause -> Error.raise_unsupported_exception_printing cause)

let raise_command_execution_error cause =
  Error.raise (Command_execution_error cause)

let parse_int ~on_error token =
  match int_of_string_opt token with
  | Option.None -> on_error ()
  | Option.Some line -> line

let parse_line_number =
  parse_int ~on_error:(fun () ->
      raise_command_execution_error Line_parse_error)

let parse_column_number =
  parse_int ~on_error:(fun () ->
      raise_command_execution_error Column_parse_error)

module type COMMAND_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  type command

  val make_command :
       name:String.t
    -> help:String.t
    -> run:(state -> input:String.t -> Unit.t)
    -> command

  val command_help : command -> String.t

  val run_command : state -> command -> input:String.t -> Unit.t

  val register_command : state -> command -> Unit.t

  val find_command_opt : state -> name:String.t -> command Option.t

  val iter_commands :
    state -> (command_name:String.t -> command:command -> Unit.t) -> Unit.t

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
end

module Make_command_state
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
    ; commands : command String.Hashtbl.t
    ; disambiguation_state : Disambiguation_state.state
    ; index_state : Indexing_state.state
    ; signature_reconstruction_state : Signature_reconstruction_state.state
    }

  and command =
    { name : String.t
    ; help : String.t
    ; run : state -> input:String.t -> Unit.t
    }

  let create_state ppf disambiguation_state index_state
      signature_reconstruction_state =
    { ppf
    ; commands = String.Hashtbl.create 20
    ; disambiguation_state
    ; index_state
    ; signature_reconstruction_state
    }

  include (
    Imperative_state.Make (struct
      type nonrec state = state
    end) :
      Imperative_state.IMPERATIVE_STATE with type state := state)

  let make_command ~name ~help ~run = { name; help; run }

  let command_help command = command.help

  let run_command state command ~input = command.run state ~input

  let is_command state command_name =
    String.Hashtbl.mem state.commands command_name

  let register_command state command =
    if String.Hashtbl.mem state.commands command.name then
      Error.raise (Duplicate_command_name command.name)
    else String.Hashtbl.add state.commands command.name command

  let find_command_opt state ~name =
    String.Hashtbl.find_opt state.commands name

  let get_commands state =
    String.Hashtbl.fold String.Map.add state.commands String.Map.empty

  let iter_commands state f =
    String.Hashtbl.iter
      (fun command_name command -> f ~command_name ~command)
      state.commands

  let fprintf state = Format.fprintf state.ppf

  let comp_expression_parser = Parser.Parsing.(only comp_expression)

  let comp_expression_disambiguator state exp =
    Parser.Disambiguation.(
      with_bindings_checkpoint state (fun state ->
          disambiguate_comp_expression state exp))

  let read_comp_expression_and_infer_type state ?(location = Location.ghost)
      input =
    let token_sequence = Lexer.lex_string ~initial_location:location input in
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
      Indexing_state.with_bindings_checkpoint state.index_state (fun state ->
          Indexer.index_comp_expression state exp)
    in
    (* FIXME: The following elaboration steps need checkpoints *)
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
    let token_sequence = Lexer.lex_string ~initial_location:location input in
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
      parser_state

  let read_checked_query state ?(location = Location.ghost) input =
    let expected, tries, identifier, extT =
      read_query state ~location input
    in
    let apxT =
      Indexing_state.with_bindings_checkpoint state.index_state (fun state ->
          Indexer.index_open_lf_typ state extT)
    in
    (* FIXME: The following reconstruction steps need checkpoints *)
    Store.FVar.clear ();
    let tA = Reconstruct.typ Lfrecon.Pi apxT in
    Reconstruct.solve_fvarCnstr Lfrecon.Pi;
    Unify.StdTrail.forceGlobalCnstr ();
    let tA', i = Abstract.typ tA in
    Reconstruct.reset_fvarCnstr ();
    Unify.StdTrail.resetGlobalCnstrs ();
    Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', Substitution.LF.id);
    (expected, tries, identifier, (tA', i))
end

module type COMMAND = sig
  include Imperative_state.IMPERATIVE_STATE
  (* TODO: *)
end

module Make (State : COMMAND_STATE) = struct
  include State

  (* The built-in commands *)

  (** Used to define command bodies requiring a certain number of arguments.

      This function checks the length of the argument list against the given
      number, and in case of success runs the given command body function. *)
  let command_with_arguments n f state ~input =
    let arguments = String.split_on_char ' ' input in
    let n' = List.length arguments in
    if n = n' then f state arguments
    else
      fprintf state "- Command requires %d arguments, but %d were given;\n" n
        n'

  let command0 f =
    command_with_arguments 0 (fun [@warning "-8"] state [] -> f state)

  let command1 f =
    command_with_arguments 1 (fun [@warning "-8"] state [ a ] -> f state a)

  let command2 f =
    command_with_arguments 2 (fun [@warning "-8"] state [ a1; a2 ] ->
        f state a1 a2)

  let countholes =
    make_command ~name:"countholes" ~help:"Print the total number of holes"
      ~run:(command0 (fun state -> fprintf state "%d;\n" (Holes.count ())))

  let chatteron =
    make_command ~name:"chatteron" ~help:"Turn on the chatter"
      ~run:
        (command0 (fun state ->
             Chatter.level := 1;
             fprintf state "The chatter is on now;\n"))

  let chatteroff =
    make_command ~name:"chatteroff" ~help:"Turn off the chatter"
      ~run:
        (command0 (fun state ->
             Chatter.level := 0;
             fprintf state "The chatter is off now;\n"))

  let types =
    make_command ~name:"types" ~help:"Print out all types currently defined"
      ~run:
        (command0 (fun state ->
             let entrylist =
               List.map Pair.snd (Store.Cid.Typ.current_entries ())
             in
             let dctx = Synint.LF.Null in
             fprintf state "@[<v>%a@];\n"
               (Format.pp_print_list ~pp_sep:Format.pp_print_cut
                  (fun state x ->
                    Format.fprintf state "%a : %a" Name.pp
                      x.Store.Cid.Typ.Entry.name
                      (P.fmt_ppr_lf_kind dctx P.l0)
                      x.Store.Cid.Typ.Entry.kind))
               entrylist))

  let reset =
    make_command ~name:"reset" ~help:"Reset the store"
      ~run:
        (command0 (fun state ->
             Store.clear ();
             Typeinfo.clear_all ();
             Holes.clear ();
             fprintf state "Reset successful;\n"))

  let clearholes =
    make_command ~name:"clearholes" ~help:"Clear all computation level holes"
      ~run:(command0 (fun _state -> Holes.clear ()))

  let reload, load =
    let do_load state path =
      ignore
        (Load.load
           (Obj.magic () (* TODO: *))
           (Obj.magic () (* TODO: *))
           path);
      fprintf state "The file %s has been successfully loaded;\n" path
    and last_load : string option ref = ref Option.none in
    let reload =
      make_command ~name:"reload"
        ~help:
          "Clears the interpreter state and repeats the last load command."
        ~run:
          (command0 (fun state ->
               match !last_load with
               | Option.None -> fprintf state "- No load to repeat;"
               | Option.Some path -> do_load state path))
    and load =
      make_command ~name:"load"
        ~help:"Clears the interpreter state and loads the file \"filename\"."
        ~run:
          (command1 (fun state path ->
               (* .bel or .cfg *)
               do_load state path;
               last_load := Option.some path))
    in
    (reload, load)

  (** Parses the given hole lookup strategy string, and retrieves a hole
      using that strategy.

      If the string is invalid, or the lookup fails, an error is displayed.
      Otherwise, the given function is executed with the hole identifier and
      information. *)
  let with_hole_from_strategy_string state (strat : string)
      (f : HoleId.t * Holes.some_hole -> unit) : unit =
    match Holes.parse_lookup_strategy strat with
    | Option.None ->
        fprintf state "- Failed to parse hole identifier `%s';\n" strat
    | Option.Some s -> (
        match Holes.get s with
        | Option.Some id_and_hole -> f id_and_hole
        | Option.None ->
            fprintf state "- No such hole %s;\n"
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
        fprintf state "- Hole %s is already solved;\n"
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
            fprintf state "- Hole %s is not a computational hole;\n"
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
            fprintf state "- Hole %s is not an LF hole;\n"
              (string_of_id_hole (id, h)))
      p

  let printhole =
    make_command ~name:"printhole"
      ~help:
        "Print out all the information of the i-th hole passed as a \
         parameter"
      ~run:
        (command1 (fun state s ->
             with_hole_from_strategy_string state s
               (fprintf state "%a;\n" Interactive.fmt_ppr_hole)))

  let lochole =
    make_command ~name:"lochole"
      ~help:
        "Print out the location information of the i-th hole passed as a \
         parameter"
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
                 fprintf state "(\"%s\" %d %d %d %d %d %d);\n" file_name
                   start_line start_bol start_off stop_line stop_bol stop_off)))

  let solvelfhole =
    make_command ~name:"solve-lf-hole"
      ~help:"Use logic programming to solve an LF hole"
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
                    (try
                       let n =
                         ref 0
                         (* FIXME: Why are we restricting the logic search by
                            some arbitrary number of iterations? *)
                       in
                       Logic.Solver.solve cD cPsi query
                         (fun (ctx, norm) ->
                           fprintf state "%a@\n"
                             (P.fmt_ppr_lf_normal cD
                                ctx P.l0)
                             norm;
                           incr n;
                           if !n = 10 then raise Logic.Frontend.Done)
                         (Option.some 100)
                     with
                    | Logic.Frontend.Done -> ()
                    | e -> raise e);
                    fprintf state ";\n"))))

  let constructors =
    make_command ~name:"constructors"
      ~help:"Print all constructors of a given type passed as a parameter"
      ~run:
        (command1 (fun state n ->
             let typ_name = Name.(mk_name (SomeString n)) in
             let entry =
               Store.Cid.Typ.index_of_name typ_name |> Store.Cid.Typ.get
             in
             let termlist =
               List.map Store.Cid.Term.get
                 !(entry.Store.Cid.Typ.Entry.constructors)
             in
             fprintf state "@[<v>%a@]@\n;@\n"
               (Format.pp_print_list ~pp_sep:Format.pp_print_cut
                  (fun state x ->
                    Format.fprintf state "%a : [%d] %a" Name.pp
                      x.Store.Cid.Term.Entry.name
                      x.Store.Cid.Term.Entry.implicit_arguments
                      (P.fmt_ppr_lf_typ LF.Empty LF.Null P.l0)
                      x.Store.Cid.Term.Entry.typ))
               termlist))

  let print_helpme state =
    iter_commands state (fun ~command_name ~command ->
        let help = command_help command in
        fprintf state "%%:%20s\t %s\n" command_name help)

  let helpme =
    make_command ~name:"help"
      ~help:"list all available commands with a short description"
      ~run:(command0 print_helpme)

  (** Actually does a split on a variable in a hole.

      Requires that the hole is a computation hole. *)
  let do_split state (hi : HoleId.t * Holes.comp_hole_info Holes.hole)
      (var : string) : unit =
    match Interactive.split var hi with
    | Option.None -> fprintf state "- No variable %s found;\n" var
    | Option.Some exp ->
        let _, h = hi in
        let { Holes.cG; _ } = h.Holes.info in
        Printer.with_normal true (fun () ->
            fprintf state "%a;\n" (P.fmt_ppr_cmp_exp h.Holes.cD cG P.l0) exp)

  let split =
    make_command ~name:"split"
      ~help:
        "`split H V` tries to split on variable V in hole H (specified by \
         name or number)"
      ~run:
        (command2 (fun state strat_s var ->
             with_hole_from_strategy_string state strat_s
               (requiring_computation_hole state (fun hi ->
                    do_split state hi var))))

  let intro =
    make_command ~name:"intro"
      ~help:"- intro n tries to introduce variables in the nth hole"
      ~run:
        (command1 (fun state strat ->
             with_hole_from_strategy_string state strat
               (requiring_computation_hole state (fun (_, h) ->
                    let exp = Interactive.intro h in
                    let Holes.{ cD; info = { Holes.cG; _ }; _ } = h in
                    Printer.Control.printNormal := true;
                    fprintf state "%a;\n" (P.fmt_ppr_cmp_exp cD cG P.l0) exp;
                    Printer.Control.printNormal := false))))

  let compconst =
    make_command ~name:"constructors-comp"
      ~help:
        "Print all constructors of a given computational datatype passed as \
         a parameter"
      ~run:
        (command1 (fun state arg ->
             let name = Name.(mk_name (SomeString arg)) in
             try
               let entry =
                 Store.Cid.CompTyp.index_of_name name
                 |> Store.Cid.CompTyp.get
               in
               let termlist =
                 List.map Store.Cid.CompConst.get
                   !(entry.Store.Cid.CompTyp.Entry.constructors)
               in
               fprintf state "@[<v>%a@]@\n;@\n"
                 (Format.pp_print_list ~pp_sep:Format.pp_print_cut
                    (fun state x ->
                      Format.fprintf state "%s : [%d] %a"
                        (Name.string_of_name x.Store.Cid.CompConst.Entry.name)
                        x.Store.Cid.CompConst.Entry.implicit_arguments
                        (P.fmt_ppr_cmp_typ LF.Empty P.l0)
                        x.Store.Cid.CompConst.Entry.typ))
                 termlist
             with
             | Not_found ->
                 fprintf state "- The type %s does not exist;\n" arg))

  let signature =
    make_command ~name:"fsig"
      ~help:
        "fsig e : Prints the signature of the function e, if such function \
         is currently defined"
      ~run:
        (command1 (fun state arg ->
             try
               let name = Name.(mk_name (SomeString arg)) in
               let entry =
                 Store.Cid.Comp.index_of_name name |> Store.Cid.Comp.get
               in
               fprintf state "%a : %a;@\n" Name.pp
                 entry.Store.Cid.Comp.Entry.name
                 (P.fmt_ppr_cmp_typ LF.Empty P.l0)
                 entry.Store.Cid.Comp.Entry.typ
             with
             | Not_found -> fprintf state "- The function does not exist;\n"))

  let printfun =
    make_command ~name:"fdef"
      ~help:"Print the type of the function with the given name"
      ~run:
        (command1 (fun state arg ->
             try
               let name = Name.(mk_name (SomeString arg)) in
               let entry =
                 Store.Cid.Comp.get (Store.Cid.Comp.index_of_name name)
               in
               match entry.Store.Cid.Comp.Entry.prog with
               | Option.Some (Synint.Comp.ThmValue (cid, body, _ms, _env)) ->
                   let d =
                     Syntax.Int.Sgn.Theorem
                       { name
                       ; cid
                       ; typ = entry.Store.Cid.Comp.Entry.typ
                       ; body
                       ; location = Location.ghost
                       }
                   in
                   fprintf state "%a@\n" P.fmt_ppr_sgn_decl
                     (Synint.Sgn.Theorems
                        { location = Location.ghost
                        ; theorems = List1.singleton d
                        })
               | _ -> fprintf state "- %s is not a function.;@\n" arg
             with
             | Not_found ->
                 fprintf state "- The function %s does not exist;@\n" arg))

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
    make_command ~name:"type"
      ~help:"Print the type of the input computation-level expression"
      ~run:(command1 read_comp_expression_and_print_type)

  let quit =
    make_command ~name:"quit" ~help:"Exit interactive mode"
      ~run:(fun state ~input:_ ->
        fprintf state "Bye bye@\n";
        exit 0)

  let query =
    make_command ~name:"query"
      ~help:"%:query EXPECTED TRIES TYP.\tQuery solutions to a given type"
      ~run:(fun state ~input ->
        try
          let location = Location.initial "<query>" in
          let expected, tries, identifier, (tA', i) =
            read_checked_query state ~location input
          in
          let name_opt = Option.map Name.make_from_identifier identifier in
          Logic.storeQuery name_opt (tA', i) Synint.LF.Empty expected tries;
          Logic.runLogic ();
          fprintf state ";\n"
        with
        | e ->
            fprintf state "- Error in query : %s;\n" (Printexc.to_string e))

  let get_type =
    make_command ~name:"get-type"
      ~help:
        "get-type [line] [column] Get the type at a location (for use in \
         emacs)"
      ~run:
        (command2 (fun state line_token column_token ->
             let line = parse_line_number line_token in
             let column = parse_column_number column_token in
             let typ = Typeinfo.type_of_position line column in
             fprintf state "%s;\n" typ))

  let lookup_hole =
    make_command ~name:"lookuphole"
      ~help:"looks up a hole's number by its name"
      ~run:
        (command1 (fun state strat ->
             with_hole_from_strategy_string state strat (fun (i, _) ->
                 fprintf state "%s;\n" (HoleId.string_of_hole_id i))))

  let is_command str =
    let str' = String.trim str in
    let l = String.length str' in
    if l >= 2 && String.equal (String.sub str' 0 2) "%:" then
      let cmd = String.sub str' 2 (l - 2) in
      `Cmd (String.trim cmd)
    else `Input str

  let do_command state input =
    let trimmed_input = String.trim input in
    if String.is_empty trimmed_input then ()
    else
      let command, arguments_input =
        match String.index_from_opt trimmed_input 0 ' ' with
        | Option.None -> (trimmed_input, "")
        | Option.Some i ->
            let command = String.sub trimmed_input 0 i in
            let arguments_input =
              String.sub trimmed_input
                (i + 1 (* Discard [' '] *))
                (String.length trimmed_input - i - 1)
            in
            (command, arguments_input)
      in
      let command_runner =
        match find_command_opt state ~name:command with
        | Option.Some command ->
            fun ~input -> run_command state command ~input
        | Option.None ->
            (* Default command *)
            fun ~input -> read_comp_expression_and_print_type state input
      in
      try command_runner ~input:arguments_input with
      | Command_execution_error _ as e ->
          fprintf state "%s" (Printexc.to_string e)
      | e ->
          fprintf state "- Unhandled exception: %s;\n" (Printexc.to_string e)

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
    ; signature
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

module Command_state =
  Make_command_state (Parser.Disambiguation_state) (Parser.Disambiguation)
    (Index_state.Indexing_state)
    (Index.Indexer)
    (Recsgn_state.Signature_reconstruction_state)
    (Recsgn.Signature_reconstruction)
module Command = Make (Command_state)

let create_initial_state = Obj.magic () (* Command_state.create_state *)

(* TODO: *)
(* TODO: Register commands *)

type state = unit

let fprintf = Obj.magic ()

let print_usage = Obj.magic ()

let interpret_command = Obj.magic ()

let load = Obj.magic ()
