open Support
open Beluga_syntax
open Common_parser

exception Illegal_comp_level_identifier of Identifier.t

let () =
  Error.register_exception_printer (function
    | Illegal_comp_level_identifier identifier ->
        Format.dprintf
          "The identifier %a may not be used as a computation-level \
           variable."
          Identifier.pp identifier
    | exn -> Error.raise_unsupported_exception_printing exn)

module type HARPOON_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val harpoon_proof : Synprs.harpoon_proof t

  val interactive_harpoon_command : Synprs.harpoon_repl_command t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Located_token.t
                 and type location = Location.t)
    (Meta_parser : Meta_parser.META_PARSER
                     with type state = Parser.state
                      and type token = Parser.token
                      and type location = Parser.location)
    (Comp_parser : Comp_parser.COMP_PARSER
                     with type state = Parser.state
                      and type token = Parser.token
                      and type location = Parser.location) :
  HARPOON_PARSER
    with type state = Parser.state
     and type token = Parser.token
     and type location = Parser.location = struct
  include Parser
  include Meta_parser
  include Comp_parser

  let boxity =
    let boxed = keyword "boxed" $> fun () -> `Boxed
    and unboxed = keyword "unboxed" $> fun () -> `Unboxed
    and strengthened = keyword "strengthened" $> fun () -> `Strengthened in
    choice [ boxed; unboxed; strengthened ]

  let interactive_harpoon_command =
    let intros =
      keyword "intros"
      &> maybe (some identifier)
      |> span
      $> (fun (location, introduced_variables) ->
           Synprs.Harpoon.Repl.Command.Intros
             { location; introduced_variables })
      |> labelled "Harpoon `intros' command"
    and split =
      keyword "split" &> comp_expression |> span
      $> (fun (location, scrutinee) ->
           Synprs.Harpoon.Repl.Command.Split { location; scrutinee })
      |> labelled "Harpoon `split' command"
    and msplit =
      keyword "msplit"
      &> span meta_object_identifier
      $> (fun (location, identifier) ->
           Synprs.Harpoon.Repl.Command.Msplit { location; identifier })
      |> labelled "Harpoon `msplit' command"
    and invert =
      keyword "invert" &> comp_expression |> span
      $> (fun (location, scrutinee) ->
           Synprs.Harpoon.Repl.Command.Invert { location; scrutinee })
      |> labelled "Harpoon `invert' command"
    and impossible =
      keyword "impossible" &> comp_expression |> span
      $> (fun (location, scrutinee) ->
           Synprs.Harpoon.Repl.Command.Impossible { location; scrutinee })
      |> labelled "Harpoon `impossible' command"
    and solve =
      keyword "solve" &> comp_expression |> span
      $> (fun (location, solution) ->
           Synprs.Harpoon.Repl.Command.Solve { location; solution })
      |> labelled "Harpoon `solve' command"
    and auto_invert_solve =
      keyword "auto-invert-solve"
      &> maybe integer |> span
      $> (fun (location, max_depth) ->
           Synprs.Harpoon.Repl.Command.Auto_invert_solve
             { location; max_depth })
      |> labelled "Harpoon `auto-invert-solve' command"
    and inductive_auto_solve =
      keyword "inductive-auto-solve"
      &> maybe integer |> span
      $> (fun (location, max_depth) ->
           Synprs.Harpoon.Repl.Command.Inductive_auto_solve
             { location; max_depth })
      |> labelled "Harpoon `inductive-auto-solve' command"
    and by =
      keyword "by"
      &> seq3 comp_expression
           (keyword "as" &> meta_object_identifier)
           (maybe boxity)
      |> span
      >>= (function
            | ( _location
              , ( _expression
                , (assignee, (`Hash | `Dollar))
                , (Option.None | Option.Some `Boxed) ) ) ->
                fail_at_location
                  (Identifier.location assignee)
                  (Illegal_comp_level_identifier assignee)
            | ( location
              , ( expression
                , (assignee, `Plain)
                , (Option.None | Option.Some `Boxed) ) ) ->
                return
                  (Synprs.Harpoon.Repl.Command.By
                     { location; assignee; expression })
            | location, (expression, assignee, Option.Some `Unboxed) ->
                return
                  (Synprs.Harpoon.Repl.Command.Unbox
                     { location
                     ; assignee
                     ; expression
                     ; modifier = Option.none
                     })
            | location, (expression, assignee, Option.Some `Strengthened) ->
                return
                  (Synprs.Harpoon.Repl.Command.Unbox
                     { location
                     ; assignee
                     ; expression
                     ; modifier = Option.some `Strengthened
                     }))
      |> labelled "Harpoon `by' command"
    and compute_type =
      keyword "type" &> comp_expression |> span
      $> (fun (location, scrutinee) ->
           Synprs.Harpoon.Repl.Command.Type { location; scrutinee })
      |> labelled "Harpoon `type' command"
    and suffices =
      let tau_list_item =
        alt
          (comp_typ $> fun tau -> `exact tau)
          (underscore |> span $> fun (loc, ()) -> `infer loc)
      in
      seq2
        (keyword "suffices" &> keyword "by" &> comp_expression)
        (keyword "toshow" &> sep_by0 ~sep:comma tau_list_item)
      |> span
      $> (fun (location, (implication, goal_premises)) ->
           Synprs.Harpoon.Repl.Command.Suffices
             { location; implication; goal_premises })
      |> labelled "Harpoon `suffices' command"
    and unbox =
      keyword "unbox"
      &> seq2 comp_expression (keyword "as" &> meta_object_identifier)
      |> span
      $> (fun (location, (expression, assignee)) ->
           Synprs.Harpoon.Repl.Command.Unbox
             { location; expression; assignee; modifier = Option.none })
      |> labelled "Harpoon `unbox' command"
    and strengthen =
      keyword "strengthen"
      &> seq2 comp_expression (keyword "as" &> meta_object_identifier)
      |> span
      $> (fun (location, (expression, assignee)) ->
           Synprs.Harpoon.Repl.Command.Unbox
             { location
             ; expression
             ; assignee
             ; modifier = Option.some `Strengthened
             })
      |> labelled "Harpoon `strengthen' command"
    and toggle_automation =
      let automation_kind =
        let auto_intros = keyword "auto-intros" $> fun () -> `auto_intros
        and auto_solve_trivial =
          keyword "auto-solve-trivial" $> fun () -> `auto_solve_trivial
        in
        choice [ auto_intros; auto_solve_trivial ]
      and automation_change =
        let on = keyword "on" $> fun () -> `on
        and off = keyword "off" $> fun () -> `off
        and toggle = keyword "toggle" $> fun () -> `toggle in
        choice [ on; off; toggle ]
      in
      keyword "toggle-automation"
      &> seq2 automation_kind (maybe automation_change)
      |> span
      $> (fun (location, (kind, change)) ->
           Synprs.Harpoon.Repl.Command.Toggle_automation
             { location
             ; kind
             ; change = Option.value ~default:`toggle change
             })
      |> labelled "Harpoon `toggle-automation' command"
    and rename =
      let level =
        let comp_level = keyword "comp" $> fun () -> `comp
        and meta_level = keyword "meta" $> fun () -> `meta in
        choice [ comp_level; meta_level ]
      in
      keyword "rename"
      &> seq3 level meta_object_identifier meta_object_identifier
      |> span
      $> (fun (location, (level, rename_from, rename_to)) ->
           Synprs.Harpoon.Repl.Command.Rename
             { location; rename_from; rename_to; level })
      |> labelled "Harpoon `rename' command"
    and select_theorem =
      keyword "select" &> qualified_identifier |> span
      $> (fun (location, theorem) ->
           Synprs.Harpoon.Repl.Command.Select_theorem { location; theorem })
      |> labelled "Harpoon `select' command"
    and theorem_command =
      let list_theorems = keyword "list" $> fun () -> `list
      and defer_theorem = keyword "defer" $> fun () -> `defer
      and dump_proof =
        keyword "dump-proof" &> string_literal $> fun s -> `dump_proof s
      and show_ihs = keyword "show-ihs" $> fun () -> `show_ihs
      and show_proof = keyword "show-proof" $> fun () -> `show_proof in
      keyword "theorem"
      &> choice
           [ list_theorems; defer_theorem; dump_proof; show_ihs; show_proof ]
      |> span
      $> (fun (location, subcommand) ->
           Synprs.Harpoon.Repl.Command.Theorem { location; subcommand })
      |> labelled "Harpoon `theorem' command"
    and session_command =
      let list_sessions = keyword "list" $> fun () -> `list
      and defer_session = keyword "defer" $> fun () -> `defer
      and create_command = keyword "create" $> fun () -> `create
      and serialize_command = keyword "serialize" $> fun () -> `serialize in
      keyword "session"
      &> choice
           [ list_sessions
           ; defer_session
           ; create_command
           ; serialize_command
           ]
      |> span
      $> (fun (location, subcommand) ->
           Synprs.Harpoon.Repl.Command.Session { location; subcommand })
      |> labelled "Harpoon `session' command"
    and subgoal_command =
      let list_subgoals = keyword "list" $> fun () -> `list
      and defer_subgoal = keyword "defer" $> fun () -> `defer in
      keyword "subgoal"
      &> choice [ list_subgoals; defer_subgoal ]
      |> span
      $> (fun (location, subcommand) ->
           Synprs.Harpoon.Repl.Command.Subgoal { location; subcommand })
      |> labelled "Harpoon `subgoal' command"
    and defer =
      keyword "defer" |> span
      $> (fun (location, ()) ->
           Synprs.Harpoon.Repl.Command.Subgoal
             { location; subcommand = `defer })
      |> labelled "Harpoon `defer' command"
    and info =
      let theorem = keyword "theorem" $> fun () -> `prog in
      let info_kind = choice [ theorem ] in
      keyword "info"
      &> seq2 info_kind qualified_identifier
      |> span
      $> (fun (location, (kind, object_identifier)) ->
           Synprs.Harpoon.Repl.Command.Info
             { location; kind; object_identifier })
      |> labelled "Harpoon `info' command"
    and translate =
      keyword "translate" &> qualified_identifier |> span
      $> (fun (location, theorem) ->
           Synprs.Harpoon.Repl.Command.Translate { location; theorem })
      |> labelled "Harpoon `translate' command"
    and undo =
      keyword "undo" |> span
      $> (fun (location, ()) ->
           Synprs.Harpoon.Repl.Command.Undo { location })
      |> labelled "Harpoon `undo' command"
    and redo =
      keyword "redo" |> span
      $> (fun (location, ()) ->
           Synprs.Harpoon.Repl.Command.Redo { location })
      |> labelled "Harpoon `redo' command"
    and history =
      keyword "history" |> span
      $> (fun (location, ()) ->
           Synprs.Harpoon.Repl.Command.History { location })
      |> labelled "Harpoon `history' command"
    and help =
      keyword "help" |> span
      $> (fun (location, ()) ->
           Synprs.Harpoon.Repl.Command.Help { location })
      |> labelled "Harpoon `help' command"
    and save =
      keyword "save" |> span
      $> (fun (location, ()) ->
           Synprs.Harpoon.Repl.Command.Session
             { location; subcommand = `serialize })
      |> labelled "Harpoon `save' command"
    in
    choice
      [ intros
      ; info
      ; split
      ; msplit
      ; compute_type
      ; invert
      ; impossible
      ; solve
      ; auto_invert_solve
      ; inductive_auto_solve
      ; by
      ; suffices
      ; unbox
      ; strengthen
      ; translate
      ; toggle_automation
      ; rename
      ; defer
      ; select_theorem
      ; theorem_command
      ; session_command
      ; subgoal_command
      ; undo
      ; redo
      ; history
      ; help
      ; save
      ]

  module rec Harpoon_parsers : sig
    val harpoon_proof : Synprs.harpoon_proof t
  end = struct
    let harpoon_command =
      let by =
        keyword "by"
        &> seq3 (comp_expression <& keyword "as") identifier (maybe boxity)
        |> span
        |> labelled "Harpoon command"
        $> function
        | location, (expression, assignee, (Option.None | Option.Some `Boxed))
          ->
            Synprs.Harpoon.Command.By { location; assignee; expression }
        | location, (expression, assignee, Option.Some `Unboxed) ->
            Synprs.Harpoon.Command.Unbox
              { location; assignee; expression; modifier = Option.none }
        | location, (expression, assignee, Option.Some `Strengthened) ->
            Synprs.Harpoon.Command.Unbox
              { location
              ; assignee
              ; expression
              ; modifier = Option.some `Strengthened
              }
      and unbox =
        keyword "unbox"
        &> seq2 (span comp_expression <& keyword "as") identifier
        $> fun ((location, expression), assignee) ->
        Synprs.Harpoon.Command.Unbox
          { location; assignee; expression; modifier = Option.none }
      and strengthen =
        keyword "strengthen"
        &> seq2 (span comp_expression <& keyword "as") identifier
        $> fun ((location, expression), assignee) ->
        Synprs.Harpoon.Command.Unbox
          { location
          ; assignee
          ; expression
          ; modifier = Option.some `Strengthened
          }
      in
      choice [ by; unbox; strengthen ]

    let split_branch_label =
      let extension_case_label =
        trying (keyword "extended" &> keyword "by")
        &> integer |> span
        |> labelled "context extension case label"
        $> fun (location, schema_element) ->
        Synprs.Harpoon.Split_branch.Label.Extended_context
          { location; schema_element }
      and empty_case_label =
        trying (keyword "empty" &> keyword "context")
        |> span
        |> labelled "empty context case label"
        $> fun (location, ()) ->
        Synprs.Harpoon.Split_branch.Label.Empty_context { location }
      and constant_case_label =
        qualified_identifier |> span |> labelled "constructor case label"
        $> fun (location, identifier) ->
        Synprs.Harpoon.Split_branch.Label.Constant { location; identifier }
      and pvar_case_label =
        hash
        &> seq2 (maybe integer) (maybe dot_integer)
        |> span
        |> labelled "parameter variable case label"
        $> fun (location, (n, k)) ->
        Synprs.Harpoon.Split_branch.Label.Parameter_variable
          { location
          ; schema_element = Option.value ~default:1 n
          ; projection = k
          }
      and bvar_case_label =
        trying (keyword "head" &> keyword "variable") |> span
        $> fun (location, ()) ->
        Synprs.Harpoon.Split_branch.Label.Bound_variable { location }
      in
      choice
        [ bvar_case_label
        ; extension_case_label
        ; empty_case_label
        ; constant_case_label
        ; pvar_case_label
        ]

    let harpoon_hypothetical =
      let hypotheses = seq3 meta_context pipe comp_context in
      seq2 (hypotheses <& semicolon) Harpoon_parsers.harpoon_proof
      |> braces |> span
      |> labelled "Harpoon hypothetical"
      $> fun (location, ((meta_context, (), comp_context), proof)) ->
      { Synprs.Harpoon.Hypothetical.location
      ; meta_context
      ; comp_context
      ; proof
      }

    let harpoon_split_branch =
      keyword "case"
      &> seq2 (split_branch_label <& colon) harpoon_hypothetical
      |> span
      |> labelled "Harpoon split branch"
      $> fun (location, (label, body)) ->
      { Synprs.Harpoon.Split_branch.location; label; body }

    let harpoon_directive =
      let intros =
        keyword "intros" &> harpoon_hypothetical |> span
        $> fun (location, hypothetical) ->
        Synprs.Harpoon.Directive.Intros { location; hypothetical }
      and solve =
        keyword "solve" &> comp_expression |> span
        $> fun (location, solution) ->
        Synprs.Harpoon.Directive.Solve { location; solution }
      and split =
        keyword "split"
        &> seq2 comp_expression (keyword "as" &> some harpoon_split_branch)
        |> span
        $> fun (location, (scrutinee, branches)) ->
        Synprs.Harpoon.Directive.Split { location; scrutinee; branches }
      and impossible =
        keyword "impossible" &> comp_expression |> span
        $> fun (location, scrutinee) ->
        Synprs.Harpoon.Directive.Impossible { location; scrutinee }
      and suffices =
        let suffices_branch =
          seq2 comp_typ (braces Harpoon_parsers.harpoon_proof) |> span
          $> fun (location, (goal, proof)) ->
          { Synprs.Harpoon.Suffices_branch.location; goal; proof }
        in
        keyword "suffices" &> keyword "by"
        &> seq2 (comp_expression <& keyword "toshow") (many suffices_branch)
        |> span
        $> fun (location, (scrutinee, branches)) ->
        Synprs.Harpoon.Directive.Suffices { location; scrutinee; branches }
      in
      choice [ intros; solve; split; impossible; suffices ]
      |> labelled "Harpoon directive"

    let harpoon_proof =
      let incomplete_proof =
        hole |> span |> labelled "Harpoon incomplete proof `?'" $> function
        | location, `Unlabelled ->
            Synprs.Harpoon.Proof.Incomplete { location; label = Option.none }
        | location, `Labelled label ->
            Synprs.Harpoon.Proof.Incomplete
              { location; label = Option.some label }
      and command_proof =
        seq2 (harpoon_command <& semicolon) Harpoon_parsers.harpoon_proof
        |> span
        $> fun (location, (command, body)) ->
        Synprs.Harpoon.Proof.Command { location; command; body }
      and directive_proof =
        harpoon_directive |> span $> fun (location, directive) ->
        Synprs.Harpoon.Proof.Directive { location; directive }
      in
      choice [ incomplete_proof; command_proof; directive_proof ]
      |> labelled "Harpoon proof"
  end

  let harpoon_proof = Harpoon_parsers.harpoon_proof
end
