open Support
open Beluga_syntax
open Common_parser
module Harpoon = Synprs.Harpoon

module rec Harpoon_parsers : sig
  val harpoon_proof : Harpoon.Proof.t t

  val interactive_harpoon_command : Harpoon.Repl.Command.t t

  val interactive_harpoon_command_sequence : Harpoon.Repl.Command.t List.t t

  val next_theorem : [> `next of Identifier.t | `quit ] t
end = struct
  let boxity =
    let boxed = keyword "boxed" $> fun () -> `Boxed
    and unboxed = keyword "unboxed" $> fun () -> `Unboxed
    and strengthened = keyword "strengthened" $> fun () -> `Strengthened in
    choice [ boxed; unboxed; strengthened ]

  let harpoon_command =
    let by =
      keyword "by"
      &> seq3
           (Comp_parser.comp_expression_object <& keyword "as")
           identifier
           (maybe_default boxity ~default:`Boxed)
      |> span
      |> labelled "Harpoon command"
      $> function
      | location, (expression, assignee, `Boxed) ->
          Harpoon.Command.By { location; assignee; expression }
      | location, (expression, assignee, `Unboxed) ->
          Harpoon.Command.Unbox
            { location; assignee; expression; modifier = Option.none }
      | location, (expression, assignee, `Strengthened) ->
          Harpoon.Command.Unbox
            { location
            ; assignee
            ; expression
            ; modifier = Option.some `Strengthened
            }
    and unbox =
      keyword "unbox"
      &> seq2
           (span Comp_parser.comp_expression_object <& keyword "as")
           identifier
      $> fun ((location, expression), assignee) ->
      Harpoon.Command.Unbox
        { location; assignee; expression; modifier = Option.none }
    and strengthen =
      keyword "strengthen"
      &> seq2
           (span Comp_parser.comp_expression_object <& keyword "as")
           identifier
      $> fun ((location, expression), assignee) ->
      Harpoon.Command.Unbox
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
      Harpoon.Split_branch.Label.Extended_context
        { location; schema_element }
    and empty_case_label =
      trying (keyword "empty" &> keyword "context")
      |> span
      |> labelled "empty context case label"
      $> fun (location, ()) ->
      Harpoon.Split_branch.Label.Empty_context { location }
    and constant_case_label =
      qualified_identifier |> span |> labelled "constructor case label"
      $> fun (location, identifier) ->
      Harpoon.Split_branch.Label.Constant { location; identifier }
    and pvar_case_label =
      hash
      &> seq2 (maybe_default integer ~default:1) (maybe dot_integer)
      |> span
      |> labelled "parameter variable case label"
      $> fun (location, (n, k)) ->
      Harpoon.Split_branch.Label.Parameter_variable
        { location; schema_element = n; projection = k }
    and bvar_case_label =
      trying (keyword "head" &> keyword "variable") |> span
      $> fun (location, ()) ->
      Harpoon.Split_branch.Label.Bound_variable { location }
    in
    choice
      [ bvar_case_label
      ; extension_case_label
      ; empty_case_label
      ; constant_case_label
      ; pvar_case_label
      ]

  let harpoon_hypothetical =
    let hypotheses =
      seq3 Meta_parser.meta_context pipe Comp_parser.comp_context
    in
    seq2 (hypotheses <& semicolon) Harpoon_parsers.harpoon_proof
    |> braces |> span
    |> labelled "Harpoon hypothetical"
    $> fun (location, ((meta_context, (), comp_context), proof)) ->
    { Harpoon.Hypothetical.location; meta_context; comp_context; proof }

  let harpoon_split_branch =
    keyword "case"
    &> seq2 (split_branch_label <& colon) harpoon_hypothetical
    |> span
    |> labelled "Harpoon split branch"
    $> fun (location, (label, body)) ->
    { Harpoon.Split_branch.location; label; body }

  let harpoon_directive =
    let intros =
      keyword "intros" &> harpoon_hypothetical |> span
      $> fun (location, hypothetical) ->
      Harpoon.Directive.Intros { location; hypothetical }
    and solve =
      keyword "solve" &> Comp_parser.comp_expression_object |> span
      $> fun (location, solution) ->
      Harpoon.Directive.Solve { location; solution }
    and split =
      keyword "split"
      &> seq2 Comp_parser.comp_expression_object
           (keyword "as" &> some harpoon_split_branch)
      |> span
      $> fun (location, (scrutinee, branches)) ->
      Harpoon.Directive.Split { location; scrutinee; branches }
    and impossible =
      keyword "impossible" &> Comp_parser.comp_expression_object |> span
      $> fun (location, scrutinee) ->
      Harpoon.Directive.Impossible { location; scrutinee }
    and suffices =
      let suffices_branch =
        seq2 Comp_parser.comp_sort_object
          (braces Harpoon_parsers.harpoon_proof)
        |> span
        $> fun (location, (goal, proof)) ->
        { Harpoon.Suffices_branch.location; goal; proof }
      in
      keyword "suffices" &> keyword "by"
      &> seq2
           (Comp_parser.comp_expression_object <& keyword "toshow")
           (many suffices_branch)
      |> span
      $> fun (location, (scrutinee, branches)) ->
      Harpoon.Directive.Suffices { location; scrutinee; branches }
    in
    choice [ intros; solve; split; impossible; suffices ]
    |> labelled "Harpoon directive"

  let harpoon_proof =
    let incomplete_proof =
      hole |> span |> labelled "Harpoon incomplete proof `?'" $> function
      | location, `Unlabelled ->
          Harpoon.Proof.Incomplete { location; label = Option.none }
      | location, `Labelled label ->
          Harpoon.Proof.Incomplete { location; label = Option.some label }
    and command_proof =
      seq2 (harpoon_command <& semicolon) Harpoon_parsers.harpoon_proof
      |> span
      $> fun (location, (command, body)) ->
      Harpoon.Proof.Command { location; command; body }
    and directive_proof =
      harpoon_directive |> span $> fun (location, directive) ->
      Harpoon.Proof.Directive { location; directive }
    in
    choice [ incomplete_proof; command_proof; directive_proof ]
    |> labelled "Harpoon proof"

  let interactive_harpoon_command =
    let intros =
      keyword "intros" &> maybe (some identifier) |> span
      $> fun (location, introduced_variables) ->
      Harpoon.Repl.Command.Intros { location; introduced_variables }
    and split =
      keyword "split" &> Comp_parser.comp_expression_object |> span
      $> fun (location, scrutinee) ->
      Harpoon.Repl.Command.Split { location; scrutinee }
    and msplit =
      keyword "msplit" &> span meta_object_identifier
      $> fun (location, identifier) ->
      Harpoon.Repl.Command.Msplit { location; identifier }
    and invert =
      keyword "invert" &> Comp_parser.comp_expression_object |> span
      $> fun (location, scrutinee) ->
      Harpoon.Repl.Command.Invert { location; scrutinee }
    and impossible =
      keyword "impossible" &> Comp_parser.comp_expression_object |> span
      $> fun (location, scrutinee) ->
      Harpoon.Repl.Command.Impossible { location; scrutinee }
    and solve =
      keyword "solve" &> Comp_parser.comp_expression_object |> span
      $> fun (location, solution) ->
      Harpoon.Repl.Command.Solve { location; solution }
    and by =
      keyword "by"
      &> seq3 Comp_parser.comp_expression_object
           (keyword "as" &> identifier)
           (maybe_default boxity ~default:`Boxed)
      |> span
      $> function
      | location, (expression, assignee, `Boxed) ->
          Harpoon.Repl.Command.By { location; assignee; expression }
      | location, (expression, assignee, `Unboxed) ->
          Harpoon.Repl.Command.Unbox
            { location; assignee; expression; modifier = Option.none }
      | location, (expression, assignee, `Strengthened) ->
          Harpoon.Repl.Command.Unbox
            { location
            ; assignee
            ; expression
            ; modifier = Option.some `Strengthened
            }
    and compute_type =
      keyword "type" &> Comp_parser.comp_expression_object |> span
      $> fun (location, scrutinee) ->
      Harpoon.Repl.Command.Type { location; scrutinee }
    and suffices =
      let tau_list_item =
        alt
          (Comp_parser.comp_sort_object $> fun tau -> `exact tau)
          (underscore |> span $> fun (loc, ()) -> `infer loc)
      in
      seq2
        (keyword "suffices" &> keyword "by"
       &> Comp_parser.comp_expression_object)
        (keyword "toshow" &> sep_by0 tau_list_item comma)
      |> span
      $> fun (location, (implication, goal_premises)) ->
      Harpoon.Repl.Command.Suffices { location; implication; goal_premises }
    and unbox =
      keyword "unbox"
      &> seq2 Comp_parser.comp_expression_object (keyword "as" &> identifier)
      |> span
      $> fun (location, (expression, assignee)) ->
      Harpoon.Repl.Command.Unbox
        { location; expression; assignee; modifier = Option.none }
    and strengthen =
      keyword "strengthen"
      &> seq2 Comp_parser.comp_expression_object (keyword "as" &> identifier)
      |> span
      $> fun (location, (expression, assignee)) ->
      Harpoon.Repl.Command.Unbox
        { location
        ; expression
        ; assignee
        ; modifier = Option.some `Strengthened
        }
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
      &> seq2 automation_kind
           (maybe_default automation_change ~default:`toggle)
      |> span
      $> fun (location, (kind, change)) ->
      Harpoon.Repl.Command.Toggle_automation { location; kind; change }
    and rename =
      let level =
        let comp_level = keyword "comp" $> fun () -> `comp
        and meta_level = keyword "meta" $> fun () -> `meta in
        choice [ comp_level; meta_level ]
      in
      keyword "rename" &> seq3 level identifier identifier |> span
      $> fun (location, (level, rename_from, rename_to)) ->
      Harpoon.Repl.Command.Rename { location; rename_from; rename_to; level }
    and select_theorem =
      keyword "select" &> qualified_identifier |> span
      $> fun (location, theorem) ->
      Harpoon.Repl.Command.Select_theorem { location; theorem }
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
      $> fun (location, subcommand) ->
      Harpoon.Repl.Command.Theorem { location; subcommand }
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
      $> fun (location, subcommand) ->
      Harpoon.Repl.Command.Session { location; subcommand }
    and subgoal_command =
      let list_subgoals = keyword "list" $> fun () -> `list
      and defer_subgoal = keyword "defer" $> fun () -> `defer in
      keyword "subgoal" &> choice [ list_subgoals; defer_subgoal ] |> span
      $> fun (location, subcommand) ->
      Harpoon.Repl.Command.Subgoal { location; subcommand }
    and defer =
      keyword "defer" |> span $> fun (location, ()) ->
      Harpoon.Repl.Command.Subgoal { location; subcommand = `defer }
    and info =
      let theorem = keyword "theorem" $> fun () -> `prog in
      let info_kind = choice [ theorem ] in
      keyword "info" &> seq2 info_kind qualified_identifier |> span
      $> fun (location, (kind, object_identifier)) ->
      Harpoon.Repl.Command.Info { location; kind; object_identifier }
    and translate =
      keyword "translate" &> qualified_identifier |> span
      $> fun (location, theorem) ->
      Harpoon.Repl.Command.Translate { location; theorem }
    and undo =
      keyword "undo" |> span $> fun (location, ()) ->
      Harpoon.Repl.Command.Undo { location }
    and redo =
      keyword "redo" |> span $> fun (location, ()) ->
      Harpoon.Repl.Command.Redo { location }
    and history =
      keyword "history" |> span $> fun (location, ()) ->
      Harpoon.Repl.Command.History { location }
    and help =
      keyword "help" |> span $> fun (location, ()) ->
      Harpoon.Repl.Command.Help { location }
    and save =
      keyword "save" |> span $> fun (location, ()) ->
      Harpoon.Repl.Command.Session { location; subcommand = `serialize }
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

  let interactive_harpoon_command_sequence =
    sep_by0 interactive_harpoon_command semicolon

  let next_theorem =
    let quit = colon &> keyword "quit" $> fun () -> `quit
    and next = identifier $> fun name -> `next name in
    choice [ quit; next ]
end

let harpoon_proof = Harpoon_parsers.harpoon_proof

let interactive_harpoon_command = Harpoon_parsers.interactive_harpoon_command

let interactive_harpoon_command_sequence =
  Harpoon_parsers.interactive_harpoon_command_sequence

let next_theorem = Harpoon_parsers.next_theorem
