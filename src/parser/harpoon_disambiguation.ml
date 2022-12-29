open Support
open Beluga_syntax
open Common_disambiguation

module type HARPOON_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Disambiguation} *)

  val disambiguate_as_proof :
    disambiguation_state -> Synprs.harpoon_proof -> Synext.harpoon_proof

  val disambiguate_as_command :
    disambiguation_state -> Synprs.harpoon_command -> Synext.harpoon_command

  val disambiguate_as_directive :
       disambiguation_state
    -> Synprs.harpoon_directive
    -> Synext.harpoon_directive

  val disambiguate_as_split_branch :
       disambiguation_state
    -> Synprs.harpoon_split_branch
    -> Synext.harpoon_split_branch

  val disambiguate_as_suffices_branch :
       disambiguation_state
    -> Synprs.harpoon_suffices_branch
    -> Synext.harpoon_suffices_branch

  val disambiguate_as_hypothetical :
       disambiguation_state
    -> Synprs.harpoon_hypothetical
    -> Synext.harpoon_hypothetical

  val disambiguate_as_repl_command :
       disambiguation_state
    -> Synprs.harpoon_repl_command
    -> Synext.harpoon_repl_command
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type disambiguation_state =
                               Disambiguation_state.t
                              and type disambiguation_state_entry =
                               Disambiguation_state.entry)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type disambiguation_state =
                               Disambiguation_state.t
                              and type disambiguation_state_entry =
                               Disambiguation_state.entry) :
  HARPOON_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  (** {1 Disambiguation} *)

  let rec disambiguate_as_proof state proof =
    match proof with
    | Synprs.Harpoon.Proof.Incomplete { location; label } ->
        Synext.Harpoon.Proof.Incomplete { location; label }
    | Synprs.Harpoon.Proof.Command { location; command; body } ->
        let command' = disambiguate_as_command state command
        and body' = disambiguate_as_proof state body in
        Synext.Harpoon.Proof.Command
          { location; command = command'; body = body' }
    | Synprs.Harpoon.Proof.Directive { location; directive } ->
        let directive' = disambiguate_as_directive state directive in
        Synext.Harpoon.Proof.Directive { location; directive = directive' }

  and disambiguate_as_command state command =
    match command with
    | Synprs.Harpoon.Command.By { location; expression; assignee } ->
        let expression' =
          Comp_disambiguation.disambiguate_as_expression state expression
        in
        Synext.Harpoon.Command.By
          { location; expression = expression'; assignee }
    | Synprs.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let expression' =
          Comp_disambiguation.disambiguate_as_expression state expression
        in
        Synext.Harpoon.Command.Unbox
          { location; expression = expression'; assignee; modifier }

  and disambiguate_as_directive state directive =
    match directive with
    | Synprs.Harpoon.Directive.Intros { location; hypothetical } ->
        let hypothetical' =
          disambiguate_as_hypothetical state hypothetical
        in
        Synext.Harpoon.Directive.Intros
          { location; hypothetical = hypothetical' }
    | Synprs.Harpoon.Directive.Solve { location; solution } ->
        let solution' =
          Comp_disambiguation.disambiguate_as_expression state solution
        in
        Synext.Harpoon.Directive.Solve { location; solution = solution' }
    | Synprs.Harpoon.Directive.Split { location; scrutinee; branches } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        and branches' =
          List1.map (disambiguate_as_split_branch state) branches
        in
        Synext.Harpoon.Directive.Split
          { location; scrutinee = scrutinee'; branches = branches' }
    | Synprs.Harpoon.Directive.Impossible { location; scrutinee } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        in
        Synext.Harpoon.Directive.Impossible
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        and branches' =
          List.map (disambiguate_as_suffices_branch state) branches
        in
        Synext.Harpoon.Directive.Suffices
          { location; scrutinee = scrutinee'; branches = branches' }

  and disambiguate_as_split_branch state split_branch =
    let { Synprs.Harpoon.Split_branch.location; label; body } =
      split_branch
    in
    let label' =
      match label with
      | Synprs.Harpoon.Split_branch.Label.Constant { location; identifier }
        ->
          Synext.Harpoon.Split_branch.Label.Constant { location; identifier }
      | Synprs.Harpoon.Split_branch.Label.Bound_variable { location } ->
          Synext.Harpoon.Split_branch.Label.Bound_variable { location }
      | Synprs.Harpoon.Split_branch.Label.Empty_context { location } ->
          Synext.Harpoon.Split_branch.Label.Empty_context { location }
      | Synprs.Harpoon.Split_branch.Label.Extended_context
          { location; schema_element } ->
          Synext.Harpoon.Split_branch.Label.Extended_context
            { location; schema_element }
      | Synprs.Harpoon.Split_branch.Label.Parameter_variable
          { location; schema_element; projection } ->
          Synext.Harpoon.Split_branch.Label.Parameter_variable
            { location; schema_element; projection }
    and body' = disambiguate_as_hypothetical state body in
    { Synext.Harpoon.Split_branch.location; label = label'; body = body' }

  and disambiguate_as_suffices_branch state suffices_branch =
    let { Synprs.Harpoon.Suffices_branch.location; goal; proof } =
      suffices_branch
    in
    let goal' = Comp_disambiguation.disambiguate_as_typ state goal
    and proof' = disambiguate_as_proof state proof in
    { Synext.Harpoon.Suffices_branch.location; goal = goal'; proof = proof' }

  and disambiguate_as_hypothetical state hypothetical =
    let { Synprs.Harpoon.Hypothetical.location
        ; meta_context
        ; comp_context
        ; proof
        } =
      hypothetical
    in
    let state', meta_context' =
      Meta_disambiguation.disambiguate_as_meta_context state meta_context
    in
    let state'', comp_context' =
      Comp_disambiguation.disambiguate_as_context state' comp_context
    in
    let proof' = disambiguate_as_proof state'' proof in
    { Synext.Harpoon.Hypothetical.location
    ; meta_context = meta_context'
    ; comp_context = comp_context'
    ; proof = proof'
    }

  and disambiguate_as_repl_command state repl_command =
    match repl_command with
    | Synprs.Harpoon.Repl.Command.Rename
        { location; rename_from; rename_to; level } ->
        Synext.Harpoon.Repl.Command.Rename
          { location; rename_from; rename_to; level }
    | Synprs.Harpoon.Repl.Command.Toggle_automation { location; kind; change }
      ->
        Synext.Harpoon.Repl.Command.Toggle_automation
          { location; kind; change }
    | Synprs.Harpoon.Repl.Command.Type { location; scrutinee } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        in
        Synext.Harpoon.Repl.Command.Type { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Info { location; kind; object_identifier }
      ->
        Synext.Harpoon.Repl.Command.Info
          { location; kind; object_identifier }
    | Synprs.Harpoon.Repl.Command.Select_theorem { location; theorem } ->
        Synext.Harpoon.Repl.Command.Select_theorem { location; theorem }
    | Synprs.Harpoon.Repl.Command.Theorem { location; subcommand } ->
        Synext.Harpoon.Repl.Command.Theorem { location; subcommand }
    | Synprs.Harpoon.Repl.Command.Session { location; subcommand } ->
        Synext.Harpoon.Repl.Command.Session { location; subcommand }
    | Synprs.Harpoon.Repl.Command.Subgoal { location; subcommand } ->
        Synext.Harpoon.Repl.Command.Subgoal { location; subcommand }
    | Synprs.Harpoon.Repl.Command.Undo { location } ->
        Synext.Harpoon.Repl.Command.Undo { location }
    | Synprs.Harpoon.Repl.Command.Redo { location } ->
        Synext.Harpoon.Repl.Command.Redo { location }
    | Synprs.Harpoon.Repl.Command.History { location } ->
        Synext.Harpoon.Repl.Command.History { location }
    | Synprs.Harpoon.Repl.Command.Translate { location; theorem } ->
        Synext.Harpoon.Repl.Command.Translate { location; theorem }
    | Synprs.Harpoon.Repl.Command.Intros { location; introduced_variables }
      ->
        Synext.Harpoon.Repl.Command.Intros { location; introduced_variables }
    | Synprs.Harpoon.Repl.Command.Split { location; scrutinee } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        in
        Synext.Harpoon.Repl.Command.Split
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Invert { location; scrutinee } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        in
        Synext.Harpoon.Repl.Command.Invert
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Impossible { location; scrutinee } ->
        let scrutinee' =
          Comp_disambiguation.disambiguate_as_expression state scrutinee
        in
        Synext.Harpoon.Repl.Command.Impossible
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Msplit
        { location; identifier = identifier, _modifier } ->
        Synext.Harpoon.Repl.Command.Msplit { location; identifier }
    | Synprs.Harpoon.Repl.Command.Solve { location; solution } ->
        let solution' =
          Comp_disambiguation.disambiguate_as_expression state solution
        in
        Synext.Harpoon.Repl.Command.Solve { location; solution = solution' }
    | Synprs.Harpoon.Repl.Command.Unbox
        { location; expression; assignee; modifier } ->
        let expression' =
          Comp_disambiguation.disambiguate_as_expression state expression
        in
        Synext.Harpoon.Repl.Command.Unbox
          { location; expression = expression'; assignee; modifier }
    | Synprs.Harpoon.Repl.Command.By { location; expression; assignee } ->
        let expression' =
          Comp_disambiguation.disambiguate_as_expression state expression
        in
        Synext.Harpoon.Repl.Command.By
          { location; expression = expression'; assignee }
    | Synprs.Harpoon.Repl.Command.Suffices
        { location; implication; goal_premises } ->
        let implication' =
          Comp_disambiguation.disambiguate_as_expression state implication
        and goal_premises' =
          List.map
            (function
              | `exact typ ->
                  `exact (Comp_disambiguation.disambiguate_as_typ state typ)
              | `infer location -> `infer location)
            goal_premises
        in
        Synext.Harpoon.Repl.Command.Suffices
          { location
          ; implication = implication'
          ; goal_premises = goal_premises'
          }
    | Synprs.Harpoon.Repl.Command.Help { location } ->
        Synext.Harpoon.Repl.Command.Help { location }
end
