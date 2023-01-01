open Support
open Beluga_syntax
open Common_disambiguation

module type HARPOON_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Disambiguation} *)

  val disambiguate_as_proof :
       Synprs.harpoon_proof
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_proof

  val disambiguate_as_command :
       Synprs.harpoon_command
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_command

  val disambiguate_as_directive :
       Synprs.harpoon_directive
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_directive

  val disambiguate_as_split_branch :
       Synprs.harpoon_split_branch
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_split_branch

  val disambiguate_as_suffices_branch :
       Synprs.harpoon_suffices_branch
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_suffices_branch

  val disambiguate_as_hypothetical :
       Synprs.harpoon_hypothetical
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_hypothetical

  val disambiguate_as_repl_command :
       Synprs.harpoon_repl_command
    -> disambiguation_state
    -> disambiguation_state * Synext.harpoon_repl_command
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

  include State.Make (Disambiguation_state)

  (** {1 Disambiguation} *)

  let rec disambiguate_as_proof proof =
    match proof with
    | Synprs.Harpoon.Proof.Incomplete { location; label } ->
        return (Synext.Harpoon.Proof.Incomplete { location; label })
    | Synprs.Harpoon.Proof.Command { location; command; body } ->
        let* command' = disambiguate_as_command command in
        let* body' = disambiguate_as_proof body in
        return
          (Synext.Harpoon.Proof.Command
             { location; command = command'; body = body' })
    | Synprs.Harpoon.Proof.Directive { location; directive } ->
        let* directive' = disambiguate_as_directive directive in
        return
          (Synext.Harpoon.Proof.Directive
             { location; directive = directive' })

  and disambiguate_as_command command =
    match command with
    | Synprs.Harpoon.Command.By { location; expression; assignee } ->
        let* expression' =
          Comp_disambiguation.disambiguate_as_expression expression
        in
        return
          (Synext.Harpoon.Command.By
             { location; expression = expression'; assignee })
    | Synprs.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let* expression' =
          Comp_disambiguation.disambiguate_as_expression expression
        in
        return
          (Synext.Harpoon.Command.Unbox
             { location; expression = expression'; assignee; modifier })

  and disambiguate_as_directive directive =
    match directive with
    | Synprs.Harpoon.Directive.Intros { location; hypothetical } ->
        let* hypothetical' = disambiguate_as_hypothetical hypothetical in
        return
          (Synext.Harpoon.Directive.Intros
             { location; hypothetical = hypothetical' })
    | Synprs.Harpoon.Directive.Solve { location; solution } ->
        let* solution' =
          Comp_disambiguation.disambiguate_as_expression solution
        in
        return
          (Synext.Harpoon.Directive.Solve { location; solution = solution' })
    | Synprs.Harpoon.Directive.Split { location; scrutinee; branches } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        get >>= fun state ->
        let branches' =
          List1.map
            (fun branch -> eval (disambiguate_as_split_branch branch) state)
            branches
        in
        return
          (Synext.Harpoon.Directive.Split
             { location; scrutinee = scrutinee'; branches = branches' })
    | Synprs.Harpoon.Directive.Impossible { location; scrutinee } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        return
          (Synext.Harpoon.Directive.Impossible
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        get >>= fun state ->
        let branches' =
          List.map
            (fun branch ->
              eval (disambiguate_as_suffices_branch branch) state)
            branches
        in
        return
          (Synext.Harpoon.Directive.Suffices
             { location; scrutinee = scrutinee'; branches = branches' })

  and disambiguate_as_split_branch split_branch =
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
    in
    let* body' = disambiguate_as_hypothetical body in
    return
      { Synext.Harpoon.Split_branch.location; label = label'; body = body' }

  and disambiguate_as_suffices_branch suffices_branch =
    let { Synprs.Harpoon.Suffices_branch.location; goal; proof } =
      suffices_branch
    in
    let* goal' = Comp_disambiguation.disambiguate_as_typ goal in
    let* proof' = disambiguate_as_proof proof in
    return
      { Synext.Harpoon.Suffices_branch.location
      ; goal = goal'
      ; proof = proof'
      }

  and disambiguate_as_hypothetical hypothetical =
    let { Synprs.Harpoon.Hypothetical.location
        ; meta_context
        ; comp_context
        ; proof
        } =
      hypothetical
    in
    let* meta_context' =
      Meta_disambiguation.disambiguate_as_meta_context meta_context
    in
    let* comp_context' =
      Comp_disambiguation.disambiguate_as_context comp_context
    in
    let* proof' = disambiguate_as_proof proof in
    return
      { Synext.Harpoon.Hypothetical.location
      ; meta_context = meta_context'
      ; comp_context = comp_context'
      ; proof = proof'
      }

  and disambiguate_as_repl_command repl_command =
    match repl_command with
    | Synprs.Harpoon.Repl.Command.Rename
        { location; rename_from; rename_to; level } ->
        return
          (Synext.Harpoon.Repl.Command.Rename
             { location; rename_from; rename_to; level })
    | Synprs.Harpoon.Repl.Command.Toggle_automation
        { location; kind; change } ->
        return
          (Synext.Harpoon.Repl.Command.Toggle_automation
             { location; kind; change })
    | Synprs.Harpoon.Repl.Command.Type { location; scrutinee } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        return
          (Synext.Harpoon.Repl.Command.Type
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Info { location; kind; object_identifier }
      ->
        return
          (Synext.Harpoon.Repl.Command.Info
             { location; kind; object_identifier })
    | Synprs.Harpoon.Repl.Command.Select_theorem { location; theorem } ->
        return
          (Synext.Harpoon.Repl.Command.Select_theorem { location; theorem })
    | Synprs.Harpoon.Repl.Command.Theorem { location; subcommand } ->
        return (Synext.Harpoon.Repl.Command.Theorem { location; subcommand })
    | Synprs.Harpoon.Repl.Command.Session { location; subcommand } ->
        return (Synext.Harpoon.Repl.Command.Session { location; subcommand })
    | Synprs.Harpoon.Repl.Command.Subgoal { location; subcommand } ->
        return (Synext.Harpoon.Repl.Command.Subgoal { location; subcommand })
    | Synprs.Harpoon.Repl.Command.Undo { location } ->
        return (Synext.Harpoon.Repl.Command.Undo { location })
    | Synprs.Harpoon.Repl.Command.Redo { location } ->
        return (Synext.Harpoon.Repl.Command.Redo { location })
    | Synprs.Harpoon.Repl.Command.History { location } ->
        return (Synext.Harpoon.Repl.Command.History { location })
    | Synprs.Harpoon.Repl.Command.Translate { location; theorem } ->
        return (Synext.Harpoon.Repl.Command.Translate { location; theorem })
    | Synprs.Harpoon.Repl.Command.Intros { location; introduced_variables }
      ->
        return
          (Synext.Harpoon.Repl.Command.Intros
             { location; introduced_variables })
    | Synprs.Harpoon.Repl.Command.Split { location; scrutinee } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        return
          (Synext.Harpoon.Repl.Command.Split
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Invert { location; scrutinee } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        return
          (Synext.Harpoon.Repl.Command.Invert
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Impossible { location; scrutinee } ->
        let* scrutinee' =
          Comp_disambiguation.disambiguate_as_expression scrutinee
        in
        return
          (Synext.Harpoon.Repl.Command.Impossible
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Msplit
        { location; identifier = identifier, _modifier } ->
        return (Synext.Harpoon.Repl.Command.Msplit { location; identifier })
    | Synprs.Harpoon.Repl.Command.Solve { location; solution } ->
        let* solution' =
          Comp_disambiguation.disambiguate_as_expression solution
        in
        return
          (Synext.Harpoon.Repl.Command.Solve
             { location; solution = solution' })
    | Synprs.Harpoon.Repl.Command.Unbox
        { location; expression; assignee; modifier } ->
        let* expression' =
          Comp_disambiguation.disambiguate_as_expression expression
        in
        return
          (Synext.Harpoon.Repl.Command.Unbox
             { location; expression = expression'; assignee; modifier })
    | Synprs.Harpoon.Repl.Command.By { location; expression; assignee } ->
        let* expression' =
          Comp_disambiguation.disambiguate_as_expression expression
        in
        return
          (Synext.Harpoon.Repl.Command.By
             { location; expression = expression'; assignee })
    | Synprs.Harpoon.Repl.Command.Suffices
        { location; implication; goal_premises } ->
        let* implication' =
          Comp_disambiguation.disambiguate_as_expression implication
        in
        get >>= fun state ->
        let goal_premises' =
          List.map
            (function
              | `exact typ ->
                  let _state', typ' =
                    Comp_disambiguation.disambiguate_as_typ typ state
                  in
                  `exact typ'
              | `infer location -> `infer location)
            goal_premises
        in
        return
          (Synext.Harpoon.Repl.Command.Suffices
             { location
             ; implication = implication'
             ; goal_premises = goal_premises'
             })
    | Synprs.Harpoon.Repl.Command.Help { location } ->
        return (Synext.Harpoon.Repl.Command.Help { location })
end
