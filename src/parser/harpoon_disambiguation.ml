open Support
open Beluga_syntax

exception Expected_constructor_constant

exception Rename_variable_kind_mismatch

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Expected_constructor_constant ->
        Format.dprintf
          "Expected an LF-level of a computation-level constructor constant."
    | Rename_variable_kind_mismatch ->
        Format.dprintf "Mismatched identifier prefixes."
    | exn -> Error.raise_unsupported_exception_printing exn)

module type HARPOON_DISAMBIGUATION = sig
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_harpoon_proof :
    state -> Synprs.harpoon_proof -> Synext.harpoon_proof

  val with_disambiguated_harpoon_command :
       state
    -> Synprs.harpoon_command
    -> (state -> Synext.harpoon_command -> 'a)
    -> 'a

  val disambiguate_harpoon_directive :
    state -> Synprs.harpoon_directive -> Synext.harpoon_directive

  val disambiguate_harpoon_split_branch :
    state -> Synprs.harpoon_split_branch -> Synext.harpoon_split_branch

  val disambiguate_harpoon_suffices_branch :
    state -> Synprs.harpoon_suffices_branch -> Synext.harpoon_suffices_branch

  val disambiguate_harpoon_hypothetical :
    state -> Synprs.harpoon_hypothetical -> Synext.harpoon_hypothetical

  val disambiguate_harpoon_repl_command :
    state -> Synprs.harpoon_repl_command -> Synext.harpoon_repl_command
end

module Make
    (Disambiguation_state : Disambiguation_state.DISAMBIGUATION_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Disambiguation_state.state) :
  HARPOON_DISAMBIGUATION with type state = Disambiguation_state.state =
struct
  include Disambiguation_state
  include Meta_disambiguation
  include Comp_disambiguation

  (** {1 Disambiguation} *)

  let rec disambiguate_harpoon_proof state = function
    | Synprs.Harpoon.Proof.Incomplete { location; label } ->
        Synext.Harpoon.Proof.Incomplete { location; label }
    | Synprs.Harpoon.Proof.Command { location; command; body } ->
        with_disambiguated_harpoon_command state command
          (fun state command' ->
            let body' = disambiguate_harpoon_proof state body in
            Synext.Harpoon.Proof.Command
              { location; command = command'; body = body' })
    | Synprs.Harpoon.Proof.Directive { location; directive } ->
        let directive' = disambiguate_harpoon_directive state directive in
        Synext.Harpoon.Proof.Directive { location; directive = directive' }

  and with_disambiguated_harpoon_command :
        'a.
           state
        -> Synprs.harpoon_command
        -> (state -> Synext.harpoon_command -> 'a)
        -> 'a =
   fun state command f ->
    match command with
    | Synprs.Harpoon.Command.By { location; expression; assignee } ->
        let expression' = disambiguate_comp_expression state expression in
        with_bound_computation_variable state assignee (fun state ->
            f state
              (Synext.Harpoon.Command.By
                 { location; expression = expression'; assignee }))
    | Synprs.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let expression' = disambiguate_comp_expression state expression in
        with_bound_contextual_variable state assignee (fun state ->
            f state
              (Synext.Harpoon.Command.Unbox
                 { location; expression = expression'; assignee; modifier }))

  and disambiguate_harpoon_directive state = function
    | Synprs.Harpoon.Directive.Intros { location; hypothetical } ->
        let hypothetical' =
          disambiguate_harpoon_hypothetical state hypothetical
        in
        Synext.Harpoon.Directive.Intros
          { location; hypothetical = hypothetical' }
    | Synprs.Harpoon.Directive.Solve { location; solution } ->
        let solution' = disambiguate_comp_expression state solution in
        Synext.Harpoon.Directive.Solve { location; solution = solution' }
    | Synprs.Harpoon.Directive.Split { location; scrutinee; branches } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        let branches' =
          traverse_list1 state disambiguate_harpoon_split_branch branches
        in
        Synext.Harpoon.Directive.Split
          { location; scrutinee = scrutinee'; branches = branches' }
    | Synprs.Harpoon.Directive.Impossible { location; scrutinee } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        Synext.Harpoon.Directive.Impossible
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        let branches' =
          traverse_list state disambiguate_harpoon_suffices_branch branches
        in
        Synext.Harpoon.Directive.Suffices
          { location; scrutinee = scrutinee'; branches = branches' }

  and disambiguate_harpoon_split_branch state = function
    | { Synprs.Harpoon.Split_branch.location; label; body } ->
        let label' = disambiguate_harpoon_split_branch_label state label in
        let body' = disambiguate_harpoon_hypothetical state body in
        { Synext.Harpoon.Split_branch.location
        ; label = label'
        ; body = body'
        }

  and disambiguate_harpoon_split_branch_label state = function
    | Synprs.Harpoon.Split_branch.Label.Constant { location; identifier }
      -> (
        match lookup state identifier with
        | entry when Entry.is_lf_term_constant entry ->
            Synext.Harpoon.Split_branch.Label.Lf_constant
              { location; identifier }
        | entry when Entry.is_computation_term_constructor entry ->
            Synext.Harpoon.Split_branch.Label.Comp_constant
              { location; identifier }
        | entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_constructor_constant
                 (actual_binding_exn identifier entry))
        | exception cause -> Error.raise_at1 location cause)
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

  and disambiguate_harpoon_suffices_branch state = function
    | { Synprs.Harpoon.Suffices_branch.location; goal; proof } ->
        let goal' = disambiguate_comp_typ state goal in
        let proof' = disambiguate_harpoon_proof state proof in
        { Synext.Harpoon.Suffices_branch.location
        ; goal = goal'
        ; proof = proof'
        }

  and disambiguate_harpoon_hypothetical state = function
    | { Synprs.Harpoon.Hypothetical.location
      ; meta_context
      ; comp_context
      ; proof
      } ->
        with_parent_scope state (fun state ->
            with_disambiguated_meta_context state meta_context
              (fun state meta_context' ->
                with_disambiguated_comp_context state comp_context
                  (fun state comp_context' ->
                    let proof' = disambiguate_harpoon_proof state proof in
                    { Synext.Harpoon.Hypothetical.location
                    ; meta_context = meta_context'
                    ; comp_context = comp_context'
                    ; proof = proof'
                    })))

  and disambiguate_harpoon_repl_command state = function
    | Synprs.Harpoon.Repl.Command.Rename
        { location; rename_from; rename_to; level } -> (
        match (level, rename_from, rename_to) with
        | `comp, (_rename_from, `Plain), (_rename_to, `Plain)
        | `meta, (_rename_from, `Plain), (_rename_to, `Plain)
        | `meta, (_rename_from, `Hash), (_rename_to, `Hash)
        | `meta, (_rename_from, `Dollar), (_rename_to, `Dollar) ->
            Synext.Harpoon.Repl.Command.Rename
              { location; rename_from; rename_to; level }
        | _ -> Error.raise_at1 location Rename_variable_kind_mismatch)
    | Synprs.Harpoon.Repl.Command.Toggle_automation
        { location; kind; change } ->
        Synext.Harpoon.Repl.Command.Toggle_automation
          { location; kind; change }
    | Synprs.Harpoon.Repl.Command.Type { location; scrutinee } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
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
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        Synext.Harpoon.Repl.Command.Split
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Invert { location; scrutinee } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        Synext.Harpoon.Repl.Command.Invert
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Impossible { location; scrutinee } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        Synext.Harpoon.Repl.Command.Impossible
          { location; scrutinee = scrutinee' }
    | Synprs.Harpoon.Repl.Command.Msplit
        { location; identifier = identifier, _modifier } ->
        Synext.Harpoon.Repl.Command.Msplit { location; identifier }
    | Synprs.Harpoon.Repl.Command.Solve { location; solution } ->
        let solution' = disambiguate_comp_expression state solution in
        Synext.Harpoon.Repl.Command.Solve { location; solution = solution' }
    | Synprs.Harpoon.Repl.Command.Unbox
        { location; expression; assignee; modifier } ->
        let expression' = disambiguate_comp_expression state expression in
        Synext.Harpoon.Repl.Command.Unbox
          { location; expression = expression'; assignee; modifier }
    | Synprs.Harpoon.Repl.Command.By { location; expression; assignee } ->
        let expression' = disambiguate_comp_expression state expression in
        Synext.Harpoon.Repl.Command.By
          { location; expression = expression'; assignee }
    | Synprs.Harpoon.Repl.Command.Suffices
        { location; implication; goal_premises } ->
        let implication' = disambiguate_comp_expression state implication in
        let goal_premises' =
          traverse_list state disambiguate_goal_premise goal_premises
        in
        Synext.Harpoon.Repl.Command.Suffices
          { location
          ; implication = implication'
          ; goal_premises = goal_premises'
          }
    | Synprs.Harpoon.Repl.Command.Help { location } ->
        Synext.Harpoon.Repl.Command.Help { location }
    | Synprs.Harpoon.Repl.Command.Auto_invert_solve { location; max_depth }
      ->
        Synext.Harpoon.Repl.Command.Auto_invert_solve { location; max_depth }
    | Synprs.Harpoon.Repl.Command.Inductive_auto_solve
        { location; max_depth } ->
        Synext.Harpoon.Repl.Command.Inductive_auto_solve
          { location; max_depth }

  and disambiguate_goal_premise state = function
    | `exact typ ->
        let typ' = disambiguate_comp_typ state typ in
        `exact typ'
    | `infer location -> `infer location
end
