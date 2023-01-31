open Support
open Beluga_syntax
open Common_disambiguation

exception Expected_constructor_constant

module type HARPOON_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_harpoon_proof :
    Synprs.harpoon_proof -> Synext.harpoon_proof t

  val disambiguate_harpoon_command :
    Synprs.harpoon_command -> Synext.harpoon_command t

  val disambiguate_harpoon_directive :
    Synprs.harpoon_directive -> Synext.harpoon_directive t

  val disambiguate_harpoon_split_branch :
    Synprs.harpoon_split_branch -> Synext.harpoon_split_branch t

  val disambiguate_harpoon_suffices_branch :
    Synprs.harpoon_suffices_branch -> Synext.harpoon_suffices_branch t

  val disambiguate_harpoon_hypothetical :
    Synprs.harpoon_hypothetical -> Synext.harpoon_hypothetical t

  val disambiguate_harpoon_repl_command :
    Synprs.harpoon_repl_command -> Synext.harpoon_repl_command t
end

module Make
    (Bindings_state : BINDINGS_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Bindings_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Bindings_state.state) :
  HARPOON_DISAMBIGUATION with type state = Bindings_state.state = struct
  include Bindings_state
  include Meta_disambiguation
  include Comp_disambiguation

  (** {1 Disambiguation} *)

  let rec disambiguate_harpoon_proof proof =
    match proof with
    | Synprs.Harpoon.Proof.Incomplete { location; label } ->
        return (Synext.Harpoon.Proof.Incomplete { location; label })
    | Synprs.Harpoon.Proof.Command { location; command; body } ->
        let* command' = disambiguate_harpoon_command command in
        let* body' = disambiguate_harpoon_proof body in
        return
          (Synext.Harpoon.Proof.Command
             { location; command = command'; body = body' })
    | Synprs.Harpoon.Proof.Directive { location; directive } ->
        let* directive' = disambiguate_harpoon_directive directive in
        return
          (Synext.Harpoon.Proof.Directive
             { location; directive = directive' })

  and disambiguate_harpoon_command command =
    match command with
    | Synprs.Harpoon.Command.By { location; expression; assignee } ->
        let* expression' = disambiguate_comp_expression expression in
        return
          (Synext.Harpoon.Command.By
             { location; expression = expression'; assignee })
    | Synprs.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let* expression' = disambiguate_comp_expression expression in
        return
          (Synext.Harpoon.Command.Unbox
             { location; expression = expression'; assignee; modifier })

  and disambiguate_harpoon_directive directive =
    match directive with
    | Synprs.Harpoon.Directive.Intros { location; hypothetical } ->
        let* hypothetical' =
          disambiguate_harpoon_hypothetical hypothetical
        in
        return
          (Synext.Harpoon.Directive.Intros
             { location; hypothetical = hypothetical' })
    | Synprs.Harpoon.Directive.Solve { location; solution } ->
        let* solution' = disambiguate_comp_expression solution in
        return
          (Synext.Harpoon.Directive.Solve { location; solution = solution' })
    | Synprs.Harpoon.Directive.Split { location; scrutinee; branches } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        let* branches' =
          traverse_list1 disambiguate_harpoon_split_branch branches
        in
        return
          (Synext.Harpoon.Directive.Split
             { location; scrutinee = scrutinee'; branches = branches' })
    | Synprs.Harpoon.Directive.Impossible { location; scrutinee } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        return
          (Synext.Harpoon.Directive.Impossible
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        let* branches' =
          traverse_list disambiguate_harpoon_suffices_branch branches
        in
        return
          (Synext.Harpoon.Directive.Suffices
             { location; scrutinee = scrutinee'; branches = branches' })

  and disambiguate_harpoon_split_branch split_branch =
    let { Synprs.Harpoon.Split_branch.location; label; body } =
      split_branch
    in
    let* label' =
      match label with
      | Synprs.Harpoon.Split_branch.Label.Constant { location; identifier }
        -> (
          lookup identifier >>= function
          | Result.Ok (Lf_term_constant, _) ->
              return
                (Synext.Harpoon.Split_branch.Label.Lf_constant
                   { location; identifier })
          | Result.Ok (Computation_term_constructor, _) ->
              return
                (Synext.Harpoon.Split_branch.Label.Comp_constant
                   { location; identifier })
          | Result.Ok entry ->
              Error.raise_at1 location
                (Error.composite_exception2 Expected_constructor_constant
                   (actual_binding_exn identifier entry))
          | Result.Error cause -> Error.raise_at1 location cause)
      | Synprs.Harpoon.Split_branch.Label.Bound_variable { location } ->
          return
            (Synext.Harpoon.Split_branch.Label.Bound_variable { location })
      | Synprs.Harpoon.Split_branch.Label.Empty_context { location } ->
          return
            (Synext.Harpoon.Split_branch.Label.Empty_context { location })
      | Synprs.Harpoon.Split_branch.Label.Extended_context
          { location; schema_element } ->
          return
            (Synext.Harpoon.Split_branch.Label.Extended_context
               { location; schema_element })
      | Synprs.Harpoon.Split_branch.Label.Parameter_variable
          { location; schema_element; projection } ->
          return
            (Synext.Harpoon.Split_branch.Label.Parameter_variable
               { location; schema_element; projection })
    in
    let* body' = disambiguate_harpoon_hypothetical body in
    return
      { Synext.Harpoon.Split_branch.location; label = label'; body = body' }

  and disambiguate_harpoon_suffices_branch suffices_branch =
    let { Synprs.Harpoon.Suffices_branch.location; goal; proof } =
      suffices_branch
    in
    let* goal' = disambiguate_comp_typ goal in
    let* proof' = disambiguate_harpoon_proof proof in
    return
      { Synext.Harpoon.Suffices_branch.location
      ; goal = goal'
      ; proof = proof'
      }

  and disambiguate_harpoon_hypothetical hypothetical =
    let { Synprs.Harpoon.Hypothetical.location
        ; meta_context
        ; comp_context
        ; proof
        } =
      hypothetical
    in
    with_disambiguated_meta_context meta_context (fun meta_context' ->
        with_disambiguated_comp_context comp_context (fun comp_context' ->
            let* proof' = disambiguate_harpoon_proof proof in
            return
              { Synext.Harpoon.Hypothetical.location
              ; meta_context = meta_context'
              ; comp_context = comp_context'
              ; proof = proof'
              }))

  and disambiguate_harpoon_repl_command repl_command =
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
        let* scrutinee' = disambiguate_comp_expression scrutinee in
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
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        return
          (Synext.Harpoon.Repl.Command.Split
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Invert { location; scrutinee } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        return
          (Synext.Harpoon.Repl.Command.Invert
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Impossible { location; scrutinee } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        return
          (Synext.Harpoon.Repl.Command.Impossible
             { location; scrutinee = scrutinee' })
    | Synprs.Harpoon.Repl.Command.Msplit
        { location; identifier = identifier, _modifier } ->
        return (Synext.Harpoon.Repl.Command.Msplit { location; identifier })
    | Synprs.Harpoon.Repl.Command.Solve { location; solution } ->
        let* solution' = disambiguate_comp_expression solution in
        return
          (Synext.Harpoon.Repl.Command.Solve
             { location; solution = solution' })
    | Synprs.Harpoon.Repl.Command.Unbox
        { location; expression; assignee; modifier } ->
        let* expression' = disambiguate_comp_expression expression in
        return
          (Synext.Harpoon.Repl.Command.Unbox
             { location; expression = expression'; assignee; modifier })
    | Synprs.Harpoon.Repl.Command.By { location; expression; assignee } ->
        let* expression' = disambiguate_comp_expression expression in
        return
          (Synext.Harpoon.Repl.Command.By
             { location; expression = expression'; assignee })
    | Synprs.Harpoon.Repl.Command.Suffices
        { location; implication; goal_premises } ->
        let* implication' = disambiguate_comp_expression implication in
        let* goal_premises' =
          traverse_list disambiguate_goal_premise goal_premises
        in
        return
          (Synext.Harpoon.Repl.Command.Suffices
             { location
             ; implication = implication'
             ; goal_premises = goal_premises'
             })
    | Synprs.Harpoon.Repl.Command.Help { location } ->
        return (Synext.Harpoon.Repl.Command.Help { location })

  and disambiguate_goal_premise = function
    | `exact typ ->
        let* typ' = disambiguate_comp_typ typ in
        return (`exact typ')
    | `infer location -> return (`infer location)
end

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Expected_constructor_constant ->
        Format.dprintf "%a" Format.pp_print_text
          "Expected an LF-level of a computation-level constructor constant."
    | exn -> Error.raise_unsupported_exception_printing exn)
