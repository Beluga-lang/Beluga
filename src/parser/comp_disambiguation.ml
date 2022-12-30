(** Disambiguation of the parser syntax to the external syntax.

    Elements of the syntax for Beluga requires the symbol table for
    disambiguation. This module contains stateful functions for elaborating
    the context-free parser syntax to the data-dependent external syntax. The
    logic for the symbol lookups is repeated in the indexing phase to the
    approximate syntax.

    The "Beluga Language Specification" document contains additional details
    as to which syntactic structures have ambiguities. *)

open Support
open Beluga_syntax
open Common_disambiguation

[@@@warning "-A"]

(** {1 Exceptions} *)

(** {2 Exceptions for computation-level kind disambiguation} *)

exception Illegal_identifier_kind

exception Illegal_qualified_identifier_kind

exception Illegal_backward_arrow_kind

exception Illegal_cross_kind

exception Illegal_box_kind

exception Illegal_application_kind

exception Illegal_untyped_pi_kind_parameter

(** {2 Exceptions for computation-level type disambiguation} *)

exception Illegal_ctype_type

exception Expected_computation_type_constant of Qualified_identifier.t

exception Unbound_computation_type_constant of Qualified_identifier.t

exception Illegal_untyped_pi_type

(** {2 Exceptions for computation-level expression disambiguation} *)

exception Illegal_variables_bound_several_times

(** {2 Exceptions for computation-level context disambiguation} *)

exception Illegal_missing_context_binding_type

(** {2 Exceptions for computation-level pattern disambiguation} *)

exception Illegal_meta_annotated_pattern_missing_identifier

exception Illegal_meta_annotated_pattern_missing_type

(** {1 Disambiguation} *)

module type COMP_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Disambiguation} *)

  val disambiguate_as_kind :
    disambiguation_state -> Synprs.Comp.Sort_object.t -> Synext.Comp.Kind.t

  val disambiguate_as_typ :
    disambiguation_state -> Synprs.Comp.Sort_object.t -> Synext.Comp.Typ.t

  val disambiguate_as_expression :
       disambiguation_state
    -> Synprs.Comp.Expression_object.t
    -> Synext.Comp.Expression.t

  val disambiguate_as_pattern :
       disambiguation_state
    -> Synprs.Comp.Pattern_object.t
    -> Synext.Comp.Pattern.t

  val disambiguate_as_context :
       disambiguation_state
    -> Synprs.Comp.Context_object.t
    -> disambiguation_state * Synext.Comp.Context.t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type disambiguation_state =
                               Disambiguation_state.t
                              and type disambiguation_state_entry =
                               Disambiguation_state.entry) :
  COMP_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  (** {1 Disambiguation State Helpers} *)

  let rec add_comp_pattern_variables_to_state_aux pattern outer_state
      inner_state output_state additions =
    match pattern with
    | Synext.Comp.Pattern.Constant _
    | Synext.Comp.Pattern.Wildcard _ ->
        (output_state, additions)
    | Synext.Comp.Pattern.Variable { identifier; _ } -> (
        match
          Disambiguation_state.lookup_toplevel identifier inner_state
        with
        | _ -> (output_state, additions)
        | exception Disambiguation_state.Unbound_identifier _ ->
            let output_state' =
              Disambiguation_state.add_computation_variable identifier
                output_state
            and additions' = identifier :: additions in
            (output_state', additions'))
    | Synext.Comp.Pattern.MetaObject { meta_pattern; _ } ->
        add_meta_pattern_variables_to_state_aux meta_pattern outer_state
          inner_state output_state additions
    | Synext.Comp.Pattern.Tuple { elements; _ } ->
        List.fold_left
          (fun (output_state, additions) element ->
            let output_state', additions' =
              add_comp_pattern_variables_to_state_aux element outer_state
                inner_state output_state additions
            in
            (output_state', additions'))
          (output_state, additions) (List2.to_list elements)
    | Synext.Comp.Pattern.Application { applicand; arguments; _ } ->
        List.fold_left
          (fun (output_state, additions) element ->
            let output_state', additions' =
              add_comp_pattern_variables_to_state_aux element outer_state
                inner_state output_state additions
            in
            (output_state', additions'))
          (add_comp_pattern_variables_to_state_aux applicand outer_state
             inner_state output_state additions)
          (List1.to_list arguments)
    | Synext.Comp.Pattern.TypeAnnotated { pattern; _ } ->
        add_comp_pattern_variables_to_state_aux pattern outer_state
          inner_state output_state additions
    | Synext.Comp.Pattern.MetaTypeAnnotated
        { annotation_identifier; annotation_type; body; _ } -> (
        match annotation_type with
        | Synext.Meta.Typ.Context_schema _ ->
            let adder =
              Disambiguation_state.add_context_variable annotation_identifier
            in
            let inner_state' = adder inner_state
            and output_state' = adder output_state
            and additions' = annotation_identifier :: additions in
            add_comp_pattern_variables_to_state_aux body outer_state
              inner_state' output_state' additions'
        | Synext.Meta.Typ.Contextual_typ _ ->
            let adder =
              Disambiguation_state.add_meta_variable annotation_identifier
            in
            let inner_state' = adder inner_state
            and output_state' = adder output_state
            and additions' = annotation_identifier :: additions in
            add_comp_pattern_variables_to_state_aux body outer_state
              inner_state' output_state' additions'
        | Synext.Meta.Typ.Parameter_typ _ ->
            let adder =
              Disambiguation_state.add_parameter_variable
                annotation_identifier
            in
            let inner_state' = adder inner_state
            and output_state' = adder output_state
            and additions' = annotation_identifier :: additions in
            add_comp_pattern_variables_to_state_aux body outer_state
              inner_state' output_state' additions'
        | Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ->
            let adder =
              Disambiguation_state.add_substitution_variable
                annotation_identifier
            in
            let inner_state' = adder inner_state
            and output_state' = adder output_state
            and additions' = annotation_identifier :: additions in
            add_comp_pattern_variables_to_state_aux body outer_state
              inner_state' output_state' additions')

  and add_comp_copattern_variables_to_state_aux copattern outer_state
      inner_state output_state additions =
    match copattern with
    | Synext.Comp.Copattern.Observation { arguments; _ } ->
        List.fold_left
          (fun (output_state, additions) element ->
            let output_state', additions' =
              add_comp_pattern_variables_to_state_aux element outer_state
                inner_state output_state additions
            in
            (output_state', additions'))
          (output_state, additions) arguments
    | Synext.Comp.Copattern.Pattern pattern ->
        add_comp_pattern_variables_to_state_aux pattern outer_state
          inner_state output_state additions

  and add_meta_pattern_variables_to_state_aux meta_pattern outer_state
      inner_state output_state additions =
    match meta_pattern with
    | Synext.Meta.Pattern.Context { context; _ } ->
        add_clf_context_pattern_variables_to_state_aux context outer_state
          inner_state output_state additions
    | Synext.Meta.Pattern.Contextual_term { context; term; _ } ->
        Obj.magic ()
    | Synext.Meta.Pattern.Plain_substitution { domain; range; _ } ->
        Obj.magic ()
    | Synext.Meta.Pattern.Renaming_substitution { domain; range; _ } ->
        Obj.magic ()

  and add_clf_substitution_pattern_variables_to_state_aux
      substitution_pattern outer_state inner_state output_state additions =
    let { Synext.CLF.Substitution.Pattern.head; terms; _ } =
      substitution_pattern
    in
    Obj.magic ()

  and add_clf_context_pattern_variables_to_state_aux context_pattern
      outer_state inner_state output_state additions =
    let { Synext.CLF.Context.Pattern.head; bindings; _ } = context_pattern in
    let output_state', additions' =
      match head with
      | Synext.CLF.Context.Pattern.Head.Context_variable { identifier; _ } ->
          let output_state' =
            Disambiguation_state.add_context_variable identifier output_state
          and additions' = identifier :: additions in
          (output_state', additions')
      | _ -> (output_state, additions)
    in
    List.fold_left
      (fun (output_state, additions) (identifier, _typ) ->
        let output_state' =
          Disambiguation_state.add_lf_term_variable identifier output_state
        and additions' = identifier :: additions in
        (output_state', additions'))
      (output_state', additions')
      bindings

  and add_clf_term_pattern_variables_to_state_aux term_pattern outer_state
      inner_state output_state additions =
    match term_pattern with
    | Synext.CLF.Term.Pattern.Variable { identifier; _ } -> (
        match
          Disambiguation_state.lookup_toplevel identifier inner_state
        with
        | _ -> (inner_state, additions)
        | exception Disambiguation_state.Unbound_identifier _ ->
            let output_state' =
              Disambiguation_state.add_lf_term_variable identifier
                output_state
            and additions' = identifier :: additions in
            (output_state', additions'))
    | Synext.CLF.Term.Pattern.Parameter_variable { identifier; _ } -> (
        match
          Disambiguation_state.lookup_toplevel identifier inner_state
        with
        | _ -> (inner_state, additions)
        | exception Disambiguation_state.Unbound_identifier _ ->
            let output_state' =
              Disambiguation_state.add_parameter_variable identifier
                output_state
            and additions' = identifier :: additions in
            (output_state', additions'))
    | Synext.CLF.Term.Pattern.Substitution_variable { identifier; _ } -> (
        match
          Disambiguation_state.lookup_toplevel identifier inner_state
        with
        | _ -> (inner_state, additions)
        | exception Disambiguation_state.Unbound_identifier _ ->
            let output_state' =
              Disambiguation_state.add_substitution_variable identifier
                output_state
            and additions' = identifier :: additions in
            (output_state', additions'))
    | Synext.CLF.Term.Pattern.Constant _
    | Synext.CLF.Term.Pattern.Wildcard _ ->
        (output_state, additions)
    | Synext.CLF.Term.Pattern.Tuple { terms; _ } ->
        List.fold_left
          (fun (output_state, additions) term_pattern ->
            let output_state', additions' =
              add_clf_term_pattern_variables_to_state_aux term_pattern
                outer_state inner_state output_state additions
            in
            (output_state', additions'))
          (output_state, additions) (List1.to_list terms)
    | Synext.CLF.Term.Pattern.Projection { term; _ } ->
        add_clf_term_pattern_variables_to_state_aux term outer_state
          inner_state output_state additions
    | Synext.CLF.Term.Pattern.Abstraction { parameter_identifier; body; _ }
      ->
        let inner_state' =
          match parameter_identifier with
          | Option.Some parameter_identifier ->
              Disambiguation_state.add_lf_term_variable parameter_identifier
                inner_state
          | Option.None -> inner_state
        in
        add_clf_term_pattern_variables_to_state_aux body outer_state
          inner_state' output_state additions
    | Synext.CLF.Term.Pattern.Substitution { term; _ } ->
        add_clf_term_pattern_variables_to_state_aux term outer_state
          inner_state output_state additions
    | Synext.CLF.Term.Pattern.Application { applicand; arguments; _ } ->
        List.fold_left
          (fun (output_state, additions) term_pattern ->
            let output_state', additions' =
              add_clf_term_pattern_variables_to_state_aux term_pattern
                outer_state inner_state output_state additions
            in
            (output_state', additions'))
          (add_clf_term_pattern_variables_to_state_aux applicand outer_state
             inner_state output_state additions)
          (List1.to_list arguments)
    | Synext.CLF.Term.Pattern.TypeAnnotated _ -> Obj.magic ()

  let add_comp_pattern_variables_to_state pattern state =
    let output_state, additions =
      add_comp_pattern_variables_to_state_aux pattern state
        Disambiguation_state.empty state []
    in
    match Identifier.find_duplicates additions with
    | Option.None -> output_state
    | Option.Some duplicates ->
        let locations = List2.map Identifier.location duplicates in
        Error.raise_at
          (List2.to_list1 locations)
          Illegal_variables_bound_several_times

  (** {1 Disambiguation} *)

  let rec disambiguate_as_kind state sort_object =
    match sort_object with
    | Synprs.Comp.Sort_object.Raw_identifier { location; _ } ->
        Error.raise_at1 location Illegal_identifier_kind
    | Synprs.Comp.Sort_object.Raw_qualified_identifier { location; _ } ->
        Error.raise_at1 location Illegal_qualified_identifier_kind
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_kind
    | Synprs.Comp.Sort_object.Raw_cross { location; _ } ->
        Error.raise_at1 location Illegal_cross_kind
    | Synprs.Comp.Sort_object.Raw_box { location; _ } ->
        Error.raise_at1 location Illegal_box_kind
    | Synprs.Comp.Sort_object.Raw_application { location; _ } ->
        Error.raise_at1 location Illegal_application_kind
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Synext.Comp.Kind.Ctype { location }
    | Synprs.Comp.Sort_object.Raw_pi
        { location; parameter_sort = Option.None; _ } ->
        Error.raise_at1 location Illegal_untyped_pi_kind_parameter
    | Synprs.Comp.Sort_object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_typ
        ; plicity
        ; body
        } -> (
        match parameter_identifier with
        | Option.None, modifier ->
            let parameter_type' =
              Meta_disambiguation.disambiguate_as_meta_typ state
                parameter_typ
            in
            (match (modifier, parameter_type') with
            | `Plain, Synext.Meta.Typ.Context_schema _ -> ()
            | `Plain, Synext.Meta.Typ.Contextual_typ _ -> ()
            | `Hash, Synext.Meta.Typ.Parameter_typ _ -> ()
            | ( `Dollar
              , ( Synext.Meta.Typ.Plain_substitution_typ _
                | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
                ()
            | _ ->
                raise (Invalid_argument "")
                (* TODO: Modifier mismatch with meta-type *));
            let body' = disambiguate_as_kind state body in
            Synext.Comp.Kind.Pi
              { location
              ; parameter_identifier = Option.none
              ; parameter_type = parameter_type'
              ; plicity
              ; body = body'
              }
        | Option.Some parameter_identifier, modifier ->
            let parameter_type' =
              Meta_disambiguation.disambiguate_as_meta_typ state
                parameter_typ
            in
            let state' =
              match (modifier, parameter_type') with
              | `Plain, Synext.Meta.Typ.Context_schema _ ->
                  Disambiguation_state.add_context_variable
                    parameter_identifier state
              | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
                  Disambiguation_state.add_meta_variable parameter_identifier
                    state
              | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
                  Disambiguation_state.add_parameter_variable
                    parameter_identifier state
              | ( `Dollar
                , ( Synext.Meta.Typ.Plain_substitution_typ _
                  | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
                  Disambiguation_state.add_substitution_variable
                    parameter_identifier state
              | _ -> raise (Invalid_argument "")
              (* TODO: Modifier mismatch *)
            in
            let body' = disambiguate_as_kind state' body in
            Synext.Comp.Kind.Pi
              { location
              ; parameter_identifier = Option.none
              ; parameter_type = parameter_type'
              ; plicity
              ; body = body'
              })
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; domain; range; orientation = `Forward } ->
        let domain' = disambiguate_as_typ state domain
        and range' = disambiguate_as_kind state range in
        Synext.Comp.Kind.Arrow { location; domain = domain'; range = range' }

  and disambiguate_as_typ state sort_object =
    match sort_object with
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Error.raise_at1 location Illegal_ctype_type
    | Synprs.Comp.Sort_object.Raw_identifier { location; identifier; quoted }
      -> (
        (* As a computation-level type, plain identifiers are necessarily
           type constants *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.Computation_type_constant { operator } ->
            Synext.Comp.Typ.Constant
              { location
              ; identifier = qualified_identifier
              ; operator
              ; quoted
              }
        | _entry ->
            Error.raise_at1 location
              (Expected_computation_type_constant qualified_identifier)
        | exception Disambiguation_state.Unbound_identifier _ ->
            Error.raise_at1 location
              (Unbound_computation_type_constant qualified_identifier))
    | Synprs.Comp.Sort_object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As a computation-level type, identifiers of the form
           [(<identifier> `::')+ <identifier>] are necessarily type
           constants. *)
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.Computation_type_constant { operator } ->
            Synext.Comp.Typ.Constant
              { location; identifier; operator; quoted }
        | _entry ->
            Error.raise_at1 location
              (Expected_computation_type_constant identifier)
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            Error.raise_at1 location
              (Unbound_computation_type_constant identifier))
    | Synprs.Comp.Sort_object.Raw_pi
        { location; parameter_identifier; parameter_sort; plicity; body } ->
        let state', parameter_typ' =
          match (parameter_identifier, parameter_sort) with
          | (Option.Some identifier, _), Option.None ->
              let location = Identifier.location identifier in
              Error.raise_at1 location Illegal_untyped_pi_type
          | (Option.None, _), Option.None ->
              Error.raise_at1 location Illegal_untyped_pi_type
          | (identifier, `Plain), Option.Some parameter_typ ->
              let parameter_typ' =
                Meta_disambiguation.disambiguate_as_meta_typ state
                  parameter_typ
              and state' =
                match identifier with
                | Option.None -> state
                | Option.Some identifier ->
                    (* TODO: Incorrect, check against [parameter_typ'] *)
                    Disambiguation_state.add_context_variable identifier
                      state
              in
              (state', parameter_typ')
          | (identifier, `Hash), Option.Some parameter_typ -> Obj.magic ()
          | (identifier, `Dollar), Option.Some parameter_typ -> Obj.magic ()
        in
        let body' = disambiguate_as_typ state' body in
        Synext.Comp.Typ.Pi
          { location
          ; parameter_identifier = Pair.fst parameter_identifier
          ; parameter_type = parameter_typ'
          ; plicity
          ; body = body'
          }
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; domain; range; orientation } ->
        let domain' = disambiguate_as_typ state domain
        and range' = disambiguate_as_typ state range in
        Synext.Comp.Typ.Arrow
          { location; domain = domain'; range = range'; orientation }
    | Synprs.Comp.Sort_object.Raw_cross { location; operands } ->
        let types' = List2.map (disambiguate_as_typ state) operands in
        Synext.Comp.Typ.Cross { location; types = types' }
    | Synprs.Comp.Sort_object.Raw_box { location; boxed } ->
        let meta_type' =
          Meta_disambiguation.disambiguate_as_meta_typ state boxed
        in
        Synext.Comp.Typ.Box { location; meta_type = meta_type' }
    | Synprs.Comp.Sort_object.Raw_application { location; objects } ->
        Obj.magic ()

  and disambiguate_as_expression state expression_object =
    match expression_object with
    | Synprs.Comp.Expression_object.Raw_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_fn { location; parameters; body } ->
        let state' =
          List.fold_left
            (fun state parameter ->
              match parameter with
              | Option.None -> state
              | Option.Some identifier ->
                  Disambiguation_state.add_computation_variable identifier
                    state)
            state
            (List1.to_list parameters)
        in
        let body' = disambiguate_as_expression state' body in
        Synext.Comp.Expression.Fn { location; parameters; body = body' }
    | Synprs.Comp.Expression_object.Raw_mlam { location; parameters; body }
      ->
        let state' =
          List.fold_left
            (fun state parameter ->
              match parameter with
              | Option.Some identifier, `Plain ->
                  Disambiguation_state.add_meta_variable identifier state
              | Option.Some identifier, `Hash ->
                  Disambiguation_state.add_parameter_variable identifier
                    state
              | Option.Some identifier, `Dollar ->
                  Disambiguation_state.add_substitution_variable identifier
                    state
              | Option.None, _ -> state)
            state
            (List1.to_list parameters)
        in
        let body' = disambiguate_as_expression state' body in
        Synext.Comp.Expression.Mlam { location; parameters; body = body' }
    | Synprs.Comp.Expression_object.Raw_fun { location; branches } ->
        let branches' =
          List1.map
            (fun (patterns, body) ->
              let patterns_rev', state', additions =
                List1.fold_left
                  (fun pattern ->
                    let pattern' = disambiguate_as_copattern state pattern in
                    let output_state', additions' =
                      add_comp_copattern_variables_to_state_aux pattern'
                        state Disambiguation_state.empty state []
                    and patterns' = List1.from pattern' [] in
                    (patterns', output_state', additions'))
                  (fun (patterns_rev', output_state, additions) pattern ->
                    let pattern' =
                      disambiguate_as_copattern output_state pattern
                    in
                    let output_state', additions' =
                      add_comp_copattern_variables_to_state_aux pattern'
                        output_state Disambiguation_state.empty output_state
                        additions
                    and patterns' = List1.cons pattern' patterns_rev' in
                    (patterns', output_state', additions'))
                  patterns
              in
              match Identifier.find_duplicates additions with
              | Option.None ->
                  let patterns' = List1.rev patterns_rev' in
                  let body' = disambiguate_as_expression state' body in
                  (patterns', body')
              | Option.Some duplicates ->
                  let locations = List2.map Identifier.location duplicates in
                  Error.raise_at
                    (List2.to_list1 locations)
                    Illegal_variables_bound_several_times)
            branches
        in
        Synext.Comp.Expression.Fun { location; branches = branches' }
    | Synprs.Comp.Expression_object.Raw_box { location; meta_object } ->
        let meta_object' =
          Meta_disambiguation.disambiguate_as_meta_object state meta_object
        in
        Synext.Comp.Expression.Box { location; meta_object = meta_object' }
    | Synprs.Comp.Expression_object.Raw_let
        { location; pattern; scrutinee; body } ->
        let pattern' = disambiguate_as_pattern state pattern in
        let scrutinee' = disambiguate_as_expression state scrutinee in
        let state' = add_comp_pattern_variables_to_state pattern' state in
        let body' = disambiguate_as_expression state' body in
        Synext.Comp.Expression.Let
          { location
          ; pattern = pattern'
          ; scrutinee = scrutinee'
          ; body = body'
          }
    | Synprs.Comp.Expression_object.Raw_impossible { location; scrutinee } ->
        let scrutinee' = disambiguate_as_expression state scrutinee in
        Synext.Comp.Expression.Impossible
          { location; scrutinee = scrutinee' }
    | Synprs.Comp.Expression_object.Raw_case
        { location; scrutinee; check_coverage; branches } ->
        let scrutinee' = disambiguate_as_expression state scrutinee
        and branches' =
          List1.map
            (fun (pattern, body) ->
              let pattern' = disambiguate_as_pattern state pattern in
              let state' =
                add_comp_pattern_variables_to_state pattern' state
              in
              let body' = disambiguate_as_expression state' body in
              (pattern', body'))
            branches
        in
        Synext.Comp.Expression.Case
          { location
          ; scrutinee = scrutinee'
          ; check_coverage
          ; branches = branches'
          }
    | Synprs.Comp.Expression_object.Raw_tuple { location; elements } ->
        let elements' =
          List2.map (disambiguate_as_expression state) elements
        in
        Synext.Comp.Expression.Tuple { location; elements = elements' }
    | Synprs.Comp.Expression_object.Raw_hole { location; label } ->
        Synext.Comp.Expression.Hole { location; label }
    | Synprs.Comp.Expression_object.Raw_box_hole { location } ->
        Synext.Comp.Expression.BoxHole { location }
    | Synprs.Comp.Expression_object.Raw_application { location; expressions }
      ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_annotated
        { location; expression; typ } ->
        let expression' = disambiguate_as_expression state expression
        and typ' = disambiguate_as_typ state typ in
        Synext.Comp.Expression.TypeAnnotated
          { location; expression = expression'; typ = typ' }

  and disambiguate_as_pattern state pattern_object =
    match pattern_object with
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_identifier = Option.None, _; _ } ->
        Error.raise_at1 location
          Illegal_meta_annotated_pattern_missing_identifier
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_typ = Option.None; _ } ->
        Error.raise_at1 location Illegal_meta_annotated_pattern_missing_type
    | Synprs.Comp.Pattern_object.Raw_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_box { location; pattern } ->
        let pattern' =
          Meta_disambiguation.disambiguate_as_meta_pattern state pattern
        in
        Synext.Comp.Pattern.MetaObject { location; meta_pattern = pattern' }
    | Synprs.Comp.Pattern_object.Raw_tuple { location; elements } ->
        let elements' = List2.map (disambiguate_as_pattern state) elements in
        Synext.Comp.Pattern.Tuple { location; elements = elements' }
    | Synprs.Comp.Pattern_object.Raw_application { location; patterns } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_annotated { location; pattern; typ } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location
        ; parameter_identifier = Option.Some identifier, identifier_modifier
        ; parameter_typ = Option.Some parameter_typ
        ; pattern
        } ->
        let parameter_typ' =
          Meta_disambiguation.disambiguate_as_meta_typ state parameter_typ
        in
        let state' =
          match (identifier_modifier, parameter_typ') with
          | `Plain, Synext.Meta.Typ.Context_schema _ ->
              Disambiguation_state.add_context_variable identifier state
          | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
              Disambiguation_state.add_meta_variable identifier state
          | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
              Disambiguation_state.add_parameter_variable identifier state
          | ( `Dollar
            , ( Synext.Meta.Typ.Plain_substitution_typ _
              | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
              Disambiguation_state.add_substitution_variable identifier state
          | identifier_modifier, typ -> raise (Invalid_argument "")
          (* TODO: Modifier mismatch *)
        in
        let pattern' = disambiguate_as_pattern state' pattern in
        Synext.Comp.Pattern.MetaTypeAnnotated
          { location
          ; annotation_identifier = identifier
          ; annotation_type = parameter_typ'
          ; body = pattern'
          }
    | Synprs.Comp.Pattern_object.Raw_wildcard { location } ->
        Synext.Comp.Pattern.Wildcard { location }

  and disambiguate_as_copattern state pattern_object =
    match pattern_object with
    | Synprs.Comp.Pattern_object.Raw_observation _ -> Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier _ -> Obj.magic ()

  and disambiguate_as_context state context_object =
    let { Synprs.Comp.Context_object.location; bindings } = context_object in
    (* Computation contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves. *)
    let state', bindings_rev' =
      List.fold_left
        (fun (state, bindings_rev') binding ->
          match binding with
          | identifier, Option.None ->
              let location = Identifier.location identifier in
              Error.raise_at1 location Illegal_missing_context_binding_type
          | identifier, Option.Some typ ->
              let typ' = disambiguate_as_typ state typ in
              let state' =
                Disambiguation_state.add_computation_variable identifier
                  state
              in
              (state', (identifier, typ') :: bindings_rev'))
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    let context' = { Synext.Comp.Context.location; bindings = bindings' } in
    (state', context')
end
