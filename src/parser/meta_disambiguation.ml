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

module type META_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Exceptions} *)

  (* TODO: *)

  (** {1 Disambiguation} *)

  val disambiguate_as_meta_typ :
    disambiguation_state -> Synprs.meta_thing -> Synext.meta_typ

  val disambiguate_as_meta_object :
    disambiguation_state -> Synprs.meta_thing -> Synext.meta_object

  val disambiguate_as_meta_pattern :
    disambiguation_state -> Synprs.meta_thing -> Synext.meta_pattern

  val disambiguate_as_schema :
    disambiguation_state -> Synprs.schema_object -> Synext.schema

  val disambiguate_as_meta_context :
       disambiguation_state
    -> Synprs.meta_context_object
    -> disambiguation_state * Synext.meta_context
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (CLF_disambiguation : Clf_disambiguation.CLF_DISAMBIGUATION
                            with type disambiguation_state =
                              Disambiguation_state.t
                             and type disambiguation_state_entry =
                              Disambiguation_state.entry) :
  META_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  (** {1 Exceptions} *)

  (** {2 Exceptions for meta-type disambiguation} *)

  exception Expected_meta_type of Location.t

  exception Illegal_context_meta_type of Location.t

  exception Illegal_substitution_or_context_contextual_type of Location.t

  (** {2 Exceptions for meta-object disambiguation} *)

  exception Illegal_missing_dollar_modifier_meta_object of Location.t

  exception Illegal_hash_modifier_meta_object of Location.t

  exception Expected_meta_object of Location.t

  (** {2 Exceptions for meta-pattern disambiguation} *)

  exception Illegal_missing_dollar_modifier_meta_pattern of Location.t

  exception Illegal_hash_modifier_meta_pattern of Location.t

  exception Expected_meta_pattern of Location.t

  (** {2 Exceptions for schema disambiguation} *)

  exception Illegal_unnamed_block_element_type of Location.t

  (** {2 Exceptions for meta-context disambiguation} *)

  exception Expected_contextual_type of Location.t

  exception Expected_plain_or_renaming_substitution_type of Location.t

  exception Expected_contextual_type_or_schema of Location.t

  exception Illegal_missing_meta_type_annotation of Location.t

  (** {1 Disambiguation State Helpers} *)

  let add_context_head_to_disambiguation_state head state =
    match head with
    | Synext.CLF.Context.Head.None _
    | Synext.CLF.Context.Head.Hole _ ->
        state
    | Synext.CLF.Context.Head.Context_variable { identifier; _ } ->
        Disambiguation_state.add_context_variable identifier state

  let add_context_pattern_head_to_disambiguation_state head state =
    match head with
    | Synext.CLF.Context.Pattern.Head.None _
    | Synext.CLF.Context.Pattern.Head.Hole _ ->
        state
    | Synext.CLF.Context.Pattern.Head.Context_variable { identifier; _ } ->
        Disambiguation_state.add_context_variable identifier state

  let add_clf_bindings_to_disambiguation_state bindings state =
    List.fold_left
      (fun state (identifier, _typ) ->
        Disambiguation_state.add_lf_term_variable identifier state)
      state bindings

  let add_clf_context_bindings_to_disambiguation_state context state =
    let { Synext.CLF.Context.head; bindings; _ } = context in
    state
    |> add_context_head_to_disambiguation_state head
    |> add_clf_bindings_to_disambiguation_state bindings

  let add_clf_context_pattern_bindings_to_disambiguation_state context state
      =
    let { Synext.CLF.Context.Pattern.head; bindings; _ } = context in
    state
    |> add_context_pattern_head_to_disambiguation_state head
    |> add_clf_bindings_to_disambiguation_state bindings

  let add_schema_some_bindings_to_disambiguation_state some state =
    add_clf_bindings_to_disambiguation_state (List1.to_list some) state

  (** {1 Disambiguation} *)

  let rec disambiguate_as_meta_typ state meta_thing =
    match meta_thing with
    | Synprs.Meta.Thing.RawContext { location; _ } ->
        raise (Illegal_context_meta_type location)
    | Synprs.Meta.Thing.RawSchema { location; schema } ->
        let schema' = disambiguate_as_schema state schema in
        Synext.Meta.Typ.Context_schema { location; schema = schema' }
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Plain }
    (* Contextual type *) -> (
        let state', context' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        match object_ with
        | { Synprs.CLF.Context_object.objects = [ (Option.None, typ) ]
          ; head = Synprs.CLF.Context_object.Head.None _
          ; _
          } ->
            let typ' = CLF_disambiguation.disambiguate_as_typ state' typ in
            Synext.Meta.Typ.Contextual_typ
              { location; context = context'; typ = typ' }
        | { Synprs.CLF.Context_object.location; _ } ->
            raise (Illegal_substitution_or_context_contextual_type location))
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Hash }
    (* Parameter type *) -> (
        let state', context' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        match object_ with
        | { Synprs.CLF.Context_object.objects = [ (Option.None, typ) ]
          ; head = Synprs.CLF.Context_object.Head.None _
          ; _
          } ->
            let typ' = CLF_disambiguation.disambiguate_as_typ state' typ in
            Synext.Meta.Typ.Parameter_typ
              { location; context = context'; typ = typ' }
        | { Synprs.CLF.Context_object.location; _ } ->
            raise (Illegal_substitution_or_context_contextual_type location))
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar }
    (* Plain substitution type *) ->
        let state', domain' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        let _state'', range' =
          CLF_disambiguation.disambiguate_as_context state' object_
        in
        Synext.Meta.Typ.Plain_substitution_typ
          { location; domain = domain'; range = range' }
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar_hash }
    (* Renaming substitution type *) ->
        let state', domain' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        let _state'', range' =
          CLF_disambiguation.disambiguate_as_context state' object_
        in
        Synext.Meta.Typ.Renaming_substitution_typ
          { location; domain = domain'; range = range' }

  and disambiguate_as_meta_object state meta_thing =
    match meta_thing with
    | Synprs.Meta.Thing.RawSchema { location; _ } ->
        raise (Expected_meta_object location)
    | Synprs.Meta.Thing.RawTurnstile { location; variant = `Hash; _ } ->
        raise (Illegal_hash_modifier_meta_object location)
    | Synprs.Meta.Thing.RawContext { location; context } (* Context *) ->
        let _state', context' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        Synext.Meta.Object.Context { location; context = context' }
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Plain }
    (* Contextual term *) -> (
        let state', context' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        let { Synprs.CLF.Context_object.head; objects; _ } = object_ in
        match (head, objects) with
        | Synprs.CLF.Context_object.Head.None _, [ (Option.None, term) ] ->
            let term' =
              CLF_disambiguation.disambiguate_as_term state' term
            in
            Synext.Meta.Object.Contextual_term
              { location; context = context'; term = term' }
        | _ -> raise (Illegal_missing_dollar_modifier_meta_object location))
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar }
    (* Plain substitution *) ->
        let state', domain' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        let range' =
          CLF_disambiguation.disambiguate_as_substitution state' object_
        in
        Synext.Meta.Object.Plain_substitution
          { location; domain = domain'; range = range' }
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar_hash }
    (* Renaming substitution *) ->
        let state', domain' =
          CLF_disambiguation.disambiguate_as_context state context
        in
        let range' =
          CLF_disambiguation.disambiguate_as_substitution state' object_
        in
        Synext.Meta.Object.Renaming_substitution
          { location; domain = domain'; range = range' }

  and disambiguate_as_meta_pattern state meta_thing =
    match meta_thing with
    | Synprs.Meta.Thing.RawSchema { location; _ } ->
        raise (Expected_meta_pattern location)
    | Synprs.Meta.Thing.RawTurnstile { location; variant = `Hash; _ } ->
        raise (Illegal_hash_modifier_meta_pattern location)
    | Synprs.Meta.Thing.RawContext { location; context } (* Context *) ->
        let context' =
          CLF_disambiguation.disambiguate_as_context_pattern state context
        in
        Synext.Meta.Pattern.Context { location; context = context' }
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Plain }
    (* Contextual term *) -> (
        let context' =
          CLF_disambiguation.disambiguate_as_context_pattern state context
        in
        let { Synprs.CLF.Context_object.head; objects; _ } = object_ in
        match (head, objects) with
        | Synprs.CLF.Context_object.Head.None _, [ (Option.None, term) ] ->
            let state' =
              add_clf_context_pattern_bindings_to_disambiguation_state
                context' state
            in
            let term' =
              CLF_disambiguation.disambiguate_as_term_pattern state' term
            in
            Synext.Meta.Pattern.Contextual_term
              { location; context = context'; term = term' }
        | _ -> raise (Illegal_missing_dollar_modifier_meta_pattern location))
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar }
    (* Plain substitution pattern *) ->
        let domain' =
          CLF_disambiguation.disambiguate_as_context_pattern state context
        in
        let state' =
          add_clf_context_pattern_bindings_to_disambiguation_state domain'
            state
        in
        let range' =
          CLF_disambiguation.disambiguate_as_substitution_pattern state'
            object_
        in
        Synext.Meta.Pattern.Plain_substitution
          { location; domain = domain'; range = range' }
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar_hash }
    (* Renaming substitution pattern *) ->
        let domain' =
          CLF_disambiguation.disambiguate_as_context_pattern state context
        in
        let state' =
          add_clf_context_pattern_bindings_to_disambiguation_state domain'
            state
        in
        let range' =
          CLF_disambiguation.disambiguate_as_substitution_pattern state'
            object_
        in
        Synext.Meta.Pattern.Renaming_substitution
          { location; domain = domain'; range = range' }

  and disambiguate_schema_some_clause state some =
    (* Schema some-clauses are dependent, meaning that bound variables on the
       left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    let state', some_rev' =
      List1.fold_left
        (fun (identifier, typ) ->
          let typ' = CLF_disambiguation.disambiguate_as_typ state typ in
          let elements' = List1.singleton (identifier, typ')
          and state' =
            Disambiguation_state.add_lf_term_variable identifier state
          in
          (state', elements'))
        (fun (state', elements') (identifier, typ) ->
          let typ' = CLF_disambiguation.disambiguate_as_typ state' typ in
          let elements'' = List1.cons (identifier, typ') elements'
          and state'' =
            Disambiguation_state.add_lf_term_variable identifier state'
          in
          (state'', elements''))
        some
    in
    let some' = List1.rev some_rev' in
    (state', some')

  and disambiguate_schema_block_clause state block =
    (* Schema block-clauses are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    match block with
    | List1.T ((Option.None, typ), []) ->
        let typ' = CLF_disambiguation.disambiguate_as_typ state typ in
        `Unnamed typ'
    | block ->
        let _state', bindings_rev' =
          List1.fold_left
            (fun element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  raise (Illegal_unnamed_block_element_type location)
              | Option.Some identifier, typ ->
                  let typ' =
                    CLF_disambiguation.disambiguate_as_typ state typ
                  in
                  let elements' = List1.singleton (identifier, typ')
                  and state' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state
                  in
                  (state', elements'))
            (fun (state', elements_rev') element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  raise (Illegal_unnamed_block_element_type location)
              | Option.Some identifier, typ ->
                  let typ' =
                    CLF_disambiguation.disambiguate_as_typ state' typ
                  in
                  let elements_rev'' =
                    List1.cons (identifier, typ') elements_rev'
                  and state'' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state'
                  in
                  (state'', elements_rev''))
            block
        in
        let bindings' = List1.rev bindings_rev' in
        `Record bindings'

  and disambiguate_as_schema state schema_object =
    match schema_object with
    | Synprs.Meta.Schema_object.Raw_constant { location; identifier } ->
        Synext.Meta.Schema.Constant { location; identifier }
    | Synprs.Meta.Schema_object.Raw_alternation { location; schemas } ->
        let schemas' = List2.map (disambiguate_as_schema state) schemas in
        Synext.Meta.Schema.Alternation { location; schemas = schemas' }
    | Synprs.Meta.Schema_object.Raw_element { location; some; block } -> (
        match some with
        | Option.None ->
            let block' = disambiguate_schema_block_clause state block in
            Synext.Meta.Schema.Element
              { location; some = Option.none; block = block' }
        | Option.Some some ->
            let state', some' = disambiguate_schema_some_clause state some in
            let block' = disambiguate_schema_block_clause state' block in
            Synext.Meta.Schema.Element
              { location; some = Option.some some'; block = block' })

  and disambiguate_as_meta_context state context_object =
    let { Synprs.Meta.Context_object.location; bindings } = context_object in
    (* Meta-contexts are dependent, meaning that bound variables on the left
       of a declaration may appear in the type of a binding on the right.
       Bindings may not recursively refer to themselves. *)
    let state', bindings_rev' =
      List.fold_left
        (fun (state, bindings_rev') binding ->
          match binding with
          | ( (identifier, _identifier_modifier)
            , Option.None (* Missing meta-type *) ) ->
              let location = Identifier.location identifier in
              raise (Illegal_missing_meta_type_annotation location)
          | (identifier, `Plain), Option.Some meta_type
          (* Plain meta-variable binding *) -> (
              let meta_type' = disambiguate_as_meta_typ state meta_type in
              match meta_type' with
              | Synext.Meta.Typ.Context_schema _ ->
                  let state' =
                    Disambiguation_state.add_context_variable identifier
                      state
                  in
                  (state', (identifier, meta_type') :: bindings_rev')
              | Synext.Meta.Typ.Contextual_typ _ ->
                  let state' =
                    Disambiguation_state.add_meta_variable identifier state
                  in
                  (state', (identifier, meta_type') :: bindings_rev')
              | _ ->
                  let location = Synext.location_of_meta_type meta_type' in
                  raise (Expected_contextual_type_or_schema location))
          | (identifier, `Hash), Option.Some meta_type
          (* Parameter variable binding *) -> (
              let state' =
                Disambiguation_state.add_parameter_variable identifier state
              and meta_type' = disambiguate_as_meta_typ state meta_type in
              match meta_type' with
              | Synext.Meta.Typ.Contextual_typ _ ->
                  (state', (identifier, meta_type') :: bindings_rev')
              | _ ->
                  let location = Synext.location_of_meta_type meta_type' in
                  raise (Expected_contextual_type location))
          | (identifier, `Dollar), Option.Some meta_type
          (* Plain substitution or renaming substitution variable binding *)
            -> (
              let state' =
                Disambiguation_state.add_substitution_variable identifier
                  state
              and meta_type' = disambiguate_as_meta_typ state meta_type in
              match disambiguate_as_meta_typ state meta_type with
              | Synext.Meta.Typ.Plain_substitution_typ _
              | Synext.Meta.Typ.Renaming_substitution_typ _ ->
                  (state', (identifier, meta_type') :: bindings_rev')
              | _ ->
                  let location = Synext.location_of_meta_type meta_type' in
                  raise
                    (Expected_plain_or_renaming_substitution_type location)))
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    let context' = { Synext.Meta.Context.location; bindings = bindings' } in
    (state', context')
end

module type COMP_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Exceptions} *)

  (* TODO: *)

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

module Comp
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguation : META_DISAMBIGUATION
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

  (** {1 Exceptions} *)

  (** {2 Exceptions for computation-level kind disambiguation} *)

  exception Illegal_identifier_kind of Location.t

  exception Illegal_qualified_identifier_kind of Location.t

  exception Illegal_backward_arrow_kind of Location.t

  exception Illegal_cross_kind of Location.t

  exception Illegal_box_kind of Location.t

  exception Illegal_application_kind of Location.t

  exception Illegal_untyped_pi_kind_parameter of Location.t

  (** {2 Exceptions for computation-level type disambiguation} *)

  exception Illegal_ctype_type of Location.t

  exception
    Expected_computation_type_constant of
      { location : Location.t
      ; actual_binding : Disambiguation_state.entry
      }

  exception
    Unbound_computation_type_constant of
      { location : Location.t
      ; identifier : Qualified_identifier.t
      }

  exception Illegal_untyped_pi_type of Location.t

  (** {2 Exceptions for computation-level expression disambiguation} *)

  exception Illegal_variables_bound_several_times of Location.t List2.t

  (** {2 Exceptions for computation-level context disambiguation} *)

  exception Illegal_missing_context_binding_type of Location.t

  (** {2 Exceptions for computation-level pattern disambiguation} *)

  exception Illegal_meta_annotated_pattern_missing_identifier of Location.t

  exception Illegal_meta_annotated_pattern_missing_type of Location.t

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
        raise (Illegal_variables_bound_several_times locations)

  (** {1 Disambiguation} *)

  let rec disambiguate_as_kind state sort_object =
    match sort_object with
    | Synprs.Comp.Sort_object.Raw_identifier { location; _ } ->
        raise (Illegal_identifier_kind location)
    | Synprs.Comp.Sort_object.Raw_qualified_identifier { location; _ } ->
        raise (Illegal_qualified_identifier_kind location)
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; orientation = `Backward; _ } ->
        raise (Illegal_backward_arrow_kind location)
    | Synprs.Comp.Sort_object.Raw_cross { location; _ } ->
        raise (Illegal_cross_kind location)
    | Synprs.Comp.Sort_object.Raw_box { location; _ } ->
        raise (Illegal_box_kind location)
    | Synprs.Comp.Sort_object.Raw_application { location; _ } ->
        raise (Illegal_application_kind location)
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Synext.Comp.Kind.Ctype { location }
    | Synprs.Comp.Sort_object.Raw_pi
        { location; parameter_sort = Option.None; _ } ->
        raise (Illegal_untyped_pi_kind_parameter location)
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
        raise (Illegal_ctype_type location)
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
        | entry ->
            raise
              (Expected_computation_type_constant
                 { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_identifier _ ->
            raise
              (Unbound_computation_type_constant
                 { location; identifier = qualified_identifier }))
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
        | entry ->
            raise
              (Expected_computation_type_constant
                 { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            raise
              (Unbound_computation_type_constant { location; identifier }))
    | Synprs.Comp.Sort_object.Raw_pi
        { location; parameter_identifier; parameter_sort; plicity; body } ->
        let state', parameter_typ' =
          match (parameter_identifier, parameter_sort) with
          | (Option.Some identifier, _), Option.None ->
              let location = Identifier.location identifier in
              raise (Illegal_untyped_pi_type location)
          | (Option.None, _), Option.None ->
              raise (Illegal_untyped_pi_type location)
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
                  raise (Illegal_variables_bound_several_times locations))
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
        raise (Illegal_meta_annotated_pattern_missing_identifier location)
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_typ = Option.None; _ } ->
        raise (Illegal_meta_annotated_pattern_missing_type location)
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
    | _ -> Obj.magic ()

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
              raise (Illegal_missing_context_binding_type location)
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
