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

(** {2 Exceptions for meta-type disambiguation} *)

exception Illegal_context_meta_type

exception Illegal_substitution_or_context_contextual_type

(** {2 Exceptions for meta-object disambiguation} *)

exception Illegal_missing_dollar_modifier_meta_object

exception Illegal_hash_modifier_meta_object

exception Expected_meta_object

(** {2 Exceptions for meta-pattern disambiguation} *)

exception Illegal_missing_dollar_modifier_meta_pattern

exception Illegal_hash_modifier_meta_pattern

exception Expected_meta_pattern

(** {2 Exceptions for schema disambiguation} *)

exception Illegal_unnamed_block_element_type

(** {2 Exceptions for meta-context disambiguation} *)

exception Expected_contextual_type

exception Expected_plain_or_renaming_substitution_type

exception Expected_contextual_type_or_schema

exception Illegal_missing_meta_type_annotation

(** {1 Disambiguation} *)

module type META_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Disambiguation} *)

  val disambiguate_as_meta_typ :
       Synprs.meta_thing
    -> disambiguation_state
    -> disambiguation_state * Synext.meta_typ

  val disambiguate_as_meta_object :
       Synprs.meta_thing
    -> disambiguation_state
    -> disambiguation_state * Synext.meta_object

  val disambiguate_as_meta_pattern :
       Synprs.meta_thing
    -> disambiguation_state
    -> disambiguation_state * Synext.meta_pattern

  val disambiguate_as_schema :
       Synprs.schema_object
    -> disambiguation_state
    -> disambiguation_state * Synext.schema

  val disambiguate_as_meta_context :
       Synprs.meta_context_object
    -> disambiguation_state
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

  include State.Make (Disambiguation_state)

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

  let rec disambiguate_as_meta_typ meta_thing =
    match meta_thing with
    | Synprs.Meta.Thing.RawContext { location; _ } ->
        Error.raise_at1 location Illegal_context_meta_type
    | Synprs.Meta.Thing.RawSchema { location; schema } ->
        let* schema' = disambiguate_as_schema schema in
        return
          (Synext.Meta.Typ.Context_schema { location; schema = schema' })
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Plain }
    (* Contextual type *) -> (
        let* context' = CLF_disambiguation.disambiguate_as_context context in
        match object_ with
        | { Synprs.CLF.Context_object.objects = [ (Option.None, typ) ]
          ; head = Synprs.CLF.Context_object.Head.None _
          ; _
          } ->
            let* typ' = CLF_disambiguation.disambiguate_as_typ typ in
            return
              (Synext.Meta.Typ.Contextual_typ
                 { location; context = context'; typ = typ' })
        | { Synprs.CLF.Context_object.location; _ } ->
            Error.raise_at1 location
              Illegal_substitution_or_context_contextual_type)
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Hash }
    (* Parameter type *) -> (
        let* context' = CLF_disambiguation.disambiguate_as_context context in
        match object_ with
        | { Synprs.CLF.Context_object.objects = [ (Option.None, typ) ]
          ; head = Synprs.CLF.Context_object.Head.None _
          ; _
          } ->
            let* typ' = CLF_disambiguation.disambiguate_as_typ typ in
            return
              (Synext.Meta.Typ.Parameter_typ
                 { location; context = context'; typ = typ' })
        | { Synprs.CLF.Context_object.location; _ } ->
            Error.raise_at1 location
              Illegal_substitution_or_context_contextual_type)
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar }
    (* Plain substitution type *) ->
        let* domain' = CLF_disambiguation.disambiguate_as_context context in
        let* range' = CLF_disambiguation.disambiguate_as_context object_ in
        return
          (Synext.Meta.Typ.Plain_substitution_typ
             { location; domain = domain'; range = range' })
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar_hash }
    (* Renaming substitution type *) ->
        let* domain' = CLF_disambiguation.disambiguate_as_context context in
        let* range' = CLF_disambiguation.disambiguate_as_context object_ in
        return
          (Synext.Meta.Typ.Renaming_substitution_typ
             { location; domain = domain'; range = range' })

  and disambiguate_as_meta_object meta_thing =
    match meta_thing with
    | Synprs.Meta.Thing.RawSchema { location; _ } ->
        Error.raise_at1 location Expected_meta_object
    | Synprs.Meta.Thing.RawTurnstile { location; variant = `Hash; _ } ->
        Error.raise_at1 location Illegal_hash_modifier_meta_object
    | Synprs.Meta.Thing.RawContext { location; context } (* Context *) ->
        let* context' = CLF_disambiguation.disambiguate_as_context context in
        return (Synext.Meta.Object.Context { location; context = context' })
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Plain }
    (* Contextual term *) -> (
        let* context' = CLF_disambiguation.disambiguate_as_context context in
        let { Synprs.CLF.Context_object.head; objects; _ } = object_ in
        match (head, objects) with
        | Synprs.CLF.Context_object.Head.None _, [ (Option.None, term) ] ->
            let* term' = CLF_disambiguation.disambiguate_as_term term in
            return
              (Synext.Meta.Object.Contextual_term
                 { location; context = context'; term = term' })
        | _ ->
            Error.raise_at1 location
              Illegal_missing_dollar_modifier_meta_object)
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar }
    (* Plain substitution *) ->
        let* domain' = CLF_disambiguation.disambiguate_as_context context in
        let* range' =
          CLF_disambiguation.disambiguate_as_substitution object_
        in
        return
          (Synext.Meta.Object.Plain_substitution
             { location; domain = domain'; range = range' })
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar_hash }
    (* Renaming substitution *) ->
        let* domain' = CLF_disambiguation.disambiguate_as_context context in
        let* range' =
          CLF_disambiguation.disambiguate_as_substitution object_
        in
        return
          (Synext.Meta.Object.Renaming_substitution
             { location; domain = domain'; range = range' })

  and disambiguate_as_meta_pattern meta_thing =
    match meta_thing with
    | Synprs.Meta.Thing.RawSchema { location; _ } ->
        Error.raise_at1 location Expected_meta_pattern
    | Synprs.Meta.Thing.RawTurnstile { location; variant = `Hash; _ } ->
        Error.raise_at1 location Illegal_hash_modifier_meta_pattern
    | Synprs.Meta.Thing.RawContext { location; context } (* Context *) ->
        let* context' =
          CLF_disambiguation.disambiguate_as_context_pattern context
        in
        return (Synext.Meta.Pattern.Context { location; context = context' })
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Plain }
    (* Contextual term *) -> (
        let* context' =
          CLF_disambiguation.disambiguate_as_context_pattern context
        in
        let { Synprs.CLF.Context_object.head; objects; _ } = object_ in
        match (head, objects) with
        | Synprs.CLF.Context_object.Head.None _, [ (Option.None, term) ] ->
            let* term' =
              locally
                (add_clf_context_pattern_bindings_to_disambiguation_state
                   context')
                (CLF_disambiguation.disambiguate_as_term_pattern term)
            in
            return
              (Synext.Meta.Pattern.Contextual_term
                 { location; context = context'; term = term' })
        | _ ->
            Error.raise_at1 location
              Illegal_missing_dollar_modifier_meta_pattern)
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar }
    (* Plain substitution pattern *) ->
        let* domain' =
          CLF_disambiguation.disambiguate_as_context_pattern context
        in
        let* range' =
          locally
            (add_clf_context_pattern_bindings_to_disambiguation_state domain')
            (CLF_disambiguation.disambiguate_as_substitution_pattern object_)
        in
        return
          (Synext.Meta.Pattern.Plain_substitution
             { location; domain = domain'; range = range' })
    | Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Dollar_hash }
    (* Renaming substitution pattern *) ->
        let* domain' =
          CLF_disambiguation.disambiguate_as_context_pattern context
        in
        let* range' =
          locally
            (add_clf_context_pattern_bindings_to_disambiguation_state domain')
            (CLF_disambiguation.disambiguate_as_substitution_pattern object_)
        in
        return
          (Synext.Meta.Pattern.Renaming_substitution
             { location; domain = domain'; range = range' })

  and disambiguate_schema_some_clause some state =
    (* Schema some-clauses are dependent, meaning that bound variables on the
       left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    let state', some_rev' =
      List1.fold_left
        (fun (identifier, typ) ->
          let _state', typ' =
            CLF_disambiguation.disambiguate_as_typ typ state
          in
          let elements' = List1.singleton (identifier, typ')
          and state'' =
            Disambiguation_state.add_lf_term_variable identifier state
          in
          (state'', elements'))
        (fun (state', elements') (identifier, typ) ->
          let _state'', typ' =
            CLF_disambiguation.disambiguate_as_typ typ state'
          in
          let elements'' = List1.cons (identifier, typ') elements'
          and state''' =
            Disambiguation_state.add_lf_term_variable identifier state'
          in
          (state''', elements''))
        some
    in
    let some' = List1.rev some_rev' in
    (state', some')

  and disambiguate_schema_block_clause block state =
    (* Schema block-clauses are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    match block with
    | List1.T ((Option.None, typ), []) ->
        let _state', typ' =
          CLF_disambiguation.disambiguate_as_typ typ state
        in
        (state, `Unnamed typ')
    | block ->
        let _state', bindings_rev' =
          List1.fold_left
            (fun element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  Error.raise_at1 location Illegal_unnamed_block_element_type
              | Option.Some identifier, typ ->
                  let _state'', typ' =
                    CLF_disambiguation.disambiguate_as_typ typ state
                  in
                  let elements' = List1.singleton (identifier, typ')
                  and state'' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state
                  in
                  (state'', elements'))
            (fun (state', elements_rev') element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  Error.raise_at1 location Illegal_unnamed_block_element_type
              | Option.Some identifier, typ ->
                  let _state'', typ' =
                    CLF_disambiguation.disambiguate_as_typ typ state'
                  in
                  let elements_rev'' =
                    List1.cons (identifier, typ') elements_rev'
                  and state''' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state'
                  in
                  (state''', elements_rev''))
            block
        in
        let bindings' = List1.rev bindings_rev' in
        (state, `Record bindings')

  and disambiguate_as_schema schema_object =
    match schema_object with
    | Synprs.Meta.Schema_object.Raw_constant { location; identifier } ->
        return (Synext.Meta.Schema.Constant { location; identifier })
    | Synprs.Meta.Schema_object.Raw_alternation { location; schemas } ->
        get >>= fun state ->
        let schemas' =
          List2.map
            (fun schema -> eval (disambiguate_as_schema schema) state)
            schemas
        in
        return
          (Synext.Meta.Schema.Alternation { location; schemas = schemas' })
    | Synprs.Meta.Schema_object.Raw_element { location; some; block } -> (
        match some with
        | Option.None ->
            let* block' = disambiguate_schema_block_clause block in
            return
              (Synext.Meta.Schema.Element
                 { location; some = Option.none; block = block' })
        | Option.Some some ->
            let* some' = disambiguate_schema_some_clause some in
            let* block' = disambiguate_schema_block_clause block in
            return
              (Synext.Meta.Schema.Element
                 { location; some = Option.some some'; block = block' }))

  and disambiguate_as_meta_context :
         Synprs.meta_context_object
      -> disambiguation_state
      -> disambiguation_state * Synext.meta_context =
   fun context_object state ->
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
              Error.raise_at1 location Illegal_missing_meta_type_annotation
          | (identifier, `Plain), Option.Some meta_type
          (* Plain meta-variable binding *) -> (
              let meta_type' =
                eval (disambiguate_as_meta_typ meta_type) state
              in
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
                  Error.raise_at1 location Expected_contextual_type_or_schema
              )
          | (identifier, `Hash), Option.Some meta_type
          (* Parameter variable binding *) -> (
              let meta_type' =
                eval (disambiguate_as_meta_typ meta_type) state
              in
              let state' =
                Disambiguation_state.add_parameter_variable identifier state
              in
              match meta_type' with
              | Synext.Meta.Typ.Contextual_typ _ ->
                  (state', (identifier, meta_type') :: bindings_rev')
              | _ ->
                  let location = Synext.location_of_meta_type meta_type' in
                  Error.raise_at1 location Expected_contextual_type)
          | (identifier, `Dollar), Option.Some meta_type
          (* Plain substitution or renaming substitution variable binding *)
            -> (
              let meta_type' =
                eval (disambiguate_as_meta_typ meta_type) state
              in
              let state' =
                Disambiguation_state.add_substitution_variable identifier
                  state
              in
              match eval (disambiguate_as_meta_typ meta_type) state with
              | Synext.Meta.Typ.Plain_substitution_typ _
              | Synext.Meta.Typ.Renaming_substitution_typ _ ->
                  (state', (identifier, meta_type') :: bindings_rev')
              | _ ->
                  let location = Synext.location_of_meta_type meta_type' in
                  Error.raise_at1 location
                    Expected_plain_or_renaming_substitution_type))
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    let context' = { Synext.Meta.Context.location; bindings = bindings' } in
    (state', context')
end
