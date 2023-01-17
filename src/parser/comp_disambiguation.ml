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

[@@@warning "-A-4-44"]

(** {1 Exceptions} *)

(** {2 Exceptions for computation-level kind disambiguation} *)

exception Illegal_identifier_comp_kind

exception Illegal_qualified_identifier_comp_kind

exception Illegal_backward_arrow_comp_kind

exception Illegal_cross_comp_kind

exception Illegal_box_comp_kind

exception Illegal_application_comp_kind

exception Illegal_untyped_comp_pi_kind_parameter

exception Illegal_comp_typ_domain_pi_comp_kind

(** {2 Exceptions for computation-level type disambiguation} *)

exception Illegal_ctype_comp_type

exception Expected_comp_type_constant of Qualified_identifier.t

exception Unbound_comp_type_constant of Qualified_identifier.t

exception Illegal_untyped_comp_pi_type

(** {2 Exceptions for computation-level expression disambiguation} *)

exception Illegal_variables_bound_several_times

(** {2 Exceptions for computation-level context disambiguation} *)

exception Illegal_missing_comp_context_binding_type

(** {2 Exceptions for computation-level pattern disambiguation} *)

exception Illegal_meta_annotated_comp_pattern_missing_identifier

exception Illegal_meta_annotated_comp_pattern_missing_type

(** {2 Exceptions for computation-level copattern disambiguation} *)

exception Expected_comp_term_destructor_constant

(** {1 Disambiguation} *)

module type COMP_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind :
    Synprs.Comp.Sort_object.t -> Synext.Comp.Kind.t t

  val disambiguate_comp_typ :
    Synprs.Comp.Sort_object.t -> Synext.Comp.Typ.t t

  val disambiguate_comp_expression :
    Synprs.Comp.Expression_object.t -> Synext.Comp.Expression.t t

  val disambiguate_comp_pattern :
    Synprs.Comp.Pattern_object.t -> Synext.Comp.Pattern.t t

  val disambiguate_comp_context :
    Synprs.Comp.Context_object.t -> Synext.Comp.Context.t t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Disambiguation_state.state = struct
  include Disambiguation_state
  include Meta_disambiguation

  exception Plain_modifier_typ_mismatch

  exception Hash_modifier_typ_mismatch

  exception Dollar_modifier_typ_mismatch

  (** {1 Disambiguation State Helpers} *)

  let add_parameter_binding identifier modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        add_context_variable identifier
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        add_meta_variable identifier
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        add_parameter_variable identifier
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        add_substitution_variable identifier
    | `Plain, typ ->
        Error.raise_at1
          (Synext.location_of_meta_type typ)
          Plain_modifier_typ_mismatch
    | `Hash, typ ->
        Error.raise_at1
          (Synext.location_of_meta_type typ)
          Hash_modifier_typ_mismatch
    | `Dollar, typ ->
        Error.raise_at1
          (Synext.location_of_meta_type typ)
          Dollar_modifier_typ_mismatch

  let add_context_variable_opt = function
    | Option.Some identifier -> add_context_variable identifier
    | Option.None -> return ()

  let add_meta_variable_opt = function
    | Option.Some identifier -> add_meta_variable identifier
    | Option.None -> return ()

  let add_parameter_variable_opt = function
    | Option.Some identifier -> add_parameter_variable identifier
    | Option.None -> return ()

  let add_substitution_variable_opt = function
    | Option.Some identifier -> add_substitution_variable identifier
    | Option.None -> return ()

  let add_parameter_binding_opt identifier_opt modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        add_context_variable_opt identifier_opt
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        add_meta_variable_opt identifier_opt
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        add_parameter_variable_opt identifier_opt
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        add_substitution_variable_opt identifier_opt
    | `Plain, typ ->
        Error.raise_at1
          (Synext.location_of_meta_type typ)
          Plain_modifier_typ_mismatch
    | `Hash, typ ->
        Error.raise_at1
          (Synext.location_of_meta_type typ)
          Hash_modifier_typ_mismatch
    | `Dollar, typ ->
        Error.raise_at1
          (Synext.location_of_meta_type typ)
          Dollar_modifier_typ_mismatch

  let pop_binding_opt = function
    | Option.Some identifier -> pop_binding identifier
    | Option.None -> return ()

  let with_parameter_binding identifier modifier typ =
    scoped
      ~set:(add_parameter_binding identifier modifier typ)
      ~unset:(pop_binding identifier)

  let with_parameter_binding_opt identifier_opt modifier typ =
    scoped
      ~set:(add_parameter_binding_opt identifier_opt modifier typ)
      ~unset:(pop_binding_opt identifier_opt)

  let add_computation_variable_opt = function
    | Option.Some identifier -> add_computation_variable identifier
    | Option.None -> return ()

  let with_function_parameters parameters =
    scoped
      ~set:(traverse_list1_void add_computation_variable_opt parameters)
      ~unset:(traverse_reverse_list1_void pop_binding_opt parameters)

  let add_meta_parameter = function
    | Option.Some identifier, `Plain -> add_meta_variable identifier
    | Option.Some identifier, `Hash -> add_parameter_variable identifier
    | Option.Some identifier, `Dollar -> add_substitution_variable identifier
    | Option.None, _ -> return ()

  let pop_meta_parameter_binding = function
    | Option.Some identifier, _ -> pop_binding identifier
    | Option.None, _ -> return ()

  let with_meta_function_parameters parameters =
    scoped
      ~set:(traverse_list1_void add_meta_parameter parameters)
      ~unset:
        (traverse_reverse_list1_void pop_meta_parameter_binding parameters)

  let with_bindings_checkpoint m =
    scoped ~set:mark_bindings ~unset:rollback_bindings m

  (** {1 Disambiguation} *)

  let rec disambiguate_comp_kind = function
    | Synprs.Comp.Sort_object.Raw_identifier { location; _ } ->
        Error.raise_at1 location Illegal_identifier_comp_kind
    | Synprs.Comp.Sort_object.Raw_qualified_identifier { location; _ } ->
        Error.raise_at1 location Illegal_qualified_identifier_comp_kind
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_comp_kind
    | Synprs.Comp.Sort_object.Raw_cross { location; _ } ->
        Error.raise_at1 location Illegal_cross_comp_kind
    | Synprs.Comp.Sort_object.Raw_box { location; _ } ->
        Error.raise_at1 location Illegal_box_comp_kind
    | Synprs.Comp.Sort_object.Raw_application { location; _ } ->
        Error.raise_at1 location Illegal_application_comp_kind
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        return (Synext.Comp.Kind.Ctype { location })
    | Synprs.Comp.Sort_object.Raw_pi
        { location; parameter_sort = Option.None; _ } ->
        Error.raise_at1 location Illegal_untyped_comp_pi_kind_parameter
    | Synprs.Comp.Sort_object.Raw_pi
        { location
        ; parameter_identifier = parameter_identifier, modifier
        ; parameter_sort = Option.Some parameter_typ
        ; plicity
        ; body
        } ->
        let* parameter_typ' = disambiguate_meta_typ parameter_typ in
        let* body' =
          (with_parameter_binding_opt parameter_identifier modifier
             parameter_typ')
            (disambiguate_comp_kind body)
        in
        return
          (Synext.Comp.Kind.Pi
             { location
             ; parameter_identifier = Option.none
             ; parameter_type = parameter_typ'
             ; plicity
             ; body = body'
             })
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; domain; range; orientation = `Forward } -> (
        let* domain' = disambiguate_comp_typ domain in
        let* range' = disambiguate_comp_kind range in
        match domain' with
        | Synext.Comp.Typ.Box { meta_type; _ } ->
            return
              (Synext.Comp.Kind.Arrow
                 { location; domain = meta_type; range = range' })
        | Synext.Comp.Typ.Constant _
        | Synext.Comp.Typ.Pi _
        | Synext.Comp.Typ.Arrow _
        | Synext.Comp.Typ.Cross _
        | Synext.Comp.Typ.Application _ ->
            Error.raise_at1
              (Synext.location_of_comp_typ domain')
              Illegal_comp_typ_domain_pi_comp_kind)

  and disambiguate_comp_typ = function
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Error.raise_at1 location Illegal_ctype_comp_type
    | Synprs.Comp.Sort_object.Raw_pi
        { parameter_sort = Option.None; location; _ } ->
        Error.raise_at1 location Illegal_untyped_comp_pi_type
    | Synprs.Comp.Sort_object.Raw_identifier { location; identifier; quoted }
      -> (
        (* As a computation-level type, plain identifiers are necessarily
           type constants *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Computation_inductive_type_constant { operator; _ }) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Inductive
                 })
        | Result.Ok (Computation_stratified_type_constant { operator; _ }) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Stratified
                 })
        | Result.Ok (Computation_abbreviation_type_constant { operator; _ })
          ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Abbreviation
                 })
        | Result.Ok (Computation_coinductive_type_constant { operator; _ })
          ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Coinductive
                 })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_comp_type_constant qualified_identifier)
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            Error.raise_at1 location
              (Unbound_comp_type_constant qualified_identifier)
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Sort_object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As a computation-level type, identifiers of the form
           [(<identifier> `::')+ <identifier>] are necessarily type
           constants. *)
        lookup identifier >>= function
        | Result.Ok (Computation_inductive_type_constant { operator; _ }) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Inductive
                 })
        | Result.Ok (Computation_stratified_type_constant { operator; _ }) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Stratified
                 })
        | Result.Ok (Computation_abbreviation_type_constant { operator; _ })
          ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Abbreviation
                 })
        | Result.Ok (Computation_coinductive_type_constant { operator; _ })
          ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Coinductive
                 })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_comp_type_constant identifier)
                 (actual_binding_exn identifier entry))
        | Result.Error (Unbound_qualified_identifier _) ->
            Error.raise_at1 location (Unbound_comp_type_constant identifier)
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Sort_object.Raw_pi
        { location
        ; parameter_identifier = parameter_identifier, modifier
        ; parameter_sort = Option.Some parameter_typ
        ; plicity
        ; body
        } ->
        let* parameter_typ' = disambiguate_meta_typ parameter_typ in
        let* body' =
          (with_parameter_binding_opt parameter_identifier modifier
             parameter_typ')
            (disambiguate_comp_typ body)
        in
        return
          (Synext.Comp.Typ.Pi
             { location
             ; parameter_identifier
             ; parameter_type = parameter_typ'
             ; plicity
             ; body = body'
             })
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; domain; range; orientation } ->
        let* domain' = disambiguate_comp_typ domain in
        let* range' = disambiguate_comp_typ range in
        return
          (Synext.Comp.Typ.Arrow
             { location; domain = domain'; range = range'; orientation })
    | Synprs.Comp.Sort_object.Raw_cross { location; operands } ->
        let* types' = traverse_list2 disambiguate_comp_typ operands in
        return (Synext.Comp.Typ.Cross { location; types = types' })
    | Synprs.Comp.Sort_object.Raw_box { location; boxed } ->
        let* meta_type' = disambiguate_meta_typ boxed in
        return (Synext.Comp.Typ.Box { location; meta_type = meta_type' })
    | Synprs.Comp.Sort_object.Raw_application { location; objects } ->
        Obj.magic ()

  and disambiguate_comp_expression = function
    | Synprs.Comp.Expression_object.Raw_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { location; identifier; quoted } ->
        (* TODO: Can be the observation(s) of a variable *)
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_fn { location; parameters; body } ->
        let* body' =
          (with_function_parameters parameters)
            (disambiguate_comp_expression body)
        in
        return
          (Synext.Comp.Expression.Fn { location; parameters; body = body' })
    | Synprs.Comp.Expression_object.Raw_mlam { location; parameters; body }
      ->
        let* body' =
          (with_meta_function_parameters parameters)
            (disambiguate_comp_expression body)
        in
        return
          (Synext.Comp.Expression.Mlam { location; parameters; body = body' })
    | Synprs.Comp.Expression_object.Raw_fun { location; branches } ->
        let* branches' =
          traverse_list1 disambiguate_cofunction_branch branches
        in
        return
          (Synext.Comp.Expression.Fun { location; branches = branches' })
    | Synprs.Comp.Expression_object.Raw_box { location; meta_object } ->
        let* meta_object' = disambiguate_meta_object meta_object in
        return
          (Synext.Comp.Expression.Box
             { location; meta_object = meta_object' })
    | Synprs.Comp.Expression_object.Raw_let
        { location; pattern; scrutinee; body } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        let* pattern', body' =
          with_bindings_checkpoint
            (seq2
               (disambiguate_comp_pattern pattern)
               (disambiguate_comp_expression body))
        in
        return
          (Synext.Comp.Expression.Let
             { location
             ; pattern = pattern'
             ; scrutinee = scrutinee'
             ; body = body'
             })
    | Synprs.Comp.Expression_object.Raw_impossible { location; scrutinee } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        return
          (Synext.Comp.Expression.Impossible
             { location; scrutinee = scrutinee' })
    | Synprs.Comp.Expression_object.Raw_case
        { location; scrutinee; check_coverage; branches } ->
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        let* branches' = traverse_list1 disambiguate_case_branch branches in
        return
          (Synext.Comp.Expression.Case
             { location
             ; scrutinee = scrutinee'
             ; check_coverage
             ; branches = branches'
             })
    | Synprs.Comp.Expression_object.Raw_tuple { location; elements } ->
        let* elements' =
          traverse_list2 disambiguate_comp_expression elements
        in
        return
          (Synext.Comp.Expression.Tuple { location; elements = elements' })
    | Synprs.Comp.Expression_object.Raw_hole { location; label } ->
        return (Synext.Comp.Expression.Hole { location; label })
    | Synprs.Comp.Expression_object.Raw_box_hole { location } ->
        return (Synext.Comp.Expression.BoxHole { location })
    | Synprs.Comp.Expression_object.Raw_application { location; expressions }
      ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_annotated
        { location; expression; typ } ->
        let* expression' = disambiguate_comp_expression expression in
        let* typ' = disambiguate_comp_typ typ in
        return
          (Synext.Comp.Expression.Type_annotated
             { location; expression = expression'; typ = typ' })
    | Synprs.Comp.Expression_object.Raw_observation
        { location; scrutinee; destructor } ->
        (* TODO: Can be observation(s) *)
        Obj.magic ()

  and disambiguate_case_branch (pattern_object, body_object) =
    with_bindings_checkpoint
      (seq2
         (disambiguate_comp_pattern pattern_object)
         (disambiguate_comp_expression body_object))

  and disambiguate_cofunction_branch (copattern_objects, body_object) =
    with_bindings_checkpoint
      (seq2
         (traverse_list1 disambiguate_as_copattern copattern_objects)
         (disambiguate_comp_expression body_object))

  and disambiguate_comp_pattern = function
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_identifier = Option.None, _; _ } ->
        Error.raise_at1 location
          Illegal_meta_annotated_comp_pattern_missing_identifier
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_typ = Option.None; _ } ->
        Error.raise_at1 location
          Illegal_meta_annotated_comp_pattern_missing_type
    | Synprs.Comp.Pattern_object.Raw_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_box { location; pattern } ->
        let* pattern' = disambiguate_meta_pattern pattern in
        return
          (Synext.Comp.Pattern.MetaObject
             { location; meta_pattern = pattern' })
    | Synprs.Comp.Pattern_object.Raw_tuple { location; elements } ->
        let* elements' = traverse_list2 disambiguate_comp_pattern elements in
        return (Synext.Comp.Pattern.Tuple { location; elements = elements' })
    | Synprs.Comp.Pattern_object.Raw_application { location; patterns } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_annotated { location; pattern; typ } ->
        let* typ' = disambiguate_comp_typ typ in
        let* pattern' = disambiguate_comp_pattern pattern in
        return
          (Synext.Comp.Pattern.Type_annotated
             { location; pattern = pattern'; typ = typ' })
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location
        ; parameter_identifier = Option.Some parameter_identifier, modifier
        ; parameter_typ = Option.Some parameter_typ
        ; pattern
        } ->
        let* parameter_typ' = disambiguate_meta_typ parameter_typ in
        let* pattern' =
          (with_parameter_binding parameter_identifier modifier
             parameter_typ')
            (disambiguate_comp_pattern pattern)
        in
        return
          (Synext.Comp.Pattern.MetaTypeAnnotated
             { location
             ; annotation_identifier = parameter_identifier
             ; annotation_type = parameter_typ'
             ; body = pattern'
             })
    | Synprs.Comp.Pattern_object.Raw_wildcard { location } ->
        return (Synext.Comp.Pattern.Wildcard { location })

  and disambiguate_as_copattern = function
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier _ ->
        (* TODO: Can be a variable pattern together with an observation *)
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } -> (
        lookup constant >>= function
        | Result.Ok (Computation_term_destructor _) ->
            let* arguments' =
              traverse_list disambiguate_comp_pattern arguments
            in
            return
              (Synext.Comp.Copattern.Observation
                 { location; observation = constant; arguments = arguments' })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2
                 Expected_comp_term_destructor_constant
                 (actual_binding_exn constant entry))
        | Result.Error cause ->
            Error.raise_at1 (Qualified_identifier.location constant) cause)
    | ( Synprs.Comp.Pattern_object.Raw_identifier _
      | Synprs.Comp.Pattern_object.Raw_box _
      | Synprs.Comp.Pattern_object.Raw_tuple _
      | Synprs.Comp.Pattern_object.Raw_application _
      | Synprs.Comp.Pattern_object.Raw_annotated _
      | Synprs.Comp.Pattern_object.Raw_meta_annotated _
      | Synprs.Comp.Pattern_object.Raw_wildcard _ ) as pattern_object ->
        let* pattern' = disambiguate_comp_pattern pattern_object in
        return (Synext.Comp.Copattern.Pattern pattern')

  and disambiguate_comp_context context_object =
    let { Synprs.Comp.Context_object.location; bindings } = context_object in
    (* Computation contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves. *)
    let* bindings' = traverse_list disambiguate_context_binding bindings in
    return { Synext.Comp.Context.location; bindings = bindings' }

  and disambiguate_context_binding = function
    | identifier, Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_missing_comp_context_binding_type
    | identifier, Option.Some typ ->
        let* typ' = disambiguate_comp_typ typ in
        let* () = add_computation_variable identifier in
        return (identifier, typ')
end
