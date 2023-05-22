(** Disambiguation of the parser syntax to the external syntax.

    Elements of the syntax for Beluga require the symbol table for
    disambiguation. This module contains stateful functions for elaborating
    the context-free parser syntax to the data-dependent external syntax. The
    logic for the symbol lookups is repeated in the indexing phase to the
    approximate syntax.

    The "Beluga Language Specification" document contains additional details
    as to which syntactic structures have ambiguities. *)

open Support
open Beluga_syntax

(** {1 Exceptions} *)

exception Plain_modifier_typ_mismatch

exception Hash_modifier_typ_mismatch

exception Dollar_modifier_typ_mismatch

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

(** {2 Exceptions for type-level application rewriting} *)

exception Expected_meta_object

(** {2 Exceptions for computation-level expression disambiguation} *)

exception Expected_program_or_constructor_constant of Qualified_identifier.t

exception Unbound_comp_term_destructor_constant of Qualified_identifier.t

(** {2 Exceptions for computation-level context disambiguation} *)

exception Illegal_missing_comp_context_binding_type of Identifier.t

(** {2 Exceptions for computation-level pattern disambiguation} *)

exception Expected_constructor_constant of Qualified_identifier.t

exception Illegal_inner_meta_annotated_comp_pattern

exception Unbound_comp_term_constructor_constant of Qualified_identifier.t

(** {2 Exceptions for computation-level copattern disambiguation} *)

exception Expected_comp_term_destructor_constant

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Plain_modifier_typ_mismatch ->
        Format.dprintf
          "A plain meta-object identifier may only be used for contextual \
           types or contexts."
    | Hash_modifier_typ_mismatch ->
        Format.dprintf
          "A hash meta-object identifier may only be used for contextual \
           parameter types."
    | Dollar_modifier_typ_mismatch ->
        Format.dprintf
          "A dollar meta-object identifier may only be used for plain or \
           renaming substitutions."
    | Illegal_identifier_comp_kind ->
        Format.dprintf
          "An identifier may not appear as a computation-level kind."
    | Illegal_qualified_identifier_comp_kind ->
        Format.dprintf
          "A qualified identifier may not appear as a computation-level \
           kind."
    | Illegal_backward_arrow_comp_kind ->
        Format.dprintf
          "Backward arrows may not appear as computation-level kinds."
    | Illegal_cross_comp_kind ->
        Format.dprintf
          "Cross operators may not appear as computation-level kinds."
    | Illegal_box_comp_kind ->
        Format.dprintf
          "Boxed types or objects may not appear as computation-level kinds."
    | Illegal_application_comp_kind ->
        Format.dprintf
          "Applications may not appear as computation-level kinds."
    | Illegal_untyped_comp_pi_kind_parameter ->
        Format.dprintf
          "Computation-level Pi kind parameters must be annotated with a \
           meta-type."
    | Illegal_comp_typ_domain_pi_comp_kind ->
        Format.dprintf
          "Computation-level Pi kind parameters may only be annotated with \
           a meta-type, not a computation-level type."
    | Illegal_ctype_comp_type ->
        Format.dprintf
          "The computation-level kind `ctype' may not appear as a \
           computation-level type."
    | Expected_comp_type_constant qualified_identifier ->
        Format.dprintf "Expected %a to be a computation-level type constant."
          Qualified_identifier.pp qualified_identifier
    | Unbound_comp_type_constant qualified_identifier ->
        Format.dprintf "The computation-level type constant %a is unbound."
          Qualified_identifier.pp qualified_identifier
    | Illegal_untyped_comp_pi_type ->
        Format.dprintf
          "Computation-level Pi type parameters must be annotated with a \
           meta-type."
    | Expected_meta_object -> Format.dprintf "Expected a meta-object."
    | Expected_program_or_constructor_constant qualified_identifier ->
        Format.dprintf
          "Expected %a to be a program constant or computation-level \
           constructor."
          Qualified_identifier.pp qualified_identifier
    | Unbound_comp_term_destructor_constant qualified_identifier ->
        Format.dprintf "Computation-level destructor constant %a is unbound."
          Qualified_identifier.pp qualified_identifier
    | Illegal_missing_comp_context_binding_type identifier ->
        Format.dprintf
          "Missing computation-level context type for binding for %a."
          Identifier.pp identifier
    | Expected_constructor_constant qualified_identifier ->
        Format.dprintf "Expected %a to be a computation-level constructor."
          Qualified_identifier.pp qualified_identifier
    | Illegal_inner_meta_annotated_comp_pattern ->
        Format.dprintf
          "Meta-context annotations to patterns cannot be nested in \
           patterns. Move this annotation to the left of the pattern."
    | Unbound_comp_term_constructor_constant identifier ->
        Format.dprintf "Unbound computation-level constructor constant %a."
          Qualified_identifier.pp identifier
    | Expected_comp_term_destructor_constant ->
        Format.dprintf
          "Expected a computation-level term destructor constant."
    | exn -> Error.raise_unsupported_exception_printing exn)

(** {1 Disambiguation} *)

module type COMP_DISAMBIGUATION = sig
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind :
    state -> Synprs.comp_sort_object -> Synext.comp_kind

  val disambiguate_comp_typ :
    state -> Synprs.comp_sort_object -> Synext.comp_typ

  val disambiguate_comp_expression :
    state -> Synprs.comp_expression_object -> Synext.comp_expression

  val disambiguate_comp_pattern :
    state -> Synprs.comp_pattern_object -> Synext.comp_pattern

  val disambiguate_comp_copattern :
    state -> Synprs.comp_copattern_object List1.t -> Synext.comp_copattern

  val with_disambiguated_comp_context :
       state
    -> Synprs.comp_context_object
    -> (state -> Synext.comp_context -> 'a)
    -> 'a
end

module Make
    (Disambiguation_state : Disambiguation_state.DISAMBIGUATION_STATE)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Disambiguation_state.state = struct
  include Disambiguation_state
  include Meta_disambiguator

  module Comp_sort_object = struct
    type t = Synprs.comp_sort_object

    type location = Location.t

    let location = Synprs.location_of_comp_sort_object
  end

  module Comp_typ_application_disambiguation =
    Application_disambiguation.Make_application_disambiguation
      (Comp_sort_object)

  let identify_typ_operator_identifier state expression identifier =
    match lookup_operator state identifier with
    | Option.None ->
        Comp_typ_application_disambiguation.make_expression expression
    | Option.Some operator ->
        Comp_typ_application_disambiguation.make_operator expression operator
          identifier

  let identify_typ_operator state expression =
    match expression with
    | Synprs.Comp.Sort_object.Raw_qualified_identifier
        { identifier; prefixed = false; _ } ->
        identify_typ_operator_identifier state expression identifier
    | Synprs.Comp.Sort_object.Raw_identifier
        { identifier; prefixed = false; _ } ->
        identify_typ_operator_identifier state expression
          (Qualified_identifier.make_simple identifier)
    | _ -> Comp_typ_application_disambiguation.make_expression expression

  module Comp_expression_object = struct
    type t = Synprs.comp_expression_object

    type location = Location.t

    let location = Synprs.location_of_comp_expression_object
  end

  module Comp_expression_application_disambiguation =
    Application_disambiguation.Make_application_disambiguation
      (Comp_expression_object)

  let identify_expression_operator_identifier state expression identifier =
    match lookup_operator state identifier with
    | Option.None ->
        Comp_expression_application_disambiguation.make_expression expression
    | Option.Some operator ->
        Comp_expression_application_disambiguation.make_operator expression
          operator identifier

  let identify_expression_operator state expression =
    match expression with
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { identifier; prefixed = false; _ } ->
        identify_expression_operator_identifier state expression identifier
    | Synprs.Comp.Expression_object.Raw_identifier
        { identifier; prefixed = false; _ } ->
        identify_expression_operator_identifier state expression
          (Qualified_identifier.make_simple identifier)
    | _ ->
        Comp_expression_application_disambiguation.make_expression expression

  module Comp_pattern_object = struct
    type t = Synprs.comp_pattern_object

    type location = Location.t

    let location = Synprs.location_of_comp_pattern_object
  end

  module Comp_pattern_application_disambiguation =
    Application_disambiguation.Make_application_disambiguation
      (Comp_pattern_object)

  let identify_pattern_operator_identifier state expression identifier =
    match lookup_operator state identifier with
    | Option.None ->
        Comp_pattern_application_disambiguation.make_expression expression
    | Option.Some operator ->
        Comp_pattern_application_disambiguation.make_operator expression
          operator identifier

  let identify_pattern_operator state expression =
    match expression with
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { identifier; prefixed = false; _ } ->
        identify_pattern_operator_identifier state expression identifier
    | Synprs.Comp.Pattern_object.Raw_identifier
        { identifier; prefixed = false; _ } ->
        identify_pattern_operator_identifier state expression
          (Qualified_identifier.make_simple identifier)
    | _ -> Comp_pattern_application_disambiguation.make_expression expression

  (** {1 Disambiguation State Helpers} *)

  let with_bound_context_variable_opt state identifier_opt f =
    match identifier_opt with
    | Option.Some identifier ->
        with_bound_context_variable state identifier f
    | Option.None -> f state

  let with_bound_meta_variable_opt state identifier_opt f =
    match identifier_opt with
    | Option.Some identifier -> with_bound_meta_variable state identifier f
    | Option.None -> f state

  let with_bound_parameter_variable_opt state identifier_opt f =
    match identifier_opt with
    | Option.Some identifier ->
        with_bound_parameter_variable state identifier f
    | Option.None -> f state

  let with_bound_substitution_variable_opt state identifier_opt f =
    match identifier_opt with
    | Option.Some identifier ->
        with_bound_substitution_variable state identifier f
    | Option.None -> f state

  let with_parameter_binding_opt state identifier_opt modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        with_bound_context_variable_opt state identifier_opt
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        with_bound_meta_variable_opt state identifier_opt
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        with_bound_parameter_variable_opt state identifier_opt
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        with_bound_substitution_variable_opt state identifier_opt
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

  let with_computation_variable_opt state identifier_opt f =
    match identifier_opt with
    | Option.Some identifier ->
        with_bound_computation_variable state identifier f
    | Option.None -> f state

  let rec with_function_parameters_list state parameters f =
    match parameters with
    | [] -> f state
    | (_location, x) :: xs ->
        with_computation_variable_opt state x (fun state ->
            with_function_parameters_list state xs f)

  let with_function_parameters_list1 state parameters f =
    let (List1.T ((_location, x), xs)) = parameters in
    with_computation_variable_opt state x (fun state ->
        with_function_parameters_list state xs f)

  let with_function_parameters = with_function_parameters_list1

  let with_meta_parameter state identifier_opt f =
    match identifier_opt with
    | Option.Some identifier, `Plain ->
        with_bound_contextual_variable state identifier f
    | Option.Some identifier, `Hash ->
        with_bound_parameter_variable state identifier f
    | Option.Some identifier, `Dollar ->
        with_bound_substitution_variable state identifier f
    | Option.None, _ -> f state

  let rec with_meta_function_parameters_list state parameters f =
    match parameters with
    | [] -> f state
    | (_location, x) :: xs ->
        with_meta_parameter state x (fun state ->
            with_meta_function_parameters_list state xs f)

  let with_meta_function_parameters_list1 state parameters f =
    let (List1.T ((_location, x), xs)) = parameters in
    with_meta_parameter state x (fun state ->
        with_meta_function_parameters_list state xs f)

  let with_meta_function_parameters = with_meta_function_parameters_list1

  let with_pattern_variables state ~pattern ~expression =
    with_free_variables_as_pattern_variables state ~pattern ~expression

  (** {1 Disambiguation} *)

  let rec disambiguate_comp_kind state = function
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
        Synext.Comp.Kind.Ctype { location }
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
        let parameter_typ' = disambiguate_meta_typ state parameter_typ in
        let body' =
          with_parameter_binding_opt state parameter_identifier modifier
            parameter_typ' (fun state -> disambiguate_comp_kind state body)
        in
        Synext.Comp.Kind.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_typ'
          ; plicity
          ; body = body'
          }
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; domain; range; orientation = `Forward } -> (
        let domain' = disambiguate_comp_typ state domain in
        let range' = disambiguate_comp_kind state range in
        match domain' with
        | Synext.Comp.Typ.Box { meta_type; _ } ->
            Synext.Comp.Kind.Arrow
              { location; domain = meta_type; range = range' }
        | Synext.Comp.Typ.Inductive_typ_constant _
        | Synext.Comp.Typ.Stratified_typ_constant _
        | Synext.Comp.Typ.Coinductive_typ_constant _
        | Synext.Comp.Typ.Abbreviation_typ_constant _
        | Synext.Comp.Typ.Pi _
        | Synext.Comp.Typ.Arrow _
        | Synext.Comp.Typ.Cross _
        | Synext.Comp.Typ.Application _ ->
            Error.raise_at1
              (Synext.location_of_comp_typ domain')
              Illegal_comp_typ_domain_pi_comp_kind)

  and disambiguate_comp_typ state = function
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Error.raise_at1 location Illegal_ctype_comp_type
    | Synprs.Comp.Sort_object.Raw_pi
        { parameter_sort = Option.None; location; _ } ->
        Error.raise_at1 location Illegal_untyped_comp_pi_type
    | Synprs.Comp.Sort_object.Raw_identifier { location; identifier; _ } -> (
        (* As a computation-level type, plain identifiers are necessarily
           computation-level type constants *)
        match lookup_toplevel state identifier with
        | entry when Entry.is_computation_inductive_type_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Typ.Inductive_typ_constant
              { location; identifier = qualified_identifier }
        | entry when Entry.is_computation_stratified_type_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Typ.Stratified_typ_constant
              { location; identifier = qualified_identifier }
        | entry when Entry.is_computation_abbreviation_type_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Typ.Abbreviation_typ_constant
              { location; identifier = qualified_identifier }
        | entry when Entry.is_computation_coinductive_type_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Typ.Coinductive_typ_constant
              { location; identifier = qualified_identifier }
        | entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_comp_type_constant qualified_identifier)
                 (actual_binding_exn qualified_identifier entry))
        | exception Unbound_identifier _ ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Unbound_comp_type_constant qualified_identifier)
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Sort_object.Raw_qualified_identifier
        { location; identifier; _ } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As a computation-level type, identifiers of the form [<identifier>
           <dot-identifier>+] are necessarily computation-level type
           constants. *)
        match lookup state identifier with
        | entry when Entry.is_computation_inductive_type_constant entry ->
            Synext.Comp.Typ.Inductive_typ_constant { location; identifier }
        | entry when Entry.is_computation_stratified_type_constant entry ->
            Synext.Comp.Typ.Stratified_typ_constant { location; identifier }
        | entry when Entry.is_computation_abbreviation_type_constant entry ->
            Synext.Comp.Typ.Abbreviation_typ_constant
              { location; identifier }
        | entry when Entry.is_computation_coinductive_type_constant entry ->
            Synext.Comp.Typ.Coinductive_typ_constant { location; identifier }
        | entry ->
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_comp_type_constant identifier)
                 (actual_binding_exn identifier entry))
        | exception Unbound_qualified_identifier _ ->
            Error.raise_at1 location (Unbound_comp_type_constant identifier)
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Sort_object.Raw_pi
        { location
        ; parameter_identifier = parameter_identifier, modifier
        ; parameter_sort = Option.Some parameter_typ
        ; plicity
        ; body
        } ->
        let parameter_typ' = disambiguate_meta_typ state parameter_typ in
        let body' =
          with_parameter_binding_opt state parameter_identifier modifier
            parameter_typ' (fun state -> disambiguate_comp_typ state body)
        in
        Synext.Comp.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_typ'
          ; plicity
          ; body = body'
          }
    | Synprs.Comp.Sort_object.Raw_arrow
        { location; domain; range; orientation } ->
        let domain' = disambiguate_comp_typ state domain in
        let range' = disambiguate_comp_typ state range in
        Synext.Comp.Typ.Arrow
          { location; domain = domain'; range = range'; orientation }
    | Synprs.Comp.Sort_object.Raw_cross { location; operands } ->
        let types' = traverse_list2 state disambiguate_comp_typ operands in
        Synext.Comp.Typ.Cross { location; types = types' }
    | Synprs.Comp.Sort_object.Raw_box { location; boxed } ->
        let meta_type' = disambiguate_meta_typ state boxed in
        Synext.Comp.Typ.Box { location; meta_type = meta_type' }
    | Synprs.Comp.Sort_object.Raw_application { location; objects } ->
        let applicand, arguments =
          disambiguate_comp_typ_application state objects
        in
        let applicand' = disambiguate_comp_typ state applicand in
        let arguments' =
          traverse_list1 state elaborate_comp_typ_operand arguments
        in
        Synext.Comp.Typ.Application
          { applicand = applicand'; arguments = arguments'; location }

  and elaborate_comp_typ_operand state operand =
    match operand with
    | Comp_typ_application_disambiguation.Atom { expression; _ } -> (
        match expression with
        | Synprs.Comp.Sort_object.Raw_box { boxed; _ } ->
            disambiguate_meta_object state boxed
        | _ ->
            Error.raise_at1
              (Synprs.location_of_comp_sort_object expression)
              Expected_meta_object)
    | Comp_typ_application_disambiguation.Application { location; _ } ->
        Error.raise_at1 location Expected_meta_object

  and disambiguate_comp_typ_application state objects =
    let objects' = traverse_list2 state identify_typ_operator objects in
    Comp_typ_application_disambiguation.disambiguate_application objects'

  and disambiguate_comp_expression state = function
    | Synprs.Comp.Expression_object.Raw_identifier
        { location; identifier; _ } -> (
        match lookup_toplevel state identifier with
        | entry when Entry.is_computation_term_constructor entry ->
            (* [identifier] appears as a bound computation-level
               constructor *)
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Expression.Constructor
              { location; identifier = qualified_identifier }
        | entry when Entry.is_program_constant entry ->
            (* [identifier] appears as a bound computation-level program *)
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Expression.Program
              { location; identifier = qualified_identifier }
        | entry when Entry.is_computation_variable entry ->
            (* [identifier] appears as a bound computation-level variable *)
            Synext.Comp.Expression.Variable { location; identifier }
        | entry ->
            (* [identifier] appears as a bound entry that is not a
               computation-level variable, constructor or program constant *)
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_program_or_constructor_constant
                    qualified_identifier)
                 (actual_binding_exn qualified_identifier entry))
        | exception Unbound_identifier _ ->
            (* [identifier] does not appear in the state, so it is a free
               variable. *)
            Synext.Comp.Expression.Variable { location; identifier }
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { location; identifier; _ } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As a computation-level expression, identifiers of the form
           [<identifier> <dot-identifier>+] are computation-level variables
           or constants with optionally trailing observation constants.

           Examples include:

           - [List.nil] (constructor)

           - [Math.fact] (program)

           - [Stream.nil .tl .hd] (constructor with observations [.tl .hd])

           - [fibonacci .tl] (variable/program with observation [.tl]) *)
        match
          maximum_lookup state (Qualified_identifier.to_list1 identifier)
        with
        | Unbound { segments = List1.T (free_variable, rest) }
        (* A free computation-level variable with (possibly) trailing
           observations *) -> (
            let location = Identifier.location free_variable in
            let scrutinee =
              Synext.Comp.Expression.Variable
                { location; identifier = free_variable }
            in
            match rest with
            | [] -> scrutinee
            | x :: xs ->
                disambiguate_trailing_observations state scrutinee
                  (List1.from x xs))
        | Partially_bound
            { leading_segments = []
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_computation_variable entry
               (* A bound computation-level variable with trailing
                  observations *) ->
            let location = Identifier.location identifier in
            let scrutinee =
              Synext.Comp.Expression.Variable { location; identifier }
            in
            disambiguate_trailing_observations state scrutinee
              unbound_segments
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_computation_term_constructor entry
               (* [constant] forms a valid constructor constant *) ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            let location = Qualified_identifier.location constant in
            let scrutinee =
              Synext.Comp.Expression.Constructor
                { location; identifier = constant }
            in
            disambiguate_trailing_observations state scrutinee
              unbound_segments
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_program_constant entry
               (* [constant] forms a valid program constant *) ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            let location = Qualified_identifier.location constant in
            let scrutinee =
              Synext.Comp.Expression.Program
                { location; identifier = constant }
            in
            disambiguate_trailing_observations state scrutinee
              unbound_segments
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; entry
            ; _
            }
        (* [constant] forms an invalid constant *) ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_program_or_constructor_constant constant)
                 (actual_binding_exn constant entry))
        | Bound { entry } when Entry.is_computation_term_constructor entry ->
            Synext.Comp.Expression.Constructor { location; identifier }
        | Bound { entry } when Entry.is_program_constant entry ->
            Synext.Comp.Expression.Program { location; identifier }
        | Bound { entry } ->
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_program_or_constructor_constant identifier)
                 (actual_binding_exn identifier entry)))
    | Synprs.Comp.Expression_object.Raw_fn { location; parameters; body } ->
        let body' =
          with_function_parameters state parameters (fun state ->
              disambiguate_comp_expression state body)
        in
        Synext.Comp.Expression.Fn { location; parameters; body = body' }
    | Synprs.Comp.Expression_object.Raw_mlam { location; parameters; body }
      ->
        let body' =
          with_meta_function_parameters state parameters (fun state ->
              disambiguate_comp_expression state body)
        in
        Synext.Comp.Expression.Mlam { location; parameters; body = body' }
    | Synprs.Comp.Expression_object.Raw_fun { location; branches } ->
        let branches' = disambiguate_fun_branches state branches in
        Synext.Comp.Expression.Fun { location; branches = branches' }
    | Synprs.Comp.Expression_object.Raw_box { location; meta_object } ->
        let meta_object' = disambiguate_meta_object state meta_object in
        Synext.Comp.Expression.Box { location; meta_object = meta_object' }
    | Synprs.Comp.Expression_object.Raw_let
        { location; meta_context; pattern; scrutinee; body } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        with_pattern_variables state
          ~pattern:(fun state ->
            with_disambiguated_meta_context_pattern state meta_context
              (fun state meta_context' ->
                let pattern' = disambiguate_comp_pattern state pattern in
                (meta_context', pattern')))
          ~expression:(fun state (meta_context', pattern') ->
            let body' = disambiguate_comp_expression state body in
            Synext.Comp.Expression.Let
              { location
              ; meta_context = meta_context'
              ; pattern = pattern'
              ; scrutinee = scrutinee'
              ; body = body'
              })
    | Synprs.Comp.Expression_object.Raw_impossible { location; scrutinee } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        Synext.Comp.Expression.Impossible
          { location; scrutinee = scrutinee' }
    | Synprs.Comp.Expression_object.Raw_case
        { location; scrutinee; check_coverage; branches } ->
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        let branches' = disambiguate_case_branches state branches in
        Synext.Comp.Expression.Case
          { location
          ; scrutinee = scrutinee'
          ; check_coverage
          ; branches = branches'
          }
    | Synprs.Comp.Expression_object.Raw_tuple { location; elements } ->
        let elements' =
          traverse_list2 state disambiguate_comp_expression elements
        in
        Synext.Comp.Expression.Tuple { location; elements = elements' }
    | Synprs.Comp.Expression_object.Raw_hole { location; label } ->
        Synext.Comp.Expression.Hole { location; label }
    | Synprs.Comp.Expression_object.Raw_box_hole { location } ->
        Synext.Comp.Expression.Box_hole { location }
    | Synprs.Comp.Expression_object.Raw_application { location; expressions }
      ->
        (* We don't have to disambiguate the qualified identifiers in
           [objects] before we disambiguate applications. It is always the
           case that actual projections and actual observations that were
           parsed as qualified identifiers are not totally bound in the
           disambiguation state, so the application disambiguation identifies
           them as operands. *)
        let applicand, arguments =
          disambiguate_comp_expression_application state expressions
        in
        let applicand' = disambiguate_comp_expression state applicand in
        let arguments' =
          traverse_list1 state elaborate_comp_expression_operand arguments
        in
        Synext.Comp.Expression.Application
          { applicand = applicand'; arguments = arguments'; location }
    | Synprs.Comp.Expression_object.Raw_annotated
        { location; expression; typ } ->
        let expression' = disambiguate_comp_expression state expression in
        let typ' = disambiguate_comp_typ state typ in
        Synext.Comp.Expression.Type_annotated
          { location; expression = expression'; typ = typ' }
    | Synprs.Comp.Expression_object.Raw_observation
        { scrutinee; destructor; _ } ->
        (* Observations of variables or constants is handled in the
           disambiguation of qualified identifiers. *)
        let scrutinee' = disambiguate_comp_expression state scrutinee in
        disambiguate_trailing_observations state scrutinee'
          (Qualified_identifier.to_list1 destructor)

  and disambiguate_fun_branches state branches =
    traverse_list1 state
      (fun state (meta_context, copatterns, body) ->
        with_pattern_variables state
          ~pattern:(fun state ->
            with_disambiguated_meta_context_pattern state meta_context
              (fun state meta_context' ->
                let copattern' =
                  disambiguate_comp_copattern state copatterns
                in
                (meta_context', copattern')))
          ~expression:(fun state (meta_context', copattern') ->
            let body' = disambiguate_comp_expression state body in
            let location =
              Location.join
                (Synext.location_of_comp_copattern copattern')
                (Synext.location_of_comp_expression body')
            in
            { Synext.Comp.Cofunction_branch.location
            ; meta_context = meta_context'
            ; copattern = copattern'
            ; body = body'
            }))
      branches

  and disambiguate_case_branches state branches =
    traverse_list1 state
      (fun state (meta_context, pattern, body) ->
        with_pattern_variables state
          ~pattern:(fun state ->
            with_disambiguated_meta_context_pattern state meta_context
              (fun state meta_context' ->
                let pattern' = disambiguate_comp_pattern state pattern in
                (meta_context', pattern')))
          ~expression:(fun state (meta_context', pattern') ->
            let body' = disambiguate_comp_expression state body in
            let location =
              Location.join
                (Synext.location_of_comp_pattern pattern')
                (Synext.location_of_comp_expression body')
            in
            { Synext.Comp.Case_branch.location
            ; meta_context = meta_context'
            ; pattern = pattern'
            ; body = body'
            }))
      branches

  and disambiguate_trailing_observations state scrutinee trailing_identifiers
      =
    match maximum_lookup state trailing_identifiers with
    | Unbound _ ->
        let qualified_identifier =
          Qualified_identifier.from_list1 trailing_identifiers
        in
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Unbound_comp_term_destructor_constant qualified_identifier)
    | Partially_bound
        { leading_segments = bound_segments
        ; segment = identifier
        ; trailing_segments = unbound_segments
        ; entry
        ; _
        }
      when Entry.is_computation_term_destructor entry
           (* [constant] forms a destructor *) ->
        let constant =
          Qualified_identifier.make ~namespaces:bound_segments identifier
        in
        let destructor = constant in
        let location =
          Location.join
            (Synext.location_of_comp_expression scrutinee)
            (Qualified_identifier.location destructor)
        in
        let scrutinee' =
          Synext.Comp.Expression.Observation
            { scrutinee; destructor; location }
        in
        disambiguate_trailing_observations state scrutinee' unbound_segments
    | Partially_bound
        { leading_segments = bound_segments; segment = identifier; entry; _ }
    (* [constant] forms an invalid constant *) ->
        let constant =
          Qualified_identifier.make ~namespaces:bound_segments identifier
        in
        Error.raise_at1
          (Qualified_identifier.location constant)
          (Error.composite_exception2 Expected_comp_term_destructor_constant
             (actual_binding_exn constant entry))
    | Bound { entry }
      when Entry.is_computation_term_destructor entry
           (* [trailing_identifiers] forms a destructor *) ->
        let destructor =
          Qualified_identifier.from_list1 trailing_identifiers
        in
        let location =
          Location.join
            (Synext.location_of_comp_expression scrutinee)
            (Qualified_identifier.location destructor)
        in
        Synext.Comp.Expression.Observation
          { scrutinee; destructor; location }
    | Bound { entry } (* [trailing_identifiers] forms an invalid constant *)
      ->
        let identifier =
          Qualified_identifier.from_list1 trailing_identifiers
        in
        Error.raise_at1
          (Qualified_identifier.location identifier)
          (Error.composite_exception2 Expected_comp_term_destructor_constant
             (actual_binding_exn identifier entry))

  and disambiguate_comp_expression_application state objects =
    let objects' =
      traverse_list2 state identify_expression_operator objects
    in
    Comp_expression_application_disambiguation.disambiguate_application
      objects'

  and elaborate_comp_expression_operand state operand =
    match operand with
    | Comp_expression_application_disambiguation.Atom { expression; _ } ->
        disambiguate_comp_expression state expression
    | Comp_expression_application_disambiguation.Application
        { applicand; arguments; location } ->
        let applicand' = disambiguate_comp_expression state applicand in
        let arguments' =
          traverse_list1 state elaborate_comp_expression_operand arguments
        in
        Synext.Comp.Expression.Application
          { applicand = applicand'; arguments = arguments'; location }

  and disambiguate_comp_pattern state = function
    | Synprs.Comp.Pattern_object.Raw_identifier { location; identifier; _ }
      -> (
        match lookup_toplevel state identifier with
        | entry when Entry.is_computation_term_constructor entry ->
            (* [identifier] appears as a bound computation-level
               constructor *)
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.Comp.Pattern.Constructor
              { location; identifier = qualified_identifier }
        | _entry ->
            (* [identifier] appears as a bound entry that is not a
               computation-level constructor *)
            (* There are no computation-level patterns under
               [fn]-abstractions, so no need to check that [identifier] is
               not inner-bound. *)
            add_free_computation_variable state identifier;
            Synext.Comp.Pattern.Variable { location; identifier }
        | exception Unbound_identifier _ ->
            (* [identifier] does not appear in the state, so it is a free
               variable. *)
            add_free_computation_variable state identifier;
            Synext.Comp.Pattern.Variable { location; identifier }
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { location; identifier; _ } -> (
        match lookup state identifier with
        | entry when Entry.is_computation_term_constructor entry ->
            (* [identifier] appears as a bound computation-level
               constructor *)
            Synext.Comp.Pattern.Constructor { location; identifier }
        | entry ->
            (* [identifier] appears as a bound entry that is not a
               computation-level constructor *)
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_constructor_constant identifier)
                 (actual_binding_exn identifier entry))
        | exception Unbound_identifier _ ->
            Error.raise_at1 location
              (Unbound_comp_term_constructor_constant identifier)
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Pattern_object.Raw_box { location; pattern } ->
        let pattern' = disambiguate_meta_pattern state pattern in
        Synext.Comp.Pattern.Meta_object { location; meta_pattern = pattern' }
    | Synprs.Comp.Pattern_object.Raw_tuple { location; elements } ->
        let elements' =
          traverse_list2 state disambiguate_comp_pattern elements
        in
        Synext.Comp.Pattern.Tuple { location; elements = elements' }
    | Synprs.Comp.Pattern_object.Raw_application { location; patterns } ->
        (* We don't have to disambiguate the qualified identifiers in
           [objects] before we disambiguate applications. It is always the
           case that actual projections and actual observations that were
           parsed as qualified identifiers are not totally bound in the
           disambiguation state, so the application disambiguation identifies
           them as operands. *)
        let applicand, arguments =
          disambiguate_comp_pattern_application state patterns
        in
        let applicand' = disambiguate_comp_pattern state applicand in
        let arguments' =
          traverse_list1 state elaborate_comp_pattern_operand arguments
        in
        Synext.Comp.Pattern.Application
          { applicand = applicand'; arguments = arguments'; location }
    | Synprs.Comp.Pattern_object.Raw_annotated { location; pattern; typ } ->
        let pattern' = disambiguate_comp_pattern state pattern in
        let typ' = disambiguate_comp_typ state typ in
        Synext.Comp.Pattern.Type_annotated
          { location; pattern = pattern'; typ = typ' }
    | Synprs.Comp.Pattern_object.Raw_meta_annotated { location; _ } ->
        Error.raise_at1 location Illegal_inner_meta_annotated_comp_pattern
    | Synprs.Comp.Pattern_object.Raw_wildcard { location } ->
        Synext.Comp.Pattern.Wildcard { location }

  and disambiguate_comp_copattern state objects =
    let (List1.T (first, rest)) = objects in
    match first with
    | Synprs.Comp.Copattern_object.Raw_pattern
        { location
        ; pattern =
            Synprs.Comp.Pattern_object.Raw_qualified_identifier
              { identifier; prefixed = false; _ }
        } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* This raw qualified identifier [<identifier> <dot-identifier>+] may
           be a computation-level variable or constant pattern followed by
           observations *)
        let identifiers = Qualified_identifier.to_list1 identifier in
        match maximum_lookup state identifiers with
        | Unbound _ ->
            (* This is a variable pattern followed by observations *)
            let[@warning "-8"] (List1.T (variable, d :: ds)) = identifiers in
            let destructors = List1.from d ds in
            let pattern' =
              Synext.Comp.Pattern.Variable
                { location = Identifier.location variable
                ; identifier = variable
                }
            in
            add_free_computation_variable state variable;
            let destructors_as_qualified_identifier =
              Qualified_identifier.from_list1 destructors
            in
            let { Synext.Comp.Copattern.location = rest_location
                ; patterns
                ; observations
                } =
              disambiguate_comp_copattern state
                (List1.from
                   (Synprs.Comp.Copattern_object.Raw_observation
                      { location =
                          Qualified_identifier.location
                            destructors_as_qualified_identifier
                      ; observation = destructors_as_qualified_identifier
                      })
                   rest)
            in
            { Synext.Comp.Copattern.location =
                Location.join location rest_location
            ; patterns = pattern' :: patterns
            ; observations
            }
        | Partially_bound
            { leading_segments = []
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_computation_term_constructor entry ->
            (* This is a constructor pattern followed by observations *)
            let constructor = Qualified_identifier.make_simple identifier in
            let pattern' =
              Synext.Comp.Pattern.Constructor
                { location = Qualified_identifier.location constructor
                ; identifier = constructor
                }
            in
            let destructors_as_qualified_identifier =
              Qualified_identifier.from_list1 unbound_segments
            in
            let { Synext.Comp.Copattern.location = rest_location
                ; patterns
                ; observations
                } =
              disambiguate_comp_copattern state
                (List1.from
                   (Synprs.Comp.Copattern_object.Raw_observation
                      { location =
                          Qualified_identifier.location
                            destructors_as_qualified_identifier
                      ; observation = destructors_as_qualified_identifier
                      })
                   rest)
            in
            { Synext.Comp.Copattern.location =
                Location.join location rest_location
            ; patterns = pattern' :: patterns
            ; observations
            }
        | Partially_bound
            { leading_segments = []; segment = identifier; entry; _ }
          when Entry.is_variable entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_constructor_constant qualified_identifier)
                 (actual_binding_exn qualified_identifier entry))
        | Partially_bound
            { leading_segments = []
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; _
            } ->
            (* This is a variable pattern followed by observations *)
            let pattern' =
              Synext.Comp.Pattern.Variable
                { location = Identifier.location identifier; identifier }
            in
            add_free_computation_variable state identifier;
            let destructors_as_qualified_identifier =
              Qualified_identifier.from_list1 unbound_segments
            in
            let { Synext.Comp.Copattern.location = rest_location
                ; patterns
                ; observations
                } =
              disambiguate_comp_copattern state
                (List1.from
                   (Synprs.Comp.Copattern_object.Raw_observation
                      { location =
                          Qualified_identifier.location
                            destructors_as_qualified_identifier
                      ; observation = destructors_as_qualified_identifier
                      })
                   rest)
            in
            { Synext.Comp.Copattern.location =
                Location.join location rest_location
            ; patterns = pattern' :: patterns
            ; observations
            }
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_computation_term_constructor entry ->
            (* This is a constructor pattern followed by observations *)
            let constructor =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            let pattern' =
              Synext.Comp.Pattern.Constructor
                { location = Qualified_identifier.location constructor
                ; identifier = constructor
                }
            in
            let destructors_as_qualified_identifier =
              Qualified_identifier.from_list1 unbound_segments
            in
            let { Synext.Comp.Copattern.location = rest_location
                ; patterns
                ; observations
                } =
              disambiguate_comp_copattern state
                (List1.from
                   (Synprs.Comp.Copattern_object.Raw_observation
                      { location =
                          Qualified_identifier.location
                            destructors_as_qualified_identifier
                      ; observation = destructors_as_qualified_identifier
                      })
                   rest)
            in
            { Synext.Comp.Copattern.location =
                Location.join location rest_location
            ; patterns = pattern' :: patterns
            ; observations
            }
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; entry
            ; _
            } ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Error.composite_exception2
                 Expected_comp_term_destructor_constant
                 (actual_binding_exn constant entry))
        | Bound { entry } when Entry.is_computation_term_constructor entry
          -> (
            (* This qualified identifier is a constructor pattern *)
            let constructor = Qualified_identifier.from_list1 identifiers in
            let pattern' =
              Synext.Comp.Pattern.Constructor
                { location = Qualified_identifier.location constructor
                ; identifier = constructor
                }
            in
            match rest with
            | [] ->
                (* The constructor pattern is not followed by copatterns *)
                { Synext.Comp.Copattern.location
                ; patterns = [ pattern' ]
                ; observations = []
                }
            | x :: xs ->
                (* The constructor pattern is followed by copatterns *)
                let { Synext.Comp.Copattern.location = rest_location
                    ; patterns
                    ; observations
                    } =
                  disambiguate_comp_copattern state (List1.from x xs)
                in
                { Synext.Comp.Copattern.location =
                    Location.join location rest_location
                ; patterns = pattern' :: patterns
                ; observations
                })
        | Bound { entry } ->
            let constructor = Qualified_identifier.from_list1 identifiers in
            Error.raise_at1
              (Qualified_identifier.location constructor)
              (Error.composite_exception2
                 Expected_comp_term_destructor_constant
                 (actual_binding_exn constructor entry)))
    | Synprs.Comp.Copattern_object.Raw_observation { location; observation }
      -> (
        (* This raw observation may be multiple observations *)
        let destructors =
          disambiguate_destructors state
            (Qualified_identifier.to_list1 observation)
        in
        match rest with
        | [] ->
            (* The copattern ended with observations without arguments *)
            let observations =
              List.map
                (fun destructor -> (destructor, []))
                (List1.to_list destructors)
            in
            { Synext.Comp.Copattern.location; patterns = []; observations }
        | x :: xs ->
            (* There may be arguments to attach to the last observation in
               [destructors] *)
            let first_destructors, last_destructor =
              List1.unsnoc destructors
            in
            let first_observations =
              List.map (fun destructor -> (destructor, [])) first_destructors
            in
            let last_observations =
              disambiguate_trailing_observation_copatterns state
                last_destructor (List1.from x xs)
            in
            { Synext.Comp.Copattern.location
            ; patterns = []
            ; observations =
                first_observations @ List1.to_list last_observations
            })
    | Synprs.Comp.Copattern_object.Raw_pattern
        { location = pattern_location; pattern } -> (
        let pattern' = disambiguate_comp_pattern state pattern in
        match rest with
        | [] ->
            (* The copattern does not have observations *)
            { Synext.Comp.Copattern.location = pattern_location
            ; patterns = [ pattern' ]
            ; observations = []
            }
        | x :: xs ->
            (* The copattern may have observations *)
            let { Synext.Comp.Copattern.location; patterns; observations } =
              disambiguate_comp_copattern state (List1.from x xs)
            in
            { Synext.Comp.Copattern.location =
                Location.join pattern_location location
            ; patterns = pattern' :: patterns
            ; observations
            })

  and disambiguate_destructors state identifiers =
    match maximum_lookup state identifiers with
    | Unbound _ ->
        let qualified_identifier =
          Qualified_identifier.from_list1 identifiers
        in
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Unbound_comp_term_destructor_constant qualified_identifier)
    | Partially_bound
        { leading_segments = bound_segments
        ; segment = identifier
        ; trailing_segments = unbound_segments
        ; entry
        ; _
        }
      when Entry.is_computation_term_destructor entry
           (* [bound_segments] forms a destructor *) ->
        let destructor =
          Qualified_identifier.make ~namespaces:bound_segments identifier
        in
        let destructors = disambiguate_destructors state unbound_segments in
        List1.cons destructor destructors
    | Partially_bound
        { leading_segments = bound_segments; segment = identifier; entry; _ }
    (* [bound_segments] forms an invalid constant *) ->
        let constant =
          Qualified_identifier.make ~namespaces:bound_segments identifier
        in
        Error.raise_at1
          (Qualified_identifier.location constant)
          (Error.composite_exception2 Expected_comp_term_destructor_constant
             (actual_binding_exn constant entry))
    | Bound { entry }
      when Entry.is_computation_term_destructor entry
           (* [bound_segments] forms a destructor *) ->
        List1.singleton (Qualified_identifier.from_list1 identifiers)
    | Bound { entry } (* [bound_segments] forms an invalid constant *) ->
        let identifier = Qualified_identifier.from_list1 identifiers in
        Error.raise_at1
          (Qualified_identifier.location identifier)
          (Error.composite_exception2 Expected_comp_term_destructor_constant
             (actual_binding_exn identifier entry))

  and disambiguate_trailing_observation_copatterns state destructor objects =
    (* [destructor] appears before [objects], so patterns in [objects] are
       arguments to [destructor] *)
    let { Synext.Comp.Copattern.patterns; observations; _ } =
      disambiguate_comp_copattern state objects
    in
    List1.from (destructor, patterns) observations

  and disambiguate_comp_pattern_application state objects =
    let objects' = traverse_list2 state identify_pattern_operator objects in
    Comp_pattern_application_disambiguation.disambiguate_application objects'

  and elaborate_comp_pattern_operand state operand =
    match operand with
    | Comp_pattern_application_disambiguation.Atom { expression; _ } ->
        disambiguate_comp_pattern state expression
    | Comp_pattern_application_disambiguation.Application
        { applicand; arguments; location } ->
        let applicand' = disambiguate_comp_pattern state applicand in
        let arguments' =
          traverse_list1 state elaborate_comp_pattern_operand arguments
        in
        Synext.Comp.Pattern.Application
          { applicand = applicand'; arguments = arguments'; location }

  and with_disambiguated_comp_context state context_object f =
    let { Synprs.Comp.Context_object.location; bindings } = context_object in
    (* Computation contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves. *)
    with_disambiguated_context_bindings_list state bindings
      (fun state bindings' ->
        f state { Synext.Comp.Context.location; bindings = bindings' })

  and with_disambiguated_context_binding state binding f =
    match binding with
    | identifier, Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Illegal_missing_comp_context_binding_type identifier)
    | identifier, Option.Some typ ->
        let typ' = disambiguate_comp_typ state typ in
        with_bound_computation_variable state identifier (fun state ->
            f state (identifier, typ'))

  and with_disambiguated_context_bindings_list state bindings f =
    match bindings with
    | [] -> f state []
    | x :: xs ->
        with_disambiguated_context_binding state x (fun state y ->
            with_disambiguated_context_bindings_list state xs
              (fun state ys -> f state (y :: ys)))
end
