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

(** {2 Exceptions for contextual LF type disambiguation} *)

exception Illegal_hole_clf_type

exception Illegal_lambda_clf_type

exception Illegal_annotated_clf_type

exception Illegal_untyped_pi_clf_type

exception Illegal_tuple_clf_type

exception Illegal_projection_clf_type

exception Illegal_substitution_clf_type

exception Illegal_unnamed_block_element_clf_type

exception Illegal_parameter_variable_clf_type

exception Illegal_substitution_variable_clf_type

exception Unbound_clf_type_constant of Qualified_identifier.t

exception Expected_clf_type_constant

exception
  Unbound_type_constant_or_illegal_projection_clf_type of
    Qualified_identifier.t

(** {2 Exceptions for contextual LF term disambiguation} *)

exception Illegal_pi_clf_term

exception Illegal_forward_arrow_clf_term

exception Illegal_backward_arrow_clf_term

exception Illegal_block_clf_term

exception Illegal_clf_term_projection

exception Illegal_substitution_variable

exception Expected_clf_term_constant

exception Expected_parameter_variable

(** {2 Exceptions for contextual LF substitution disambiguation} *)

exception Illegal_clf_subtitution_term_label

exception Expected_substitution_variable

(** {2 Exceptions for contextual LF context disambiguation} *)

exception Illegal_clf_context_parameter_variable_binding

exception Illegal_clf_context_substitution_variable_binding

exception Illegal_clf_context_missing_binding_identifier

exception Illegal_clf_context_identity

exception Expected_context_variable

(** {2 Exceptions for contextual LF term pattern disambiguation} *)

exception Illegal_pi_clf_term_pattern

exception Illegal_forward_arrow_clf_term_pattern

exception Illegal_backward_arrow_clf_term_pattern

exception Illegal_block_clf_term_pattern

exception Illegal_labellable_hole_term_pattern

(** {2 Exceptions for contextual LF substitution pattern disambiguation} *)

exception Illegal_subtitution_clf_pattern_term_label

(** {2 Exceptions for contextual LF context pattern disambiguation} *)

exception Illegal_clf_context_pattern_missing_binding_type

exception Illegal_clf_context_pattern_parameter_variable_binding

exception Illegal_clf_context_pattern_substitution_variable_binding

exception Illegal_clf_context_pattern_missing_binding_identifier

exception Illegal_clf_context_pattern_identity

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Illegal_hole_clf_type ->
        Format.dprintf "Holes may not appear as contextual LF types."
    | Illegal_lambda_clf_type ->
        Format.dprintf "Lambdas may not appear as contextual LF types."
    | Illegal_annotated_clf_type ->
        Format.dprintf
          "Type ascriptions to terms may not appear as contextual LF types."
    | Illegal_untyped_pi_clf_type ->
        Format.dprintf
          "The contextual LF Pi type is missing its parameter type \
           annotation."
    | Illegal_tuple_clf_type ->
        Format.dprintf "Tuple terms may not appear as contextual LF types."
    | Illegal_projection_clf_type ->
        Format.dprintf
          "Projection terms may not appear as contextual LF types."
    | Illegal_substitution_clf_type ->
        Format.dprintf
          "Substitution terms may not appear as contextual LF types."
    | Illegal_unnamed_block_element_clf_type ->
        Format.dprintf
          "Contextual LF block type element missing an identifier."
    | Illegal_parameter_variable_clf_type ->
        Format.dprintf
          "Parameter variables may not appear as contextual LF types."
    | Illegal_substitution_variable_clf_type ->
        Format.dprintf
          "Substitution variables may not appear as contextual LF types."
    | Unbound_clf_type_constant identifier ->
        Format.dprintf "The LF type-level constant %a is unbound."
          Qualified_identifier.pp identifier
    | Expected_clf_type_constant ->
        Format.dprintf "Expected a LF type-level constant."
    | Unbound_type_constant_or_illegal_projection_clf_type identifier ->
        Format.dprintf
          "Either the LF type-level constant %a is unbound, or a projection \
           term may not appear as a contextual LF type."
          Qualified_identifier.pp identifier
    | Illegal_pi_clf_term ->
        Format.dprintf
          "Pi kinds or types may not appear as contextual LF terms."
    | Illegal_forward_arrow_clf_term ->
        Format.dprintf
          "Forward arrows may not appear as contextual LF terms."
    | Illegal_backward_arrow_clf_term ->
        Format.dprintf
          "Backward arrows may not appear as contextual LF terms."
    | Illegal_block_clf_term ->
        Format.dprintf "Block types may not appear as contextual LF terms."
    | Illegal_clf_term_projection ->
        Format.dprintf "Illegal contextual LF projection head."
    | Illegal_substitution_variable ->
        Format.dprintf
          "This substitution variable is illegal since it is not in a \
           substitution."
    | Expected_parameter_variable ->
        Format.dprintf "Expected a parameter variable."
    | Illegal_clf_subtitution_term_label ->
        Format.dprintf "Terms in a substitution may not be labelled."
    | Expected_substitution_variable ->
        Format.dprintf "Expected a substitution variable."
    | Illegal_clf_context_parameter_variable_binding ->
        Format.dprintf
          "Parameter variable bindings may not occur in contextual LF \
           contexts."
    | Illegal_clf_context_substitution_variable_binding ->
        Format.dprintf
          "Substitution variable bindings may not occur in contextual LF \
           contexts."
    | Illegal_clf_context_missing_binding_identifier ->
        Format.dprintf
          "Identifier missing for the binding in the contextual LF context."
    | Illegal_clf_context_identity ->
        Format.dprintf
          "Contextual LF contexts may not begin with the identity \
           substitution."
    | Expected_context_variable ->
        Format.dprintf "Expected a context variable."
    | Expected_clf_term_constant ->
        Format.dprintf "Expected an LF term-level constant."
    | Illegal_pi_clf_term_pattern ->
        Format.dprintf
          "Pi kinds or types may not appear as contextual LF term patterns."
    | Illegal_forward_arrow_clf_term_pattern ->
        Format.dprintf
          "Forward arrow types may not appear as contextual LF term \
           patterns."
    | Illegal_backward_arrow_clf_term_pattern ->
        Format.dprintf
          "Backward arrow types may not appear as contextual LF term \
           patterns."
    | Illegal_block_clf_term_pattern ->
        Format.dprintf
          "Block types may not appear as contextual LF term patterns."
    | Illegal_labellable_hole_term_pattern ->
        Format.dprintf
          "Labellable holes may not appear as contextual LF term patterns."
    | Illegal_subtitution_clf_pattern_term_label ->
        Format.dprintf "Terms in a substitution pattern may not be labelled."
    | Illegal_clf_context_pattern_missing_binding_type ->
        Format.dprintf
          "Contextual LF context pattern bindings require type annotations."
    | Illegal_clf_context_pattern_parameter_variable_binding ->
        Format.dprintf
          "Parameter variable bindings may not occur in contextual LF \
           context patterns."
    | Illegal_clf_context_pattern_substitution_variable_binding ->
        Format.dprintf
          "Substitution variable bindings may not occur in contextual LF \
           context patterns."
    | Illegal_clf_context_pattern_missing_binding_identifier ->
        Format.dprintf
          "Identifier missing for the binding in the contextual LF context \
           pattern."
    | Illegal_clf_context_pattern_identity ->
        Format.dprintf
          "Contextual LF context patterns may not begin with the identity \
           substitution."
    | exn -> Error.raise_unsupported_exception_printing exn)

(** {1 Disambiguation} *)

module type CLF_DISAMBIGUATION = sig
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_clf_typ : state -> Synprs.clf_object -> Synext.clf_typ

  val disambiguate_clf_term : state -> Synprs.clf_object -> Synext.clf_term

  val disambiguate_clf_substitution :
    state -> Synprs.clf_context_object -> Synext.clf_substitution

  val with_disambiguated_clf_context :
       state
    -> Synprs.clf_context_object
    -> (state -> Synext.clf_context -> 'a)
    -> 'a

  val disambiguate_clf_term_pattern :
    state -> Synprs.clf_object -> Synext.clf_term_pattern

  val disambiguate_clf_substitution_pattern :
    state -> Synprs.clf_context_object -> Synext.clf_substitution_pattern

  val with_disambiguated_clf_context_pattern :
       state
    -> Synprs.clf_context_object
    -> (state -> Synext.clf_context_pattern -> 'a)
    -> 'a

  val disambiguate_clf_context_pattern :
    state -> Synprs.clf_context_object -> Synext.clf_context_pattern
end

(** Disambiguation of contextual LF types, terms and patterns from the parser
    syntax to the external syntax.

    This disambiguation does not perform normalization nor validation. *)
module Make
    (Disambiguation_state : Disambiguation_state.DISAMBIGUATION_STATE) :
  CLF_DISAMBIGUATION with type state = Disambiguation_state.state = struct
  include Disambiguation_state

  (** {1 Disambiguation} *)

  module Clf_object = struct
    type t = Synprs.clf_object

    type location = Location.t

    let location = Synprs.location_of_clf_object
  end

  module Clf_application_disambiguation =
    Application_disambiguation.Make_application_disambiguation (Clf_object)

  let identify_operator_identifier state expression identifier =
    match lookup_operator state identifier with
    | Option.None ->
        Clf_application_disambiguation.make_expression expression
    | Option.Some operator ->
        Clf_application_disambiguation.make_operator expression operator
          identifier

  let identify_operator state expression =
    match expression with
    | Synprs.CLF.Object.Raw_qualified_identifier
        { identifier; prefixed = false; _ } ->
        identify_operator_identifier state expression identifier
    | Synprs.CLF.Object.Raw_identifier
        { identifier = identifier, `Plain; prefixed = false; _ } ->
        identify_operator_identifier state expression
          (Qualified_identifier.make_simple identifier)
    | _ -> Clf_application_disambiguation.make_expression expression

  let[@inline] with_bound_lf_variable_opt state identifier_opt f =
    match identifier_opt with
    | Option.None -> f state
    | Option.Some identifier -> with_bound_lf_variable state identifier f

  let rec disambiguate_clf_typ state = function
    | Synprs.CLF.Object.Raw_hole { location; _ } ->
        Error.raise_at1 location Illegal_hole_clf_type
    | Synprs.CLF.Object.Raw_lambda { location; _ } ->
        Error.raise_at1 location Illegal_lambda_clf_type
    | Synprs.CLF.Object.Raw_annotated { location; _ } ->
        Error.raise_at1 location Illegal_annotated_clf_type
    | Synprs.CLF.Object.Raw_pi { location; parameter_sort = Option.None; _ }
      ->
        Error.raise_at1 location Illegal_untyped_pi_clf_type
    | Synprs.CLF.Object.Raw_tuple { location; _ } ->
        Error.raise_at1 location Illegal_tuple_clf_type
    | Synprs.CLF.Object.Raw_projection { location; _ } ->
        Error.raise_at1 location Illegal_projection_clf_type
    | Synprs.CLF.Object.Raw_substitution { location; _ } ->
        Error.raise_at1 location Illegal_substitution_clf_type
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Hash; _ } ->
        Error.raise_at1 location Illegal_parameter_variable_clf_type
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Dollar; _ } ->
        Error.raise_at1 location Illegal_substitution_variable_clf_type
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; _ } -> (
        (* As an LF type, plain identifiers are necessarily type-level
           constants. *)
        match lookup_toplevel state identifier with
        | entry when Entry.is_lf_type_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.CLF.Typ.Constant
              { location; identifier = qualified_identifier }
        | entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_type_constant
                 (actual_binding_exn qualified_identifier entry))
        | exception Unbound_identifier _ ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Unbound_clf_type_constant qualified_identifier)
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier { location; identifier; _ }
      -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers. *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As an LF type, identifiers of the form [<identifier>
           <dot-identifier>+] are type-level constants, or illegal named
           projections. *)
        match lookup state identifier with
        | entry when Entry.is_lf_type_constant entry ->
            Synext.CLF.Typ.Constant { location; identifier }
        | entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_type_constant
                 (actual_binding_exn identifier entry))
        | exception Unbound_qualified_identifier _ ->
            Error.raise_at1 location
              (Unbound_type_constant_or_illegal_projection_clf_type
                 identifier)
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_arrow { location; domain; range; orientation } ->
        let domain' = disambiguate_clf_typ state domain in
        let range' = disambiguate_clf_typ state range in
        Synext.CLF.Typ.Arrow
          { location; domain = domain'; range = range'; orientation }
    | Synprs.CLF.Object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; plicity
        ; body
        } ->
        let parameter_type' = disambiguate_clf_typ state parameter_type in
        let body' =
          match parameter_identifier with
          | Option.None -> disambiguate_clf_typ state body
          | Option.Some parameter_identifier ->
              with_bound_lf_variable state parameter_identifier (fun state ->
                  disambiguate_clf_typ state body)
        in
        Synext.CLF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; plicity
          ; body = body'
          }
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        (* We don't have to disambiguate the qualified identifiers in
           [objects] before we disambiguate applications. It is always the
           case that actual projections that were parsed as qualified
           identifiers are not totally bound in the disambiguation state, so
           the application disambiguation identifies them as operands. *)
        let applicand, arguments =
          disambiguate_clf_application state objects
        in
        let applicand' = disambiguate_clf_typ state applicand in
        let arguments' =
          traverse_list1 state elaborate_clf_operand arguments
        in
        Synext.CLF.Typ.Application
          { applicand = applicand'; arguments = arguments'; location }
    | Synprs.CLF.Object.Raw_block
        { location; elements = List1.T ((Option.None, typ), []) } ->
        let typ' = disambiguate_clf_typ state typ in
        Synext.CLF.Typ.Block { location; elements = `Unnamed typ' }
    | Synprs.CLF.Object.Raw_block { location; elements } ->
        let bindings =
          List1.map
            (function
              | Option.None, typ ->
                  Error.raise_at1
                    (Synprs.location_of_clf_object typ)
                    Illegal_unnamed_block_element_clf_type
              | Option.Some identifier, typ -> (identifier, typ))
            elements
        in
        let elements' =
          disambiguate_binding_list1_as_clf_dependent_types state bindings
        in
        Synext.CLF.Typ.Block { location; elements = `Record elements' }

  and disambiguate_binding_list_as_clf_dependent_types state = function
    | [] -> []
    | (identifier, typ) :: xs ->
        let typ' = disambiguate_clf_typ state typ in
        let ys =
          with_bound_lf_variable state identifier (fun state ->
              disambiguate_binding_list_as_clf_dependent_types state xs)
        in
        (identifier, typ') :: ys

  and disambiguate_binding_list1_as_clf_dependent_types state bindings =
    let (List1.T ((identifier, typ), xs)) = bindings in
    let typ' = disambiguate_clf_typ state typ in
    let ys =
      with_bound_lf_variable state identifier (fun state ->
          disambiguate_binding_list_as_clf_dependent_types state xs)
    in
    List1.from (identifier, typ') ys

  and disambiguate_clf_term state = function
    | Synprs.CLF.Object.Raw_pi { location; _ } ->
        Error.raise_at1 location Illegal_pi_clf_term
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        Error.raise_at1 location Illegal_forward_arrow_clf_term
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_clf_term
    | Synprs.CLF.Object.Raw_block { location; _ } ->
        Error.raise_at1 location Illegal_block_clf_term
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Hash; _ } -> (
        (* A possibly free parameter variable. *)
        match lookup_toplevel state identifier with
        | entry when Entry.is_parameter_variable entry ->
            Synext.CLF.Term.Parameter_variable { location; identifier }
        | entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2 Expected_parameter_variable
                 (actual_binding_exn qualified_identifier entry))
        | exception Unbound_identifier _ ->
            (* Free variable. *)
            add_free_parameter_variable state identifier;
            Synext.CLF.Term.Parameter_variable { location; identifier }
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Dollar; _ } ->
        Error.raise_at1 location Illegal_substitution_variable
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; _ } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        match lookup_toplevel state identifier with
        | entry when Entry.is_lf_term_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.CLF.Term.Constant
              { location; identifier = qualified_identifier }
        | entry when Entry.is_lf_variable entry ->
            (* LF-bound variable *)
            Synext.CLF.Term.Variable { location; identifier }
        | entry when Entry.is_meta_variable entry ->
            (* Bound meta-variable *)
            Synext.CLF.Term.Meta_variable { location; identifier }
        | entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn qualified_identifier entry))
        | exception Unbound_identifier _ ->
            (* Free variable. *)
            add_free_meta_variable state identifier;
            Synext.CLF.Term.Meta_variable { location; identifier }
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier { location; identifier; _ }
      -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As an LF term, identifiers of the form [<identifier>
           <dot-identifier>+] are either term-level constants, or named
           projections or a variable. *)
        let (* helper function *) reduce_projections base projections =
          List.fold_left
            (fun term projection_identifier ->
              let location =
                Location.join
                  (Synext.location_of_clf_term term)
                  (Identifier.location projection_identifier)
              in
              Synext.CLF.Term.Projection
                { location
                ; term
                ; projection = `By_identifier projection_identifier
                })
            base projections
        in
        (* At this point, we need to figure out which segments of the
           qualified identifier refer to a constant, an LF-bound variable, or
           a meta-variable, and which segments are named projections. *)
        match
          maximum_lookup state (Qualified_identifier.to_list1 identifier)
        with
        | Unbound { segments = List1.T (free_variable, projections) }
        (* Projections of a free variable. *) ->
            add_free_meta_variable state free_variable;
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = free_variable }
            in
            reduce_projections term projections
        | Partially_bound
            { leading_segments = []
            ; segment = variable_identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_lf_variable entry
               (* Projections of an LF-bound variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = variable_identifier }
            in
            reduce_projections term (List1.to_list unbound_segments)
        | Partially_bound
            { leading_segments = []
            ; segment = variable_identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_meta_variable entry
               (* Projections of a bound meta-variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Meta_variable
                { location; identifier = variable_identifier }
            in
            reduce_projections term (List1.to_list unbound_segments)
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_lf_term_constant entry
               (* Projections of a bound LF term constant. This is an error
                  case, but type-checking will provide a better error
                  message. *) ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            let location = Qualified_identifier.location constant in
            let term =
              Synext.CLF.Term.Constant { location; identifier = constant }
            in
            reduce_projections term (List1.to_list unbound_segments)
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; entry
            ; _
            }
        (* Invalid projection of some other bound constant *) ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2 Illegal_clf_term_projection
                 (actual_binding_exn constant entry))
        | Bound { entry }
          when Entry.is_lf_term_constant entry (* Bound LF term constant *)
          ->
            Synext.CLF.Term.Constant { identifier; location }
        | Bound { entry } (* Some other invalid bound constant *) ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn identifier entry)))
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        (* We don't have to disambiguate the qualified identifiers in
           [objects] before we disambiguate applications. It is always the
           case that actual projections that were parsed as qualified
           identifiers are not totally bound in the disambiguation state, so
           the application disambiguation identifies them as operands. *)
        let applicand, arguments =
          disambiguate_clf_application state objects
        in
        let applicand' = disambiguate_clf_term state applicand in
        let arguments' =
          traverse_list1 state elaborate_clf_operand arguments
        in
        Synext.CLF.Term.Application
          { applicand = applicand'; arguments = arguments'; location }
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } ->
        let parameter_type' =
          traverse_option state disambiguate_clf_typ parameter_sort
        in
        let body' =
          with_bound_lf_variable_opt state parameter_identifier (fun state ->
              disambiguate_clf_term state body)
        in
        Synext.CLF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
    | Synprs.CLF.Object.Raw_hole { location; variant } ->
        Synext.CLF.Term.Hole { location; variant }
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let terms' = traverse_list1 state disambiguate_clf_term elements in
        Synext.CLF.Term.Tuple { location; terms = terms' }
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let term' = disambiguate_clf_term state object_ in
        Synext.CLF.Term.Projection { location; term = term'; projection }
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let term' = disambiguate_clf_term state object_ in
        let substitution' =
          disambiguate_clf_substitution state substitution
        in
        Synext.CLF.Term.Substitution
          { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let term' = disambiguate_clf_term state object_ in
        let typ' = disambiguate_clf_typ state sort in
        Synext.CLF.Term.Type_annotated { location; term = term'; typ = typ' }

  (** [disambiguate_clf_substitution state substitution] disambiguates
      [substitution] as a contextual LF substitution. Substitutions were
      parsed as a context object, so we have to ensure that every element in
      [substitution] is untyped, and we must allow identifiers with the
      dollar modifier (substitution variable) in head position. *)
  and disambiguate_clf_substitution state substitution =
    let { Synprs.CLF.Context_object.location; head; objects } =
      substitution
    in
    let objects' =
      List.map
        (function
          | Option.None, object_ -> object_
          | Option.Some identifier, _object ->
              Error.raise_at1
                (Identifier.location identifier)
                Illegal_clf_subtitution_term_label)
        objects
    in
    match head with
    | Synprs.CLF.Context_object.Head.None { location = head_location }
    (* List of contextual LF objects *) ->
        let head', objects'' =
          match objects' with
          | Synprs.CLF.Object.Raw_substitution
              { object_ =
                  Synprs.CLF.Object.Raw_identifier
                    { location; identifier = identifier, `Dollar; _ }
              ; substitution = closure
              ; _
              } (* A substitution closure *)
            :: xs ->
              (match lookup_toplevel state identifier with
              | entry when Entry.is_substitution_variable entry -> ()
              | exception Unbound_identifier _ ->
                  add_free_substitution_variable state identifier
              | entry ->
                  Error.raise_at1 location
                    (Error.composite_exception2
                       Expected_substitution_variable
                       (actual_binding_exn
                          (Qualified_identifier.make_simple identifier)
                          entry))
              | exception cause -> Error.raise_at1 location cause);
              let closure' = disambiguate_clf_substitution state closure in
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              in
              (head', xs)
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              (match lookup_toplevel state identifier with
              | entry when Entry.is_substitution_variable entry -> ()
              | exception Unbound_identifier _ ->
                  add_free_substitution_variable state identifier
              | entry ->
                  Error.raise_at1 location
                    (Error.composite_exception2
                       Expected_substitution_variable
                       (actual_binding_exn
                          (Qualified_identifier.make_simple identifier)
                          entry))
              | exception cause -> Error.raise_at1 location cause);
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              in
              (head', xs)
          | objects' ->
              let head' =
                Synext.CLF.Substitution.Head.None
                  { location = head_location }
              in
              (head', objects')
        in
        let terms' = traverse_list state disambiguate_clf_term objects'' in
        { Synext.CLF.Substitution.location; head = head'; terms = terms' }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location }
    (* List of contextual LF objects, starting with the identity substitution
       [..] *) ->
        let terms' = traverse_list state disambiguate_clf_term objects' in
        let head' =
          Synext.CLF.Substitution.Head.Identity { location = head_location }
        in
        { Synext.CLF.Substitution.location; head = head'; terms = terms' }

  (** [with_disambiguated_context_bindings bindings f state] is
      [f bindings' state'] where [state'] is the disambiguation state derived
      from [state] with the addition of the variables in the domain of
      [bindings], and [bindings'] is the disambiguated context bindings.

      Context variables cannot occur in [bindings]. A context variable in the
      head position of a context is handled in
      {!with_disambiguated_clf_context}. *)
  and with_disambiguated_context_bindings_list state bindings f =
    (* Contextual LF contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    match bindings with
    | [] -> f state []
    | x :: xs ->
        with_disambiguated_context_binding state x (fun state y ->
            with_disambiguated_context_bindings_list state xs
              (fun state ys -> f state (y :: ys)))

  and with_disambiguated_context_binding state binding f =
    (* Contextual LF contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    match binding with
    | Option.Some identifier, typ (* Typed binding *) ->
        let typ' = disambiguate_clf_typ state typ in
        with_bound_lf_variable state identifier (fun state ->
            f state (identifier, Option.some typ'))
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Plain; _ } )
    (* Untyped contextual LF variable *) ->
        with_bound_lf_variable state identifier (fun state ->
            f state (identifier, Option.none))
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Hash; _ } )
    (* Parameter variables may only occur in meta-contexts *) ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_clf_context_parameter_variable_binding
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Dollar; _ } )
    (* Substitution variables may only occur in meta-contexts *) ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_clf_context_substitution_variable_binding
    | Option.None, typ (* Binding identifier missing *) ->
        Error.raise_at1
          (Synprs.location_of_clf_object typ)
          Illegal_clf_context_missing_binding_identifier

  (** [with_disambiguated_clf_context state context f] is [f state' context']
      where [state'] is derived from [state] with the addition of variables
      bound in [context]. After [f] is called, those bindings are removed. *)
  and with_disambiguated_clf_context state context f =
    let { Synprs.CLF.Context_object.location; head; objects } = context in
    match head with
    | Synprs.CLF.Context_object.Head.Identity { location } ->
        Error.raise_at1 location Illegal_clf_context_identity
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
        match objects with
        | ( Option.None
          , Synprs.CLF.Object.Raw_hole
              { variant = `Underscore; location = head_location } )
            (* Hole as context head *)
          :: xs ->
            let head' =
              Synext.CLF.Context.Head.Hole { location = head_location }
            in
            with_disambiguated_context_bindings_list state xs
              (fun state bindings' ->
                f state
                  { Synext.CLF.Context.location
                  ; head = head'
                  ; bindings = bindings'
                  })
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* A context variable as context head *)
          :: bindings -> (
            let identifier_location = Identifier.location identifier in
            let head' =
              Synext.CLF.Context.Head.Context_variable
                { identifier; location = identifier_location }
            in
            match lookup_toplevel state identifier with
            | entry when Entry.is_context_variable entry ->
                with_disambiguated_context_bindings_list state bindings
                  (fun state bindings' ->
                    f state
                      { Synext.CLF.Context.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | entry when Entry.is_variable entry ->
                Error.raise_at1 identifier_location
                  (Error.composite_exception2 Expected_context_variable
                     (actual_binding_exn
                        (Qualified_identifier.make_simple identifier)
                        entry))
            | _
            | (exception Unbound_identifier _) ->
                add_free_context_variable state identifier;
                with_disambiguated_context_bindings_list state bindings
                  (fun state bindings' ->
                    f state
                      { Synext.CLF.Context.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | exception cause -> Error.raise_at1 location cause)
        | objects ->
            (* Context is just a list of bindings without context
               variables *)
            let head' =
              Synext.CLF.Context.Head.None { location = head_location }
            in
            with_disambiguated_context_bindings_list state objects
              (fun state bindings' ->
                f state
                  { Synext.CLF.Context.location
                  ; head = head'
                  ; bindings = bindings'
                  }))

  and disambiguate_clf_application state objects =
    let objects' = traverse_list2 state identify_operator objects in
    Clf_application_disambiguation.disambiguate_application objects'

  and elaborate_clf_operand state operand =
    match operand with
    | Clf_application_disambiguation.Atom { expression; _ } ->
        disambiguate_clf_term state expression
    | Clf_application_disambiguation.Application
        { applicand; arguments; location } ->
        let applicand' = disambiguate_clf_term state applicand in
        let arguments' =
          traverse_list1 state elaborate_clf_operand arguments
        in
        Synext.CLF.Term.Application
          { applicand = applicand'; arguments = arguments'; location }

  and disambiguate_clf_term_pattern state object_ =
    match object_ with
    | Synprs.CLF.Object.Raw_pi { location; _ } ->
        Error.raise_at1 location Illegal_pi_clf_term_pattern
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        Error.raise_at1 location Illegal_forward_arrow_clf_term_pattern
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_clf_term_pattern
    | Synprs.CLF.Object.Raw_block { location; _ } ->
        Error.raise_at1 location Illegal_block_clf_term_pattern
    | Synprs.CLF.Object.Raw_hole
        { location; variant = `Unlabelled | `Labelled _ } ->
        Error.raise_at1 location Illegal_labellable_hole_term_pattern
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Hash; _ } -> (
        match lookup_toplevel state identifier with
        | entry when Entry.is_parameter_variable entry ->
            Synext.CLF.Term.Pattern.Parameter_variable
              { location; identifier }
        | entry when Entry.is_variable entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_parameter_variable
                 (actual_binding_exn
                    (Qualified_identifier.make_simple identifier)
                    entry))
        | _
        | (exception Unbound_identifier _) ->
            add_free_parameter_variable state identifier;
            Synext.CLF.Term.Pattern.Parameter_variable
              { location; identifier }
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Dollar; _ } ->
        Error.raise_at1 location Illegal_substitution_variable
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; _ } -> (
        (* As an LF term pattern, plain identifiers are either term-level
           constants, variables bound in the pattern, or new pattern
           variables. *)
        match lookup_toplevel state identifier with
        | entry when Entry.is_lf_term_constant entry ->
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Synext.CLF.Term.Pattern.Constant
              { location; identifier = qualified_identifier }
        | entry when Entry.is_lf_variable entry ->
            Synext.CLF.Term.Pattern.Variable { location; identifier }
        | entry when Entry.is_meta_variable entry ->
            Synext.CLF.Term.Pattern.Meta_variable { location; identifier }
        | entry when Entry.is_variable entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn
                    (Qualified_identifier.make_simple identifier)
                    entry))
        | _
        | (exception Unbound_identifier _) ->
            add_free_meta_variable state identifier;
            Synext.CLF.Term.Pattern.Meta_variable { location; identifier }
        | exception cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier { location; identifier; _ }
      -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As an LF term, identifiers of the form [<identifier>
           <dot-identifier>+] are either term-level constants, or named
           projections. *)
        let reduce_projections base projections =
          List.fold_left
            (fun term projection_identifier ->
              let location =
                Location.join
                  (Synext.location_of_clf_term_pattern term)
                  (Identifier.location projection_identifier)
              in
              Synext.CLF.Term.Pattern.Projection
                { location
                ; term
                ; projection = `By_identifier projection_identifier
                })
            base projections
        in
        match
          maximum_lookup state (Qualified_identifier.to_list1 identifier)
        with
        | Unbound { segments = List1.T (free_variable, projections) }
        (* Projections of a free variable *) ->
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = free_variable }
            in
            add_free_meta_variable state free_variable;
            reduce_projections term projections
        | Partially_bound
            { leading_segments = []
            ; segment = variable_identifier
            ; trailing_segments = unbound_segments
            ; entry
            }
          when Entry.is_lf_variable entry
               (* Projections of a bound variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = variable_identifier }
            in
            reduce_projections term (List1.to_list unbound_segments)
        | Partially_bound
            { leading_segments = []
            ; segment = variable_identifier
            ; trailing_segments = unbound_segments
            ; entry
            ; _
            }
          when Entry.is_meta_variable entry
               (* Projections of a bound variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = variable_identifier }
            in
            reduce_projections term (List1.to_list unbound_segments)
        | Partially_bound
            { leading_segments = []; segment = identifier; entry; _ } ->
            let identifier_location = Identifier.location identifier in
            let qualified_identifier =
              Qualified_identifier.make_simple identifier
            in
            Error.raise_at1 identifier_location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn qualified_identifier entry))
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; entry
            ; trailing_segments = unbound_segments
            }
          when Entry.is_lf_term_constant entry ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            let location = Qualified_identifier.location constant in
            let term =
              Synext.CLF.Term.Pattern.Constant
                { location; identifier = constant }
            in
            reduce_projections term (List1.to_list unbound_segments)
        | Partially_bound
            { leading_segments = bound_segments
            ; segment = identifier
            ; entry
            ; _
            } ->
            let constant =
              Qualified_identifier.make ~namespaces:bound_segments identifier
            in
            Error.raise_at1 location
              (Error.composite_exception2 Illegal_clf_term_projection
                 (actual_binding_exn constant entry))
        | Bound { entry } when Entry.is_lf_term_constant entry ->
            Synext.CLF.Term.Pattern.Constant { identifier; location }
        | Bound { entry } ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (Disambiguation_state.actual_binding_exn identifier entry)))
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let applicand, arguments =
          disambiguate_clf_application state objects
        in
        let applicand' = disambiguate_clf_term_pattern state applicand in
        let arguments' =
          traverse_list1 state elaborate_clf_operand_pattern arguments
        in
        Synext.CLF.Term.Pattern.Application
          { applicand = applicand'; arguments = arguments'; location }
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let parameter_type' =
          traverse_option state disambiguate_clf_typ parameter_sort
        in
        match parameter_identifier with
        | Option.None ->
            let body' = disambiguate_clf_term_pattern state body in
            Synext.CLF.Term.Pattern.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              }
        | Option.Some parameter_identifier' ->
            let body' =
              with_bound_lf_variable state parameter_identifier'
                (fun state -> disambiguate_clf_term_pattern state body)
            in
            Synext.CLF.Term.Pattern.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })
    | Synprs.CLF.Object.Raw_hole { location; variant = `Underscore } ->
        Synext.CLF.Term.Pattern.Wildcard { location }
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let terms' =
          traverse_list1 state disambiguate_clf_term_pattern elements
        in
        Synext.CLF.Term.Pattern.Tuple { location; terms = terms' }
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let term' = disambiguate_clf_term_pattern state object_ in
        Synext.CLF.Term.Pattern.Projection
          { location; term = term'; projection }
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let term' = disambiguate_clf_term_pattern state object_ in
        let substitution' =
          disambiguate_clf_substitution state substitution
        in
        Synext.CLF.Term.Pattern.Substitution
          { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let typ' = disambiguate_clf_typ state sort in
        let term' = disambiguate_clf_term_pattern state object_ in
        Synext.CLF.Term.Pattern.Type_annotated
          { location; term = term'; typ = typ' }

  and elaborate_clf_operand_pattern state operand =
    match operand with
    | Clf_application_disambiguation.Atom { expression; _ } ->
        disambiguate_clf_term_pattern state expression
    | Clf_application_disambiguation.Application
        { applicand; arguments; location } ->
        let applicand' = disambiguate_clf_term_pattern state applicand in
        let arguments' =
          traverse_list1 state elaborate_clf_operand_pattern arguments
        in
        Synext.CLF.Term.Pattern.Application
          { applicand = applicand'; arguments = arguments'; location }

  and disambiguate_clf_substitution_pattern state substitution_pattern =
    let { Synprs.CLF.Context_object.location; head; objects } =
      substitution_pattern
    in
    let objects' =
      List.map
        (function
          | Option.None, object_ -> object_
          | Option.Some identifier, _ ->
              Error.raise_at1
                (Identifier.location identifier)
                Illegal_subtitution_clf_pattern_term_label)
        objects
    in
    match head with
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
        match objects' with
        | Synprs.CLF.Object.Raw_substitution
            { object_ =
                Synprs.CLF.Object.Raw_identifier
                  { location = identifier_location
                  ; identifier = identifier, `Dollar
                  ; _
                  }
            ; substitution = closure
            ; location = substitution_location
            } (* A substitution closure *)
          :: xs -> (
            let closure' = disambiguate_clf_substitution state closure in
            let head' =
              Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                { location = substitution_location
                ; identifier
                ; closure = Option.some closure'
                }
            in
            let terms' =
              traverse_list state disambiguate_clf_term_pattern xs
            in
            let substitution' =
              { Synext.CLF.Substitution.Pattern.location
              ; head = head'
              ; terms = terms'
              }
            in
            match lookup_toplevel state identifier with
            | entry when Entry.is_substitution_variable entry ->
                substitution'
            | exception Unbound_identifier _ ->
                add_free_substitution_variable state identifier;
                substitution'
            | entry ->
                Error.raise_at1 identifier_location
                  (Error.composite_exception2 Expected_substitution_variable
                     (actual_binding_exn
                        (Qualified_identifier.make_simple identifier)
                        entry))
            | exception cause -> Error.raise_at1 identifier_location cause)
        | Synprs.CLF.Object.Raw_identifier
            { location = identifier_location
            ; identifier = identifier, `Dollar
            ; _
            } (* A substitution variable *)
          :: xs -> (
            let head' =
              Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                { location = identifier_location
                ; identifier
                ; closure = Option.none
                }
            in
            let terms' =
              traverse_list state disambiguate_clf_term_pattern xs
            in
            let substitution' =
              { Synext.CLF.Substitution.Pattern.location
              ; head = head'
              ; terms = terms'
              }
            in
            match lookup_toplevel state identifier with
            | entry when Entry.is_substitution_variable entry ->
                substitution'
            | exception Unbound_identifier _ ->
                add_free_substitution_variable state identifier;
                substitution'
            | entry ->
                Error.raise_at1 identifier_location
                  (Error.composite_exception2 Expected_substitution_variable
                     (actual_binding_exn
                        (Qualified_identifier.make_simple identifier)
                        entry))
            | exception cause -> Error.raise_at1 identifier_location cause)
        | objects' ->
            let head' =
              Synext.CLF.Substitution.Pattern.Head.None
                { location = head_location }
            in
            let terms' =
              traverse_list state disambiguate_clf_term_pattern objects'
            in
            { Synext.CLF.Substitution.Pattern.location
            ; head = head'
            ; terms = terms'
            })
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let head' =
          Synext.CLF.Substitution.Pattern.Head.Identity
            { location = head_location }
        in
        let terms' =
          traverse_list state disambiguate_clf_term_pattern objects'
        in
        { Synext.CLF.Substitution.Pattern.location
        ; head = head'
        ; terms = terms'
        }

  and with_disambiguated_context_pattern_binding :
        'a.
           state
        -> Identifier.t option * Synprs.clf_object
        -> (state -> Identifier.t * Synext.clf_typ -> 'a)
        -> 'a =
   fun state binding f ->
    match binding with
    | Option.Some identifier, typ ->
        let typ' = disambiguate_clf_typ state typ in
        with_bound_lf_variable state identifier (fun state ->
            f state (identifier, typ'))
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Plain; _ } ) ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_clf_context_pattern_missing_binding_type
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Hash; _ } ) ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_clf_context_pattern_parameter_variable_binding
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Dollar; _ } ) ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_clf_context_pattern_substitution_variable_binding
    | Option.None, typ ->
        Error.raise_at1
          (Synprs.location_of_clf_object typ)
          Illegal_clf_context_pattern_missing_binding_identifier

  and with_disambiguated_context_pattern_bindings_list :
        'a.
           state
        -> (Identifier.t option * Synprs.clf_object) list
        -> (state -> (Identifier.t * Synext.clf_typ) list -> 'a)
        -> 'a =
   fun state bindings f ->
    match bindings with
    | [] -> f state []
    | x :: xs ->
        with_disambiguated_context_pattern_binding state x (fun state y ->
            with_disambiguated_context_pattern_bindings_list state xs
              (fun state ys -> f state (y :: ys)))

  and with_disambiguated_clf_context_pattern :
        'a.
           state
        -> Synprs.clf_context_object
        -> (state -> Synext.clf_context_pattern -> 'a)
        -> 'a =
   fun state context_pattern f ->
    let { Synprs.CLF.Context_object.location; head; objects } =
      context_pattern
    in
    match head with
    | Synprs.CLF.Context_object.Head.Identity { location } ->
        Error.raise_at1 location Illegal_clf_context_pattern_identity
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
        match objects with
        | ( Option.None
          , Synprs.CLF.Object.Raw_hole
              { variant = `Underscore; location = head_location } )
            (* Hole as context head *)
          :: bindings ->
            let head' =
              Synext.CLF.Context.Pattern.Head.Hole
                { location = head_location }
            in
            with_disambiguated_context_pattern_bindings_list state bindings
              (fun state bindings' ->
                f state
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  })
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* A context variable as context head *)
          :: bindings -> (
            let identifier_location = Identifier.location identifier in
            let head' =
              Synext.CLF.Context.Pattern.Head.Context_variable
                { identifier; location = identifier_location }
            in
            match lookup_toplevel state identifier with
            | entry when Entry.is_context_variable entry ->
                with_disambiguated_context_pattern_bindings_list state
                  bindings (fun state bindings' ->
                    f state
                      { Synext.CLF.Context.Pattern.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | entry when Entry.is_variable entry ->
                Error.raise_at1 identifier_location
                  (Error.composite_exception2 Expected_context_variable
                     (actual_binding_exn
                        (Qualified_identifier.make_simple identifier)
                        entry))
            | _
            | (exception Unbound_identifier _) ->
                add_free_context_variable state identifier;
                with_disambiguated_context_pattern_bindings_list state
                  bindings (fun state bindings' ->
                    f state
                      { Synext.CLF.Context.Pattern.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | exception cause -> Error.raise_at1 location cause)
        | _ ->
            let head' =
              Synext.CLF.Context.Pattern.Head.None
                { location = head_location }
            in
            with_disambiguated_context_pattern_bindings_list state objects
              (fun state bindings' ->
                f state
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  }))

  and disambiguate_clf_context_pattern state context_pattern =
    with_disambiguated_clf_context_pattern state context_pattern
      (fun _state context_pattern' -> context_pattern')
end
