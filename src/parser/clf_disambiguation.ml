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
open Common_disambiguation

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

exception Unbound_clf_term_constant of Qualified_identifier.t

exception Illegal_clf_term_projection

exception Expected_clf_term_constant

exception Expected_parameter_variable

exception Expected_substitution_variable

(** {2 Exceptions for contextual LF substitution disambiguation} *)

exception Illegal_clf_subtitution_term_label

(** {2 Exceptions for contextual LF context disambiguation} *)

exception Illegal_clf_context_parameter_variable_binding

exception Illegal_clf_context_substitution_variable_binding

exception Illegal_clf_context_missing_binding_identifier

exception Illegal_clf_context_identity

(** {2 Exceptions for application rewriting} *)

exception Misplaced_clf_operator

exception Ambiguous_clf_operator_placement of Qualified_identifier.t

exception
  Consecutive_applications_of_non_associative_clf_operators of
    Qualified_identifier.t

exception
  Clf_arity_mismatch of
    { operator_identifier : Qualified_identifier.t
    ; expected_arguments_count : Int.t
    ; actual_arguments_count : Int.t
    }

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

(** {1 Disambiguation} *)

(** Contextual LF operands for application rewriting with
    {!module:Application_disambiguation.Make}. *)
module Clf_operand = struct
  type expression = Synprs.clf_object

  type t =
    | Atom of expression
    | Application of
        { applicand : expression
        ; arguments : t List1.t
        }

  let rec location operand =
    match operand with
    | Atom object_ -> Synprs.location_of_clf_object object_
    | Application { applicand; arguments } ->
        let applicand_location = Synprs.location_of_clf_object applicand in
        let arguments_location =
          Location.join_all1_contramap location arguments
        in
        Location.join applicand_location arguments_location
end

(** Contextual LF operators for application rewriting with
    {!module:Application_disambiguation.Make}. *)
module Clf_operator = struct
  type associativity = Associativity.t

  type fixity = Fixity.t

  type operand = Clf_operand.t

  type t =
    { identifier : Qualified_identifier.t
    ; operator : Operator.t
    ; applicand : Synprs.clf_object
    }

  let[@inline] make ~identifier ~operator ~applicand =
    { identifier; operator; applicand }

  let[@inline] operator o = o.operator

  let[@inline] applicand o = o.applicand

  let[@inline] identifier o = o.identifier

  let arity = Fun.(operator >> Operator.arity)

  let precedence = Fun.(operator >> Operator.precedence)

  let fixity = Fun.(operator >> Operator.fixity)

  let associativity = Fun.(operator >> Operator.associativity)

  let location = Fun.(applicand >> Synprs.location_of_clf_object)

  (** [write operator arguments] constructs the application of [operator]
      with [arguments] for the shunting yard algorithm. Since nullary
      operators are treated as arguments, it is always the case that
      [List.length arguments > 0]. *)
  let write operator arguments =
    let applicand = applicand operator in
    let arguments =
      List1.unsafe_of_list arguments (* [List.length arguments > 0] *)
    in
    Clf_operand.Application { applicand; arguments }

  (** Instance of equality by operator identifier.

      Since applications do not introduce bound variables, occurrences of
      operators are equal by their identifier. That is, in an application
      like [a o1 a o2 a], the operators [o1] and [o2] are equal if and only
      if they are textually equal. *)
  include (
    (val Eq.contramap (module Qualified_identifier) identifier) :
      Eq.EQ with type t := t)
end

(** Disambiguation state for contextual LF application rewriting with
    {!module:Application_disambiguation.Make}. *)
module Make_clf_application_disambiguation_state
    (Bindings_state : BINDINGS_STATE) :
  Application_disambiguation.APPLICATION_DISAMBIGUATION_STATE
    with type state = Bindings_state.state
     and type operator = Clf_operator.t
     and type expression = Synprs.clf_object = struct
  include Bindings_state

  type operator = Clf_operator.t

  type expression = Synprs.clf_object

  let guard_identifier_operator identifier expression =
    lookup identifier >>= function
    | Result.Ok (Lf_type_constant, { operator = Option.Some operator; _ })
    | Result.Ok (Lf_term_constant, { operator = Option.Some operator; _ }) ->
        if Operator.is_nullary operator then return Option.none
        else
          return
            (Option.some
               (Clf_operator.make ~identifier ~operator ~applicand:expression))
    | Result.Ok _
    | Result.Error (Unbound_identifier _) ->
        return Option.none
    | Result.Error cause ->
        Error.raise_at1 (Qualified_identifier.location identifier) cause

  let guard_operator expression =
    match expression with
    | Synprs.CLF.Object.Raw_identifier { quoted; _ }
    | Synprs.CLF.Object.Raw_qualified_identifier { quoted; _ }
      when quoted ->
        return Option.none
    | Synprs.CLF.Object.Raw_identifier { identifier = identifier, `Plain; _ }
      ->
        let identifier = Qualified_identifier.make_simple identifier in
        guard_identifier_operator identifier expression
    | Synprs.CLF.Object.Raw_qualified_identifier { identifier; _ } ->
        guard_identifier_operator identifier expression
    | Synprs.CLF.Object.Raw_identifier
        { identifier = _, (`Dollar | `Hash); _ }
    | Synprs.CLF.Object.Raw_hole _
    | Synprs.CLF.Object.Raw_pi _
    | Synprs.CLF.Object.Raw_lambda _
    | Synprs.CLF.Object.Raw_arrow _
    | Synprs.CLF.Object.Raw_annotated _
    | Synprs.CLF.Object.Raw_application _
    | Synprs.CLF.Object.Raw_block _
    | Synprs.CLF.Object.Raw_tuple _
    | Synprs.CLF.Object.Raw_projection _
    | Synprs.CLF.Object.Raw_substitution _ ->
        return Option.none
end

module type CLF_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_clf_typ : Synprs.clf_object -> Synext.clf_typ t

  val disambiguate_clf_term : Synprs.clf_object -> Synext.clf_term t

  val disambiguate_clf_substitution :
    Synprs.clf_context_object -> Synext.clf_substitution t

  val with_disambiguated_clf_context :
    Synprs.clf_context_object -> (Synext.clf_context -> 'a t) -> 'a t
end

module type CLF_PATTERN_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_clf_term_pattern :
    Synprs.clf_object -> Synext.clf_term_pattern t

  val disambiguate_clf_substitution_pattern :
    Synprs.clf_context_object -> Synext.clf_substitution_pattern t

  val with_disambiguated_clf_context_pattern :
    Synprs.clf_context_object -> (Synext.clf_context_pattern -> 'a t) -> 'a t

  val disambiguate_clf_context_pattern :
    Synprs.clf_context_object -> Synext.clf_context_pattern t
end

(** Disambiguation of contextual LF types, terms and patterns from the parser
    syntax to the external syntax.

    This disambiguation does not perform normalization nor validation. *)
module Make (Bindings_state : BINDINGS_STATE) :
  CLF_DISAMBIGUATION with type state = Bindings_state.state = struct
  include Bindings_state

  (** {1 Disambiguation} *)

  (** [disambiguate_clf_typ object_ state] is [object_] rewritten as a
      contextual LF type with respect to the disambiguation context [state].

      Type applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification. *)
  let rec disambiguate_clf_typ object_ =
    match object_ with
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
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF type, plain identifiers are necessarily type-level
           constants. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_type_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_type_constant
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            Error.raise_at1 location
              (Unbound_clf_type_constant qualified_identifier)
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers. *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As an LF type, identifiers of the form [<identifier>
           <dot-identifier>+] are type-level constants, or illegal named
           projections. *)
        lookup identifier >>= function
        | Result.Ok (Lf_type_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Typ.Constant
                 { location; identifier; operator; quoted })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_type_constant
                 (actual_binding_exn identifier entry))
        | Result.Error (Unbound_qualified_identifier _) ->
            Error.raise_at1 location
              (Unbound_type_constant_or_illegal_projection_clf_type
                 identifier)
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_arrow { location; domain; range; orientation } ->
        let* domain' = disambiguate_clf_typ domain in
        let* range' = disambiguate_clf_typ range in
        return
          (Synext.CLF.Typ.Arrow
             { location; domain = domain'; range = range'; orientation })
    | Synprs.CLF.Object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; plicity
        ; body
        } ->
        let* parameter_type' = disambiguate_clf_typ parameter_type in
        let* body' =
          match parameter_identifier with
          | Option.None -> disambiguate_clf_typ body
          | Option.Some parameter_identifier ->
              with_lf_term_variable parameter_identifier
                (disambiguate_clf_typ body)
        in
        return
          (Synext.CLF.Typ.Pi
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; plicity
             ; body = body'
             })
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let* applicand, arguments = disambiguate_clf_application objects in
        let* applicand' = disambiguate_clf_typ applicand in
        let* arguments' = traverse_list1 elaborate_lf_operand arguments in
        return
          (Synext.CLF.Typ.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.CLF.Object.Raw_block
        { location; elements = List1.T ((Option.None, typ), []) } ->
        let* typ' = disambiguate_clf_typ typ in
        return (Synext.CLF.Typ.Block { location; elements = `Unnamed typ' })
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
        let* elements' =
          disambiguate_binding_list1_as_clf_dependent_types bindings
        in
        return
          (Synext.CLF.Typ.Block { location; elements = `Record elements' })

  and disambiguate_binding_list_as_clf_dependent_types bindings =
    match bindings with
    | [] -> return []
    | (identifier, typ) :: xs ->
        let* typ' = disambiguate_clf_typ typ in
        let* ys =
          (with_lf_term_variable identifier)
            (disambiguate_binding_list_as_clf_dependent_types xs)
        in
        return ((identifier, typ') :: ys)

  and disambiguate_binding_list1_as_clf_dependent_types bindings =
    let (List1.T ((identifier, typ), xs)) = bindings in
    let* typ' = disambiguate_clf_typ typ in
    let* ys =
      (with_lf_term_variable identifier)
        (disambiguate_binding_list_as_clf_dependent_types xs)
    in
    return (List1.from (identifier, typ') ys)

  (** [disambiguate_clf_term object_ state] is [object_] rewritten as a
      contextual LF term with respect to the disambiguation context [state].

      Term applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification. *)
  and disambiguate_clf_term = function
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
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Parameter_variable, _) ->
            return
              (Synext.CLF.Term.Parameter_variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_parameter_variable
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            (* Free variable. *)
            return
              (Synext.CLF.Term.Parameter_variable { location; identifier })
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } -> (
        (* A possibly free substitution variable. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Substitution_variable, _) ->
            return
              (Synext.CLF.Term.Substitution_variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_substitution_variable
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            (* Free variable. *)
            return
              (Synext.CLF.Term.Substitution_variable { location; identifier })
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_term_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Term.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Result.Ok (Lf_term_variable, _)
        | Result.Ok (Meta_variable, _) ->
            (* Bound variable *)
            return (Synext.CLF.Term.Variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            (* Free variable. *)
            return (Synext.CLF.Term.Variable { location; identifier })
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
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
        partial_lookup identifier >>= function
        | `Totally_unbound (List1.T (free_variable, projections)) ->
            (* Projections of a free variable. *)
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = free_variable }
            in
            return (reduce_projections term projections)
        | `Partially_bound
            ( List1.T
                ( ( variable_identifier
                  , (Lf_term_variable, _ | Meta_variable, _) )
                , [] )
            , unbound_segments )
        (* Projections of a bound variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = variable_identifier }
            in
            return (reduce_projections term (List1.to_list unbound_segments))
        | `Partially_bound (List1.T (_, []), unbound_segments)
        | `Partially_bound (_, unbound_segments)
        (* Projections of a bound constant *) ->
            Error.raise_at1
              (Location.join_all1_contramap Identifier.location
                 unbound_segments)
              Illegal_clf_term_projection
        | `Totally_bound bound_segments (* A constant *) -> (
            match List1.last bound_segments with
            | ( _identifier
              , (Lf_term_constant, { operator = Option.Some operator; _ }) )
              ->
                return
                  (Synext.CLF.Term.Constant
                     { identifier; location; operator; quoted })
            | _identifier, entry ->
                Error.raise_at1 location
                  (Error.composite_exception2 Expected_clf_term_constant
                     (actual_binding_exn identifier entry))))
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let* applicand, arguments = disambiguate_clf_application objects in
        let* applicand' = disambiguate_clf_term applicand in
        let* arguments' = traverse_list1 elaborate_lf_operand arguments in
        return
          (Synext.CLF.Term.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } ->
        let* parameter_type' =
          traverse_option disambiguate_clf_typ parameter_sort
        in
        let* body' =
          match parameter_identifier with
          | Option.None -> disambiguate_clf_term body
          | Option.Some parameter_identifier ->
              with_lf_term_variable parameter_identifier
                (disambiguate_clf_term body)
        in
        return
          (Synext.CLF.Term.Abstraction
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; body = body'
             })
    | Synprs.CLF.Object.Raw_hole { location; variant } ->
        return (Synext.CLF.Term.Hole { location; variant })
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let* terms' = traverse_list1 disambiguate_clf_term elements in
        return (Synext.CLF.Term.Tuple { location; terms = terms' })
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let* term' = disambiguate_clf_term object_ in
        return
          (Synext.CLF.Term.Projection { location; term = term'; projection })
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let* term' = disambiguate_clf_term object_ in
        let* substitution' = disambiguate_clf_substitution substitution in
        return
          (Synext.CLF.Term.Substitution
             { location; term = term'; substitution = substitution' })
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let* term' = disambiguate_clf_term object_ in
        let* typ' = disambiguate_clf_typ sort in
        return
          (Synext.CLF.Term.Type_annotated
             { location; term = term'; typ = typ' })

  and disambiguate_clf_substitution substitution =
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
    | Synprs.CLF.Context_object.Head.None { location = head_location } ->
        let* head', objects'' =
          match objects' with
          | Synprs.CLF.Object.Raw_substitution
              { object_ =
                  Synprs.CLF.Object.Raw_identifier
                    { location; identifier = identifier, `Dollar; _ }
              ; substitution = closure
              ; _
              } (* A substitution closure *)
            :: xs ->
              let* closure' = disambiguate_clf_substitution closure in
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              in
              return (head', xs)
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              in
              return (head', xs)
          | objects' ->
              let head' =
                Synext.CLF.Substitution.Head.None
                  { location = head_location }
              in
              return (head', objects')
        in
        let* terms' = traverse_list disambiguate_clf_term objects'' in
        return
          { Synext.CLF.Substitution.location; head = head'; terms = terms' }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let* terms' = traverse_list disambiguate_clf_term objects' in
        let head' =
          Synext.CLF.Substitution.Head.Identity { location = head_location }
        in
        return
          { Synext.CLF.Substitution.location; head = head'; terms = terms' }

  (** [with_disambiguated_context_bindings bindings f state] is
      [f bindings' state'] where [state'] is the disambiguation state derived
      from [state] with the addition of the variables in the domain of
      [bindings], and [bindings'] is the disambiguated context bindings.

      Context variables cannot occur in [bindings]. A context variable in the
      head position of a context is handled in
      {!with_disambiguated_clf_context}. *)
  and with_disambiguated_context_bindings_list bindings f =
    (* Contextual LF contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    match bindings with
    | [] -> f []
    | x :: xs ->
        with_disambiguated_context_binding x (fun y ->
            with_disambiguated_context_bindings_list xs (fun ys ->
                f (y :: ys)))

  and with_disambiguated_context_binding binding f =
    (* Contextual LF contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    match binding with
    | Option.Some identifier, typ (* Typed binding *) ->
        let* typ' = disambiguate_clf_typ typ in
        with_lf_term_variable identifier (f (identifier, Option.some typ'))
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Plain; _ } )
    (* Untyped contextual LF variable *) ->
        with_lf_term_variable identifier (f (identifier, Option.none))
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

  and with_disambiguated_clf_context context f =
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
            with_disambiguated_context_bindings_list xs (fun bindings' ->
                f
                  { Synext.CLF.Context.location
                  ; head = head'
                  ; bindings = bindings'
                  })
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* Possibly a context variable as context head *)
          :: xs -> (
            lookup_toplevel identifier >>= function
            | Result.Ok (Context_variable, _) ->
                let head' =
                  Synext.CLF.Context.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                in
                with_disambiguated_context_bindings_list xs (fun bindings' ->
                    f
                      { Synext.CLF.Context.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | Result.Error (Unbound_identifier _) ->
                let head' =
                  Synext.CLF.Context.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                in
                with_context_variable identifier
                  (with_disambiguated_context_bindings_list xs
                     (fun bindings' ->
                       f
                         { Synext.CLF.Context.location
                         ; head = head'
                         ; bindings = bindings'
                         }))
            | Result.Ok _ ->
                let head' =
                  Synext.CLF.Context.Head.None { location = head_location }
                in
                with_disambiguated_context_bindings_list objects
                  (fun bindings' ->
                    f
                      { Synext.CLF.Context.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | Result.Error cause -> Error.raise_at1 head_location cause)
        | objects ->
            (* Context is just a list of bindings without context
               variables *)
            let head' =
              Synext.CLF.Context.Head.None { location = head_location }
            in
            with_disambiguated_context_bindings_list objects
              (fun bindings' ->
                f
                  { Synext.CLF.Context.location
                  ; head = head'
                  ; bindings = bindings'
                  }))

  and disambiguate_clf_application =
    let open
      Application_disambiguation.Make (Associativity) (Fixity) (Clf_operand)
        (Clf_operator)
        (Make_clf_application_disambiguation_state (Bindings_state)) in
    disambiguate_application >=> function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Ambiguous_operator_placement { left_operator; right_operator }) ->
        let left_operator_location = Clf_operator.location left_operator in
        let right_operator_location = Clf_operator.location right_operator in
        let identifier = Clf_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_clf_operator_placement identifier)
    | Result.Error (Arity_mismatch { operator; operator_arity; operands }) ->
        let operator_identifier = Clf_operator.identifier operator in
        let operator_location = Clf_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations = List.map Clf_operand.location operands in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Clf_arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier = Clf_operator.identifier left_operator in
        let left_operator_location = Clf_operator.location left_operator in
        let right_operator_location = Clf_operator.location right_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_clf_operators
             operator_identifier)
    | Result.Error (Misplaced_operator { operator; operands }) ->
        let operator_location = Clf_operator.location operator
        and operand_locations = List.map Clf_operand.location operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_clf_operator
    | Result.Error cause -> Error.raise cause

  and elaborate_lf_operand operand =
    match operand with
    | Clf_operand.Atom object_ -> disambiguate_clf_term object_
    | Clf_operand.Application { applicand; arguments } ->
        let* applicand' = disambiguate_clf_term applicand in
        let* arguments' = traverse_list1 elaborate_lf_operand arguments in
        let location =
          Location.join_all1_contramap Synext.location_of_clf_term
            (List1.cons applicand' arguments')
        in
        return
          (Synext.CLF.Term.Application
             { applicand = applicand'; arguments = arguments'; location })
end

module Make_pattern_disambiguator
    (Bindings_state : BINDINGS_STATE)
    (Disambiguation_state : PATTERN_DISAMBGUATION_STATE
                              with module S = Bindings_state) :
  CLF_PATTERN_DISAMBIGUATION with type state = Disambiguation_state.state =
struct
  include Disambiguation_state

  let lookup_toplevel identifier =
    with_wrapped_state (Bindings_state.lookup_toplevel identifier)

  let lookup identifier =
    with_wrapped_state (Bindings_state.lookup identifier)

  let partial_lookup identifier =
    with_wrapped_state (Bindings_state.partial_lookup identifier)

  let with_inner_bound_lf_term_variable ?location identifier f =
    with_inner_binding identifier
      (with_lf_term_variable ?location identifier f)

  let lf_term_variable_adder identifier =
    { run = (fun m -> Bindings_state.with_lf_term_variable identifier m) }

  let parameter_variable_adder identifier =
    { run = (fun m -> Bindings_state.with_parameter_variable identifier m) }

  let substitution_variable_adder identifier =
    { run = (fun m -> Bindings_state.with_substitution_variable identifier m)
    }

  let context_variable_adder identifier =
    { run = (fun m -> Bindings_state.with_context_variable identifier m) }

  let add_pattern_lf_term_variable identifier =
    add_pattern_variable identifier (lf_term_variable_adder identifier)

  let add_pattern_parameter_variable identifier =
    add_pattern_variable identifier (parameter_variable_adder identifier)

  let add_pattern_substitution_variable identifier =
    add_pattern_variable identifier (substitution_variable_adder identifier)

  let add_pattern_context_variable identifier =
    add_pattern_variable identifier (context_variable_adder identifier)

  let actual_binding_exn = Bindings_state.actual_binding_exn

  (** {1 Disambiguation} *)

  (** [disambiguate_clf_typ object_ state] is [(state', typ')] where [typ']
      is the disambiguated contextual LF type corresponding to [object_] with
      respect to the pattern disambiguation state. This is duplicated from
      the *)
  let rec disambiguate_clf_typ object_ =
    match object_ with
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
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As a contextual LF type occuring in a pattern, plain identifiers
           are necessarily bound type-level constants. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_type_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_type_constant
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            Error.raise_at1 location
              (Unbound_clf_type_constant qualified_identifier)
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers. *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As a contextual LF type occuring in a pattern, identifiers of the
           form [<identifier> <dot-identifier>+] are bound type-level
           constants, or illegal named projections. *)
        lookup identifier >>= function
        | Result.Ok (Lf_type_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Typ.Constant
                 { location; identifier; operator; quoted })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_type_constant
                 (actual_binding_exn identifier entry))
        | Result.Error (Unbound_qualified_identifier _) ->
            Error.raise_at1 location
              (Unbound_type_constant_or_illegal_projection_clf_type
                 identifier)
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_arrow { location; domain; range; orientation } ->
        let* domain' = disambiguate_clf_typ domain in
        let* range' = disambiguate_clf_typ range in
        return
          (Synext.CLF.Typ.Arrow
             { location; domain = domain'; range = range'; orientation })
    | Synprs.CLF.Object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; plicity
        ; body
        } ->
        let* parameter_type' = disambiguate_clf_typ parameter_type in
        let* body' =
          match parameter_identifier with
          | Option.None -> disambiguate_clf_typ body
          | Option.Some parameter_identifier ->
              with_lf_term_variable parameter_identifier
                (disambiguate_clf_typ body)
        in
        return
          (Synext.CLF.Typ.Pi
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; plicity
             ; body = body'
             })
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let* applicand, arguments =
          with_wrapped_state (disambiguate_clf_application objects)
        in
        let* applicand' = disambiguate_clf_typ applicand in
        let* arguments' = traverse_list1 elaborate_lf_operand arguments in
        return
          (Synext.CLF.Typ.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.CLF.Object.Raw_block
        { location; elements = List1.T ((Option.None, typ), []) } ->
        let* typ' = disambiguate_clf_typ typ in
        return (Synext.CLF.Typ.Block { location; elements = `Unnamed typ' })
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
        let* elements' =
          disambiguate_binding_list1_as_clf_dependent_types bindings
        in
        return
          (Synext.CLF.Typ.Block { location; elements = `Record elements' })

  and disambiguate_binding_list_as_clf_dependent_types bindings =
    match bindings with
    | [] -> return []
    | (identifier, typ) :: xs ->
        let* typ' = disambiguate_clf_typ typ in
        let* ys =
          (with_lf_term_variable identifier)
            (disambiguate_binding_list_as_clf_dependent_types xs)
        in
        return ((identifier, typ') :: ys)

  and disambiguate_binding_list1_as_clf_dependent_types bindings =
    let (List1.T ((identifier, typ), xs)) = bindings in
    let* typ' = disambiguate_clf_typ typ in
    let* ys =
      (with_lf_term_variable identifier)
        (disambiguate_binding_list_as_clf_dependent_types xs)
    in
    return (List1.from (identifier, typ') ys)

  and disambiguate_clf_term = function
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
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Parameter_variable, _) ->
            return
              (Synext.CLF.Term.Parameter_variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_parameter_variable
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) -> (
            (* Free parameter variable in a type occuring in a pattern. Its
               meta-type annotation binder will be introduced during the
               abstraction phase of term reconstruction. It is added as an
               inner binding to simulate that binder. *)
            let term' =
              Synext.CLF.Term.Parameter_variable { location; identifier }
            in
            is_inner_bound identifier >>= function
            | true ->
                (* A separate free occurrence of the variable has already
                   occurred, so we don't duplicate it. *)
                return term'
            | false ->
                let* () = add_pattern_parameter_variable identifier in
                let* () = push_inner_binding identifier in
                return term')
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } -> (
        (* A possibly free substitution variable. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Substitution_variable, _) ->
            return
              (Synext.CLF.Term.Substitution_variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_substitution_variable
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) -> (
            (* Free substitution variable in a contextgual LF term occuring
               in a pattern. Its meta-type annotation binder will be
               introduced during the abstraction phase of term
               reconstruction. It is added as an inner binding to simulate
               that binder. *)
            let term' =
              Synext.CLF.Term.Substitution_variable { location; identifier }
            in
            is_inner_bound identifier >>= function
            | true ->
                (* A separate free occurrence of the variable has already
                   occurred, so we don't duplicate it. *)
                return term'
            | false ->
                let* () = add_pattern_substitution_variable identifier in
                let* () = push_inner_binding identifier in
                return term')
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_term_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Term.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Result.Ok (Lf_term_variable, _)
        | Result.Ok (Meta_variable, _) ->
            (* Bound variable *)
            return (Synext.CLF.Term.Variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) -> (
            (* Free variable in a contextual LF term occuring in a pattern.
               Its meta-type annotation binder will be introduced during the
               abstraction phase of term reconstruction. It is added as an
               inner binding to simulate that binder. *)
            let term' = Synext.CLF.Term.Variable { location; identifier } in
            is_inner_bound identifier >>= function
            | true ->
                (* A separate free occurrence of the variable has already
                   occurred, so we don't duplicate it. *)
                return term'
            | false ->
                let* () = add_pattern_lf_term_variable identifier in
                let* () = push_inner_binding identifier in
                return term')
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
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
        partial_lookup identifier >>= function
        | `Totally_unbound (List1.T (free_variable, projections)) -> (
            (* Projections of a free variable in a type occuring in a
               pattern. Its meta-type annotation binder will be introduced
               during the abstraction phase of term reconstruction. It is
               added as an inner binding to simulate that binder. *)
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = free_variable }
            in
            let term' = reduce_projections term projections in
            is_inner_bound free_variable >>= function
            | true ->
                (* A separate free occurrence of the variable has already
                   occurred, so we don't duplicate it. *)
                return term'
            | false ->
                let* () = add_pattern_lf_term_variable free_variable in
                let* () = push_inner_binding free_variable in
                return term')
        | `Partially_bound
            ( List1.T
                ( ( variable_identifier
                  , (Lf_term_variable, _ | Meta_variable, _) )
                , [] )
            , unbound_segments )
        (* Projections of a bound variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = variable_identifier }
            in
            return (reduce_projections term (List1.to_list unbound_segments))
        | `Partially_bound (List1.T (_, []), unbound_segments)
        | `Partially_bound (_, unbound_segments)
        (* Projections of a bound constant *) ->
            Error.raise_at1
              (Location.join_all1_contramap Identifier.location
                 unbound_segments)
              Illegal_clf_term_projection
        | `Totally_bound bound_segments (* A constant *) -> (
            match List1.last bound_segments with
            | ( _identifier
              , (Lf_term_constant, { operator = Option.Some operator; _ }) )
              ->
                return
                  (Synext.CLF.Term.Constant
                     { identifier; location; operator; quoted })
            | _identifier, entry ->
                Error.raise_at1 location
                  (Error.composite_exception2 Expected_clf_term_constant
                     (actual_binding_exn identifier entry))))
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let* applicand, arguments =
          with_wrapped_state (disambiguate_clf_application objects)
        in
        let* applicand' = disambiguate_clf_term applicand in
        let* arguments' = traverse_list1 elaborate_lf_operand arguments in
        return
          (Synext.CLF.Term.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } ->
        let* parameter_type' =
          traverse_option disambiguate_clf_typ parameter_sort
        in
        let* body' =
          match parameter_identifier with
          | Option.None -> disambiguate_clf_term body
          | Option.Some parameter_identifier ->
              with_lf_term_variable parameter_identifier
                (disambiguate_clf_term body)
        in
        return
          (Synext.CLF.Term.Abstraction
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; body = body'
             })
    | Synprs.CLF.Object.Raw_hole { location; variant } ->
        return (Synext.CLF.Term.Hole { location; variant })
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let* terms' = traverse_list1 disambiguate_clf_term elements in
        return (Synext.CLF.Term.Tuple { location; terms = terms' })
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let* term' = disambiguate_clf_term object_ in
        return
          (Synext.CLF.Term.Projection { location; term = term'; projection })
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let* term' = disambiguate_clf_term object_ in
        let* substitution' = disambiguate_clf_substitution substitution in
        return
          (Synext.CLF.Term.Substitution
             { location; term = term'; substitution = substitution' })
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let* term' = disambiguate_clf_term object_ in
        let* typ' = disambiguate_clf_typ sort in
        return
          (Synext.CLF.Term.Type_annotated
             { location; term = term'; typ = typ' })

  and disambiguate_clf_substitution substitution =
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
    | Synprs.CLF.Context_object.Head.None { location = head_location } ->
        let* head', objects'' =
          match objects' with
          | Synprs.CLF.Object.Raw_substitution
              { object_ =
                  Synprs.CLF.Object.Raw_identifier
                    { location; identifier = identifier, `Dollar; _ }
              ; substitution = closure
              ; _
              } (* A substitution closure *)
            :: xs ->
              let* closure' = disambiguate_clf_substitution closure in
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              in
              return (head', xs)
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              in
              return (head', xs)
          | objects' ->
              let head' =
                Synext.CLF.Substitution.Head.None
                  { location = head_location }
              in
              return (head', objects')
        in
        let* terms' = traverse_list disambiguate_clf_term objects'' in
        return
          { Synext.CLF.Substitution.location; head = head'; terms = terms' }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let* terms' = traverse_list disambiguate_clf_term objects' in
        let head' =
          Synext.CLF.Substitution.Head.Identity { location = head_location }
        in
        return
          { Synext.CLF.Substitution.location; head = head'; terms = terms' }

  and disambiguate_clf_application =
    let open
      Application_disambiguation.Make (Associativity) (Fixity) (Clf_operand)
        (Clf_operator)
        (Make_clf_application_disambiguation_state (Bindings_state)) in
    disambiguate_application >=> function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Ambiguous_operator_placement { left_operator; right_operator }) ->
        let left_operator_location = Clf_operator.location left_operator in
        let right_operator_location = Clf_operator.location right_operator in
        let identifier = Clf_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_clf_operator_placement identifier)
    | Result.Error (Arity_mismatch { operator; operator_arity; operands }) ->
        let operator_identifier = Clf_operator.identifier operator in
        let operator_location = Clf_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations = List.map Clf_operand.location operands in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Clf_arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier = Clf_operator.identifier left_operator in
        let left_operator_location = Clf_operator.location left_operator in
        let right_operator_location = Clf_operator.location right_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_clf_operators
             operator_identifier)
    | Result.Error (Misplaced_operator { operator; operands }) ->
        let operator_location = Clf_operator.location operator
        and operand_locations = List.map Clf_operand.location operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_clf_operator
    | Result.Error cause -> Error.raise cause

  and elaborate_lf_operand operand =
    match operand with
    | Clf_operand.Atom object_ -> disambiguate_clf_term object_
    | Clf_operand.Application { applicand; arguments } ->
        let* applicand' = disambiguate_clf_term applicand in
        let* arguments' = traverse_list1 elaborate_lf_operand arguments in
        let location =
          Location.join_all1_contramap Synext.location_of_clf_term
            (List1.cons applicand' arguments')
        in
        return
          (Synext.CLF.Term.Application
             { applicand = applicand'; arguments = arguments'; location })

  let rec disambiguate_clf_term_pattern object_ =
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
        let pattern' =
          Synext.CLF.Term.Pattern.Parameter_variable { location; identifier }
        in
        is_inner_bound identifier >>= function
        | true -> return pattern'
        | false ->
            let* () = add_pattern_parameter_variable identifier in
            let* () = push_inner_binding identifier in
            return pattern')
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } -> (
        let pattern' =
          Synext.CLF.Term.Pattern.Substitution_variable
            { location; identifier }
        in
        is_inner_bound identifier >>= function
        | true -> return pattern'
        | false ->
            let* () = add_pattern_substitution_variable identifier in
            let* () = push_inner_binding identifier in
            return pattern')
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF term pattern, plain identifiers are either term-level
           constants, variables bound in the pattern, or new pattern
           variables. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_term_constant, { operator = Option.Some operator; _ })
          ->
            return
              (Synext.CLF.Term.Pattern.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Result.Ok (Lf_term_variable, _)
        | Result.Ok (Meta_variable, _) -> (
            let pattern' =
              Synext.CLF.Term.Pattern.Variable { location; identifier }
            in
            is_inner_bound identifier >>= function
            | true -> return pattern'
            | false ->
                let* () = add_pattern_lf_term_variable identifier in
                let* () = push_inner_binding identifier in
                return pattern')
        | Result.Ok _
        | Result.Error (Unbound_identifier _) -> (
            let pattern' =
              Synext.CLF.Term.Pattern.Variable { location; identifier }
            in
            is_inner_bound identifier >>= function
            | true -> return pattern'
            | false ->
                let* () = add_pattern_lf_term_variable identifier in
                let* () = push_inner_binding identifier in
                return pattern')
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
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
        partial_lookup identifier >>= function
        | `Totally_unbound (List1.T (free_variable, projections))
        (* Projections of a free variable *) -> (
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = free_variable }
            in
            let term' = reduce_projections term projections in
            is_inner_bound free_variable >>= function
            | true -> return term'
            | false ->
                let* () = add_pattern_lf_term_variable free_variable in
                let* () = push_inner_binding free_variable in
                return term')
        | `Partially_bound
            ( List1.T
                ( ( variable_identifier
                  , (Lf_term_variable, _ | Meta_variable, _) )
                , [] )
            , unbound_segments )
        (* Projections of a bound variable *) -> (
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = variable_identifier }
            in
            let term' =
              reduce_projections term (List1.to_list unbound_segments)
            in
            is_inner_bound variable_identifier >>= function
            | true -> return term'
            | false ->
                let* () = add_pattern_lf_term_variable variable_identifier in
                let* () = push_inner_binding variable_identifier in
                return term')
        | `Partially_bound (List1.T (_, []), unbound_segments)
        | `Partially_bound (_, unbound_segments)
        (* Projections of a bound constant *) ->
            Error.raise_at1
              (Location.join_all1_contramap Identifier.location
                 unbound_segments)
              Illegal_clf_term_projection
        | `Totally_bound bound_segments (* A constant *) -> (
            match List1.last bound_segments with
            | ( _identifier
              , (Lf_term_constant, { operator = Option.Some operator; _ }) )
              ->
                return
                  (Synext.CLF.Term.Pattern.Constant
                     { identifier; location; operator; quoted })
            | _identifier, entry ->
                Error.raise_at1 location
                  (Error.composite_exception2 Expected_clf_term_constant
                     (Bindings_state.actual_binding_exn identifier entry))))
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let* applicand, arguments =
          with_wrapped_state (disambiguate_clf_application objects)
        in
        let* applicand' = disambiguate_clf_term_pattern applicand in
        let* arguments' =
          traverse_list1 elaborate_lf_operand_pattern arguments
        in
        return
          (Synext.CLF.Term.Pattern.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let* parameter_type' =
          traverse_option disambiguate_clf_typ parameter_sort
        in
        match parameter_identifier with
        | Option.None ->
            let* body' = disambiguate_clf_term_pattern body in
            return
              (Synext.CLF.Term.Pattern.Abstraction
                 { location
                 ; parameter_identifier
                 ; parameter_type = parameter_type'
                 ; body = body'
                 })
        | Option.Some parameter_identifier' ->
            let* body' =
              with_inner_bound_lf_term_variable parameter_identifier'
                (disambiguate_clf_term_pattern body)
            in
            return
              (Synext.CLF.Term.Pattern.Abstraction
                 { location
                 ; parameter_identifier
                 ; parameter_type = parameter_type'
                 ; body = body'
                 }))
    | Synprs.CLF.Object.Raw_hole { location; variant = `Underscore } ->
        return (Synext.CLF.Term.Pattern.Wildcard { location })
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let* terms' =
          traverse_list1 disambiguate_clf_term_pattern elements
        in
        return (Synext.CLF.Term.Pattern.Tuple { location; terms = terms' })
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let* term' = disambiguate_clf_term_pattern object_ in
        return
          (Synext.CLF.Term.Pattern.Projection
             { location; term = term'; projection })
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let* term' = disambiguate_clf_term_pattern object_ in
        let* substitution' = disambiguate_clf_substitution substitution in
        return
          (Synext.CLF.Term.Pattern.Substitution
             { location; term = term'; substitution = substitution' })
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let* typ' = disambiguate_clf_typ sort in
        let* term' = disambiguate_clf_term_pattern object_ in
        return
          (Synext.CLF.Term.Pattern.Type_annotated
             { location; term = term'; typ = typ' })

  and elaborate_lf_operand_pattern operand =
    match operand with
    | Clf_operand.Atom object_ -> disambiguate_clf_term_pattern object_
    | Clf_operand.Application { applicand; arguments } ->
        let* applicand' = disambiguate_clf_term_pattern applicand in
        let* arguments' =
          traverse_list1 elaborate_lf_operand_pattern arguments
        in
        let location =
          Location.join_all1_contramap Synext.location_of_clf_term_pattern
            (List1.cons applicand' arguments')
        in
        return
          (Synext.CLF.Term.Pattern.Application
             { applicand = applicand'; arguments = arguments'; location })

  and disambiguate_clf_substitution_pattern substitution_pattern =
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
                  { location; identifier = identifier, `Dollar; _ }
            ; substitution = closure
            ; _
            } (* A substitution closure *)
          :: xs -> (
            let* closure' = disambiguate_clf_substitution closure in
            let head' =
              Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                { location; identifier; closure = Option.some closure' }
            in
            let* terms' = traverse_list disambiguate_clf_term_pattern xs in
            let substitution' =
              { Synext.CLF.Substitution.Pattern.location
              ; head = head'
              ; terms = terms'
              }
            in
            is_inner_bound identifier >>= function
            | true ->
                (* The substitution variable is explicitly bound in the
                   pattern we are currently disambiguating. We do not add it
                   to the pattern variables. *)
                return substitution'
            | false ->
                (* The substitution variable is not explicitly bound in the
                   pattern we are currently disambiguating. Hence it is
                   treated as a pattern variable, and its implicit binder
                   will be introduced during the abstraction phase of term
                   reconstruction. *)
                let* () = add_pattern_substitution_variable identifier in
                let* () = push_inner_binding identifier in
                return substitution')
        | Synprs.CLF.Object.Raw_identifier
            { location; identifier = identifier, `Dollar; _ }
            (* A substitution variable *)
          :: xs -> (
            let head' =
              Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                { location; identifier; closure = Option.none }
            in
            let* terms' = traverse_list disambiguate_clf_term_pattern xs in
            let substitution' =
              { Synext.CLF.Substitution.Pattern.location
              ; head = head'
              ; terms = terms'
              }
            in
            is_inner_bound identifier >>= function
            | true ->
                (* The substitution variable is explicitly bound in the
                   pattern we are currently disambiguating. We do not add it
                   to the pattern variables. *)
                return substitution'
            | false ->
                (* The substitution variable is not explicitly bound in the
                   pattern we are currently disambiguating. Hence it is
                   treated as a pattern variable, and its implicit binder
                   will be introduced during the abstraction phase of term
                   reconstruction. *)
                let* () = add_pattern_substitution_variable identifier in
                let* () = push_inner_binding identifier in
                return substitution')
        | objects' ->
            let head' =
              Synext.CLF.Substitution.Pattern.Head.None
                { location = head_location }
            in
            let* terms' =
              traverse_list disambiguate_clf_term_pattern objects'
            in
            return
              { Synext.CLF.Substitution.Pattern.location
              ; head = head'
              ; terms = terms'
              })
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let head' =
          Synext.CLF.Substitution.Pattern.Head.Identity
            { location = head_location }
        in
        let* terms' = traverse_list disambiguate_clf_term_pattern objects' in
        return
          { Synext.CLF.Substitution.Pattern.location
          ; head = head'
          ; terms = terms'
          }

  and with_disambiguated_context_pattern_binding :
        'a.
           Identifier.t option * Clf_operand.expression
        -> (Identifier.t * Synext.clf_typ -> 'a t)
        -> 'a t =
   fun binding f ->
    match binding with
    | Option.Some identifier, typ ->
        let* typ' = disambiguate_clf_typ typ in
        let y = (identifier, typ') in
        with_lf_term_variable identifier (f y)
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
           (Identifier.t option * Clf_operand.expression) list
        -> ((Identifier.t * Synext.clf_typ) list -> 'a t)
        -> 'a t =
   fun bindings f ->
    match bindings with
    | [] -> f []
    | x :: xs ->
        with_disambiguated_context_pattern_binding x (fun y ->
            with_disambiguated_context_pattern_bindings_list xs (fun ys ->
                f (y :: ys)))

  and with_disambiguated_clf_context_pattern :
        'a.
           Synprs.clf_context_object
        -> (Synext.clf_context_pattern -> 'a t)
        -> 'a t =
   fun context_pattern f ->
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
            with_disambiguated_context_pattern_bindings_list bindings
              (fun bindings' ->
                f
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  })
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* Possibly a context variable as context head *)
          :: bindings -> (
            lookup_toplevel identifier >>= function
            | Result.Ok (Context_variable, _) -> (
                let head' =
                  Synext.CLF.Context.Pattern.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                in
                is_inner_bound identifier >>= function
                | true ->
                    (* The context variable is explicitly bound in the
                       pattern we are currently disambiguating. We do not add
                       it to the pattern variables. *)
                    with_disambiguated_context_pattern_bindings_list bindings
                      (fun bindings' ->
                        f
                          { Synext.CLF.Context.Pattern.location
                          ; head = head'
                          ; bindings = bindings'
                          })
                | false ->
                    (* The context variable is not explicitly bound in the
                       pattern we are currently disambiguating. Hence it is
                       treated as a pattern variable, and its implicit binder
                       will be introduced during the abstraction phase of
                       term reconstruction. *)
                    let* () = add_pattern_context_variable identifier in
                    let* () = push_inner_binding identifier in
                    with_disambiguated_context_pattern_bindings_list bindings
                      (fun bindings' ->
                        f
                          { Synext.CLF.Context.Pattern.location
                          ; head = head'
                          ; bindings = bindings'
                          }))
            | Result.Error (Unbound_identifier _) ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                in
                (* The context variable is not explicitly bound in the
                   pattern we are currently disambiguating. Hence it is
                   treated as a pattern variable, and its implicit binder
                   will be introduced during the abstraction phase of term
                   reconstruction. *)
                let* () = add_pattern_context_variable identifier in
                let* () = push_inner_binding identifier in
                with_disambiguated_context_pattern_bindings_list bindings
                  (fun bindings' ->
                    f
                      { Synext.CLF.Context.Pattern.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | Result.Ok _ ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.None
                    { location = head_location }
                in
                with_disambiguated_context_pattern_bindings_list bindings
                  (fun bindings' ->
                    f
                      { Synext.CLF.Context.Pattern.location
                      ; head = head'
                      ; bindings = bindings'
                      })
            | Result.Error cause ->
                Error.raise_at1 (Identifier.location identifier) cause)
        | _ ->
            let head' =
              Synext.CLF.Context.Pattern.Head.None
                { location = head_location }
            in
            with_disambiguated_context_pattern_bindings_list objects
              (fun bindings' ->
                f
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  }))

  and disambiguate_clf_context_pattern context_pattern =
    with_disambiguated_clf_context_pattern context_pattern return
end

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
        Format.dprintf "Expected a contextual LF type-level constant."
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
    | Unbound_clf_term_constant identifier ->
        Format.dprintf "The LF term-level constant %a is unbound."
          Qualified_identifier.pp identifier
    | Illegal_clf_term_projection ->
        Format.dprintf "Illegal contextual LF projection(s)."
    | Expected_parameter_variable ->
        Format.dprintf "Expected a parameter variable."
    | Expected_substitution_variable ->
        Format.dprintf "Expected a substitution variable."
    | Illegal_clf_subtitution_term_label ->
        Format.dprintf "Terms in a substitution may not be labelled."
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
    | Expected_clf_term_constant ->
        Format.dprintf "Expected an LF term-level constant."
    | Ambiguous_clf_operator_placement operator_identifier ->
        Format.dprintf
          "Ambiguous occurrences of the LF term-level or type-level \
           operator %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Misplaced_clf_operator ->
        Format.dprintf
          "Misplaced contextual LF term-level or type-level operator."
    | Consecutive_applications_of_non_associative_clf_operators
        operator_identifier ->
        Format.dprintf
          "Consecutive occurrences of the contextual LF term-level or \
           type-level operator %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Clf_arity_mismatch
        { operator_identifier
        ; expected_arguments_count
        ; actual_arguments_count
        } ->
        Format.dprintf "Operator %a expected %d arguments but got %d."
          Qualified_identifier.pp operator_identifier
          expected_arguments_count actual_arguments_count
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
