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

(** {2 Exceptions for contextual LF substitution disambiguation} *)

exception Illegal_clf_subtitution_term_label

(** {2 Exceptions for contextual LF context disambiguation} *)

exception Illegal_clf_context_parameter_variable_binding

exception Illegal_clf_context_substitution_variable_binding

exception Illegal_clf_context_missing_binding_identifier

exception Illegal_clf_context_identity

(** {2 Exceptions for application rewriting} *)

exception Expected_clf_term_constant

exception Expected_clf_type_constant

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

(** {2 Exception Printing} *)
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

  val with_disambiguated_clf_term_pattern :
       Synprs.clf_object
    -> Identifier.t List1.t Identifier.Hamt.t
    -> Identifier.t list
    -> (   Synext.clf_term_pattern
        -> Identifier.t List1.t Identifier.Hamt.t
        -> Identifier.t list
        -> 'a t)
    -> 'a t

  val with_disambiguated_clf_substitution_pattern :
       Synprs.clf_context_object
    -> Identifier.t List1.t Identifier.Hamt.t
    -> Identifier.t list
    -> (   Synext.clf_substitution_pattern
        -> Identifier.t List1.t Identifier.Hamt.t
        -> Identifier.t list
        -> 'a t)
    -> 'a t

  val with_disambiguated_clf_context_pattern :
       Synprs.clf_context_object
    -> Identifier.t List1.t Identifier.Hamt.t
    -> Identifier.t list
    -> (   Synext.clf_context_pattern
        -> Identifier.t List1.t Identifier.Hamt.t
        -> Identifier.t list
        -> 'a t)
    -> 'a t
end

(** Disambiguation of contextual LF types, terms and patterns from the parser
    syntax to the external syntax.

    This disambiguation does not perform normalization nor validation. *)
module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  CLF_DISAMBIGUATION with type state = Disambiguation_state.state = struct
  include Disambiguation_state

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
  module Clf_application_disambiguation_state = struct
    include Disambiguation_state

    type operator = Clf_operator.t

    type expression = Synprs.clf_object

    let guard_identifier_operator identifier expression =
      lookup identifier >>= function
      | Result.Ok (Lf_type_constant { operator; _ })
      | Result.Ok (Lf_term_constant { operator; _ }) ->
          if Operator.is_nullary operator then return Option.none
          else
            return
              (Option.some
                 (Clf_operator.make ~identifier ~operator
                    ~applicand:expression))
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
      | Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Plain; _ } ->
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

  module Clf_application_disambiguation =
    Application_disambiguation.Make (Associativity) (Fixity) (Clf_operand)
      (Clf_operator)
      (Clf_application_disambiguation_state)

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
        | Result.Ok (Lf_type_constant { operator; _ }) ->
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
        | Result.Ok (Lf_type_constant { operator; _ }) ->
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
        { location; identifier = identifier, `Hash; _ } ->
        return (Synext.CLF.Term.Parameter_variable { location; identifier })
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } ->
        return
          (Synext.CLF.Term.Substitution_variable { location; identifier })
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_term_constant { operator; _ }) ->
            return
              (Synext.CLF.Term.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Result.Ok (Lf_term_variable _)
        | Result.Ok (Meta_variable _) ->
            (* Bound variable *)
            return (Synext.CLF.Term.Variable { location; identifier })
        | Result.Ok entry ->
            Error.raise_at1 location
              (Error.composite_exception2 Expected_clf_term_constant
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            (* Free variable *)
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
        | `Totally_unbound (List1.T (free_variable, projections))
        (* Projections of a free variable *) ->
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Variable
                { location; identifier = free_variable }
            in
            return (reduce_projections term projections)
        | `Partially_bound
            ( List1.T
                ( ( variable_identifier
                  , (Lf_term_variable _ | Meta_variable _) )
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
            | _identifier, Lf_term_constant { operator; _ } ->
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
        with_lf_term_variable identifier
          (let y = (identifier, Option.some typ') in
           f y)
    | ( Option.None
      , Synprs.CLF.Object.Raw_identifier
          { identifier = identifier, `Plain; _ } )
    (* Untyped contextual LF variable *) ->
        with_lf_term_variable identifier
          (let y = (identifier, Option.none) in
           f y)
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
            | Result.Ok (Context_variable _) ->
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

  and disambiguate_clf_application objects =
    Clf_application_disambiguation.disambiguate_application objects
    >>= function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Clf_application_disambiguation.Ambiguous_operator_placement
          { left_operator; right_operator }) ->
        let left_operator_location = Clf_operator.location left_operator in
        let right_operator_location = Clf_operator.location right_operator in
        let identifier = Clf_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_clf_operator_placement identifier)
    | Result.Error
        (Clf_application_disambiguation.Arity_mismatch
          { operator; operator_arity; operands }) ->
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
        (Clf_application_disambiguation.Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier = Clf_operator.identifier left_operator in
        let left_operator_location = Clf_operator.location left_operator in
        let right_operator_location = Clf_operator.location right_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_clf_operators
             operator_identifier)
    | Result.Error
        (Clf_application_disambiguation.Misplaced_operator
          { operator; operands }) ->
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

  let push_binding identifier bindings =
    match Identifier.Hamt.find_opt identifier bindings with
    | Option.None ->
        Identifier.Hamt.add identifier (List1.singleton identifier) bindings
    | Option.Some binding_stack ->
        Identifier.Hamt.add identifier
          (List1.cons identifier binding_stack)
          bindings

  let pop_binding identifier bindings =
    match Identifier.Hamt.find_opt identifier bindings with
    | Option.None -> Error.violation "[pop_binding]"
    | Option.Some (List1.T (_head, [])) ->
        Identifier.Hamt.remove identifier bindings
    | Option.Some (List1.T (_head, x :: xs)) ->
        Identifier.Hamt.add identifier (List1.from x xs) bindings

  let rec with_disambiguated_clf_term_patterns_list :
      type a.
         Synprs.clf_object list
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_term_pattern list
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun objects inner_bound_variables pattern_variables f ->
    match objects with
    | [] -> f [] inner_bound_variables pattern_variables
    | x :: xs ->
        with_disambiguated_clf_term_pattern x inner_bound_variables
          pattern_variables
          (fun y inner_bound_variables' pattern_variables' ->
            with_disambiguated_clf_term_patterns_list xs
              inner_bound_variables' pattern_variables'
              (fun ys inner_bound_variables'' pattern_variables'' ->
                f (y :: ys) inner_bound_variables'' pattern_variables''))

  and with_disambiguated_clf_term_patterns_list1 :
      type a.
         Synprs.clf_object List1.t
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_term_pattern List1.t
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun objects inner_bound_variables pattern_variables f ->
    let (List1.T (x, xs)) = objects in
    with_disambiguated_clf_term_pattern x inner_bound_variables
      pattern_variables (fun y inner_bound_variables' pattern_variables' ->
        with_disambiguated_clf_term_patterns_list xs inner_bound_variables'
          pattern_variables'
          (fun ys inner_bound_variables'' pattern_variables'' ->
            f (List1.from y ys) inner_bound_variables'' pattern_variables''))

  and with_disambiguated_clf_term_pattern :
      type a.
         Synprs.clf_object
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_term_pattern
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun object_ inner_bound_variables pattern_variables f ->
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
        { location; identifier = identifier, `Hash; _ } ->
        let pattern' =
          Synext.CLF.Term.Pattern.Parameter_variable { location; identifier }
        in
        if Identifier.Hamt.mem identifier inner_bound_variables then
          f pattern' inner_bound_variables pattern_variables
        else
          with_parameter_variable identifier
            (f pattern' inner_bound_variables
               (identifier :: pattern_variables))
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } ->
        let pattern' =
          Synext.CLF.Term.Pattern.Substitution_variable
            { location; identifier }
        in
        if Identifier.Hamt.mem identifier inner_bound_variables then
          f pattern' inner_bound_variables pattern_variables
        else
          with_substitution_variable identifier
            (f pattern' inner_bound_variables
               (identifier :: pattern_variables))
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF term pattern, plain identifiers are either term-level
           constants, variables bound in the pattern, or new pattern
           variables. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok (Lf_term_constant { operator; _ }) ->
            let pattern' =
              Synext.CLF.Term.Pattern.Constant
                { location
                ; identifier = qualified_identifier
                ; operator
                ; quoted
                }
            in
            f pattern' inner_bound_variables pattern_variables
        | Result.Ok (Lf_term_variable _)
        | Result.Ok (Meta_variable _) ->
            let pattern' =
              Synext.CLF.Term.Pattern.Variable { location; identifier }
            in
            if Identifier.Hamt.mem identifier inner_bound_variables then
              f pattern' inner_bound_variables pattern_variables
            else
              with_lf_term_variable identifier
                (f pattern' inner_bound_variables
                   (identifier :: pattern_variables))
        | Result.Ok _
        | Result.Error (Unbound_identifier _) ->
            let pattern' =
              Synext.CLF.Term.Pattern.Variable { location; identifier }
            in
            with_lf_term_variable identifier
              (f pattern' inner_bound_variables
                 (identifier :: pattern_variables))
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
        (* Projections of a free variable *) ->
            let location = Identifier.location free_variable in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = free_variable }
            in
            with_lf_term_variable free_variable
              (f
                 (reduce_projections term projections)
                 inner_bound_variables
                 (free_variable :: pattern_variables))
        | `Partially_bound
            ( List1.T
                ( ( variable_identifier
                  , (Lf_term_variable _ | Meta_variable _) )
                , [] )
            , unbound_segments )
        (* Projections of a bound variable *) ->
            let location = Identifier.location variable_identifier in
            let term =
              Synext.CLF.Term.Pattern.Variable
                { location; identifier = variable_identifier }
            in
            if Identifier.Hamt.mem variable_identifier inner_bound_variables
            then
              (* The variable's binder is within the pattern, so this is not
                 a pattern variable. *)
              f term inner_bound_variables pattern_variables
            else
              (* The variable's binder is outside the pattern, so this is a
                 pattern variable. *)
              with_lf_term_variable variable_identifier
                (f
                   (reduce_projections term (List1.to_list unbound_segments))
                   inner_bound_variables
                   (variable_identifier :: pattern_variables))
        | `Partially_bound (List1.T (_, []), unbound_segments)
        | `Partially_bound (_, unbound_segments)
        (* Projections of a bound constant *) ->
            Error.raise_at1
              (Location.join_all1_contramap Identifier.location
                 unbound_segments)
              Illegal_clf_term_projection
        | `Totally_bound bound_segments (* A constant *) -> (
            match List1.last bound_segments with
            | _identifier, Lf_term_constant { operator; _ } ->
                f
                  (Synext.CLF.Term.Pattern.Constant
                     { identifier; location; operator; quoted })
                  inner_bound_variables pattern_variables
            | _identifier, entry ->
                Error.raise_at1 location
                  (Error.composite_exception2 Expected_clf_term_constant
                     (actual_binding_exn identifier entry))))
    | Synprs.CLF.Object.Raw_application { objects; location } ->
        let* applicand, arguments = disambiguate_clf_application objects in
        with_disambiguated_clf_term_pattern applicand inner_bound_variables
          pattern_variables
          (fun applicand' inner_bound_variables' pattern_variables' ->
            with_elaborated_clf_pattern_operands_list1 arguments
              inner_bound_variables' pattern_variables'
              (fun arguments' inner_bound_variables'' pattern_variables'' ->
                f
                  (Synext.CLF.Term.Pattern.Application
                     { applicand = applicand'
                     ; arguments = arguments'
                     ; location
                     })
                  inner_bound_variables'' pattern_variables''))
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let* parameter_type' =
          traverse_option disambiguate_clf_typ parameter_sort
        in
        match parameter_identifier with
        | Option.None ->
            with_disambiguated_clf_term_pattern body inner_bound_variables
              pattern_variables
              (fun body' inner_bound_variables' pattern_variables' ->
                f
                  (Synext.CLF.Term.Pattern.Abstraction
                     { location
                     ; parameter_identifier
                     ; parameter_type = parameter_type'
                     ; body = body'
                     })
                  inner_bound_variables' pattern_variables')
        | Option.Some parameter_identifier' ->
            (with_lf_term_variable parameter_identifier')
              (with_disambiguated_clf_term_pattern body
                 (push_binding parameter_identifier' inner_bound_variables)
                 pattern_variables
                 (fun body' inner_bound_variables' pattern_variables' ->
                   f
                     (Synext.CLF.Term.Pattern.Abstraction
                        { location
                        ; parameter_identifier
                        ; parameter_type = parameter_type'
                        ; body = body'
                        })
                     (pop_binding parameter_identifier'
                        inner_bound_variables')
                     pattern_variables')))
    | Synprs.CLF.Object.Raw_hole { location; variant = `Underscore } ->
        f
          (Synext.CLF.Term.Pattern.Wildcard { location })
          inner_bound_variables pattern_variables
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        with_disambiguated_clf_term_patterns_list1 elements
          inner_bound_variables pattern_variables
          (fun terms' inner_bound_variables' pattern_variables' ->
            f
              (Synext.CLF.Term.Pattern.Tuple { location; terms = terms' })
              inner_bound_variables' pattern_variables')
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        with_disambiguated_clf_term_pattern object_ inner_bound_variables
          pattern_variables
          (fun term' inner_bound_variables' pattern_variables' ->
            f
              (Synext.CLF.Term.Pattern.Projection
                 { location; term = term'; projection })
              inner_bound_variables' pattern_variables')
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        with_disambiguated_clf_term_pattern object_ inner_bound_variables
          pattern_variables
          (fun term' inner_bound_variables' pattern_variables' ->
            let* substitution' =
              disambiguate_clf_substitution substitution
            in
            f
              (Synext.CLF.Term.Pattern.Substitution
                 { location; term = term'; substitution = substitution' })
              inner_bound_variables' pattern_variables')
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let* typ' = disambiguate_clf_typ sort in
        with_disambiguated_clf_term_pattern object_ inner_bound_variables
          pattern_variables
          (fun term' inner_bound_variables' pattern_variables' ->
            f
              (Synext.CLF.Term.Pattern.Type_annotated
                 { location; term = term'; typ = typ' })
              inner_bound_variables' pattern_variables')

  and with_elaborated_clf_pattern_operands_list :
      type a.
         Clf_operand.t list
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_term_pattern list
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun operands inner_bound_variables pattern_variables f ->
    match operands with
    | [] -> f [] inner_bound_variables pattern_variables
    | x :: xs ->
        with_elaborated_clf_pattern_operand x inner_bound_variables
          pattern_variables
          (fun y inner_bound_variables' pattern_variables' ->
            with_elaborated_clf_pattern_operands_list xs
              inner_bound_variables' pattern_variables'
              (fun ys inner_bound_variables'' pattern_variables'' ->
                f (y :: ys) inner_bound_variables'' pattern_variables''))

  and with_elaborated_clf_pattern_operands_list1 :
      type a.
         Clf_operand.t List1.t
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_term_pattern List1.t
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun operands inner_bound_variables pattern_variables f ->
    let (List1.T (x, xs)) = operands in
    with_elaborated_clf_pattern_operand x inner_bound_variables
      pattern_variables (fun y inner_bound_variables' pattern_variables' ->
        with_elaborated_clf_pattern_operands_list xs inner_bound_variables'
          pattern_variables'
          (fun ys inner_bound_variables'' pattern_variables'' ->
            f (List1.from y ys) inner_bound_variables'' pattern_variables''))

  and with_elaborated_clf_pattern_operand :
      type a.
         Clf_operand.t
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_term_pattern
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun operand inner_bound_variables pattern_variables f ->
    match operand with
    | Clf_operand.Atom object_ ->
        with_disambiguated_clf_term_pattern object_ inner_bound_variables
          pattern_variables f
    | Clf_operand.Application { applicand; arguments } ->
        with_disambiguated_clf_term_pattern applicand inner_bound_variables
          pattern_variables
          (fun applicand' inner_bound_variables' pattern_variables' ->
            with_elaborated_clf_pattern_operands_list1 arguments
              inner_bound_variables' pattern_variables'
              (fun arguments' inner_bound_variables'' pattern_variables'' ->
                let location =
                  Location.join_all1_contramap
                    Synext.location_of_clf_term_pattern
                    (List1.cons applicand' arguments')
                in
                f
                  (Synext.CLF.Term.Pattern.Application
                     { applicand = applicand'
                     ; arguments = arguments'
                     ; location
                     })
                  inner_bound_variables'' pattern_variables''))

  and with_disambiguated_clf_substitution_pattern substitution_pattern
      inner_bound_variables pattern_variables f =
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
          :: xs ->
            let* closure' = disambiguate_clf_substitution closure in
            let head' =
              Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                { location; identifier; closure = Option.some closure' }
            in
            let pattern_variables' =
              if Identifier.Hamt.mem identifier inner_bound_variables then
                pattern_variables
              else identifier :: pattern_variables
            in
            with_disambiguated_clf_term_patterns_list xs
              inner_bound_variables pattern_variables'
              (fun terms' inner_bound_variables' pattern_variables'' ->
                f
                  { Synext.CLF.Substitution.Pattern.location
                  ; head = head'
                  ; terms = terms'
                  }
                  inner_bound_variables' pattern_variables'')
        | Synprs.CLF.Object.Raw_identifier
            { location; identifier = identifier, `Dollar; _ }
            (* A substitution variable *)
          :: xs ->
            let head' =
              Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                { location; identifier; closure = Option.none }
            in
            let pattern_variables' =
              if Identifier.Hamt.mem identifier inner_bound_variables then
                pattern_variables
              else identifier :: pattern_variables
            in
            with_disambiguated_clf_term_patterns_list xs
              inner_bound_variables pattern_variables'
              (fun terms' inner_bound_variables' pattern_variables'' ->
                f
                  { Synext.CLF.Substitution.Pattern.location
                  ; head = head'
                  ; terms = terms'
                  }
                  inner_bound_variables' pattern_variables'')
        | _ ->
            let head' =
              Synext.CLF.Substitution.Pattern.Head.None
                { location = head_location }
            in
            with_disambiguated_clf_term_patterns_list objects'
              inner_bound_variables pattern_variables
              (fun terms' inner_bound_variables' pattern_variables' ->
                f
                  { Synext.CLF.Substitution.Pattern.location
                  ; head = head'
                  ; terms = terms'
                  }
                  inner_bound_variables' pattern_variables'))
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let head' =
          Synext.CLF.Substitution.Pattern.Head.Identity
            { location = head_location }
        in
        with_disambiguated_clf_term_patterns_list objects'
          inner_bound_variables pattern_variables
          (fun terms' inner_bound_variables' pattern_variables' ->
            f
              { Synext.CLF.Substitution.Pattern.location
              ; head = head'
              ; terms = terms'
              }
              inner_bound_variables' pattern_variables')

  and with_disambiguated_context_pattern_binding :
      type a.
         Identifier.t option * Synprs.clf_object
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Identifier.t * Synext.clf_typ
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun binding inner_bound_variables pattern_variables f ->
    match binding with
    | Option.Some identifier, typ ->
        let* typ' = disambiguate_clf_typ typ in
        with_lf_term_variable identifier
          (let y = (identifier, typ') in
           f y
             (push_binding identifier inner_bound_variables)
             (identifier :: pattern_variables))
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
      type a.
         (Identifier.t option * Synprs.clf_object) list
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   (Identifier.t * Synext.clf_typ) list
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun bindings inner_bound_variables pattern_variables f ->
    match bindings with
    | [] -> f [] inner_bound_variables pattern_variables
    | x :: xs ->
        with_disambiguated_context_pattern_binding x inner_bound_variables
          pattern_variables
          (fun y inner_bound_variables' pattern_variables' ->
            with_disambiguated_context_pattern_bindings_list xs
              inner_bound_variables' pattern_variables'
              (fun ys inner_bound_variables'' pattern_variables'' ->
                f (y :: ys) inner_bound_variables'' pattern_variables''))

  and with_disambiguated_clf_context_pattern :
      type a.
         Synprs.clf_context_object
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.clf_context_pattern
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun context_pattern inner_bound_variables pattern_variables f ->
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
              inner_bound_variables pattern_variables
              (fun bindings' inner_bound_variables' pattern_variables' ->
                f
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  }
                  inner_bound_variables' pattern_variables')
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* Possibly a context variable as context head *)
          :: bindings -> (
            lookup_toplevel identifier >>= function
            | Result.Ok (Context_variable _) ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                in
                if Identifier.Hamt.mem identifier inner_bound_variables then
                  with_disambiguated_context_pattern_bindings_list bindings
                    inner_bound_variables pattern_variables
                    (fun bindings' inner_bound_variables' pattern_variables''
                    ->
                      f
                        { Synext.CLF.Context.Pattern.location
                        ; head = head'
                        ; bindings = bindings'
                        }
                        inner_bound_variables' pattern_variables'')
                else
                  with_context_variable identifier
                    (with_disambiguated_context_pattern_bindings_list
                       bindings inner_bound_variables
                       (identifier :: pattern_variables)
                       (fun
                         bindings'
                         inner_bound_variables'
                         pattern_variables''
                       ->
                         f
                           { Synext.CLF.Context.Pattern.location
                           ; head = head'
                           ; bindings = bindings'
                           }
                           inner_bound_variables' pattern_variables''))
            | Result.Error (Unbound_identifier _) ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                in
                with_context_variable identifier
                  (with_disambiguated_context_pattern_bindings_list bindings
                     inner_bound_variables (identifier :: pattern_variables)
                     (fun bindings' inner_bound_variables' pattern_variables'
                     ->
                       f
                         { Synext.CLF.Context.Pattern.location
                         ; head = head'
                         ; bindings = bindings'
                         }
                         inner_bound_variables' pattern_variables'))
            | Result.Ok _ ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.None
                    { location = head_location }
                in
                with_disambiguated_context_pattern_bindings_list bindings
                  inner_bound_variables pattern_variables
                  (fun bindings' inner_bound_variables' pattern_variables' ->
                    f
                      { Synext.CLF.Context.Pattern.location
                      ; head = head'
                      ; bindings = bindings'
                      }
                      inner_bound_variables' pattern_variables')
            | Result.Error cause ->
                Error.raise_at1 (Identifier.location identifier) cause)
        | _ ->
            let head' =
              Synext.CLF.Context.Pattern.Head.None
                { location = head_location }
            in
            with_disambiguated_context_pattern_bindings_list objects
              inner_bound_variables pattern_variables
              (fun bindings' inner_bound_variables' pattern_variables' ->
                f
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  }
                  inner_bound_variables' pattern_variables'))
end

let pp_exception ppf = function
  | Illegal_hole_clf_type ->
      Format.fprintf ppf "Holes may not appear as contextual LF types."
  | Illegal_lambda_clf_type ->
      Format.fprintf ppf "Lambdas may not appear as contextual LF types."
  | Illegal_annotated_clf_type ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF types."
  | Illegal_untyped_pi_clf_type ->
      Format.fprintf ppf
        "The contextual LF Pi type is missing its parameter type annotation."
  | Illegal_tuple_clf_type ->
      Format.fprintf ppf "Tuple terms may not appear as contextual LF types."
  | Illegal_projection_clf_type ->
      Format.fprintf ppf
        "Projection terms may not appear as contextual LF types."
  | Illegal_substitution_clf_type ->
      Format.fprintf ppf
        "Substitution terms may not appear as contextual LF types."
  | Illegal_unnamed_block_element_clf_type ->
      Format.fprintf ppf
        "Contextual LF block type element missing an identifier."
  | Illegal_parameter_variable_clf_type ->
      Format.fprintf ppf
        "Parameter variables may not appear as contextual LF types."
  | Illegal_substitution_variable_clf_type ->
      Format.fprintf ppf
        "Substitution variables may not appear as contextual LF types."
  | Unbound_clf_type_constant identifier ->
      Format.fprintf ppf "The LF type-level constant %a is unbound."
        Qualified_identifier.pp identifier
  | Unbound_type_constant_or_illegal_projection_clf_type identifier ->
      Format.fprintf ppf
        "Either the LF type-level constant %a is unbound, or a projection \
         term may not appear as a contextual LF type."
        Qualified_identifier.pp identifier
  | Illegal_pi_clf_term ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF terms."
  | Illegal_forward_arrow_clf_term ->
      Format.fprintf ppf
        "Forward arrows may not appear as contextual LF terms."
  | Illegal_backward_arrow_clf_term ->
      Format.fprintf ppf
        "Backward arrows may not appear as contextual LF terms."
  | Illegal_block_clf_term ->
      Format.fprintf ppf "Block types may not appear as contextual LF terms."
  | Unbound_clf_term_constant identifier ->
      Format.fprintf ppf "The LF term-level constant %a is unbound."
        Qualified_identifier.pp identifier
  | Illegal_clf_term_projection ->
      Format.fprintf ppf "Illegal contextual LF projection(s)."
  | Illegal_clf_subtitution_term_label ->
      Format.fprintf ppf "Terms in a substitution may not be labelled."
  | Illegal_clf_context_parameter_variable_binding ->
      Format.fprintf ppf
        "Parameter variable bindings may not occur in contextual LF \
         contexts."
  | Illegal_clf_context_substitution_variable_binding ->
      Format.fprintf ppf
        "Substitution variable bindings may not occur in contextual LF \
         contexts."
  | Illegal_clf_context_missing_binding_identifier ->
      Format.fprintf ppf
        "Identifier missing for the binding in the contextual LF context."
  | Illegal_clf_context_identity ->
      Format.fprintf ppf
        "Contextual LF contexts may not begin with the identity \
         substitution."
  | Expected_clf_term_constant ->
      Format.fprintf ppf "Expected an LF term-level constant."
  | Expected_clf_type_constant ->
      Format.fprintf ppf "Expected an LF type-level constant."
  | Ambiguous_clf_operator_placement operator_identifier ->
      Format.fprintf ppf
        "Ambiguous occurrences of the LF term-level or type-level operator \
         %a after rewriting."
        Qualified_identifier.pp operator_identifier
  | Misplaced_clf_operator ->
      Format.fprintf ppf
        "Misplaced contextual LF term-level or type-level operator."
  | Consecutive_applications_of_non_associative_clf_operators
      operator_identifier ->
      Format.fprintf ppf
        "Consecutive occurrences of the contextual LF term-level or \
         type-level operator %a after rewriting."
        Qualified_identifier.pp operator_identifier
  | Clf_arity_mismatch
      { operator_identifier
      ; expected_arguments_count
      ; actual_arguments_count
      } ->
      Format.fprintf ppf "Operator %a expected %d arguments but got %d."
        Qualified_identifier.pp operator_identifier expected_arguments_count
        actual_arguments_count
  | Illegal_pi_clf_term_pattern ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF term patterns."
  | Illegal_forward_arrow_clf_term_pattern ->
      Format.fprintf ppf
        "Forward arrow types may not appear as contextual LF term patterns."
  | Illegal_backward_arrow_clf_term_pattern ->
      Format.fprintf ppf
        "Backward arrow types may not appear as contextual LF term patterns."
  | Illegal_block_clf_term_pattern ->
      Format.fprintf ppf
        "Block types may not appear as contextual LF term patterns."
  | Illegal_labellable_hole_term_pattern ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF term patterns."
  | Illegal_subtitution_clf_pattern_term_label ->
      Format.fprintf ppf
        "Terms in a substitution pattern may not be labelled."
  | Illegal_clf_context_pattern_missing_binding_type ->
      Format.fprintf ppf
        "Contextual LF context pattern bindings require type annotations."
  | Illegal_clf_context_pattern_parameter_variable_binding ->
      Format.fprintf ppf
        "Parameter variable bindings may not occur in contextual LF context \
         patterns."
  | Illegal_clf_context_pattern_substitution_variable_binding ->
      Format.fprintf ppf
        "Substitution variable bindings may not occur in contextual LF \
         context patterns."
  | Illegal_clf_context_pattern_missing_binding_identifier ->
      Format.fprintf ppf
        "Identifier missing for the binding in the contextual LF context \
         pattern."
  | Illegal_clf_context_pattern_identity ->
      Format.fprintf ppf
        "Contextual LF context patterns may not begin with the identity \
         substitution."
  | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
