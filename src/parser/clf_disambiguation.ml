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

exception Illegal_hole_type

exception Illegal_lambda_type

exception Illegal_annotated_type

exception Illegal_untyped_pi_type

exception Illegal_tuple_type

exception Illegal_projection_type

exception Illegal_substitution_type

exception Illegal_unnamed_block_element_type

exception Illegal_parameter_variable_type

exception Illegal_substitution_variable_type

exception Unbound_type_constant of Qualified_identifier.t

exception
  Unbound_type_constant_or_illegal_projection_type of Qualified_identifier.t

(** {2 Exceptions for contextual LF term disambiguation} *)

exception Illegal_pi_term

exception Illegal_forward_arrow_term

exception Illegal_backward_arrow_term

exception Illegal_block_term

exception Unbound_term_constant of Qualified_identifier.t

(** {2 Exceptions for contextual LF substitution disambiguation} *)

exception Illegal_subtitution_term_label

(** {2 Exceptions for contextual LF context disambiguation} *)

exception Illegal_context_parameter_variable_binding

exception Illegal_context_substitution_variable_binding

exception Illegal_context_missing_binding_identifier

exception Illegal_context_identity

(** {2 Exceptions for application rewriting} *)

exception Expected_term_constant

exception Expected_type_constant

exception Expected_term

exception Expected_type

exception Expected_term_pattern

exception Expected_type_pattern

exception Misplaced_operator

exception Ambiguous_operator_placement of Qualified_identifier.t

exception
  Consecutive_applications_of_non_associative_operators of
    Qualified_identifier.t

exception
  Arity_mismatch of
    { operator_identifier : Qualified_identifier.t
    ; expected_arguments_count : Int.t
    ; actual_arguments_count : Int.t
    }

(** {2 Exceptions for contextual LF type pattern disambiguation} *)

exception Illegal_wildcard_type_pattern

exception Illegal_labellable_hole_type_pattern

exception Illegal_lambda_type_pattern

exception Illegal_annotated_type_pattern

exception Illegal_untyped_pi_type_pattern

exception Illegal_tuple_type_pattern

exception Illegal_projection_type_pattern

exception Illegal_substitution_type_pattern

exception Illegal_unnamed_block_element_type_pattern

(** {2 Exceptions for contextual LF term pattern disambiguation} *)

exception Illegal_pi_term_pattern

exception Illegal_forward_arrow_term_pattern

exception Illegal_backward_arrow_term_pattern

exception Illegal_block_term_pattern

exception Illegal_labellable_hole_term_pattern

(** {2 Exceptions for contextual LF substitution pattern disambiguation} *)

exception Illegal_subtitution_pattern_term_label

(** {2 Exceptions for contextual LF context pattern disambiguation} *)

exception Illegal_context_pattern_missing_binding_type

exception Illegal_context_pattern_parameter_variable_binding

exception Illegal_context_pattern_substitution_variable_binding

exception Illegal_context_pattern_missing_binding_identifier

exception Illegal_context_pattern_identity

(** {1 Disambiguation} *)

module type CLF_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Disambiguation} *)

  val disambiguate_as_typ :
       Synprs.clf_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_typ

  val disambiguate_as_term :
       Synprs.clf_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_term

  val disambiguate_as_substitution :
       Synprs.clf_context_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_substitution

  val disambiguate_as_context :
       Synprs.clf_context_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_context

  val disambiguate_as_term_pattern :
       Synprs.clf_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_term_pattern

  val disambiguate_as_substitution_pattern :
       Synprs.clf_context_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_substitution_pattern

  val disambiguate_as_context_pattern :
       Synprs.clf_context_object
    -> disambiguation_state
    -> disambiguation_state * Synext.clf_context_pattern
end

(** Disambiguation of contextual LF types, terms and patterns from the parser
    syntax to the external syntax.

    This disambiguation does not perform normalization nor validation. *)
module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  CLF_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  include State.Make (Disambiguation_state)

  (** {1 Disambiguation} *)

  (** [resolve_lf_operator state ~quoted identifier] determines whether
      [identifier] is an LF type-level or term-level operator in [state], and
      whether it is quoted. *)
  let resolve_lf_operator state ~quoted identifier =
    match Disambiguation_state.lookup identifier state with
    | Disambiguation_state.LF_type_constant { operator } ->
        if quoted then `Quoted_type_operator
        else `Type_operator (identifier, operator)
    | Disambiguation_state.LF_term_constant { operator } ->
        if quoted then `Quoted_term_operator
        else `Term_operator (identifier, operator)
    | _
    | (exception Disambiguation_state.Unbound_identifier _) ->
        `Not_an_operator

  (** [identifier_lf_operator state term] identifies whether [term] is an LF
      type-level or term-level operator in [state] while accounting for
      operator quoting. If a bound operator appears in parentheses, then it
      is quoted, meaning that the operator appears either in prefix notation
      or as an argument to another application. *)
  let identify_lf_operator state term =
    match term with
    | Synprs.CLF.Object.Raw_identifier
        { identifier = identifier, _modifier; quoted; _ } ->
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        resolve_lf_operator state ~quoted qualified_identifier
    | Synprs.CLF.Object.Raw_qualified_identifier { identifier; quoted; _ } ->
        resolve_lf_operator state ~quoted identifier
    | _ -> `Not_an_operator

  (** Contextual LF term-level or type-level operands for rewriting of
      prefix, infix and postfix operators using {!Shunting_yard}. *)
  module CLF_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext.clf_typ
          (** A disambiguated contextual LF type. *)
      | External_term of Synext.CLF.Term.t
          (** A disambiguated contextual LF term. *)
      | Parser_object of Synprs.clf_object
          (** A contextual LF object that has yet to be disambiguated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.clf_object | `Term of Synprs.clf_object ]
          ; arguments : Synprs.clf_object List.t
          }  (** A contextual LF type-level or term-level application. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext.location_of_clf_typ t
      | External_term t -> Synext.location_of_clf_term t
      | Parser_object t -> Synprs.location_of_clf_object t
      | Application { applicand; arguments } ->
          let applicand_location =
            match applicand with
            | `Typ applicand
            | `Term applicand ->
                Synprs.location_of_clf_object applicand
          in
          Location.join_all_contramap Synprs.location_of_clf_object
            applicand_location arguments
  end

  (** Contextual LF term-level or type-level operators for rewriting of
      prefix, infix and postfix operators using {!Shunting_yard}. *)
  module CLF_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : Qualified_identifier.t
          ; operator : Operator.t
          ; applicand : Synprs.clf_object
          }
          (** A contextual LF type-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)
      | Term_constant of
          { identifier : Qualified_identifier.t
          ; operator : Operator.t
          ; applicand : Synprs.clf_object
          }
          (** A contextual LF term-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ }
      | Term_constant { operator; _ } ->
          operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ }
      | Term_constant { applicand; _ } ->
          applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ }
      | Term_constant { identifier; _ } ->
          identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.location_of_clf_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module Qualified_identifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [disambiguate_as_typ object_ state] is [object_] rewritten as a
      contextual LF type with respect to the disambiguation context [state].

      Type applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification. *)
  let rec disambiguate_as_typ object_ =
    match object_ with
    | Synprs.CLF.Object.Raw_hole { location; _ } ->
        Error.raise_at1 location Illegal_hole_type
    | Synprs.CLF.Object.Raw_lambda { location; _ } ->
        Error.raise_at1 location Illegal_lambda_type
    | Synprs.CLF.Object.Raw_annotated { location; _ } ->
        Error.raise_at1 location Illegal_annotated_type
    | Synprs.CLF.Object.Raw_pi { location; parameter_sort = Option.None; _ }
      ->
        Error.raise_at1 location Illegal_untyped_pi_type
    | Synprs.CLF.Object.Raw_tuple { location; _ } ->
        Error.raise_at1 location Illegal_tuple_type
    | Synprs.CLF.Object.Raw_projection { location; _ } ->
        Error.raise_at1 location Illegal_projection_type
    | Synprs.CLF.Object.Raw_substitution { location; _ } ->
        Error.raise_at1 location Illegal_substitution_type
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Hash; _ } ->
        Error.raise_at1 location Illegal_parameter_variable_type
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Dollar; _ } ->
        Error.raise_at1 location Illegal_substitution_variable_type
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF type, plain identifiers are necessarily type-level
           constants. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        get >>= fun state ->
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            return
              (Synext.CLF.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | _entry -> Error.raise_at1 location Expected_type_constant
        | exception Disambiguation_state.Unbound_identifier _ ->
            Error.raise_at1 location
              (Unbound_type_constant qualified_identifier))
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers. *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As an LF type, identifiers of the form [<identifier>
           <dot-identifier>+] are type-level constants, or illegal named
           projections. *)
        get >>= fun state ->
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            return
              (Synext.CLF.Typ.Constant
                 { location; identifier; operator; quoted })
        | _entry -> Error.raise_at1 location Expected_type_constant
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            Error.raise_at1 location
              (Unbound_type_constant_or_illegal_projection_type identifier))
    | Synprs.CLF.Object.Raw_arrow { location; domain; range; orientation } ->
        let* domain' = disambiguate_as_typ domain in
        let* range' = disambiguate_as_typ range in
        return
          (Synext.CLF.Typ.Arrow
             { location; domain = domain'; range = range'; orientation })
    | Synprs.CLF.Object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
        let* parameter_type' = disambiguate_as_typ parameter_type in
        match parameter_identifier with
        | Option.None ->
            let* body' = disambiguate_as_typ body in
            return
              (Synext.CLF.Typ.Pi
                 { location
                 ; parameter_identifier
                 ; parameter_type = parameter_type'
                 ; body = body'
                 })
        | Option.Some parameter ->
            let* body' =
              locally
                (Disambiguation_state.add_lf_term_variable parameter)
                (disambiguate_as_typ body)
            in
            return
              (Synext.CLF.Typ.Pi
                 { location
                 ; parameter_identifier
                 ; parameter_type = parameter_type'
                 ; body = body'
                 }))
    | Synprs.CLF.Object.Raw_application { objects; _ } -> (
        disambiguate_application objects >>= function
        | `Term term ->
            let location = Synext.location_of_clf_term term in
            Error.raise_at1 location Expected_type
        | `Typ typ -> return typ)
    | Synprs.CLF.Object.Raw_block
        { location; elements = List1.T ((Option.None, t), []) } ->
        let* t' = disambiguate_as_typ t in
        return (Synext.CLF.Typ.Block { location; elements = `Unnamed t' })
    | Synprs.CLF.Object.Raw_block { location; elements } ->
        get >>= fun state ->
        let _state', elements_rev' =
          List1.fold_left
            (fun element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  Error.raise_at1 location Illegal_unnamed_block_element_type
              | Option.Some identifier, typ ->
                  let _state', typ' = disambiguate_as_typ typ state in
                  let elements' = List1.singleton (identifier, typ')
                  and state'' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state
                  in
                  (state'', elements'))
            (fun (state', elements') element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  Error.raise_at1 location Illegal_unnamed_block_element_type
              | Option.Some identifier, typ ->
                  let _state'', typ' = disambiguate_as_typ typ state' in
                  let elements'' = List1.cons (identifier, typ') elements'
                  and state''' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state'
                  in
                  (state''', elements''))
            elements
        in
        let elements' = List1.rev elements_rev' in
        return
          (Synext.CLF.Typ.Block { location; elements = `Record elements' })

  (** [disambiguate_as_term object_ state] is [object_] rewritten as a
      contextual LF term with respect to the disambiguation context [state].

      Term applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification. *)
  and disambiguate_as_term object_ =
    match object_ with
    | Synprs.CLF.Object.Raw_pi { location; _ } ->
        Error.raise_at1 location Illegal_pi_term
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        Error.raise_at1 location Illegal_forward_arrow_term
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_term
    | Synprs.CLF.Object.Raw_block { location; _ } ->
        Error.raise_at1 location Illegal_block_term
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
        get >>= fun state ->
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            return
              (Synext.CLF.Term.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Disambiguation_state.LF_term_variable
        | Disambiguation_state.Meta_variable ->
            (* Bound variable *)
            return (Synext.CLF.Term.Variable { location; identifier })
        | _entry -> Error.raise_at1 location Expected_term_constant
        | exception Disambiguation_state.Unbound_identifier _ ->
            (* Free variable *)
            return (Synext.CLF.Term.Variable { location; identifier }))
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
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
        let reduce_projections' base projections last_projection =
          let sub_term = reduce_projections base projections in
          let location =
            Location.join
              (Synext.location_of_clf_term sub_term)
              (Identifier.location last_projection)
          in
          Synext.CLF.Term.Projection
            { location
            ; term = sub_term
            ; projection = `By_identifier last_projection
            }
        in
        let modules = Qualified_identifier.modules identifier
        and name = Qualified_identifier.name identifier in
        get >>= fun state ->
        match modules with
        | [] ->
            (* Qualified identifiers without modules were parsed as plain
               identifiers *)
            Error.violation
              "[disambiguate_as_term] encountered a qualified identifier \
               without modules."
        | m :: ms -> (
            match Disambiguation_state.lookup_toplevel m state with
            | Disambiguation_state.Module _ ->
                let rec helper state looked_up_identifiers next_identifier
                    remaining_identifiers =
                  match Identifier.Hamt.find_opt next_identifier state with
                  | Option.Some
                      (List1.T
                        ( Disambiguation_state.Module { entries = state' }
                        , _rest )) -> (
                      match remaining_identifiers with
                      | [] ->
                          (* Lookups ended with a module. *)
                          Error.raise_at1 location Expected_term_constant
                      | next_identifier' :: remaining_identifiers' ->
                          let looked_up_identifiers' =
                            next_identifier :: looked_up_identifiers
                          in
                          helper state' looked_up_identifiers'
                            next_identifier' remaining_identifiers')
                  | Option.Some
                      (List1.T
                        ( Disambiguation_state.LF_term_constant { operator }
                        , _rest )) -> (
                      (* Lookups ended with an LF term constant. The
                         remaining identifiers are named projections. *)
                      match remaining_identifiers with
                      | [] ->
                          (* The overall qualified identifier has no
                             projections. In this case, it may be quoted. *)
                          Synext.CLF.Term.Constant
                            { location; identifier; operator; quoted }
                      | _ ->
                          (* The qualified identifier has projections. It
                             cannot be quoted. *)
                          let identifier =
                            Qualified_identifier.make
                              ~modules:(List.rev looked_up_identifiers)
                              next_identifier
                          in
                          let location =
                            Qualified_identifier.location identifier
                          in
                          let term =
                            Synext.CLF.Term.Constant
                              { location
                              ; identifier
                              ; operator
                              ; quoted = false
                              }
                          in
                          reduce_projections term remaining_identifiers)
                  | Option.Some _entry ->
                      (* Lookups ended with an entry that cannot be used in a
                         contextual LF term projection. *)
                      let location =
                        Location.join_all1_contramap Identifier.location
                          (List1.from next_identifier looked_up_identifiers)
                      in
                      Error.raise_at1 location Expected_term_constant
                      (* TODO: Misleading, modules are allowed as well *)
                  | Option.None -> (
                      match remaining_identifiers with
                      | [] ->
                          Error.raise_at1 location
                            (Unbound_term_constant identifier)
                      | _ ->
                          let module_identifier =
                            Qualified_identifier.make
                              ~modules:(List.rev looked_up_identifiers)
                              next_identifier
                          in
                          raise
                            (Disambiguation_state.Unbound_namespace
                               module_identifier))
                in
                return
                  (helper
                     (Disambiguation_state.get_bindings state)
                     [] m (ms @ [ name ]))
            | Disambiguation_state.LF_term_constant { operator } ->
                (* Immediately looked up an LF term constant. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let identifier = Qualified_identifier.make_simple m in
                let term =
                  Synext.CLF.Term.Constant
                    { identifier; location; operator; quoted = false }
                in
                return (reduce_projections' term ms name)
            | Disambiguation_state.LF_term_variable
            | Disambiguation_state.Meta_variable ->
                (* Immediately looked up an LF term variable or a
                   meta-variable. The remaining identifiers are named
                   projections. *)
                let location = Identifier.location m in
                let term =
                  Synext.CLF.Term.Variable { location; identifier = m }
                in
                return (reduce_projections' term ms name)
            | _entry ->
                (* First lookup ended with an entry that cannot be used in a
                   contextual LF term projection. *)
                let location = Identifier.location m in
                Error.raise_at1 location Expected_term_constant
                (* TODO: Misleading, module, term variable, meta-variable are
                   allowed *)
            | exception Disambiguation_state.Unbound_identifier _ ->
                (* Immediately looked up a free variable. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let term =
                  Synext.CLF.Term.Variable { location; identifier = m }
                in
                return (reduce_projections' term ms name)))
    | Synprs.CLF.Object.Raw_application { objects; _ } -> (
        disambiguate_application objects >>= function
        | `Typ typ ->
            let location = Synext.location_of_clf_typ typ in
            Error.raise_at1 location Expected_term
        | `Term term -> return term)
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let* parameter_type' =
          match parameter_sort with
          | Option.None -> return Option.none
          | Option.Some parameter_sort ->
              let* parameter_typ' = disambiguate_as_typ parameter_sort in
              return (Option.some parameter_typ')
        in
        match parameter_identifier with
        | Option.None ->
            let* body' = disambiguate_as_term body in
            return
              (Synext.CLF.Term.Abstraction
                 { location
                 ; parameter_identifier
                 ; parameter_type = parameter_type'
                 ; body = body'
                 })
        | Option.Some name ->
            let* body' =
              locally
                (Disambiguation_state.add_lf_term_variable name)
                (disambiguate_as_term body)
            in
            return
              (Synext.CLF.Term.Abstraction
                 { location
                 ; parameter_identifier
                 ; parameter_type = parameter_type'
                 ; body = body'
                 }))
    | Synprs.CLF.Object.Raw_hole { location; variant } ->
        return (Synext.CLF.Term.Hole { location; variant })
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        get >>= fun state ->
        let elements' =
          List1.map
            (fun element ->
              let _state', element' = disambiguate_as_term element state in
              element')
            elements
        in
        return (Synext.CLF.Term.Tuple { location; terms = elements' })
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let* term' = disambiguate_as_term object_ in
        return
          (Synext.CLF.Term.Projection { location; term = term'; projection })
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let* term' = disambiguate_as_term object_ in
        let* substitution' = disambiguate_as_substitution substitution in
        return
          (Synext.CLF.Term.Substitution
             { location; term = term'; substitution = substitution' })
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let* term' = disambiguate_as_term object_ in
        let* typ' = disambiguate_as_typ sort in
        return
          (Synext.CLF.Term.TypeAnnotated
             { location; term = term'; typ = typ' })

  and disambiguate_as_substitution substitution state =
    let { Synprs.CLF.Context_object.location; head; objects } =
      substitution
    in
    let objects' =
      List.map
        (function
          | Option.None, object_ -> object_
          | Option.Some identifier, _ ->
              let location = Identifier.location identifier in
              Error.raise_at1 location Illegal_subtitution_term_label)
        objects
    in
    match head with
    | Synprs.CLF.Context_object.Head.None { location = head_location } ->
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
              let closure' =
                eval (disambiguate_as_substitution closure) state
              in
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              in
              (head', xs)
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              let head' =
                Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              in
              (head', xs)
          | _ ->
              let head' =
                Synext.CLF.Substitution.Head.None
                  { location = head_location }
              in
              (head', objects')
        in
        let terms' =
          List.map
            (fun object_ -> eval (disambiguate_as_term object_) state)
            objects''
        in
        let substitution' =
          { Synext.CLF.Substitution.location; head = head'; terms = terms' }
        in
        (state, substitution')
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let terms' =
          List.map
            (fun object_ -> eval (disambiguate_as_term object_) state)
            objects'
        in
        let head' =
          Synext.CLF.Substitution.Head.Identity { location = head_location }
        in
        let substitution' =
          { Synext.CLF.Substitution.location; head = head'; terms = terms' }
        in
        (state, substitution')

  (** [disambiguate_context_bindings bindings state] is [(state', bindings')]
      where [state'] is the disambiguation state derived from [state] with
      the addition of the variables in the domain of [bindings], and
      [bindings'] is the disambiguated context bindings.

      Context variables cannot occur in [bindings]. A context variable in the
      head position of a context is handled in {!disambiguate_as_context}. *)
  and disambiguate_context_bindings bindings state =
    (* Contextual LF contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    let state', bindings_rev' =
      List.fold_left
        (fun (state, bindings_rev') binding ->
          match binding with
          | Option.Some identifier, typ (* Typed binding *) ->
              let typ' = eval (disambiguate_as_typ typ) state in
              let state' =
                Disambiguation_state.add_lf_term_variable identifier state
              and binding' = (identifier, Option.some typ') in
              (state', binding' :: bindings_rev')
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Plain; _ } )
          (* Untyped contextual LF variable *) ->
              let state' =
                Disambiguation_state.add_lf_term_variable identifier state
              and binding' = (identifier, Option.none) in
              (state', binding' :: bindings_rev')
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Hash; _ } )
          (* Parameter variables may only occur in meta-contexts *) ->
              let location = Identifier.location identifier in
              Error.raise_at1 location
                Illegal_context_parameter_variable_binding
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Dollar; _ } )
          (* Substitution variables may only occur in meta-contexts *) ->
              let location = Identifier.location identifier in
              Error.raise_at1 location
                Illegal_context_substitution_variable_binding
          | Option.None, typ (* Binding identifier missing *) ->
              let location = Synprs.location_of_clf_object typ in
              Error.raise_at1 location
                Illegal_context_missing_binding_identifier)
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    (state', bindings')

  (** [disambiguate_as_context context state] is [(state', context')] where
      [state'] is the disambiguation state derived from [state] with the
      addition of the variables in the domain of [context], and [context'] is
      the disambiguated context.

      - If [context] corresponds to [_, x1 : A1, x2 : A2, ..., xn : An], then
        [_] is the omission of the context variable.
      - If [context] corresponds to [g, x1 : A1, x2 : A2, ..., xn : An] where
        [g] occurs in [state] as a context variable, then [g] is the context
        variable for [context'].
      - Bindings in a contextual LF context may omit the typings, meaning
        that [g, x1, x2, ..., xn] is a valid context. However,
        [g, A1, A2, ..., An] is invalid if [A1], [A2], ..., [An] are types
        because their associated identifiers are missing. *)
  and disambiguate_as_context context state =
    let { Synprs.CLF.Context_object.location; head; objects } = context in
    match head with
    | Synprs.CLF.Context_object.Head.Identity { location } ->
        Error.raise_at1 location Illegal_context_identity
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
            let state', bindings' = disambiguate_context_bindings xs state in
            let context' =
              { Synext.CLF.Context.location
              ; head = head'
              ; bindings = bindings'
              }
            in
            (state', context')
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* Possibly a context variable as context head *)
          :: xs -> (
            match Disambiguation_state.lookup_toplevel identifier state with
            | Disambiguation_state.Context_variable ->
                let head' =
                  Synext.CLF.Context.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                and state', bindings' =
                  disambiguate_context_bindings xs state
                in
                let context' =
                  { Synext.CLF.Context.location
                  ; head = head'
                  ; bindings = bindings'
                  }
                in
                (state', context')
            | _
            | (exception Disambiguation_state.Unbound_identifier _) ->
                let head' =
                  Synext.CLF.Context.Head.None { location = head_location }
                in
                let state', bindings' =
                  disambiguate_context_bindings objects state
                in
                let context' =
                  { Synext.CLF.Context.location
                  ; head = head'
                  ; bindings = bindings'
                  }
                in
                (state', context'))
        | _ ->
            (* Context is just a list of bindings without context
               variables *)
            let head' =
              Synext.CLF.Context.Head.None { location = head_location }
            in
            let state', bindings' =
              disambiguate_context_bindings objects state
            in
            let context' =
              { Synext.CLF.Context.location
              ; head = head'
              ; bindings = bindings'
              }
            in
            (state', context'))

  (** [disambiguate_application objects state] disambiguates [objects] as
      either a type-level or term-level contextual LF application with
      respect to the disambiguation context [state].

      In both type-level and term-level contextual LF applications, arguments
      are contextual LF terms.

      This disambiguation is in three steps:

      - First, LF type-level and term-level constants are identified as
        operators (with or without quoting) using [state], and the rest are
        identified as operands.
      - Second, consecutive operands are combined as an application
        (juxtaposition) that has yet to be disambiguated, and written in
        prefix notation with the first operand being the application head.
      - Third, Dijkstra's shunting yard algorithm is used to rewrite the
        identified prefix, infix and postfix operators to applications. *)
  and disambiguate_application objects state =
    let disambiguate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term applicand
        | `Typ applicand ->
            Synprs.location_of_clf_object applicand
      in
      let application_location =
        Location.join_all_contramap Synprs.location_of_clf_object
          applicand_location arguments
      in
      match applicand with
      | `Term applicand ->
          let applicand' = eval (disambiguate_as_term applicand) state in
          let arguments' =
            List1.map
              (fun object_ -> eval (disambiguate_as_term object_) state)
              (List1.unsafe_of_list arguments)
          in
          `Term
            (Synext.CLF.Term.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
      | `Typ applicand ->
          let applicand' = eval (disambiguate_as_typ applicand) state in
          let arguments' =
            List1.map
              (fun object_ -> eval (disambiguate_as_term object_) state)
              (List1.unsafe_of_list arguments)
          in
          `Typ
            (Synext.CLF.Typ.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
    in
    let module Shunting_yard =
      Centiparsec.Shunting_yard.Make (Associativity) (Fixity) (CLF_operand)
        (struct
          type associativity = Associativity.t

          type fixity = Fixity.t

          type operand = CLF_operand.t

          include CLF_operator

          (** [disambiguate_argument argument] disambiguates [argument] to an
              LF term.

              @raise Expected_term *)
          let disambiguate_argument argument =
            match argument with
            | CLF_operand.External_term term -> term
            | CLF_operand.External_typ typ ->
                let location = Synext.location_of_clf_typ typ in
                Error.raise_at1 location Expected_term
            | CLF_operand.Parser_object object_ ->
                eval (disambiguate_as_term object_) state
            | CLF_operand.Application { applicand; arguments } -> (
                match disambiguate_juxtaposition applicand arguments with
                | `Term term -> term
                | `Typ typ ->
                    let location = Synext.location_of_clf_typ typ in
                    Error.raise_at1 location Expected_term)

          let disambiguate_arguments arguments =
            List1.map disambiguate_argument arguments

          let write operator arguments =
            let application_location =
              Location.join_all_contramap CLF_operand.location
                (CLF_operator.location operator)
                arguments
            in
            match operator with
            | CLF_operator.Type_constant { applicand; _ } ->
                let applicand' =
                  eval (disambiguate_as_typ applicand) state
                in
                let arguments' =
                  disambiguate_arguments (List1.unsafe_of_list arguments)
                in
                CLF_operand.External_typ
                  (Synext.CLF.Typ.Application
                     { location = application_location
                     ; applicand = applicand'
                     ; arguments = arguments'
                     })
            | CLF_operator.Term_constant { applicand; _ } ->
                let applicand' =
                  eval (disambiguate_as_term applicand) state
                in
                let arguments' =
                  disambiguate_arguments (List1.unsafe_of_list arguments)
                in
                CLF_operand.External_term
                  (Synext.CLF.Term.Application
                     { location = application_location
                     ; applicand = applicand'
                     ; arguments = arguments'
                     })
        end)
    in
    (* [prepare_objects objects] identifies operators in [objects] and
       rewrites juxtapositions to applications in prefix notation. The
       objects themselves are not disambiguated to LF types or terms yet.
       This is only done in the shunting yard algorithm so that the leftmost
       syntax error gets reported. *)
    let prepare_objects objects =
      (* Predicate for identifying objects that may appear as juxtaposed
         arguments to an application in prefix notation. This predicate does
         not apply to the application head. *)
      let is_argument = function
        | `Not_an_operator, _
        | `Quoted_type_operator, _
        | `Quoted_term_operator, _ ->
            true
        | `Type_operator (_, operator), _
        | `Term_operator (_, operator), _ ->
            Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
            match List.take_while is_argument ts with
            | [], rest (* [t] is an operand not in juxtaposition *) ->
                Shunting_yard.operand (CLF_operand.Parser_object t)
                :: reduce_juxtapositions_and_identify_operators rest
            | arguments, rest
            (* [t] is an applicand in juxtaposition with [arguments] *) ->
                let arguments' = List.map Pair.snd arguments in
                Shunting_yard.operand
                  (CLF_operand.Application
                     { applicand = `Term t; arguments = arguments' })
                :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            Shunting_yard.operand
              (CLF_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            Shunting_yard.operand
              (CLF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
            if Operator.is_prefix operator then
              let arguments, rest = List.take_while is_argument ts in
              let arguments' = List.map Pair.snd arguments in
              Shunting_yard.operand
                (CLF_operand.Application
                   { applicand = `Typ t; arguments = arguments' })
              :: reduce_juxtapositions_and_identify_operators rest
            else
              Shunting_yard.operator
                (CLF_operator.Type_constant
                   { identifier; operator; applicand = t })
              :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
            if Operator.is_prefix operator then
              let arguments, rest = List.take_while is_argument ts in
              let arguments' = List.map Pair.snd arguments in
              Shunting_yard.operand
                (CLF_operand.Application
                   { applicand = `Term t; arguments = arguments' })
              :: reduce_juxtapositions_and_identify_operators rest
            else
              Shunting_yard.operator
                (CLF_operator.Term_constant
                   { identifier; operator; applicand = t })
              :: reduce_juxtapositions_and_identify_operators ts
        | [] -> []
      in
      objects |> List2.to_list
      |> List.map (fun term ->
             let tag = identify_lf_operator state term in
             (tag, term))
      |> reduce_juxtapositions_and_identify_operators
    in
    try
      match Shunting_yard.shunting_yard (prepare_objects objects) with
      | CLF_operand.External_typ t -> (state, `Typ t)
      | CLF_operand.External_term t -> (state, `Term t)
      | CLF_operand.Application { applicand; arguments } ->
          (state, disambiguate_juxtaposition applicand arguments)
      | CLF_operand.Parser_object _ ->
          Error.violation
            "[CLF.disambiguate_application] unexpectedly did not \
             disambiguate LF operands in rewriting"
    with
    | Shunting_yard.Empty_expression ->
        Error.violation
          "[CLF.disambiguate_application] unexpectedly ended with an empty \
           expression"
    | Shunting_yard.Leftover_expressions _ ->
        Error.violation
          "[CLF.disambiguate_application] unexpectedly ended with leftover \
           expressions"
    | Shunting_yard.Misplaced_operator { operator; operands } ->
        let operator_location = CLF_operator.location operator
        and operand_locations = List.map CLF_operand.location operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_operator
    | Shunting_yard.Ambiguous_operator_placement
        { left_operator; right_operator } ->
        let operator_identifier = CLF_operator.identifier left_operator
        and left_operator_location = CLF_operator.location left_operator
        and right_operator_location = CLF_operator.location right_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_operator_placement operator_identifier)
    | Shunting_yard.Consecutive_non_associative_operators
        { left_operator; right_operator } ->
        let operator_identifier = CLF_operator.identifier left_operator
        and left_operator_location = CLF_operator.location left_operator
        and right_operator_location = CLF_operator.location right_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_operators
             operator_identifier)
    | Shunting_yard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = CLF_operator.identifier operator
        and operator_location = CLF_operator.location operator
        and expected_arguments_count = operator_arity
        and operand_locations = List.map CLF_operand.location operands
        and actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })

  (** Contextual LF term-level or type-level pattern operands for rewriting
      of prefix, infix and postfix operators using {!Shunting_yard}. *)
  module CLF_pattern_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext.clf_typ
          (** A disambiguated contextual LF type. *)
      | External_term_pattern of Synext.clf_term_pattern
          (** A disambiguated contextual LF term pattern. *)
      | Parser_object of Synprs.clf_object
          (** A contextual LF object that has yet to be disambiguated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.clf_object
              | `Term_pattern of Synprs.clf_object
              ]
          ; arguments : Synprs.clf_object List.t
          }
          (** A contextual LF type-level or term-level application pattern. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext.location_of_clf_typ t
      | External_term_pattern t -> Synext.location_of_clf_term_pattern t
      | Parser_object t -> Synprs.location_of_clf_object t
      | Application { applicand; arguments } ->
          let applicand_location =
            match applicand with
            | `Typ applicand
            | `Term_pattern applicand ->
                Synprs.location_of_clf_object applicand
          in
          Location.join_all_contramap Synprs.location_of_clf_object
            applicand_location arguments
  end

  (** Contextual LF term-level or type-level pattern operators for rewriting
      of prefix, infix and postfix operators using {!Shunting_yard}. *)
  module CLF_pattern_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : Qualified_identifier.t
          ; operator : Operator.t
          ; applicand : Synprs.clf_object
          }
          (** A contextual LF type-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)
      | Term_constant of
          { identifier : Qualified_identifier.t
          ; operator : Operator.t
          ; applicand : Synprs.clf_object
          }
          (** A contextual LF term-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ }
      | Term_constant { operator; _ } ->
          operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ }
      | Term_constant { applicand; _ } ->
          applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ }
      | Term_constant { identifier; _ } ->
          identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.location_of_clf_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module Qualified_identifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [disambiguate_as_term_pattern object_ state] is [object_] rewritten as
      a contextual LF term pattern with respect to the disambiguation context
      [state].

      Term applications are rewritten with
      {!disambiguate_application_pattern} using Dijkstra's shunting yard
      algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification. *)
  let rec disambiguate_as_term_pattern object_ =
    match object_ with
    | Synprs.CLF.Object.Raw_pi { location; _ } ->
        Error.raise_at1 location Illegal_pi_term_pattern
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        Error.raise_at1 location Illegal_forward_arrow_term_pattern
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_term_pattern
    | Synprs.CLF.Object.Raw_block { location; _ } ->
        Error.raise_at1 location Illegal_block_term_pattern
    | Synprs.CLF.Object.Raw_hole
        { location; variant = `Unlabelled | `Labelled _ } ->
        Error.raise_at1 location Illegal_labellable_hole_term_pattern
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Hash; _ } ->
        return
          (Synext.CLF.Term.Pattern.Parameter_variable
             { location; identifier })
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } ->
        return
          (Synext.CLF.Term.Pattern.Substitution_variable
             { location; identifier })
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, _modifier; quoted; _ } -> (
        (* As an LF term pattern, plain identifiers are either term-level
           constants, variables already present in the pattern, or new
           pattern variables. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        get >>= fun state ->
        match Disambiguation_state.lookup qualified_identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            return
              (Synext.CLF.Term.Pattern.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | _ ->
            return
              (Synext.CLF.Term.Pattern.Variable { location; identifier }))
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
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
        let reduce_projections' base projections last_projection =
          let sub_term = reduce_projections base projections in
          let location =
            Location.join
              (Synext.location_of_clf_term_pattern sub_term)
              (Identifier.location last_projection)
          in
          Synext.CLF.Term.Pattern.Projection
            { location
            ; term = sub_term
            ; projection = `By_identifier last_projection
            }
        in
        let modules = Qualified_identifier.modules identifier
        and name = Qualified_identifier.name identifier in
        get >>= fun state ->
        match modules with
        | [] ->
            (* Qualified identifiers without modules were parsed as plain
               identifiers *)
            Error.violation
              "[disambiguate_as_term_pattern] encountered a qualified \
               identifier without modules."
        | m :: ms -> (
            match Disambiguation_state.lookup_toplevel m state with
            | Disambiguation_state.Module _ ->
                let rec helper state looked_up_identifiers next_identifier
                    remaining_identifiers =
                  match Identifier.Hamt.find_opt next_identifier state with
                  | Option.Some
                      (List1.T
                        ( Disambiguation_state.Module { entries = state' }
                        , _rest )) -> (
                      match remaining_identifiers with
                      | [] ->
                          (* Lookups ended with a module. *)
                          Error.raise_at1 location Expected_term_constant
                      | next_identifier' :: remaining_identifiers' ->
                          let looked_up_identifiers' =
                            next_identifier :: looked_up_identifiers
                          in
                          helper state' looked_up_identifiers'
                            next_identifier' remaining_identifiers')
                  | Option.Some
                      (List1.T
                        ( Disambiguation_state.LF_term_constant { operator }
                        , _rest )) -> (
                      (* Lookups ended with an LF term constant. The
                         remaining identifiers are named projections. *)
                      match remaining_identifiers with
                      | [] ->
                          (* The overall qualified identifier has no
                             projections. In this case, it may be quoted. *)
                          Synext.CLF.Term.Pattern.Constant
                            { location; identifier; operator; quoted }
                      | _ ->
                          (* The qualified identifier has projections. It
                             cannot be quoted. *)
                          let identifier =
                            Qualified_identifier.make
                              ~modules:(List.rev looked_up_identifiers)
                              next_identifier
                          in
                          let location =
                            Qualified_identifier.location identifier
                          in
                          let term =
                            Synext.CLF.Term.Pattern.Constant
                              { location
                              ; identifier
                              ; operator
                              ; quoted = false
                              }
                          in
                          reduce_projections term remaining_identifiers)
                  | Option.Some _entry ->
                      (* Lookups ended with an entry that cannot be used in a
                         contextual LF term projection. *)
                      let location =
                        Location.join_all1_contramap Identifier.location
                          (List1.from next_identifier looked_up_identifiers)
                      in
                      Error.raise_at1 location Expected_term_constant
                  | Option.None -> (
                      match remaining_identifiers with
                      | [] ->
                          Error.raise_at1 location
                            (Unbound_term_constant identifier)
                      | _ ->
                          let module_identifier =
                            Qualified_identifier.make
                              ~modules:(List.rev looked_up_identifiers)
                              next_identifier
                          in
                          raise
                            (Disambiguation_state.Unbound_namespace
                               module_identifier))
                in
                return
                  (helper
                     (Disambiguation_state.get_bindings state)
                     [] m (ms @ [ name ]))
            | Disambiguation_state.LF_term_constant { operator } ->
                (* Immediately looked up an LF term constant. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let identifier = Qualified_identifier.make_simple m in
                let term =
                  Synext.CLF.Term.Pattern.Constant
                    { identifier; location; operator; quoted = false }
                in
                return (reduce_projections' term ms name)
            | Disambiguation_state.LF_term_variable
            | Disambiguation_state.Meta_variable ->
                (* Immediately looked up an LF term variable or a
                   meta-variable. The remaining identifiers are named
                   projections. *)
                let location = Identifier.location m in
                let term =
                  Synext.CLF.Term.Pattern.Variable
                    { location; identifier = m }
                in
                return (reduce_projections' term ms name)
            | _entry ->
                (* First lookup ended with an entry that cannot be used in a
                   contextual LF term projection. *)
                let location = Identifier.location m in
                Error.raise_at1 location Expected_term_constant
                (* TODO: Misleading, module, term variable, meta-variable are
                   allowed *)
            | exception Disambiguation_state.Unbound_identifier _ ->
                (* Immediately looked up a free variable. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let term =
                  Synext.CLF.Term.Pattern.Variable
                    { location; identifier = m }
                in
                return (reduce_projections' term ms name)))
    | Synprs.CLF.Object.Raw_application { objects; _ } -> (
        disambiguate_application_pattern objects >>= function
        | `Typ typ ->
            let location = Synext.location_of_clf_typ typ in
            Error.raise_at1 location Expected_term_pattern
        | `Term_pattern term_pattern -> return term_pattern)
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } ->
        let* parameter_type' =
          match parameter_sort with
          | Option.Some parameter_sort ->
              let* parameter_typ' = disambiguate_as_typ parameter_sort in
              return (Option.some parameter_typ')
          | Option.None -> return Option.none
        in
        let* body' =
          match parameter_identifier with
          | Option.None -> disambiguate_as_term_pattern body
          | Option.Some name ->
              locally
                (Disambiguation_state.add_lf_term_variable name)
                (disambiguate_as_term_pattern body)
        in
        return
          (Synext.CLF.Term.Pattern.Abstraction
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; body = body'
             })
    | Synprs.CLF.Object.Raw_hole { location; variant = `Underscore } ->
        return (Synext.CLF.Term.Pattern.Wildcard { location })
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        get >>= fun state ->
        let elements' =
          List1.map
            (fun element ->
              eval (disambiguate_as_term_pattern element) state)
            elements
        in
        return
          (Synext.CLF.Term.Pattern.Tuple { location; terms = elements' })
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let* term' = disambiguate_as_term_pattern object_ in
        return
          (Synext.CLF.Term.Pattern.Projection
             { location; term = term'; projection })
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let* term' = disambiguate_as_term_pattern object_ in
        let* substitution' = disambiguate_as_substitution substitution in
        return
          (Synext.CLF.Term.Pattern.Substitution
             { location; term = term'; substitution = substitution' })
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let* term' = disambiguate_as_term_pattern object_ in
        let* typ' = disambiguate_as_typ sort in
        return
          (Synext.CLF.Term.Pattern.TypeAnnotated
             { location; term = term'; typ = typ' })

  and disambiguate_as_substitution_pattern substitution_pattern state =
    let { Synprs.CLF.Context_object.location; head; objects } =
      substitution_pattern
    in
    let objects' =
      List.map
        (function
          | Option.None, object_ -> object_
          | Option.Some identifier, _ ->
              let location = Identifier.location identifier in
              Error.raise_at1 location Illegal_subtitution_pattern_term_label)
        objects
    in
    match head with
    | Synprs.CLF.Context_object.Head.None { location = head_location } ->
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
              let closure' =
                eval (disambiguate_as_substitution closure) state
              in
              let head' =
                Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              in
              (head', xs)
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              let head' =
                Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              in
              (head', xs)
          | _ ->
              let head' =
                Synext.CLF.Substitution.Pattern.Head.None
                  { location = head_location }
              in
              (head', objects')
        in
        let terms' =
          List.map
            (fun object_ ->
              eval (disambiguate_as_term_pattern object_) state)
            objects''
        in
        let substitution_pattern' =
          { Synext.CLF.Substitution.Pattern.location
          ; head = head'
          ; terms = terms'
          }
        in
        (state, substitution_pattern')
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let terms' =
          List.map
            (fun object_ ->
              eval (disambiguate_as_term_pattern object_) state)
            objects'
        in
        let head' =
          Synext.CLF.Substitution.Pattern.Head.Identity
            { location = head_location }
        in
        let substitution_pattern' =
          { Synext.CLF.Substitution.Pattern.location
          ; head = head'
          ; terms = terms'
          }
        in
        (state, substitution_pattern')

  and disambiguate_context_pattern_bindings bindings state =
    let _state', bindings_rev' =
      List.fold_left
        (fun (state, bindings_rev') binding ->
          match binding with
          | Option.Some identifier, typ ->
              let typ' = eval (disambiguate_as_typ typ) state in
              let state' =
                Disambiguation_state.add_lf_term_variable identifier state
              and binding' = (identifier, typ') in
              (state', binding' :: bindings_rev')
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Plain; _ } ) ->
              let location = Identifier.location identifier in
              Error.raise_at1 location
                Illegal_context_pattern_missing_binding_type
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Hash; _ } ) ->
              let location = Identifier.location identifier in
              Error.raise_at1 location
                Illegal_context_pattern_parameter_variable_binding
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Dollar; _ } ) ->
              let location = Identifier.location identifier in
              Error.raise_at1 location
                Illegal_context_pattern_substitution_variable_binding
          | Option.None, typ ->
              let location = Synprs.location_of_clf_object typ in
              Error.raise_at1 location
                Illegal_context_pattern_missing_binding_identifier)
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    bindings'

  and disambiguate_as_context_pattern context_pattern state =
    let { Synprs.CLF.Context_object.location; head; objects } =
      context_pattern
    in
    match head with
    | Synprs.CLF.Context_object.Head.Identity { location } ->
        Error.raise_at1 location Illegal_context_pattern_identity
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
        match objects with
        | ( Option.None
          , Synprs.CLF.Object.Raw_hole
              { variant = `Underscore; location = head_location } )
            (* Hole as context head *)
          :: xs ->
            let head' =
              Synext.CLF.Context.Pattern.Head.Hole
                { location = head_location }
            and bindings' = disambiguate_context_pattern_bindings xs state in
            let context' =
              { Synext.CLF.Context.Pattern.location
              ; head = head'
              ; bindings = bindings'
              }
            in
            (state, context')
        | ( Option.None
          , Synprs.CLF.Object.Raw_identifier
              { identifier = identifier, `Plain; _ } )
            (* Possibly a context variable as context head *)
          :: xs -> (
            match Disambiguation_state.lookup_toplevel identifier state with
            | Disambiguation_state.Context_variable ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.Context_variable
                    { identifier; location = Identifier.location identifier }
                and bindings' =
                  disambiguate_context_pattern_bindings xs state
                in
                let context' =
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  }
                in
                (state, context')
            | _
            | (exception Disambiguation_state.Unbound_identifier _) ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.None
                    { location = head_location }
                and bindings' =
                  disambiguate_context_pattern_bindings objects state
                in
                let context' =
                  { Synext.CLF.Context.Pattern.location
                  ; head = head'
                  ; bindings = bindings'
                  }
                in
                (state, context'))
        | _ ->
            let head' =
              Synext.CLF.Context.Pattern.Head.None
                { location = head_location }
            and bindings' =
              disambiguate_context_pattern_bindings objects state
            in
            let context' =
              { Synext.CLF.Context.Pattern.location
              ; head = head'
              ; bindings = bindings'
              }
            in
            (state, context'))

  (** [disambiguate_application_pattern state objects] disambiguates
      [objects] as either a type-level or term-level LF application with
      respect to the disambiguation context [state].

      In both type-level and term-level LF applications, arguments are LF
      terms.

      This disambiguation is in three steps:

      - First, LF type-level and term-level constants are identified as
        operators (with or without quoting) using [state], and the rest are
        identified as operands.
      - Second, consecutive operands are combined as an application
        (juxtaposition) that has yet to be disambiguated, and written in
        prefix notation with the first operand being the application head.
      - Third, Dijkstra's shunting yard algorithm is used to rewrite the
        identified prefix, infix and postfix operators to applications. *)
  and disambiguate_application_pattern objects state =
    let disambiguate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term_pattern applicand
        | `Typ applicand ->
            Synprs.location_of_clf_object applicand
      in
      let application_location =
        Location.join_all_contramap Synprs.location_of_clf_object
          applicand_location arguments
      in
      match applicand with
      | `Term_pattern applicand ->
          let applicand' =
            eval (disambiguate_as_term_pattern applicand) state
          in
          let arguments' =
            List1.map
              (fun argument ->
                eval (disambiguate_as_term_pattern argument) state)
              (List1.unsafe_of_list arguments)
          in
          `Term_pattern
            (Synext.CLF.Term.Pattern.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
      | `Typ applicand ->
          let applicand' = eval (disambiguate_as_typ applicand) state in
          let arguments' =
            List1.map
              (fun argument -> eval (disambiguate_as_term argument) state)
              (List1.unsafe_of_list arguments)
          in
          `Typ
            (Synext.CLF.Typ.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
    in
    let module Shunting_yard =
      Centiparsec.Shunting_yard.Make (Associativity) (Fixity)
        (CLF_pattern_operand)
        (struct
          type associativity = Associativity.t

          type fixity = Fixity.t

          type operand = CLF_pattern_operand.t

          include CLF_pattern_operator

          (** [disambiguate_argument argument] disambiguates [argument] to a
              contextual LF term or term pattern.

              @raise Expected_term_pattern
              @raise Expected_term *)
          let disambiguate_argument argument =
            match argument with
            | CLF_pattern_operand.External_term_pattern term_pattern ->
                let location =
                  Synext.location_of_clf_term_pattern term_pattern
                in
                Error.raise_at1 location Expected_term
            | CLF_pattern_operand.External_typ typ ->
                let location = Synext.location_of_clf_typ typ in
                Error.raise_at1 location Expected_term_pattern
            | CLF_pattern_operand.Parser_object object_ ->
                eval (disambiguate_as_term object_) state
            | CLF_pattern_operand.Application { applicand; arguments } -> (
                match disambiguate_juxtaposition applicand arguments with
                | `Term_pattern term_pattern ->
                    let location =
                      Synext.location_of_clf_term_pattern term_pattern
                    in
                    Error.raise_at1 location Expected_term
                | `Typ typ ->
                    let location = Synext.location_of_clf_typ typ in
                    Error.raise_at1 location Expected_term)

          (** [disambiguate_argument_pattern argument] disambiguates
              [argument] to an LF term pattern.

              @raise Expected_term_pattern *)
          let disambiguate_argument_pattern argument =
            match argument with
            | CLF_pattern_operand.External_term_pattern term_pattern ->
                term_pattern
            | CLF_pattern_operand.External_typ typ ->
                let location = Synext.location_of_clf_typ typ in
                Error.raise_at1 location Expected_term_pattern
            | CLF_pattern_operand.Parser_object object_ ->
                eval (disambiguate_as_term_pattern object_) state
            | CLF_pattern_operand.Application { applicand; arguments } -> (
                match disambiguate_juxtaposition applicand arguments with
                | `Term_pattern term_pattern -> term_pattern
                | `Typ typ ->
                    let location = Synext.location_of_clf_typ typ in
                    Error.raise_at1 location Expected_term_pattern)

          let write operator arguments =
            let application_location =
              Location.join_all_contramap CLF_pattern_operand.location
                (CLF_pattern_operator.location operator)
                arguments
            in
            match operator with
            | CLF_pattern_operator.Type_constant { applicand; _ } ->
                let applicand' =
                  eval (disambiguate_as_typ applicand) state
                in
                let arguments' =
                  List1.map disambiguate_argument
                    (List1.unsafe_of_list arguments)
                in
                CLF_pattern_operand.External_typ
                  (Synext.CLF.Typ.Application
                     { location = application_location
                     ; applicand = applicand'
                     ; arguments = arguments'
                     })
            | CLF_pattern_operator.Term_constant { applicand; _ } ->
                let applicand' =
                  eval (disambiguate_as_term_pattern applicand) state
                in
                let arguments' =
                  List1.map disambiguate_argument_pattern
                    (List1.unsafe_of_list arguments)
                in
                CLF_pattern_operand.External_term_pattern
                  (Synext.CLF.Term.Pattern.Application
                     { location = application_location
                     ; applicand = applicand'
                     ; arguments = arguments'
                     })
        end)
    in
    (* [prepare_objects objects] identifies operators in [objects] and
       rewrites juxtapositions to applications in prefix notation. The
       objects themselves are not disambiguated to LF types or terms yet.
       This is only done in the shunting yard algorithm so that the leftmost
       syntax error gets reported. *)
    let prepare_objects objects =
      (* Predicate for identified objects that may appear as juxtaposed
         arguments to an application in prefix notation. This predicate does
         not apply to the application head. *)
      let is_argument = function
        | `Not_an_operator, _
        | `Quoted_type_operator, _
        | `Quoted_term_operator, _ ->
            true
        | `Type_operator (_, operator), _
        | `Term_operator (_, operator), _ ->
            Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
            match List.take_while is_argument ts with
            | [], rest (* [t] is an operand not in juxtaposition *) ->
                Shunting_yard.operand (CLF_pattern_operand.Parser_object t)
                :: reduce_juxtapositions_and_identify_operators rest
            | arguments, rest
            (* [t] is an applicand in juxtaposition with [arguments] *) ->
                let arguments' = List.map Pair.snd arguments in
                Shunting_yard.operand
                  (CLF_pattern_operand.Application
                     { applicand = `Term_pattern t; arguments = arguments' })
                :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            Shunting_yard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            Shunting_yard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Term_pattern t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
            if Operator.is_prefix operator then
              let arguments, rest = List.take_while is_argument ts in
              let arguments' = List.map Pair.snd arguments in
              Shunting_yard.operand
                (CLF_pattern_operand.Application
                   { applicand = `Typ t; arguments = arguments' })
              :: reduce_juxtapositions_and_identify_operators rest
            else
              Shunting_yard.operator
                (CLF_pattern_operator.Type_constant
                   { identifier; operator; applicand = t })
              :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
            if Operator.is_prefix operator then
              let arguments, rest = List.take_while is_argument ts in
              let arguments' = List.map Pair.snd arguments in
              Shunting_yard.operand
                (CLF_pattern_operand.Application
                   { applicand = `Term_pattern t; arguments = arguments' })
              :: reduce_juxtapositions_and_identify_operators rest
            else
              Shunting_yard.operator
                (CLF_pattern_operator.Term_constant
                   { identifier; operator; applicand = t })
              :: reduce_juxtapositions_and_identify_operators ts
        | [] -> []
      in
      objects |> List2.to_list
      |> List.map (fun term ->
             let tag = identify_lf_operator state term in
             (tag, term))
      |> reduce_juxtapositions_and_identify_operators
    in
    try
      match Shunting_yard.shunting_yard (prepare_objects objects) with
      | CLF_pattern_operand.External_typ t -> (state, `Typ t)
      | CLF_pattern_operand.External_term_pattern t ->
          (state, `Term_pattern t)
      | CLF_pattern_operand.Application { applicand; arguments } ->
          (state, disambiguate_juxtaposition applicand arguments)
      | CLF_pattern_operand.Parser_object _ ->
          Error.violation
            "[CLF.disambiguate_application_pattern] unexpectedly did not \
             disambiguate LF operands in rewriting"
    with
    | Shunting_yard.Empty_expression ->
        Error.violation
          "[CLF.disambiguate_application_pattern] unexpectedly ended with \
           an empty expression"
    | Shunting_yard.Leftover_expressions _ ->
        Error.violation
          "[CLF.disambiguate_application_pattern] unexpectedly ended with \
           leftover expressions"
    | Shunting_yard.Misplaced_operator { operator; operands } ->
        let operator_location = CLF_pattern_operator.location operator
        and operand_locations =
          List.map CLF_pattern_operand.location operands
        in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_operator
    | Shunting_yard.Ambiguous_operator_placement
        { left_operator; right_operator } ->
        let operator_identifier =
          CLF_pattern_operator.identifier left_operator
        and left_operator_location =
          CLF_pattern_operator.location left_operator
        and right_operator_location =
          CLF_pattern_operator.location right_operator
        in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_operator_placement operator_identifier)
    | Shunting_yard.Consecutive_non_associative_operators
        { left_operator; right_operator } ->
        let operator_identifier =
          CLF_pattern_operator.identifier left_operator
        and left_operator_location =
          CLF_pattern_operator.location left_operator
        and right_operator_location =
          CLF_pattern_operator.location right_operator
        in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_operators
             operator_identifier)
    | Shunting_yard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = CLF_pattern_operator.identifier operator
        and operator_location = CLF_pattern_operator.location operator
        and expected_arguments_count = operator_arity
        and operand_locations =
          List.map CLF_pattern_operand.location operands
        and actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
end

(** {2 Exception Printing} *)

let pp_exception ppf = function
  | Illegal_hole_type ->
      Format.fprintf ppf "Holes may not appear as contextual LF types."
  | Illegal_lambda_type ->
      Format.fprintf ppf "Lambdas may not appear as contextual LF types."
  | Illegal_annotated_type ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF types."
  | Illegal_untyped_pi_type ->
      Format.fprintf ppf
        "The contextual LF Pi type is missing its parameter type annotation."
  | Illegal_tuple_type ->
      Format.fprintf ppf "Tuple terms may not appear as contextual LF types."
  | Illegal_projection_type ->
      Format.fprintf ppf
        "Projection terms may not appear as contextual LF types."
  | Illegal_substitution_type ->
      Format.fprintf ppf
        "Substitution terms may not appear as contextual LF types."
  | Illegal_unnamed_block_element_type ->
      Format.fprintf ppf
        "Contextual LF block type element missing an identifier."
  | Illegal_parameter_variable_type ->
      Format.fprintf ppf
        "Parameter variables may not appear as contextual LF types."
  | Illegal_substitution_variable_type ->
      Format.fprintf ppf
        "Substitution variables may not appear as contextual LF types."
  | Unbound_type_constant identifier ->
      Format.fprintf ppf "The LF type-level constant %a is unbound."
        Qualified_identifier.pp identifier
  | Unbound_type_constant_or_illegal_projection_type identifier ->
      Format.fprintf ppf
        "Either the LF type-level constant %a is unbound, or a projection \
         term may not appear as a contextual LF type."
        Qualified_identifier.pp identifier
  | Illegal_pi_term ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF terms."
  | Illegal_forward_arrow_term ->
      Format.fprintf ppf
        "Forward arrows may not appear as contextual LF terms."
  | Illegal_backward_arrow_term ->
      Format.fprintf ppf
        "Backward arrows may not appear as contextual LF terms."
  | Illegal_block_term ->
      Format.fprintf ppf "Block types may not appear as contextual LF terms."
  | Unbound_term_constant identifier ->
      Format.fprintf ppf "The LF term-level constant %a is unbound."
        Qualified_identifier.pp identifier
  | Illegal_subtitution_term_label ->
      Format.fprintf ppf "Terms in a substitution may not be labelled."
  | Illegal_context_parameter_variable_binding ->
      Format.fprintf ppf
        "Parameter variable bindings may not occur in contextual LF \
         contexts."
  | Illegal_context_substitution_variable_binding ->
      Format.fprintf ppf
        "Substitution variable bindings may not occur in contextual LF \
         contexts."
  | Illegal_context_missing_binding_identifier ->
      Format.fprintf ppf
        "Identifier missing for the binding in the contextual LF context."
  | Illegal_context_identity ->
      Format.fprintf ppf
        "Contextual LF contexts may not begin with the identity \
         substitution."
  | Expected_term_constant ->
      Format.fprintf ppf "Expected an LF term-level constant."
  | Expected_type_constant ->
      Format.fprintf ppf "Expected an LF type-level constant."
  | Expected_term ->
      Format.fprintf ppf
        "Expected a contextual LF term but found a contextual LF type \
         instead."
  | Expected_type ->
      Format.fprintf ppf "Expected an LF type but found an LF term instead."
  | Ambiguous_operator_placement operator_identifier ->
      Format.fprintf ppf
        "Ambiguous occurrences of the LF term-level or type-level operator \
         %a after rewriting."
        Qualified_identifier.pp operator_identifier
  | Misplaced_operator ->
      Format.fprintf ppf
        "Misplaced contextual LF term-level or type-level operator."
  | Consecutive_applications_of_non_associative_operators operator_identifier
    ->
      Format.fprintf ppf
        "Consecutive occurrences of the contextual LF term-level or \
         type-level operator %a after rewriting."
        Qualified_identifier.pp operator_identifier
  | Arity_mismatch
      { operator_identifier
      ; expected_arguments_count
      ; actual_arguments_count
      } ->
      Format.fprintf ppf "Operator %a expected %d arguments but got %d."
        Qualified_identifier.pp operator_identifier expected_arguments_count
        actual_arguments_count
  | Expected_term_pattern ->
      Format.fprintf ppf
        "Expected a contextual LF term pattern but found a contextual LF \
         type pattern instead."
  | Expected_type_pattern ->
      Format.fprintf ppf
        "Expected a contextual LF type pattern but found a contextual LF \
         term pattern instead."
  | Illegal_wildcard_type_pattern ->
      Format.fprintf ppf
        "Wildcards may not appear as contextual LF type patterns."
  | Illegal_labellable_hole_type_pattern ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF type patterns."
  | Illegal_lambda_type_pattern ->
      Format.fprintf ppf
        "Lambdas may not appear as contextual LF type patterns."
  | Illegal_annotated_type_pattern ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF type \
         patterns."
  | Illegal_untyped_pi_type_pattern ->
      Format.fprintf ppf
        "The contextual LF Pi type pattern is missing its parameter type \
         annotation."
  | Illegal_tuple_type_pattern ->
      Format.fprintf ppf
        "Tuple term patterns may not appear as contextual LF type patterns."
  | Illegal_projection_type_pattern ->
      Format.fprintf ppf
        "Projection term patterns may not appear as contextual LF type \
         patterns."
  | Illegal_substitution_type_pattern ->
      Format.fprintf ppf
        "Substitution term patterns may not appear as contextual LF type \
         patterns."
  | Illegal_unnamed_block_element_type_pattern ->
      Format.fprintf ppf
        "Contextual LF block type pattern element missing an identifier."
  | Illegal_pi_term_pattern ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF term patterns."
  | Illegal_forward_arrow_term_pattern ->
      Format.fprintf ppf
        "Forward arrow types may not appear as contextual LF term patterns."
  | Illegal_backward_arrow_term_pattern ->
      Format.fprintf ppf
        "Backward arrow types may not appear as contextual LF term patterns."
  | Illegal_block_term_pattern ->
      Format.fprintf ppf
        "Block types may not appear as contextual LF term patterns."
  | Illegal_labellable_hole_term_pattern ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF term patterns."
  | Illegal_subtitution_pattern_term_label ->
      Format.fprintf ppf
        "Terms in a substitution pattern may not be labelled."
  | Illegal_context_pattern_parameter_variable_binding ->
      Format.fprintf ppf
        "Parameter variable bindings may not occur in contextual LF context \
         patterns."
  | Illegal_context_pattern_substitution_variable_binding ->
      Format.fprintf ppf
        "Substitution variable bindings may not occur in contextual LF \
         context patterns."
  | Illegal_context_pattern_missing_binding_identifier ->
      Format.fprintf ppf
        "Identifier missing for the binding in the contextual LF context \
         pattern."
  | Illegal_context_pattern_identity ->
      Format.fprintf ppf
        "Contextual LF context patterns may not begin with the identity \
         substitution."
  | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
