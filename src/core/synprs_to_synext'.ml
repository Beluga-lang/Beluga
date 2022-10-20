open Support

(** Module type for the type state used in disambiguating the parser syntax
    to the external syntax. *)
module type DISAMBIGUATION_STATE = sig
  type t

  type entry = private
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t
    | LF_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_type_constant of Operator.t
    | Computation_term_constructor of Operator.t
    | Computation_cotype_constant of Operator.t
    | Computation_term_destructor
    | Query
    | MQuery

  (** {1 Constructors} *)

  val empty : t

  val add_lf_term_variable : Identifier.t -> t -> t

  val add_prefix_lf_type_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_lf_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_lf_type_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_prefix_lf_term_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_lf_term_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_lf_term_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_meta_variable : Identifier.t -> t -> t

  val add_parameter_variable : Identifier.t -> t -> t

  val add_substitution_variable : Identifier.t -> t -> t

  val add_context_variable : Identifier.t -> t -> t

  val add_schema_constant : Identifier.t -> t -> t

  val add_computation_variable : Identifier.t -> t -> t

  val add_prefix_computation_type_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_computation_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_computation_type_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_prefix_computation_term_constructor :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_computation_term_constructor :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_computation_term_constructor :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_prefix_computation_cotype_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_computation_cotype_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_computation_cotype_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_computation_term_destructor : Identifier.t -> t -> t

  val add_query : Identifier.t -> t -> t

  val add_mquery : Identifier.t -> t -> t

  val add_module :
    entry QualifiedIdentifier.Dictionary.t -> Identifier.t -> t -> t

  (** Getters, setters and mutators *)

  val set_default_associativity : Associativity.t -> t -> t

  val get_default_associativity : t -> Associativity.t

  val get_bindings : t -> entry QualifiedIdentifier.Dictionary.t

  val modify_bindings :
       (   entry QualifiedIdentifier.Dictionary.t
        -> entry QualifiedIdentifier.Dictionary.t)
    -> t
    -> t

  val modify_binding :
       modify_entry:(entry -> entry)
    -> modify_module:
         (   entry QualifiedIdentifier.Dictionary.t
          -> entry QualifiedIdentifier.Dictionary.t)
    -> QualifiedIdentifier.t
    -> t
    -> t

  exception Expected_operator of QualifiedIdentifier.t

  val modify_operator :
    (Operator.t -> Operator.t) -> QualifiedIdentifier.t -> t -> t

  (** {1 Lookup} *)

  val lookup :
    QualifiedIdentifier.t -> t -> entry QualifiedIdentifier.Dictionary.value

  val lookup_toplevel :
    Identifier.t -> t -> entry QualifiedIdentifier.Dictionary.value
end

(** A minimal disambiguation state backed by a dictionary over qualified
    identifiers. *)
module Disambiguation_state : DISAMBIGUATION_STATE = struct
  type t =
    { bindings : entry QualifiedIdentifier.Dictionary.t
    ; default_associativity : Associativity.t
    }

  and entry =
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t
    | LF_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_type_constant of Operator.t
    | Computation_term_constructor of Operator.t
    | Computation_cotype_constant of Operator.t
    | Computation_term_destructor
    | Query
    | MQuery

  let empty =
    { bindings = QualifiedIdentifier.Dictionary.empty
    ; default_associativity = Associativity.non_associative
    }

  let[@inline] set_default_associativity default_associativity state =
    { state with default_associativity }

  let[@inline] get_default_associativity { default_associativity; _ } =
    default_associativity

  let[@inline] set_bindings bindings state = { state with bindings }

  let[@inline] get_bindings { bindings; _ } = bindings

  let[@inline] modify_bindings f state =
    { state with bindings = f state.bindings }

  let add_lf_term_variable identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         LF_term_variable

  let add_prefix_lf_type_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (LF_type_constant operator)

  let add_infix_lf_type_constant ~associativity ~precedence identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (LF_type_constant operator)

  let add_postfix_lf_type_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (LF_type_constant operator)

  let add_prefix_lf_term_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (LF_term_constant operator)

  let add_infix_lf_term_constant ~associativity ~precedence identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (LF_term_constant operator)

  let add_postfix_lf_term_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (LF_term_constant operator)

  let add_meta_variable identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Meta_variable

  let add_parameter_variable identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Parameter_variable

  let add_substitution_variable identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Substitution_variable

  let add_context_variable identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Context_variable

  let add_schema_constant identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Schema_constant

  let add_computation_variable identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Computation_variable

  let add_prefix_computation_type_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_type_constant operator)

  let add_infix_computation_type_constant ~associativity ~precedence
      identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_type_constant operator)

  let add_postfix_computation_type_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_type_constant operator)

  let add_prefix_computation_term_constructor ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_term_constructor operator)

  let add_infix_computation_term_constructor ~associativity ~precedence
      identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_term_constructor operator)

  let add_postfix_computation_term_constructor ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_term_constructor operator)

  let add_prefix_computation_cotype_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_cotype_constant operator)

  let add_infix_computation_cotype_constant ~associativity ~precedence
      identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_cotype_constant operator)

  let add_postfix_computation_cotype_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         (Computation_cotype_constant operator)

  let add_computation_term_destructor identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier
         Computation_term_destructor

  let add_query identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier Query

  let add_mquery identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_entry identifier MQuery

  let add_module module_dictionary identifier =
    modify_bindings
    @@ QualifiedIdentifier.Dictionary.add_toplevel_module identifier
         module_dictionary

  let lookup query state =
    QualifiedIdentifier.Dictionary.lookup query (get_bindings state)

  let lookup_toplevel query state =
    QualifiedIdentifier.Dictionary.lookup_toplevel query (get_bindings state)

  let modify_binding ~modify_entry ~modify_module identifier state =
    match lookup identifier state with
    | QualifiedIdentifier.Dictionary.Entry entry ->
      (modify_bindings
      @@ QualifiedIdentifier.Dictionary.add_entry identifier
           (modify_entry entry))
        state
    | QualifiedIdentifier.Dictionary.Module module_ ->
      (modify_bindings
      @@ QualifiedIdentifier.Dictionary.add_module identifier
           (modify_module module_))
        state

  exception Expected_operator of QualifiedIdentifier.t

  let modify_operator f identifier state =
    modify_binding
      ~modify_entry:(function
        | LF_type_constant operator -> LF_type_constant (f operator)
        | LF_term_constant operator -> LF_term_constant (f operator)
        | Computation_type_constant operator ->
          Computation_type_constant (f operator)
        | Computation_term_constructor operator ->
          Computation_term_constructor (f operator)
        | Computation_cotype_constant operator ->
          Computation_cotype_constant (f operator)
        | LF_term_variable
        | Meta_variable
        | Parameter_variable
        | Substitution_variable
        | Context_variable
        | Schema_constant
        | Computation_variable
        | Computation_term_destructor
        | Query
        | MQuery -> raise @@ Expected_operator identifier)
      ~modify_module:(fun _ -> raise @@ Expected_operator identifier)
      identifier state
end

module type LF_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Exceptions} *)

  (** {2 Exceptions for LF kind disambiguation} *)

  exception Illegal_identifier_kind of Location.t

  exception Illegal_qualified_identifier_kind of Location.t

  exception Illegal_backward_arrow_kind of Location.t

  exception Illegal_hole_kind of Location.t

  exception Illegal_lambda_kind of Location.t

  exception Illegal_annotated_kind of Location.t

  exception Illegal_application_kind of Location.t

  exception Illegal_untyped_pi_kind of Location.t

  (** {2 Exceptions for LF type disambiguation} *)

  exception Illegal_type_kind_type of Location.t

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception
    Unbound_type_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for LF term disambiguation} *)

  exception Illegal_type_kind_term of Location.t

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception Expected_term of Location.t

  exception Expected_type of Location.t

  exception
    Misplaced_operator of
      { operator_location : Location.t
      ; operand_locations : Location.t List.t
      }

  exception
    Ambiguous_operator_placement of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : QualifiedIdentifier.t
      ; operator_location : Location.t
      ; operator_arity : Int.t
      ; actual_argument_locations : Location.t List.t
      }

  exception Too_many_arguments of Location.t

  (** {1 Disambiguation} *)

  val disambiguate_as_kind :
    disambiguation_state -> Synprs.LF.Object.t -> Synext'.LF.Kind.t

  val disambiguate_as_typ :
    disambiguation_state -> Synprs.LF.Object.t -> Synext'.LF.Typ.t

  val disambiguate_as_term :
    disambiguation_state -> Synprs.LF.Object.t -> Synext'.LF.Term.t
end

(** Disambiguation of LF kinds, types and terms from the parser syntax to the
    external syntax.

    This disambiguation does not perform normalization nor validation. *)
module LF (Disambiguation_state : DISAMBIGUATION_STATE) :
  LF_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  (** {1 Exceptions} *)

  (** {2 Exceptions for LF kind disambiguation} *)

  exception Illegal_identifier_kind of Location.t

  exception Illegal_qualified_identifier_kind of Location.t

  exception Illegal_backward_arrow_kind of Location.t

  exception Illegal_hole_kind of Location.t

  exception Illegal_lambda_kind of Location.t

  exception Illegal_annotated_kind of Location.t

  exception Illegal_application_kind of Location.t

  exception Illegal_untyped_pi_kind of Location.t

  (** {2 Exceptions for LF type disambiguation} *)

  exception Illegal_type_kind_type of Location.t

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception
    Unbound_type_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for LF term disambiguation} *)

  exception Illegal_type_kind_term of Location.t

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception Expected_term of Location.t

  exception Expected_type of Location.t

  exception
    Misplaced_operator of
      { operator_location : Location.t
      ; operand_locations : Location.t List.t
      }

  exception
    Ambiguous_operator_placement of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : QualifiedIdentifier.t
      ; operator_location : Location.t
      ; operator_arity : Int.t
      ; actual_argument_locations : Location.t List.t
      }

  exception Too_many_arguments of Location.t

  (** {2 Exception Printing} *)

  let pp_exception ppf = function
    | Illegal_identifier_kind location ->
      Format.fprintf ppf "Identifiers may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_qualified_identifier_kind location ->
      Format.fprintf ppf
        "Qualified identifiers may not appear as LF kinds: %a@." Location.pp
        location
    | Illegal_backward_arrow_kind location ->
      Format.fprintf ppf "Backward arrows may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_hole_kind location ->
      Format.fprintf ppf "Holes may not appear as LF kinds: %a@." Location.pp
        location
    | Illegal_lambda_kind location ->
      Format.fprintf ppf "Lambdas may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_annotated_kind location ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_application_kind location ->
      Format.fprintf ppf "Term applications may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_untyped_pi_kind location ->
      Format.fprintf ppf
        "The LF Pi kind is missing its parameter type annotation: %a@."
        Location.pp location
    | Illegal_type_kind_type location ->
      Format.fprintf ppf "The kind `type' may not appear as LF types: %a@."
        Location.pp location
    | Illegal_hole_type location ->
      Format.fprintf ppf "Holes may not appear as LF types: %a@." Location.pp
        location
    | Illegal_lambda_type location ->
      Format.fprintf ppf "Lambdas may not appear as LF types: %a@."
        Location.pp location
    | Illegal_annotated_type location ->
      Format.fprintf ppf "Type ascriptions may not appear as LF types: %a@."
        Location.pp location
    | Illegal_untyped_pi_type location ->
      Format.fprintf ppf
        "The LF Pi type is missing its parameter type annotation: %a@."
        Location.pp location
    | Unbound_type_constant { location; identifier } ->
      Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Illegal_type_kind_term location ->
      Format.fprintf ppf "The kind `type' may not appear as LF terms: %a@."
        Location.pp location
    | Illegal_pi_term location ->
      Format.fprintf ppf "Pi kinds or types may not appear as LF terms: %a@."
        Location.pp location
    | Illegal_forward_arrow_term location ->
      Format.fprintf ppf "Forward arrows may not appear as LF terms: %a@."
        Location.pp location
    | Illegal_backward_arrow_term location ->
      Format.fprintf ppf "Backward arrows may not appear as LF terms: %a@."
        Location.pp location
    | Unbound_term_constant { location; identifier } ->
      Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.LF_type_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found an LF type constant \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.LF_term_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found an LF term variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Meta_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a meta-variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Parameter_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a parameter variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Substitution_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a substitution \
         variable instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Context_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a context variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         variable instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_type_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         type constant instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_term_constructor _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         term constructor constant instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_cotype_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         cotype constant instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_term_destructor
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         type destructor constant instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry Disambiguation_state.Query
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a logic programming \
         query identifier instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry Disambiguation_state.MQuery
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a logic programming \
         meta-query identifier instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = QualifiedIdentifier.Dictionary.Module _
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a module instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.LF_term_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found an LF term constant \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.LF_term_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found an LF term variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Meta_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a meta-variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Parameter_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a parameter variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Substitution_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a substitution \
         variable instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Context_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a context variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         variable instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_type_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         type constant instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_term_constructor _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         term constructor instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_cotype_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         cotype constant instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_term_destructor
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         term destructor instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry Disambiguation_state.Query
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a logic programming \
         query identifier instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry Disambiguation_state.MQuery
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a logic programming \
         meta-query identifier instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = QualifiedIdentifier.Dictionary.Module _
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a module instead: %a@."
        Location.pp location
    | Expected_term location ->
      Format.fprintf ppf
        "Expected an LF term but found an LF type instead: %a@." Location.pp
        location
    | Expected_type location ->
      Format.fprintf ppf
        "Expected an LF type but found an LF term instead: %a@." Location.pp
        location
    | Misplaced_operator { operator_location; _ } ->
      Format.fprintf ppf
        "Misplaced LF term-level or type-level operator: %a@." Location.pp
        operator_location
    | Ambiguous_operator_placement
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
      Format.fprintf ppf
        "Ambiguous occurrences of the LF term-level or type-level operator \
         %a after rewriting: %a and %a@."
        QualifiedIdentifier.pp operator_identifier Location.pp
        left_operator_location Location.pp right_operator_location
    | Consecutive_non_associative_operators
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
      Format.fprintf ppf
        "Consecutive occurrences of the LF term-level or type-level \
         operator %a after rewriting: %a and %a@."
        QualifiedIdentifier.pp operator_identifier Location.pp
        left_operator_location Location.pp right_operator_location
    | Arity_mismatch
        { operator_identifier
        ; operator_location
        ; operator_arity
        ; actual_argument_locations
        } ->
      let expected_arguments_count = operator_arity
      and actual_arguments_count = List.length actual_argument_locations in
      Format.fprintf ppf "Operator %a expected %d arguments but got %d: %a@."
        QualifiedIdentifier.pp operator_identifier expected_arguments_count
        actual_arguments_count Location.pp operator_location
    | Too_many_arguments location ->
      Format.fprintf ppf
        "Too many arguments are supplied to an operator: %a@." Location.pp
        location
    | _ -> raise @@ Invalid_argument "[pp_exception] unsupported exception"

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some @@ Format.stringify pp_exception exn
        with Invalid_argument _ -> Option.none)

  (** {1 Disambiguation} *)

  (** [resolve_lf_operator state ~quoted identifier] determines whether
      [identifier] is an LF type-level or term-level operator in [state], and
      whether it is quoted. *)
  let resolve_lf_operator state ~quoted identifier =
    match Disambiguation_state.lookup identifier state with
    | QualifiedIdentifier.Dictionary.Entry
        (Disambiguation_state.LF_type_constant operator) ->
      if quoted then `Quoted_type_operator
      else `Type_operator (identifier, operator)
    | QualifiedIdentifier.Dictionary.Entry
        (Disambiguation_state.LF_term_constant operator) ->
      if quoted then `Quoted_term_operator
      else `Term_operator (identifier, operator)
    | _ | (exception QualifiedIdentifier.Dictionary.Unbound_identifier _) ->
      `Not_an_operator

  (** [identifier_lf_operator state term] identifies whether [term] is an LF
      type-level or term-level operator in [state] while accounting for
      operator quoting. If a bound operator appears in parentheses, then it
      is quoted, meaning that the operator appears either in prefix notation
      or as an argument to another application. *)
  let identify_lf_operator state term =
    match term with
    | Synprs.LF.Object.RawIdentifier { identifier; quoted; _ } ->
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      resolve_lf_operator state ~quoted qualified_identifier
    | Synprs.LF.Object.RawQualifiedIdentifier { identifier; quoted; _ } ->
      resolve_lf_operator state ~quoted identifier
    | _ -> `Not_an_operator

  (** LF term-level or type-level operands for rewriting of prefix, infix and
      postfix operators using {!ShuntingYard}. *)
  module LF_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext'.LF.Typ.t  (** A disambiguated LF type. *)
      | External_term of Synext'.LF.Term.t  (** A disambiguated LF term. *)
      | Parser_object of Synprs.LF.Object.t
          (** An LF object that has yet to be disambiguated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.LF.Object.t | `Term of Synprs.LF.Object.t ]
          ; arguments : Synprs.LF.Object.t List.t
          }  (** An LF type-level or term-level application. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext'.LF.location_of_typ t
      | External_term t -> Synext'.LF.location_of_term t
      | Parser_object t -> Synprs.LF.location_of_object t
      | Application { applicand; arguments } ->
        let applicand_location =
          match applicand with
          | `Typ applicand | `Term applicand ->
            Synprs.LF.location_of_object applicand
        in
        Location.join_all_contramap Synprs.LF.location_of_object
          applicand_location arguments
  end

  (** LF term-level or type-level operators for rewriting of prefix, infix
      and postfix operators using {!ShuntingYard}. *)
  module LF_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.LF.Object.t
          }
          (** An LF type-level constant with its operator definition in the
              disambiguation context, and its corresponding AST. *)
      | Term_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.LF.Object.t
          }
          (** An LF term-level constant with its operator definition in the
              disambiguation context, and its corresponding AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ } | Term_constant { identifier; _ } ->
        identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.LF.location_of_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module QualifiedIdentifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [disambiguate_as_kind state object_] is [object_] rewritten as an LF
      kind with respect to the disambiguation context [state].

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF kinds, see the Beluga language specification.

      Examples of invalid kinds that may result from this disambiguation
      include:

      - [type -> type]
      - [(type -> type) -> type]
      - [{ x : tp } type -> type] *)
  let rec disambiguate_as_kind state object_ =
    match object_ with
    | Synprs.LF.Object.RawIdentifier { location; _ } ->
      raise @@ Illegal_identifier_kind location
    | Synprs.LF.Object.RawQualifiedIdentifier { location; _ } ->
      raise @@ Illegal_qualified_identifier_kind location
    | Synprs.LF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_kind location
    | Synprs.LF.Object.RawHole { location; _ } ->
      raise @@ Illegal_hole_kind location
    | Synprs.LF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_kind location
    | Synprs.LF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_kind location
    | Synprs.LF.Object.RawApplication { location; _ } ->
      raise @@ Illegal_application_kind location
    | Synprs.LF.Object.RawPi { location; parameter_sort = Option.None; _ } ->
      raise @@ Illegal_untyped_pi_kind location
    | Synprs.LF.Object.RawType { location } ->
      Synext'.LF.Kind.Typ { location }
    | Synprs.LF.Object.RawArrow
        { location; domain; range; orientation = `Forward } ->
      let domain' = disambiguate_as_typ state domain
      and range' = disambiguate_as_kind state range in
      Synext'.LF.Kind.Arrow { location; domain = domain'; range = range' }
    | Synprs.LF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } ->
      let parameter_type' = disambiguate_as_typ state parameter_type in
      let body' =
        match parameter_identifier with
        | Option.None -> disambiguate_as_kind state body
        | Option.Some identifier ->
          let state' =
            Disambiguation_state.add_lf_term_variable identifier state
          in
          disambiguate_as_kind state' body
      in
      Synext'.LF.Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }

  (** [disambiguate_as_typ state object_] is [object_] rewritten as an LF
      type with respect to the disambiguation context [state].

      Type applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification.

      Examples of invalid types that may result from this disambiguation
      include:

      - [c (_ _) _] *)
  and disambiguate_as_typ state object_ =
    match object_ with
    | Synprs.LF.Object.RawType { location; _ } ->
      raise @@ Illegal_type_kind_type location
    | Synprs.LF.Object.RawHole { location; _ } ->
      raise @@ Illegal_hole_type location
    | Synprs.LF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_type location
    | Synprs.LF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_type location
    | Synprs.LF.Object.RawPi { location; parameter_sort = Option.None; _ } ->
      raise @@ Illegal_untyped_pi_type location
    | Synprs.LF.Object.RawIdentifier { location; identifier; quoted } -> (
      (* As an LF type, plain identifiers are necessarily type-level
         constants. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Disambiguation_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_type_constant operator) ->
        Synext'.LF.Typ.Constant
          { location; identifier = qualified_identifier; operator; quoted }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise
        @@ Unbound_type_constant
             { location; identifier = qualified_identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier
        { location; identifier; quoted } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF type, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily type-level constants. *)
      match Disambiguation_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_type_constant operator) ->
        Synext'.LF.Typ.Constant { location; identifier; operator; quoted }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_type_constant { location; identifier })
    | Synprs.LF.Object.RawArrow { location; domain; range; orientation } ->
      let domain' = disambiguate_as_typ state domain
      and range' = disambiguate_as_typ state range in
      Synext'.LF.Typ.Arrow
        { location; domain = domain'; range = range'; orientation }
    | Synprs.LF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
      let parameter_type' = disambiguate_as_typ state parameter_type in
      match parameter_identifier with
      | Option.None ->
        let body' = disambiguate_as_typ state body in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some parameter ->
        let state' =
          Disambiguation_state.add_lf_term_variable parameter state
        in
        let body' = disambiguate_as_typ state' body in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Object.RawApplication { objects; _ } -> (
      match disambiguate_application state objects with
      | `Term term ->
        let location = Synext'.LF.location_of_term term in
        raise @@ Expected_type location
      | `Typ typ -> typ)

  (** [disambiguate_as_term state object_] is [object_] rewritten as an LF
      term with respect to the disambiguation context [state].

      Term applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification.

      Examples of invalid terms that may result from this disambiguation
      include:

      - [_ _]
      - [\\_. _ _] *)
  and disambiguate_as_term state object_ =
    match object_ with
    | Synprs.LF.Object.RawType { location; _ } ->
      raise @@ Illegal_type_kind_term location
    | Synprs.LF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term location
    | Synprs.LF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_term location
    | Synprs.LF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_term location
    | Synprs.LF.Object.RawIdentifier { location; identifier; quoted } -> (
      (* As an LF term, plain identifiers are either term-level constants or
         variables (bound or free). *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Disambiguation_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_term_constant operator) ->
        Synext'.LF.Term.Constant
          { location; identifier = qualified_identifier; operator; quoted }
      | QualifiedIdentifier.Dictionary.Entry
          Disambiguation_state.LF_term_variable ->
        (* Bound variable *)
        Synext'.LF.Term.Variable { location; identifier }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        (* Free variable *)
        Synext'.LF.Term.Variable { location; identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier
        { location; identifier; quoted } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF term, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily term-level constants. *)
      match Disambiguation_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_term_constant operator) ->
        Synext'.LF.Term.Constant { location; identifier; operator; quoted }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.LF.Object.RawApplication { objects; _ } -> (
      match disambiguate_application state objects with
      | `Typ typ ->
        let location = Synext'.LF.location_of_typ typ in
        raise @@ Expected_term location
      | `Term term -> term)
    | Synprs.LF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (disambiguate_as_typ state) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = disambiguate_as_term state body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let state' = Disambiguation_state.add_lf_term_variable name state in
        let body' = disambiguate_as_term state' body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Object.RawHole { location } ->
      Synext'.LF.Term.Wildcard { location }
    | Synprs.LF.Object.RawAnnotated { location; object_; sort } ->
      let term' = disambiguate_as_term state object_
      and typ' = disambiguate_as_typ state sort in
      Synext'.LF.Term.TypeAnnotated { location; term = term'; typ = typ' }

  (** [disambiguate_application state objects] disambiguates [objects] as
      either a type-level or term-level LF application with respect to the
      disambiguation context [state].

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
  and disambiguate_application state =
    let disambiguate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term applicand | `Typ applicand ->
          Synprs.LF.location_of_object applicand
      in
      let application_location =
        Location.join_all_contramap Synprs.LF.location_of_object
          applicand_location arguments
      in
      match applicand with
      | `Term applicand ->
        let applicand' = disambiguate_as_term state applicand in
        let arguments' = List.map (disambiguate_as_term state) arguments in
        `Term
          (Synext'.LF.Term.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ applicand ->
        let applicand' = disambiguate_as_typ state applicand in
        let arguments' = List.map (disambiguate_as_term state) arguments in
        `Typ
          (Synext'.LF.Typ.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module LF_application_writer = struct
      (** [disambiguate_argument argument] disambiguates [argument] to an LF
          term.

          @raise Expected_term *)
      let disambiguate_argument argument =
        match argument with
        | LF_operand.External_term term -> term
        | LF_operand.External_typ typ ->
          let location = Synext'.LF.location_of_typ typ in
          raise @@ Expected_term location
        | LF_operand.Parser_object object_ ->
          disambiguate_as_term state object_
        | LF_operand.Application { applicand; arguments } -> (
          match disambiguate_juxtaposition applicand arguments with
          | `Term term -> term
          | `Typ typ ->
            let location = Synext'.LF.location_of_typ typ in
            raise @@ Expected_term location)

      let disambiguate_arguments arguments =
        List.map disambiguate_argument arguments

      let write operator arguments =
        let application_location =
          Location.join_all_contramap LF_operand.location
            (LF_operator.location operator)
            arguments
        in
        match operator with
        | LF_operator.Type_constant { applicand; _ } ->
          let applicand' = disambiguate_as_typ state applicand in
          let arguments' = disambiguate_arguments arguments in
          LF_operand.External_typ
            (Synext'.LF.Typ.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
        | LF_operator.Term_constant { applicand; _ } ->
          let applicand' = disambiguate_as_term state applicand in
          let arguments' = disambiguate_arguments arguments in
          LF_operand.External_term
            (Synext'.LF.Term.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
    end in
    let module ShuntingYard =
      ShuntingYard.Make (LF_operand) (LF_operator) (LF_application_writer)
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
        | `Quoted_term_operator, _ -> true
        | `Type_operator (_, operator), _ | `Term_operator (_, operator), _
          -> Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
          match List.take_while is_argument ts with
          | [], rest (* [t] is an operand not in juxtaposition *) ->
            ShuntingYard.operand (LF_operand.Parser_object t)
            :: reduce_juxtapositions_and_identify_operators rest
          | arguments, rest
          (* [t] is an applicand in juxtaposition with [arguments] *) ->
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (LF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (LF_operand.Application
               { applicand = `Typ t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (LF_operand.Application
               { applicand = `Term t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (LF_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (LF_operator.Type_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (LF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (LF_operator.Term_constant
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
    fun objects ->
      try
        match ShuntingYard.shunting_yard (prepare_objects objects) with
        | LF_operand.External_typ t -> `Typ t
        | LF_operand.External_term t -> `Term t
        | LF_operand.Application { applicand; arguments } ->
          disambiguate_juxtaposition applicand arguments
        | LF_operand.Parser_object _ ->
          Error.violation
            "[LF.disambiguate_application] unexpectedly did not \
             disambiguate LF operands in rewriting"
      with
      | ShuntingYard.Empty_expression ->
        Error.violation
          "[LF.disambiguate_application] unexpectedly ended with an empty \
           expression"
      | ShuntingYard.Leftover_expressions _ ->
        Error.violation
          "[LF.disambiguate_application] unexpectedly ended with leftover \
           expressions"
      | ShuntingYard.Misplaced_operator { operator; operands } ->
        let operator_location = LF_operator.location operator
        and operand_locations = List.map LF_operand.location operands in
        raise @@ Misplaced_operator { operator_location; operand_locations }
      | ShuntingYard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
        let operator_identifier = LF_operator.identifier left_operator
        and left_operator_location = LF_operator.location left_operator
        and right_operator_location = LF_operator.location right_operator in
        raise
        @@ Ambiguous_operator_placement
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        let operator_identifier = LF_operator.identifier left_operator
        and left_operator_location = LF_operator.location left_operator
        and right_operator_location = LF_operator.location right_operator in
        raise
        @@ Consecutive_non_associative_operators
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = LF_operator.identifier operator
        and operator_location = LF_operator.location operator
        and actual_argument_locations =
          List.map LF_operand.location operands
        in
        raise
        @@ Arity_mismatch
             { operator_identifier
             ; operator_location
             ; operator_arity
             ; actual_argument_locations
             }
end

module type CLF_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Exceptions} *)

  (** {2 Exceptions for contextual LF type disambiguation} *)

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception Illegal_tuple_type of Location.t

  exception Illegal_projection_type of Location.t

  exception Illegal_substitution_type of Location.t

  exception Illegal_unnamed_block_element_type of Location.t

  exception Illegal_parameter_variable_type of Location.t

  exception Illegal_substitution_variable_type of Location.t

  exception
    Unbound_type_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for contextual LF term disambiguation} *)

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception Illegal_block_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception Expected_term of Location.t

  exception Expected_type of Location.t

  exception Expected_term_pattern of Location.t

  exception Expected_type_pattern of Location.t

  exception
    Misplaced_operator of
      { operator_location : Location.t
      ; operand_locations : Location.t List.t
      }

  exception
    Ambiguous_operator_placement of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : QualifiedIdentifier.t
      ; operator_location : Location.t
      ; operator_arity : Int.t
      ; actual_argument_locations : Location.t List.t
      }

  exception Too_many_arguments of Location.t

  (** {2 Exceptions for contextual LF type pattern disambiguation} *)

  exception Illegal_wildcard_type_pattern of Location.t

  exception Illegal_labellable_hole_type_pattern of Location.t

  exception Illegal_lambda_type_pattern of Location.t

  exception Illegal_annotated_type_pattern of Location.t

  exception Illegal_untyped_pi_type_pattern of Location.t

  exception Illegal_tuple_type_pattern of Location.t

  exception Illegal_projection_type_pattern of Location.t

  exception Illegal_substitution_type_pattern of Location.t

  exception Illegal_unnamed_block_element_type_pattern of Location.t

  (** {2 Exceptions for contextual LF term pattern disambiguation} *)

  exception Illegal_pi_term_pattern of Location.t

  exception Illegal_forward_arrow_term_pattern of Location.t

  exception Illegal_backward_arrow_term_pattern of Location.t

  exception Illegal_block_term_pattern of Location.t

  exception Illegal_labellable_hole_term_pattern of Location.t

  (** {1 Disambiguation} *)

  val disambiguate_as_typ :
    disambiguation_state -> Synprs.CLF.Object.t -> Synext'.CLF.Typ.t

  val disambiguate_as_term :
    disambiguation_state -> Synprs.CLF.Object.t -> Synext'.CLF.Term.t

  val disambiguate_as_substitution :
       disambiguation_state
    -> Synprs.CLF.Context_object.t
    -> Synext'.CLF.Substitution.t

  val disambiguate_as_context :
       disambiguation_state
    -> Synprs.CLF.Context_object.t
    -> disambiguation_state * Synext'.CLF.Context.t

  val disambiguate_as_term_pattern :
    disambiguation_state -> Synprs.CLF.Object.t -> Synext'.CLF.Term.Pattern.t

  val disambiguate_as_substitution_pattern :
       disambiguation_state
    -> Synprs.CLF.Context_object.t
    -> Synext'.CLF.Substitution.Pattern.t

  val disambiguate_as_context_pattern :
       disambiguation_state
    -> Synprs.CLF.Context_object.t
    -> Synext'.CLF.Context.Pattern.t
end

(** Disambiguation of contextual LF types, terms and patterns from the parser
    syntax to the external syntax.

    This disambiguation does not perform normalization nor validation. *)
module CLF (Disambiguation_state : DISAMBIGUATION_STATE) :
  CLF_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  (** {1 Exceptions} *)

  (** {2 Exceptions for contextual LF type disambiguation} *)

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception Illegal_tuple_type of Location.t

  exception Illegal_projection_type of Location.t

  exception Illegal_substitution_type of Location.t

  exception Illegal_unnamed_block_element_type of Location.t

  exception Illegal_parameter_variable_type of Location.t

  exception Illegal_substitution_variable_type of Location.t

  exception
    Unbound_type_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for contextual LF term disambiguation} *)

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception Illegal_block_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for contextual LF substitution disambiguation} *)

  exception Illegal_subtitution_term_label of Location.t

  (** {2 Exceptions for contextual LF context disambiguation} *)

  exception Illegal_context_parameter_variable_binding of Location.t

  exception Illegal_context_substitution_variable_binding of Location.t

  exception Illegal_context_missing_binding_identifier of Location.t

  exception Illegal_context_identity of Location.t

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding :
          disambiguation_state_entry QualifiedIdentifier.Dictionary.value
      }

  exception Expected_term of Location.t

  exception Expected_type of Location.t

  exception Expected_term_pattern of Location.t

  exception Expected_type_pattern of Location.t

  exception
    Misplaced_operator of
      { operator_location : Location.t
      ; operand_locations : Location.t List.t
      }

  exception
    Ambiguous_operator_placement of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : QualifiedIdentifier.t
      ; operator_location : Location.t
      ; operator_arity : Int.t
      ; actual_argument_locations : Location.t List.t
      }

  exception Too_many_arguments of Location.t

  (** {2 Exceptions for contextual LF type pattern disambiguation} *)

  exception Illegal_wildcard_type_pattern of Location.t

  exception Illegal_labellable_hole_type_pattern of Location.t

  exception Illegal_lambda_type_pattern of Location.t

  exception Illegal_annotated_type_pattern of Location.t

  exception Illegal_untyped_pi_type_pattern of Location.t

  exception Illegal_tuple_type_pattern of Location.t

  exception Illegal_projection_type_pattern of Location.t

  exception Illegal_substitution_type_pattern of Location.t

  exception Illegal_unnamed_block_element_type_pattern of Location.t

  (** {2 Exceptions for contextual LF term pattern disambiguation} *)

  exception Illegal_pi_term_pattern of Location.t

  exception Illegal_forward_arrow_term_pattern of Location.t

  exception Illegal_backward_arrow_term_pattern of Location.t

  exception Illegal_block_term_pattern of Location.t

  exception Illegal_labellable_hole_term_pattern of Location.t

  (** {2 Exceptions for contextual LF substitution pattern disambiguation} *)

  exception Illegal_subtitution_pattern_term_label of Location.t

  (** {2 Exceptions for contextual LF context pattern disambiguation} *)

  exception Illegal_context_pattern_missing_binding_type of Location.t

  exception Illegal_context_pattern_parameter_variable_binding of Location.t

  exception
    Illegal_context_pattern_substitution_variable_binding of Location.t

  exception Illegal_context_pattern_missing_binding_identifier of Location.t

  exception Illegal_context_pattern_identity of Location.t

  (** {2 Exception Printing} *)

  let pp_exception ppf = function
    | Illegal_hole_type location ->
      Format.fprintf ppf "Holes may not appear as contextual LF types: %a@."
        Location.pp location
    | Illegal_lambda_type location ->
      Format.fprintf ppf
        "Lambdas may not appear as contextual LF types: %a@." Location.pp
        location
    | Illegal_annotated_type location ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF types: \
         %a@."
        Location.pp location
    | Illegal_untyped_pi_type location ->
      Format.fprintf ppf
        "The contextual LF Pi type is missing its parameter type \
         annotation: %a@."
        Location.pp location
    | Illegal_tuple_type location ->
      Format.fprintf ppf
        "Tuple terms may not appear as contextual LF types: %a@." Location.pp
        location
    | Illegal_projection_type location ->
      Format.fprintf ppf
        "Projection terms may not appear as contextual LF types: %a@."
        Location.pp location
    | Illegal_substitution_type location ->
      Format.fprintf ppf
        "Substitution terms may not appear as contextual LF types: %a@."
        Location.pp location
    | Illegal_unnamed_block_element_type location ->
      Format.fprintf ppf
        "Contextual LF block type element missing an identifier: %a@."
        Location.pp location
    | Illegal_parameter_variable_type location ->
      Format.fprintf ppf
        "Parameter variables may not appear as contextual LF types: %a@."
        Location.pp location
    | Illegal_substitution_variable_type location ->
      Format.fprintf ppf
        "Substitution variables may not appear as contextual LF types: %a@."
        Location.pp location
    | Unbound_type_constant { location; identifier } ->
      Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Illegal_pi_term location ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF terms: %a@."
        Location.pp location
    | Illegal_forward_arrow_term location ->
      Format.fprintf ppf
        "Forward arrows may not appear as contextual LF terms: %a@."
        Location.pp location
    | Illegal_backward_arrow_term location ->
      Format.fprintf ppf
        "Backward arrows may not appear as contextual LF terms: %a@."
        Location.pp location
    | Illegal_block_term location ->
      Format.fprintf ppf
        "Block types may not appear as contextual LF terms: %a@." Location.pp
        location
    | Unbound_term_constant { location; identifier } ->
      Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Illegal_subtitution_term_label location ->
      Format.fprintf ppf "Terms in a substitution may not be labelled: %a@."
        Location.pp location
    | Illegal_context_parameter_variable_binding location ->
      Format.fprintf ppf
        "Parameter variable bindings may not occur in contextual LF \
         contexts: %a@."
        Location.pp location
    | Illegal_context_substitution_variable_binding location ->
      Format.fprintf ppf
        "Substitution variable bindings may not occur in contextual LF \
         contexts: %a@."
        Location.pp location
    | Illegal_context_missing_binding_identifier location ->
      Format.fprintf ppf
        "Identifier missing for the binding in the contextual LF context: \
         %a@."
        Location.pp location
    | Illegal_context_identity location ->
      Format.fprintf ppf
        "Contextual LF contexts may not begin with the identity \
         substitution: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.LF_type_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found an LF type constant \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.LF_term_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found an LF term variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Meta_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a meta-variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Parameter_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a parameter variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Substitution_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a substitution \
         variable instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Context_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a context variable \
         instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_variable
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         variable instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_type_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         type constant instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_term_constructor _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         term constructor instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_cotype_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         cotype constant instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_term_destructor
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a computation-level \
         term destructor instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry Disambiguation_state.Query
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a logic programming \
         query identifier instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry Disambiguation_state.MQuery
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a logic programming \
         meta-query identifier instead: %a@."
        Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = QualifiedIdentifier.Dictionary.Module _
        } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found a module instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.LF_term_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found an LF term constant \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.LF_term_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found an LF term variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Meta_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a meta-variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Parameter_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a parameter variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Substitution_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a substitution \
         variable instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Context_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a context variable \
         instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_variable
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         variable instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_type_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         type constant instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_term_constructor _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         term constructor instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              (Disambiguation_state.Computation_cotype_constant _)
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         cotype constant instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            QualifiedIdentifier.Dictionary.Entry
              Disambiguation_state.Computation_term_destructor
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a computation-level \
         term destructor instead: %a@."
        Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = QualifiedIdentifier.Dictionary.Module _
        } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found a module instead: %a@."
        Location.pp location
    | Expected_term location ->
      Format.fprintf ppf
        "Expected a contextual LF term but found a contextual LF type \
         instead: %a@."
        Location.pp location
    | Expected_type location ->
      Format.fprintf ppf
        "Expected an LF type but found an LF term instead: %a@." Location.pp
        location
    | Ambiguous_operator_placement
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
      Format.fprintf ppf
        "Ambiguous occurrences of the LF term-level or type-level operator \
         %a after rewriting: %a and %a@."
        QualifiedIdentifier.pp operator_identifier Location.pp
        left_operator_location Location.pp right_operator_location
    | Misplaced_operator { operator_location; _ } ->
      Format.fprintf ppf
        "Misplaced contextual LF term-level or type-level operator: %a@."
        Location.pp operator_location
    | Consecutive_non_associative_operators
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
      Format.fprintf ppf
        "Consecutive occurrences of the contextual LF term-level or \
         type-level operator %a after rewriting: %a and %a@."
        QualifiedIdentifier.pp operator_identifier Location.pp
        left_operator_location Location.pp right_operator_location
    | Arity_mismatch
        { operator_identifier
        ; operator_location
        ; operator_arity
        ; actual_argument_locations
        } ->
      let expected_arguments_count = operator_arity
      and actual_arguments_count = List.length actual_argument_locations in
      Format.fprintf ppf "Operator %a expected %d arguments but got %d: %a@."
        QualifiedIdentifier.pp operator_identifier expected_arguments_count
        actual_arguments_count Location.pp operator_location
    | Too_many_arguments location ->
      Format.fprintf ppf
        "Too many arguments are supplied to an operator: %a@." Location.pp
        location
    | Expected_term_pattern location ->
      Format.fprintf ppf
        "Expected a contextual LF term pattern but found a contextual LF \
         type pattern instead: %a@."
        Location.pp location
    | Expected_type_pattern location ->
      Format.fprintf ppf
        "Expected a contextual LF type pattern but found a contextual LF \
         term pattern instead: %a@."
        Location.pp location
    | Illegal_wildcard_type_pattern location ->
      Format.fprintf ppf
        "Wildcards may not appear as contextual LF type patterns: %a@."
        Location.pp location
    | Illegal_labellable_hole_type_pattern location ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_lambda_type_pattern location ->
      Format.fprintf ppf
        "Lambdas may not appear as contextual LF type patterns: %a@."
        Location.pp location
    | Illegal_annotated_type_pattern location ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF type \
         patterns: %a@."
        Location.pp location
    | Illegal_untyped_pi_type_pattern location ->
      Format.fprintf ppf
        "The contextual LF Pi type pattern is missing its parameter type \
         annotation: %a@."
        Location.pp location
    | Illegal_tuple_type_pattern location ->
      Format.fprintf ppf
        "Tuple term patterns may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_projection_type_pattern location ->
      Format.fprintf ppf
        "Projection term patterns may not appear as contextual LF type \
         patterns: %a@."
        Location.pp location
    | Illegal_substitution_type_pattern location ->
      Format.fprintf ppf
        "Substitution term patterns may not appear as contextual LF type \
         patterns: %a@."
        Location.pp location
    | Illegal_unnamed_block_element_type_pattern location ->
      Format.fprintf ppf
        "Contextual LF block type pattern element missing an identifier: \
         %a@."
        Location.pp location
    | Illegal_pi_term_pattern location ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF term patterns: \
         %a@."
        Location.pp location
    | Illegal_forward_arrow_term_pattern location ->
      Format.fprintf ppf
        "Forward arrow types may not appear as contextual LF term patterns: \
         %a@."
        Location.pp location
    | Illegal_backward_arrow_term_pattern location ->
      Format.fprintf ppf
        "Backward arrow types may not appear as contextual LF term \
         patterns: %a@."
        Location.pp location
    | Illegal_block_term_pattern location ->
      Format.fprintf ppf
        "Block types may not appear as contextual LF term patterns: %a@."
        Location.pp location
    | Illegal_labellable_hole_term_pattern location ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF term patterns: \
         %a@."
        Location.pp location
    | Illegal_subtitution_pattern_term_label location ->
      Format.fprintf ppf
        "Terms in a substitution pattern may not be labelled: %a@."
        Location.pp location
    | Illegal_context_pattern_parameter_variable_binding location ->
      Format.fprintf ppf
        "Parameter variable bindings may not occur in contextual LF context \
         patterns: %a@."
        Location.pp location
    | Illegal_context_pattern_substitution_variable_binding location ->
      Format.fprintf ppf
        "Substitution variable bindings may not occur in contextual LF \
         context patterns: %a@."
        Location.pp location
    | Illegal_context_pattern_missing_binding_identifier location ->
      Format.fprintf ppf
        "Identifier missing for the binding in the contextual LF context \
         pattern: %a@."
        Location.pp location
    | Illegal_context_pattern_identity location ->
      Format.fprintf ppf
        "Contextual LF context patterns may not begin with the identity \
         substitution: %a@."
        Location.pp location
    | _ -> raise @@ Invalid_argument "[pp_exception] unsupported exception"

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some @@ Format.stringify pp_exception exn
        with Invalid_argument _ -> Option.none)

  (** {1 Disambiguation} *)

  (** [resolve_lf_operator state ~quoted identifier] determines whether
      [identifier] is an LF type-level or term-level operator in [state], and
      whether it is quoted. *)
  let resolve_lf_operator state ~quoted identifier =
    match Disambiguation_state.lookup identifier state with
    | QualifiedIdentifier.Dictionary.Entry
        (Disambiguation_state.LF_type_constant operator) ->
      if quoted then `Quoted_type_operator
      else `Type_operator (identifier, operator)
    | QualifiedIdentifier.Dictionary.Entry
        (Disambiguation_state.LF_term_constant operator) ->
      if quoted then `Quoted_term_operator
      else `Term_operator (identifier, operator)
    | _ | (exception QualifiedIdentifier.Dictionary.Unbound_identifier _) ->
      `Not_an_operator

  (** [identifier_lf_operator state term] identifies whether [term] is an LF
      type-level or term-level operator in [state] while accounting for
      operator quoting. If a bound operator appears in parentheses, then it
      is quoted, meaning that the operator appears either in prefix notation
      or as an argument to another application. *)
  let identify_lf_operator state term =
    match term with
    | Synprs.CLF.Object.RawIdentifier
        { identifier = identifier, _modifier; quoted; _ } ->
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      resolve_lf_operator state ~quoted qualified_identifier
    | Synprs.CLF.Object.RawQualifiedIdentifier { identifier; quoted; _ } ->
      resolve_lf_operator state ~quoted identifier
    | _ -> `Not_an_operator

  (** Contextual LF term-level or type-level operands for rewriting of
      prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext'.CLF.Typ.t
          (** A disambiguated contextual LF type. *)
      | External_term of Synext'.CLF.Term.t
          (** A disambiguated contextual LF term. *)
      | Parser_object of Synprs.CLF.Object.t
          (** A contextual LF object that has yet to be disambiguated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.CLF.Object.t | `Term of Synprs.CLF.Object.t ]
          ; arguments : Synprs.CLF.Object.t List.t
          }  (** A contextual LF type-level or term-level application. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext'.CLF.location_of_typ t
      | External_term t -> Synext'.CLF.location_of_term t
      | Parser_object t -> Synprs.CLF.location_of_object t
      | Application { applicand; arguments } ->
        let applicand_location =
          match applicand with
          | `Typ applicand | `Term applicand ->
            Synprs.CLF.location_of_object applicand
        in
        Location.join_all_contramap Synprs.CLF.location_of_object
          applicand_location arguments
  end

  (** Contextual LF term-level or type-level operators for rewriting of
      prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF type-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)
      | Term_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF term-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ } | Term_constant { identifier; _ } ->
        identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.CLF.location_of_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module QualifiedIdentifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [disambiguate_as_typ state object_] is [object_] rewritten as a
      contextual LF type with respect to the disambiguation context [state].

      Type applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification.

      Examples of invalid types that may result from this disambiguation
      include:

      - [c (_ _) _] *)
  let rec disambiguate_as_typ state object_ =
    match object_ with
    | Synprs.CLF.Object.RawHole { location; _ } ->
      raise @@ Illegal_hole_type location
    | Synprs.CLF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_type location
    | Synprs.CLF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_type location
    | Synprs.CLF.Object.RawPi { location; parameter_sort = Option.None; _ }
      -> raise @@ Illegal_untyped_pi_type location
    | Synprs.CLF.Object.RawTuple { location; _ } ->
      raise @@ Illegal_tuple_type location
    | Synprs.CLF.Object.RawProjection { location; _ } ->
      raise @@ Illegal_projection_type location
    | Synprs.CLF.Object.RawSubstitution { location; _ } ->
      raise @@ Illegal_substitution_type location
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = _identifier, `Hash; _ } ->
      raise @@ Illegal_parameter_variable_type location
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = _identifier, `Dollar; _ } ->
      raise @@ Illegal_substitution_variable_type location
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
      (* As an LF type, plain identifiers are necessarily type-level
         constants. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Disambiguation_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_type_constant operator) ->
        Synext'.CLF.Typ.Constant
          { location; identifier = qualified_identifier; operator; quoted }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise
        @@ Unbound_type_constant
             { location; identifier = qualified_identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier
        { location; identifier; quoted } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF type, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily type-level constants. *)
      match Disambiguation_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_type_constant operator) ->
        Synext'.CLF.Typ.Constant { location; identifier; operator; quoted }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_type_constant { location; identifier })
    | Synprs.CLF.Object.RawArrow { location; domain; range; orientation } ->
      let domain' = disambiguate_as_typ state domain
      and range' = disambiguate_as_typ state range in
      Synext'.CLF.Typ.Arrow
        { location; domain = domain'; range = range'; orientation }
    | Synprs.CLF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
      let parameter_type' = disambiguate_as_typ state parameter_type in
      match parameter_identifier with
      | Option.None ->
        let body' = disambiguate_as_typ state body in
        Synext'.CLF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some parameter ->
        let state' =
          Disambiguation_state.add_lf_term_variable parameter state
        in
        let body' = disambiguate_as_typ state' body in
        Synext'.CLF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match disambiguate_application state objects with
      | `Term term ->
        let location = Synext'.CLF.location_of_term term in
        raise @@ Expected_type location
      | `Typ typ -> typ)
    | Synprs.CLF.Object.RawBlock
        { location; elements = List1.T ((Option.None, t), []) } ->
      let t' = disambiguate_as_typ state t in
      Synext'.CLF.Typ.Block { location; elements = `Unnamed t' }
    | Synprs.CLF.Object.RawBlock { location; elements } ->
      let _state', elements_rev' =
        List1.fold_left
          (fun element ->
            match element with
            | Option.None, typ ->
              let location = Synprs.CLF.location_of_object typ in
              raise @@ Illegal_unnamed_block_element_type location
            | Option.Some identifier, typ ->
              let typ' = disambiguate_as_typ state typ in
              let elements' = List1.singleton (identifier, typ')
              and state' =
                Disambiguation_state.add_lf_term_variable identifier state
              in
              (state', elements'))
          (fun (state', elements') element ->
            match element with
            | Option.None, typ ->
              let location = Synprs.CLF.location_of_object typ in
              raise @@ Illegal_unnamed_block_element_type location
            | Option.Some identifier, typ ->
              let typ' = disambiguate_as_typ state' typ in
              let elements'' = List1.cons (identifier, typ') elements'
              and state'' =
                Disambiguation_state.add_lf_term_variable identifier state'
              in
              (state'', elements''))
          elements
      in
      let elements' = List1.rev elements_rev' in
      Synext'.CLF.Typ.Block { location; elements = `Record elements' }

  (** [disambiguate_as_term state object_] is [object_] rewritten as a
      contextual LF term with respect to the disambiguation context [state].

      Term applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification.

      Examples of invalid terms that may result from this disambiguation
      include:

      - [_ _]
      - [\\_. _ _] *)
  and disambiguate_as_term state object_ =
    match object_ with
    | Synprs.CLF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_term location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_term location
    | Synprs.CLF.Object.RawBlock { location; _ } ->
      raise @@ Illegal_block_term location
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, `Hash; _ } ->
      Synext'.CLF.Term.Parameter_variable { location; identifier }
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, `Dollar; _ } ->
      Synext'.CLF.Term.Substitution_variable { location; identifier }
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
      (* As an LF term, plain identifiers are either term-level constants or
         variables (bound or free). *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Disambiguation_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Constant
          { location; identifier = qualified_identifier; operator; quoted }
      | QualifiedIdentifier.Dictionary.Entry
          ( Disambiguation_state.LF_term_variable
          | Disambiguation_state.Meta_variable ) ->
        (* Bound variable *)
        Synext'.CLF.Term.Variable { location; identifier }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        (* Free variable *)
        Synext'.CLF.Term.Variable { location; identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier
        { location; identifier; quoted } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF term, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily term-level constants. *)
      match Disambiguation_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Constant { location; identifier; operator; quoted }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match disambiguate_application state objects with
      | `Typ typ ->
        let location = Synext'.CLF.location_of_typ typ in
        raise @@ Expected_term location
      | `Term term -> term)
    | Synprs.CLF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (disambiguate_as_typ state) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = disambiguate_as_term state body in
        Synext'.CLF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let state' = Disambiguation_state.add_lf_term_variable name state in
        let body' = disambiguate_as_term state' body in
        Synext'.CLF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.CLF.Object.RawHole { location; variant } ->
      Synext'.CLF.Term.Hole { location; variant }
    | Synprs.CLF.Object.RawTuple { location; elements } ->
      let elements' = List1.map (disambiguate_as_term state) elements in
      Synext'.CLF.Term.Tuple { location; terms = elements' }
    | Synprs.CLF.Object.RawProjection { location; object_; projection } ->
      let term' = disambiguate_as_term state object_ in
      Synext'.CLF.Term.Projection { location; term = term'; projection }
    | Synprs.CLF.Object.RawSubstitution { location; object_; substitution }
      ->
      let term' = disambiguate_as_term state object_ in
      let substitution' = disambiguate_as_substitution state substitution in
      Synext'.CLF.Term.Substitution
        { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.RawAnnotated { location; object_; sort } ->
      let term' = disambiguate_as_term state object_
      and typ' = disambiguate_as_typ state sort in
      Synext'.CLF.Term.TypeAnnotated { location; term = term'; typ = typ' }

  and disambiguate_as_substitution state substitution =
    let { Synprs.CLF.Context_object.location; head; objects } =
      substitution
    in
    let objects' =
      List.map
        (function
          | Option.None, object_ -> object_
          | Option.Some identifier, _ ->
            let location = Identifier.location identifier in
            raise @@ Illegal_subtitution_term_label location)
        objects
    in
    match head with
    | Synprs.CLF.Context_object.Head.None { location = head_location } ->
      let head', objects'' =
        match objects' with
        | Synprs.CLF.Object.RawSubstitution
            { object_ =
                Synprs.CLF.Object.RawIdentifier
                  { location; identifier = identifier, `Dollar; _ }
            ; substitution = closure
            ; _
            } (* A substitution closure *)
          :: xs ->
          let closure' = disambiguate_as_substitution state closure in
          ( Synext'.CLF.Substitution.Head.Substitution_variable
              { location; identifier; closure = Option.some closure' }
          , xs )
        | Synprs.CLF.Object.RawIdentifier
            { location; identifier = identifier, `Dollar; _ }
            (* A substitution variable *)
          :: xs ->
          ( Synext'.CLF.Substitution.Head.Substitution_variable
              { location; identifier; closure = Option.none }
          , xs )
        | _ ->
          ( Synext'.CLF.Substitution.Head.None { location = head_location }
          , objects' )
      in
      let terms' = List.map (disambiguate_as_term state) objects'' in
      { Synext'.CLF.Substitution.location; head = head'; terms = terms' }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
      let terms' = List.map (disambiguate_as_term state) objects' in
      { Synext'.CLF.Substitution.location
      ; head =
          Synext'.CLF.Substitution.Head.Identity { location = head_location }
      ; terms = terms'
      }

  (** [disambiguate_context_bindings state bindings] is [(state', bindings')]
      where [state'] is the disambiguation state derived from [state] with
      the addition of the variables in the domain of [bindings], and
      [bindings'] is the disambiguated context bindings.

      Context variables cannot occur in [bindings]. A context variable in the
      head position of a context is handled in {!disambiguate_as_context}. *)
  and disambiguate_context_bindings state bindings =
    (* Contextual LF contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves.*)
    let state', bindings_rev' =
      List.fold_left
        (fun (state, bindings_rev') binding ->
          match binding with
          | Option.Some identifier, typ (* Typed binding *) ->
            let typ' = disambiguate_as_typ state typ in
            let state' =
              Disambiguation_state.add_lf_term_variable identifier state
            and binding' = (identifier, Option.some typ') in
            (state', binding' :: bindings_rev')
          | ( Option.None
            , Synprs.CLF.Object.RawIdentifier
                { identifier = identifier, `Plain; _ } )
          (* Untyped contextual LF variable *) ->
            let state' =
              Disambiguation_state.add_lf_term_variable identifier state
            and binding' = (identifier, Option.none) in
            (state', binding' :: bindings_rev')
          | ( Option.None
            , Synprs.CLF.Object.RawIdentifier
                { identifier = identifier, `Hash; _ } )
          (* Parameter variables may only occur in meta-contexts *) ->
            let location = Identifier.location identifier in
            raise @@ Illegal_context_parameter_variable_binding location
          | ( Option.None
            , Synprs.CLF.Object.RawIdentifier
                { identifier = identifier, `Dollar; _ } )
          (* Substitution variables may only occur in meta-contexts *) ->
            let location = Identifier.location identifier in
            raise @@ Illegal_context_substitution_variable_binding location
          | Option.None, typ (* Binding identifier missing *) ->
            let location = Synprs.CLF.location_of_object typ in
            raise @@ Illegal_context_missing_binding_identifier location)
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    (state', bindings')

  (** [disambiguate_as_context state context] is [(state', context')] where
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
  and disambiguate_as_context state context =
    let { Synprs.CLF.Context_object.location; head; objects } = context in
    match head with
    | Synprs.CLF.Context_object.Head.Identity { location } ->
      raise @@ Illegal_context_identity location
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
      match objects with
      | ( Option.None
        , Synprs.CLF.Object.RawHole
            { variant = `Underscore; location = head_location } )
          (* Hole as context head *)
        :: xs ->
        let head' =
          Synext'.CLF.Context.Head.Hole { location = head_location }
        and state', bindings' = disambiguate_context_bindings state xs in
        let context' =
          { Synext'.CLF.Context.location
          ; head = head'
          ; bindings = bindings'
          }
        in
        (state', context')
      | ( Option.None
        , Synprs.CLF.Object.RawIdentifier
            { identifier = identifier, `Plain; _ } )
          (* Possibly a context variable as context head *)
        :: xs -> (
        match Disambiguation_state.lookup_toplevel identifier state with
        | QualifiedIdentifier.Dictionary.Entry
            Disambiguation_state.Context_variable ->
          let head' =
            Synext'.CLF.Context.Head.Context_variable
              { identifier; location = Identifier.location identifier }
          and state', bindings' = disambiguate_context_bindings state xs in
          let context' =
            { Synext'.CLF.Context.location
            ; head = head'
            ; bindings = bindings'
            }
          in
          (state', context')
        | _ | (exception QualifiedIdentifier.Dictionary.Unbound_identifier _)
          ->
          let head' =
            Synext'.CLF.Context.Head.None { location = head_location }
          and state', bindings' =
            disambiguate_context_bindings state objects
          in
          let context' =
            { Synext'.CLF.Context.location
            ; head = head'
            ; bindings = bindings'
            }
          in
          (state', context'))
      | _ ->
        (* Context is just a list of bindings without context variables *)
        let head' =
          Synext'.CLF.Context.Head.None { location = head_location }
        and state', bindings' =
          disambiguate_context_bindings state objects
        in
        let context' =
          { Synext'.CLF.Context.location
          ; head = head'
          ; bindings = bindings'
          }
        in
        (state', context'))

  (** [disambiguate_application state objects] disambiguates [objects] as
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
  and disambiguate_application state =
    let disambiguate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term applicand | `Typ applicand ->
          Synprs.CLF.location_of_object applicand
      in
      let application_location =
        Location.join_all_contramap Synprs.CLF.location_of_object
          applicand_location arguments
      in
      match applicand with
      | `Term applicand ->
        let applicand' = disambiguate_as_term state applicand in
        let arguments' = List.map (disambiguate_as_term state) arguments in
        `Term
          (Synext'.CLF.Term.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ applicand ->
        let applicand' = disambiguate_as_typ state applicand in
        let arguments' = List.map (disambiguate_as_term state) arguments in
        `Typ
          (Synext'.CLF.Typ.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module ShuntingYard =
      ShuntingYard.Make (CLF_operand) (CLF_operator)
        (struct
          (** [disambiguate_argument argument] disambiguates [argument] to an
              LF term.

              @raise Expected_term *)
          let disambiguate_argument argument =
            match argument with
            | CLF_operand.External_term term -> term
            | CLF_operand.External_typ typ ->
              let location = Synext'.CLF.location_of_typ typ in
              raise @@ Expected_term location
            | CLF_operand.Parser_object object_ ->
              disambiguate_as_term state object_
            | CLF_operand.Application { applicand; arguments } -> (
              match disambiguate_juxtaposition applicand arguments with
              | `Term term -> term
              | `Typ typ ->
                let location = Synext'.CLF.location_of_typ typ in
                raise @@ Expected_term location)

          let disambiguate_arguments arguments =
            List.map disambiguate_argument arguments

          let write operator arguments =
            let application_location =
              Location.join_all_contramap CLF_operand.location
                (CLF_operator.location operator)
                arguments
            in
            match operator with
            | CLF_operator.Type_constant { applicand; _ } ->
              let applicand' = disambiguate_as_typ state applicand in
              let arguments' = disambiguate_arguments arguments in
              CLF_operand.External_typ
                (Synext'.CLF.Typ.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
            | CLF_operator.Term_constant { applicand; _ } ->
              let applicand' = disambiguate_as_term state applicand in
              let arguments' = disambiguate_arguments arguments in
              CLF_operand.External_term
                (Synext'.CLF.Term.Application
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
        | `Quoted_term_operator, _ -> true
        | `Type_operator (_, operator), _ | `Term_operator (_, operator), _
          -> Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
          match List.take_while is_argument ts with
          | [], rest (* [t] is an operand not in juxtaposition *) ->
            ShuntingYard.operand (CLF_operand.Parser_object t)
            :: reduce_juxtapositions_and_identify_operators rest
          | arguments, rest
          (* [t] is an applicand in juxtaposition with [arguments] *) ->
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_operand.Application
               { applicand = `Typ t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_operand.Application
               { applicand = `Term t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (CLF_operator.Type_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
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
    fun objects ->
      try
        match ShuntingYard.shunting_yard (prepare_objects objects) with
        | CLF_operand.External_typ t -> `Typ t
        | CLF_operand.External_term t -> `Term t
        | CLF_operand.Application { applicand; arguments } ->
          disambiguate_juxtaposition applicand arguments
        | CLF_operand.Parser_object _ ->
          Error.violation
            "[CLF.disambiguate_application] unexpectedly did not \
             disambiguate LF operands in rewriting"
      with
      | ShuntingYard.Empty_expression ->
        Error.violation
          "[CLF.disambiguate_application] unexpectedly ended with an empty \
           expression"
      | ShuntingYard.Leftover_expressions _ ->
        Error.violation
          "[CLF.disambiguate_application] unexpectedly ended with leftover \
           expressions"
      | ShuntingYard.Misplaced_operator { operator; operands } ->
        let operator_location = CLF_operator.location operator
        and operand_locations = List.map CLF_operand.location operands in
        raise @@ Misplaced_operator { operator_location; operand_locations }
      | ShuntingYard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
        let operator_identifier = CLF_operator.identifier left_operator
        and left_operator_location = CLF_operator.location left_operator
        and right_operator_location = CLF_operator.location right_operator in
        raise
        @@ Ambiguous_operator_placement
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        let operator_identifier = CLF_operator.identifier left_operator
        and left_operator_location = CLF_operator.location left_operator
        and right_operator_location = CLF_operator.location right_operator in
        raise
        @@ Consecutive_non_associative_operators
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = CLF_operator.identifier operator
        and operator_location = CLF_operator.location operator
        and actual_argument_locations =
          List.map CLF_operand.location operands
        in
        raise
        @@ Arity_mismatch
             { operator_identifier
             ; operator_location
             ; operator_arity
             ; actual_argument_locations
             }

  (** Contextual LF term-level or type-level pattern operands for rewriting
      of prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_pattern_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext'.CLF.Typ.t
          (** A disambiguated contextual LF type. *)
      | External_term_pattern of Synext'.CLF.Term.Pattern.t
          (** A disambiguated contextual LF term pattern. *)
      | Parser_object of Synprs.CLF.Object.t
          (** A contextual LF object that has yet to be disambiguated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.CLF.Object.t
              | `Term_pattern of Synprs.CLF.Object.t
              ]
          ; arguments : Synprs.CLF.Object.t List.t
          }
          (** A contextual LF type-level or term-level application pattern. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext'.CLF.location_of_typ t
      | External_term_pattern t -> Synext'.CLF.location_of_term_pattern t
      | Parser_object t -> Synprs.CLF.location_of_object t
      | Application { applicand; arguments } ->
        let applicand_location =
          match applicand with
          | `Typ applicand | `Term_pattern applicand ->
            Synprs.CLF.location_of_object applicand
        in
        Location.join_all_contramap Synprs.CLF.location_of_object
          applicand_location arguments
  end

  (** Contextual LF term-level or type-level pattern operators for rewriting
      of prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_pattern_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF type-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)
      | Term_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF term-level constant with its operator
              definition in the disambiguation context, and its corresponding
              AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ } | Term_constant { identifier; _ } ->
        identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.CLF.location_of_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module QualifiedIdentifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [disambiguate_as_term_pattern state object_] is [object_] rewritten as
      a contextual LF term pattern with respect to the disambiguation context
      [state].

      Term applications are rewritten with
      {!disambiguate_application_pattern} using Dijkstra's shunting yard
      algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification.

      Examples of invalid term patterns that may result from this
      disambiguation include:

      - [c x x], where [x] is a free pattern variable *)
  let rec disambiguate_as_term_pattern state object_ =
    match object_ with
    | Synprs.CLF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term_pattern location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_term_pattern location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_term_pattern location
    | Synprs.CLF.Object.RawBlock { location; _ } ->
      raise @@ Illegal_block_term_pattern location
    | Synprs.CLF.Object.RawHole
        { location; variant = `Unlabelled | `Labelled _ } ->
      raise @@ Illegal_labellable_hole_term_pattern location
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, `Hash; _ } ->
      Synext'.CLF.Term.Pattern.Parameter_variable { location; identifier }
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, `Dollar; _ } ->
      Synext'.CLF.Term.Pattern.Substitution_variable { location; identifier }
    | Synprs.CLF.Object.RawIdentifier
        { location; identifier = identifier, _modifier; quoted; _ } -> (
      (* As an LF term pattern, plain identifiers are either term-level
         constants, variables already present in the pattern, or new pattern
         variables. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Disambiguation_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Pattern.Constant
          { location; identifier = qualified_identifier; operator; quoted }
      | _ -> Synext'.CLF.Term.Pattern.Variable { location; identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier
        { location; identifier; quoted } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF term pattern, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily term-level constants. *)
      match Disambiguation_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Disambiguation_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Pattern.Constant
          { location; identifier; operator; quoted }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match disambiguate_application_pattern state objects with
      | `Typ typ ->
        let location = Synext'.CLF.location_of_typ typ in
        raise @@ Expected_term_pattern location
      | `Term_pattern term_pattern -> term_pattern)
    | Synprs.CLF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (disambiguate_as_typ state) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = disambiguate_as_term_pattern state body in
        Synext'.CLF.Term.Pattern.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let state' = Disambiguation_state.add_lf_term_variable name state in
        let body' = disambiguate_as_term_pattern state' body in
        Synext'.CLF.Term.Pattern.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.CLF.Object.RawHole { location; variant = `Underscore } ->
      Synext'.CLF.Term.Pattern.Wildcard { location }
    | Synprs.CLF.Object.RawTuple { location; elements } ->
      let elements' =
        List1.map (disambiguate_as_term_pattern state) elements
      in
      Synext'.CLF.Term.Pattern.Tuple { location; terms = elements' }
    | Synprs.CLF.Object.RawProjection { location; object_; projection } ->
      let term' = disambiguate_as_term_pattern state object_ in
      Synext'.CLF.Term.Pattern.Projection
        { location; term = term'; projection }
    | Synprs.CLF.Object.RawSubstitution { location; object_; substitution }
      ->
      let term' = disambiguate_as_term_pattern state object_ in
      let substitution' = disambiguate_as_substitution state substitution in
      Synext'.CLF.Term.Pattern.Substitution
        { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.RawAnnotated { location; object_; sort } ->
      let term' = disambiguate_as_term_pattern state object_
      and typ' = disambiguate_as_typ state sort in
      Synext'.CLF.Term.Pattern.TypeAnnotated
        { location; term = term'; typ = typ' }

  and disambiguate_as_substitution_pattern state substitution_pattern =
    let { Synprs.CLF.Context_object.location; head; objects } =
      substitution_pattern
    in
    let objects' =
      List.map
        (function
          | Option.None, object_ -> object_
          | Option.Some identifier, _ ->
            let location = Identifier.location identifier in
            raise @@ Illegal_subtitution_pattern_term_label location)
        objects
    in
    match head with
    | Synprs.CLF.Context_object.Head.None { location = head_location } ->
      let head', objects'' =
        match objects' with
        | Synprs.CLF.Object.RawSubstitution
            { object_ =
                Synprs.CLF.Object.RawIdentifier
                  { location; identifier = identifier, `Dollar; _ }
            ; substitution = closure
            ; _
            } (* A substitution closure *)
          :: xs ->
          let closure' = disambiguate_as_substitution state closure in
          ( Synext'.CLF.Substitution.Pattern.Head.Substitution_variable
              { location; identifier; closure = Option.some closure' }
          , xs )
        | Synprs.CLF.Object.RawIdentifier
            { location; identifier = identifier, `Dollar; _ }
            (* A substitution variable *)
          :: xs ->
          ( Synext'.CLF.Substitution.Pattern.Head.Substitution_variable
              { location; identifier; closure = Option.none }
          , xs )
        | _ ->
          ( Synext'.CLF.Substitution.Pattern.Head.None
              { location = head_location }
          , objects' )
      in
      let terms' = List.map (disambiguate_as_term_pattern state) objects'' in
      { Synext'.CLF.Substitution.Pattern.location
      ; head = head'
      ; terms = terms'
      }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
      let terms' = List.map (disambiguate_as_term_pattern state) objects' in
      { Synext'.CLF.Substitution.Pattern.location
      ; head =
          Synext'.CLF.Substitution.Pattern.Head.Identity
            { location = head_location }
      ; terms = terms'
      }

  and disambiguate_context_pattern_bindings state bindings =
    let _state', bindings_rev' =
      List.fold_left
        (fun (state, bindings_rev') binding ->
          match binding with
          | Option.Some identifier, typ ->
            let typ' = disambiguate_as_typ state typ in
            let state' =
              Disambiguation_state.add_lf_term_variable identifier state
            and binding' = (identifier, typ') in
            (state', binding' :: bindings_rev')
          | ( Option.None
            , Synprs.CLF.Object.RawIdentifier
                { identifier = identifier, `Plain; _ } ) ->
            let location = Identifier.location identifier in
            raise @@ Illegal_context_pattern_missing_binding_type location
          | ( Option.None
            , Synprs.CLF.Object.RawIdentifier
                { identifier = identifier, `Hash; _ } ) ->
            let location = Identifier.location identifier in
            raise
            @@ Illegal_context_pattern_parameter_variable_binding location
          | ( Option.None
            , Synprs.CLF.Object.RawIdentifier
                { identifier = identifier, `Dollar; _ } ) ->
            let location = Identifier.location identifier in
            raise
            @@ Illegal_context_pattern_substitution_variable_binding location
          | Option.None, typ ->
            let location = Synprs.CLF.location_of_object typ in
            raise
            @@ Illegal_context_pattern_missing_binding_identifier location)
        (state, []) bindings
    in
    let bindings' = List.rev bindings_rev' in
    bindings'

  and disambiguate_as_context_pattern state context_pattern =
    let { Synprs.CLF.Context_object.location; head; objects } =
      context_pattern
    in
    match head with
    | Synprs.CLF.Context_object.Head.Identity { location } ->
      raise @@ Illegal_context_pattern_identity location
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
      match objects with
      | ( Option.None
        , Synprs.CLF.Object.RawHole
            { variant = `Underscore; location = head_location } )
          (* Hole as context head *)
        :: xs ->
        let head' =
          Synext'.CLF.Context.Pattern.Head.Hole { location = head_location }
        and bindings' = disambiguate_context_pattern_bindings state xs in
        { Synext'.CLF.Context.Pattern.location
        ; head = head'
        ; bindings = bindings'
        }
      | ( Option.None
        , Synprs.CLF.Object.RawIdentifier
            { identifier = identifier, `Plain; _ } )
          (* Possibly a context variable as context head *)
        :: xs -> (
        match Disambiguation_state.lookup_toplevel identifier state with
        | QualifiedIdentifier.Dictionary.Entry
            Disambiguation_state.Context_variable ->
          let head' =
            Synext'.CLF.Context.Pattern.Head.Context_variable
              { identifier; location = Identifier.location identifier }
          and bindings' = disambiguate_context_pattern_bindings state xs in
          { Synext'.CLF.Context.Pattern.location
          ; head = head'
          ; bindings = bindings'
          }
        | _ | (exception QualifiedIdentifier.Dictionary.Unbound_identifier _)
          ->
          let head' =
            Synext'.CLF.Context.Pattern.Head.None
              { location = head_location }
          and bindings' =
            disambiguate_context_pattern_bindings state objects
          in
          { Synext'.CLF.Context.Pattern.location
          ; head = head'
          ; bindings = bindings'
          })
      | _ ->
        let head' =
          Synext'.CLF.Context.Pattern.Head.None { location = head_location }
        and bindings' =
          disambiguate_context_pattern_bindings state objects
        in
        { Synext'.CLF.Context.Pattern.location
        ; head = head'
        ; bindings = bindings'
        })

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
  and disambiguate_application_pattern state =
    let disambiguate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term_pattern applicand | `Typ applicand ->
          Synprs.CLF.location_of_object applicand
      in
      let application_location =
        Location.join_all_contramap Synprs.CLF.location_of_object
          applicand_location arguments
      in
      match applicand with
      | `Term_pattern applicand ->
        let applicand' = disambiguate_as_term_pattern state applicand in
        let arguments' =
          List.map (disambiguate_as_term_pattern state) arguments
        in
        `Term_pattern
          (Synext'.CLF.Term.Pattern.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ applicand ->
        let applicand' = disambiguate_as_typ state applicand in
        let arguments' = List.map (disambiguate_as_term state) arguments in
        `Typ
          (Synext'.CLF.Typ.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module ShuntingYard =
      ShuntingYard.Make (CLF_pattern_operand) (CLF_pattern_operator)
        (struct
          (** [disambiguate_argument argument] disambiguates [argument] to a
              contextual LF term or term pattern.

              @raise Expected_term_pattern
              @raise Expected_term *)
          let disambiguate_argument argument =
            match argument with
            | CLF_pattern_operand.External_term_pattern term_pattern ->
              let location =
                Synext'.CLF.location_of_term_pattern term_pattern
              in
              raise @@ Expected_term location
            | CLF_pattern_operand.External_typ typ ->
              let location = Synext'.CLF.location_of_typ typ in
              raise @@ Expected_term_pattern location
            | CLF_pattern_operand.Parser_object object_ ->
              disambiguate_as_term state object_
            | CLF_pattern_operand.Application { applicand; arguments } -> (
              match disambiguate_juxtaposition applicand arguments with
              | `Term_pattern term_pattern ->
                let location =
                  Synext'.CLF.location_of_term_pattern term_pattern
                in
                raise @@ Expected_term location
              | `Typ typ ->
                let location = Synext'.CLF.location_of_typ typ in
                raise @@ Expected_term location)

          (** [disambiguate_argument_pattern argument] disambiguates
              [argument] to an LF term pattern.

              @raise Expected_term_pattern *)
          let disambiguate_argument_pattern argument =
            match argument with
            | CLF_pattern_operand.External_term_pattern term_pattern ->
              term_pattern
            | CLF_pattern_operand.External_typ typ ->
              let location = Synext'.CLF.location_of_typ typ in
              raise @@ Expected_term_pattern location
            | CLF_pattern_operand.Parser_object object_ ->
              disambiguate_as_term_pattern state object_
            | CLF_pattern_operand.Application { applicand; arguments } -> (
              match disambiguate_juxtaposition applicand arguments with
              | `Term_pattern term_pattern -> term_pattern
              | `Typ typ ->
                let location = Synext'.CLF.location_of_typ typ in
                raise @@ Expected_term_pattern location)

          let write operator arguments =
            let application_location =
              Location.join_all_contramap CLF_pattern_operand.location
                (CLF_pattern_operator.location operator)
                arguments
            in
            match operator with
            | CLF_pattern_operator.Type_constant { applicand; _ } ->
              let applicand' = disambiguate_as_typ state applicand in
              let arguments' = List.map disambiguate_argument arguments in
              CLF_pattern_operand.External_typ
                (Synext'.CLF.Typ.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
            | CLF_pattern_operator.Term_constant { applicand; _ } ->
              let applicand' =
                disambiguate_as_term_pattern state applicand
              in
              let arguments' =
                List.map disambiguate_argument_pattern arguments
              in
              CLF_pattern_operand.External_term_pattern
                (Synext'.CLF.Term.Pattern.Application
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
        | `Quoted_term_operator, _ -> true
        | `Type_operator (_, operator), _ | `Term_operator (_, operator), _
          -> Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
          match List.take_while is_argument ts with
          | [], rest (* [t] is an operand not in juxtaposition *) ->
            ShuntingYard.operand (CLF_pattern_operand.Parser_object t)
            :: reduce_juxtapositions_and_identify_operators rest
          | arguments, rest
          (* [t] is an applicand in juxtaposition with [arguments] *) ->
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Term_pattern t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_pattern_operand.Application
               { applicand = `Typ t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_pattern_operand.Application
               { applicand = `Term_pattern t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (CLF_pattern_operator.Type_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Term_pattern t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
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
    fun objects ->
      try
        match ShuntingYard.shunting_yard (prepare_objects objects) with
        | CLF_pattern_operand.External_typ t -> `Typ t
        | CLF_pattern_operand.External_term_pattern t -> `Term_pattern t
        | CLF_pattern_operand.Application { applicand; arguments } ->
          disambiguate_juxtaposition applicand arguments
        | CLF_pattern_operand.Parser_object _ ->
          Error.violation
            "[CLF.disambiguate_application_pattern] unexpectedly did not \
             disambiguate LF operands in rewriting"
      with
      | ShuntingYard.Empty_expression ->
        Error.violation
          "[CLF.disambiguate_application_pattern] unexpectedly ended with \
           an empty expression"
      | ShuntingYard.Leftover_expressions _ ->
        Error.violation
          "[CLF.disambiguate_application_pattern] unexpectedly ended with \
           leftover expressions"
      | ShuntingYard.Misplaced_operator { operator; operands } ->
        let operator_location = CLF_pattern_operator.location operator
        and operand_locations =
          List.map CLF_pattern_operand.location operands
        in
        raise @@ Misplaced_operator { operator_location; operand_locations }
      | ShuntingYard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
        let operator_identifier =
          CLF_pattern_operator.identifier left_operator
        and left_operator_location =
          CLF_pattern_operator.location left_operator
        and right_operator_location =
          CLF_pattern_operator.location right_operator
        in
        raise
        @@ Ambiguous_operator_placement
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        let operator_identifier =
          CLF_pattern_operator.identifier left_operator
        and left_operator_location =
          CLF_pattern_operator.location left_operator
        and right_operator_location =
          CLF_pattern_operator.location right_operator
        in
        raise
        @@ Consecutive_non_associative_operators
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = CLF_pattern_operator.identifier operator
        and operator_location = CLF_pattern_operator.location operator
        and actual_argument_locations =
          List.map CLF_pattern_operand.location operands
        in
        raise
        @@ Arity_mismatch
             { operator_identifier
             ; operator_location
             ; operator_arity
             ; actual_argument_locations
             }
end
