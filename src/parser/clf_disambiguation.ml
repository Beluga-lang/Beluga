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
      ; identifier : Qualified_identifier.t
      }

  exception
    Unbound_type_constant_or_illegal_projection_type of
      { location : Location.t
      ; identifier : Qualified_identifier.t
      }

  (** {2 Exceptions for contextual LF term disambiguation} *)

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception Illegal_block_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : Qualified_identifier.t
      }

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding : disambiguation_state_entry
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding : disambiguation_state_entry
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
      { operator_identifier : Qualified_identifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : Qualified_identifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : Qualified_identifier.t
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
    disambiguation_state -> Synprs.clf_object -> Synext.clf_typ

  val disambiguate_as_term :
    disambiguation_state -> Synprs.clf_object -> Synext.clf_term

  val disambiguate_as_substitution :
       disambiguation_state
    -> Synprs.clf_context_object
    -> Synext.clf_substitution

  val disambiguate_as_context :
       disambiguation_state
    -> Synprs.clf_context_object
    -> disambiguation_state * Synext.clf_context

  val disambiguate_as_term_pattern :
    disambiguation_state -> Synprs.clf_object -> Synext.clf_term_pattern

  val disambiguate_as_substitution_pattern :
       disambiguation_state
    -> Synprs.clf_context_object
    -> Synext.clf_substitution_pattern

  val disambiguate_as_context_pattern :
       disambiguation_state
    -> Synprs.clf_context_object
    -> Synext.clf_context_pattern
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
      ; identifier : Qualified_identifier.t
      }

  exception
    Unbound_type_constant_or_illegal_projection_type of
      { location : Location.t
      ; identifier : Qualified_identifier.t
      }

  (** {2 Exceptions for contextual LF term disambiguation} *)

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception Illegal_block_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : Qualified_identifier.t
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
      ; actual_binding : disambiguation_state_entry
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding : disambiguation_state_entry
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
      { operator_identifier : Qualified_identifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : Qualified_identifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : Qualified_identifier.t
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
        Format.fprintf ppf
          "Holes may not appear as contextual LF types: %a@." Location.pp
          location
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
          "Tuple terms may not appear as contextual LF types: %a@."
          Location.pp location
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
          "Substitution variables may not appear as contextual LF types: \
           %a@."
          Location.pp location
    | Unbound_type_constant { location; identifier } ->
        Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
          Qualified_identifier.pp identifier Location.pp location
    | Unbound_type_constant_or_illegal_projection_type
        { location; identifier } ->
        Format.fprintf ppf
          "Either the LF type-level constant %a is unbound, or a projection \
           term may not appear as a contextual LF type: %a@."
          Qualified_identifier.pp identifier Location.pp location
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
          "Block types may not appear as contextual LF terms: %a@."
          Location.pp location
    | Unbound_term_constant { location; identifier } ->
        Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
          Qualified_identifier.pp identifier Location.pp location
    | Illegal_subtitution_term_label location ->
        Format.fprintf ppf
          "Terms in a substitution may not be labelled: %a@." Location.pp
          location
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
        ; actual_binding = Disambiguation_state.LF_type_constant _
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found an LF type constant \
           instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location; actual_binding = Disambiguation_state.LF_term_variable }
      ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found an LF term variable \
           instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location; actual_binding = Disambiguation_state.Meta_variable } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a meta-variable \
           instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = Disambiguation_state.Parameter_variable
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a parameter \
           variable instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = Disambiguation_state.Substitution_variable
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a substitution \
           variable instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location; actual_binding = Disambiguation_state.Context_variable }
      ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a context variable \
           instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_variable
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a computation-level \
           variable instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_type_constant _
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a computation-level \
           type constant instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding =
            Disambiguation_state.Computation_term_constructor _
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a computation-level \
           term constructor instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_cotype_constant _
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a computation-level \
           cotype constant instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_term_destructor
        } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a computation-level \
           term destructor instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location; actual_binding = Disambiguation_state.Query } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a logic programming \
           query identifier instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location; actual_binding = Disambiguation_state.MQuery } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a logic programming \
           meta-query identifier instead: %a@."
          Location.pp location
    | Expected_term_constant
        { location; actual_binding = Disambiguation_state.Module _ } ->
        Format.fprintf ppf
          "Expected an LF term-level constant but found a module instead: \
           %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.LF_term_constant _
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found an LF term constant \
           instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location; actual_binding = Disambiguation_state.LF_term_variable }
      ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found an LF term variable \
           instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location; actual_binding = Disambiguation_state.Meta_variable } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a meta-variable \
           instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.Parameter_variable
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a parameter \
           variable instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.Substitution_variable
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a substitution \
           variable instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location; actual_binding = Disambiguation_state.Context_variable }
      ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a context variable \
           instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_variable
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a computation-level \
           variable instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_type_constant _
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a computation-level \
           type constant instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding =
            Disambiguation_state.Computation_term_constructor _
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a computation-level \
           term constructor instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_cotype_constant _
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a computation-level \
           cotype constant instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location
        ; actual_binding = Disambiguation_state.Computation_term_destructor
        } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a computation-level \
           term destructor instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location; actual_binding = Disambiguation_state.Module _ } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a module instead: \
           %a@."
          Location.pp location
    | Expected_term location ->
        Format.fprintf ppf
          "Expected a contextual LF term but found a contextual LF type \
           instead: %a@."
          Location.pp location
    | Expected_type location ->
        Format.fprintf ppf
          "Expected an LF type but found an LF term instead: %a@."
          Location.pp location
    | Ambiguous_operator_placement
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
        Format.fprintf ppf
          "Ambiguous occurrences of the LF term-level or type-level \
           operator %a after rewriting: %a and %a@."
          Qualified_identifier.pp operator_identifier Location.pp
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
          Qualified_identifier.pp operator_identifier Location.pp
          left_operator_location Location.pp right_operator_location
    | Arity_mismatch
        { operator_identifier
        ; operator_location
        ; operator_arity
        ; actual_argument_locations
        } ->
        let expected_arguments_count = operator_arity
        and actual_arguments_count = List.length actual_argument_locations in
        Format.fprintf ppf
          "Operator %a expected %d arguments but got %d: %a@."
          Qualified_identifier.pp operator_identifier
          expected_arguments_count actual_arguments_count Location.pp
          operator_location
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
          "Tuple term patterns may not appear as contextual LF type \
           patterns: %a@."
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
          "Forward arrow types may not appear as contextual LF term \
           patterns: %a@."
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
          "Parameter variable bindings may not occur in contextual LF \
           context patterns: %a@."
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
    | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some (Format.stringify pp_exception exn) with
        | Invalid_argument _ -> Option.none)

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
    | Synprs.CLF.Object.Raw_hole { location; _ } ->
        raise (Illegal_hole_type location)
    | Synprs.CLF.Object.Raw_lambda { location; _ } ->
        raise (Illegal_lambda_type location)
    | Synprs.CLF.Object.Raw_annotated { location; _ } ->
        raise (Illegal_annotated_type location)
    | Synprs.CLF.Object.Raw_pi { location; parameter_sort = Option.None; _ }
      ->
        raise (Illegal_untyped_pi_type location)
    | Synprs.CLF.Object.Raw_tuple { location; _ } ->
        raise (Illegal_tuple_type location)
    | Synprs.CLF.Object.Raw_projection { location; _ } ->
        raise (Illegal_projection_type location)
    | Synprs.CLF.Object.Raw_substitution { location; _ } ->
        raise (Illegal_substitution_type location)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Hash; _ } ->
        raise (Illegal_parameter_variable_type location)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = _identifier, `Dollar; _ } ->
        raise (Illegal_substitution_variable_type location)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF type, plain identifiers are necessarily type-level
           constants. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            Synext.CLF.Typ.Constant
              { location
              ; identifier = qualified_identifier
              ; operator
              ; quoted
              }
        | entry ->
            raise
              (Expected_type_constant { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_identifier _ ->
            raise
              (Unbound_type_constant
                 { location; identifier = qualified_identifier }))
    | Synprs.CLF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers. *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As an LF type, identifiers of the form [<identifier>
           <dot-identifier>+] are type-level constants, or illegal named
           projections. *)
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            Synext.CLF.Typ.Constant
              { location; identifier; operator; quoted }
        | entry ->
            raise
              (Expected_type_constant { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            raise
              (Unbound_type_constant_or_illegal_projection_type
                 { location; identifier }))
    | Synprs.CLF.Object.Raw_arrow { location; domain; range; orientation } ->
        let domain' = disambiguate_as_typ state domain
        and range' = disambiguate_as_typ state range in
        Synext.CLF.Typ.Arrow
          { location; domain = domain'; range = range'; orientation }
    | Synprs.CLF.Object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
        let parameter_type' = disambiguate_as_typ state parameter_type in
        match parameter_identifier with
        | Option.None ->
            let body' = disambiguate_as_typ state body in
            Synext.CLF.Typ.Pi
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
            Synext.CLF.Typ.Pi
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })
    | Synprs.CLF.Object.Raw_application { objects; _ } -> (
        match disambiguate_application state objects with
        | `Term term ->
            let location = Synext.location_of_clf_term term in
            raise (Expected_type location)
        | `Typ typ -> typ)
    | Synprs.CLF.Object.Raw_block
        { location; elements = List1.T ((Option.None, t), []) } ->
        let t' = disambiguate_as_typ state t in
        Synext.CLF.Typ.Block { location; elements = `Unnamed t' }
    | Synprs.CLF.Object.Raw_block { location; elements } ->
        let _state', elements_rev' =
          List1.fold_left
            (fun element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  raise (Illegal_unnamed_block_element_type location)
              | Option.Some identifier, typ ->
                  let typ' = disambiguate_as_typ state typ in
                  let elements' = List1.singleton (identifier, typ')
                  and state' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state
                  in
                  (state', elements'))
            (fun (state', elements') element ->
              match element with
              | Option.None, typ ->
                  let location = Synprs.location_of_clf_object typ in
                  raise (Illegal_unnamed_block_element_type location)
              | Option.Some identifier, typ ->
                  let typ' = disambiguate_as_typ state' typ in
                  let elements'' = List1.cons (identifier, typ') elements'
                  and state'' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state'
                  in
                  (state'', elements''))
            elements
        in
        let elements' = List1.rev elements_rev' in
        Synext.CLF.Typ.Block { location; elements = `Record elements' }

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
    | Synprs.CLF.Object.Raw_pi { location; _ } ->
        raise (Illegal_pi_term location)
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        raise (Illegal_forward_arrow_term location)
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        raise (Illegal_backward_arrow_term location)
    | Synprs.CLF.Object.Raw_block { location; _ } ->
        raise (Illegal_block_term location)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Hash; _ } ->
        Synext.CLF.Term.Parameter_variable { location; identifier }
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } ->
        Synext.CLF.Term.Substitution_variable { location; identifier }
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Plain; quoted; _ } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            Synext.CLF.Term.Constant
              { location
              ; identifier = qualified_identifier
              ; operator
              ; quoted
              }
        | Disambiguation_state.LF_term_variable
        | Disambiguation_state.Meta_variable ->
            (* Bound variable *)
            Synext.CLF.Term.Variable { location; identifier }
        | entry ->
            raise
              (Expected_term_constant { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_identifier _ ->
            (* Free variable *)
            Synext.CLF.Term.Variable { location; identifier })
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
                      (Disambiguation_state.Module { entries = state' } as
                      entry) -> (
                      match remaining_identifiers with
                      | [] ->
                          (* Lookups ended with a module. *)
                          raise
                            (Expected_term_constant
                               { location; actual_binding = entry })
                      | next_identifier' :: remaining_identifiers' ->
                          let looked_up_identifiers' =
                            next_identifier :: looked_up_identifiers
                          in
                          helper state' looked_up_identifiers'
                            next_identifier' remaining_identifiers')
                  | Option.Some
                      (Disambiguation_state.LF_term_constant { operator })
                    -> (
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
                  | Option.Some entry ->
                      (* Lookups ended with an entry that cannot be used in a
                         contextual LF term projection. *)
                      let location =
                        Location.join_all1_contramap Identifier.location
                          (List1.from next_identifier looked_up_identifiers)
                      in
                      raise
                        (Expected_term_constant
                           { location; actual_binding = entry })
                      (* TODO: Misleading, modules are allowed as well *)
                  | Option.None -> (
                      match remaining_identifiers with
                      | [] ->
                          raise
                            (Unbound_term_constant { location; identifier })
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
                helper
                  (Disambiguation_state.get_bindings state)
                  [] m (ms @ [ name ])
            | Disambiguation_state.LF_term_constant { operator } ->
                (* Immediately looked up an LF term constant. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let identifier = Qualified_identifier.make_simple m in
                let term =
                  Synext.CLF.Term.Constant
                    { identifier; location; operator; quoted = false }
                in
                reduce_projections' term ms name
            | Disambiguation_state.LF_term_variable
            | Disambiguation_state.Meta_variable ->
                (* Immediately looked up an LF term variable or a
                   meta-variable. The remaining identifiers are named
                   projections. *)
                let location = Identifier.location m in
                let term =
                  Synext.CLF.Term.Variable { location; identifier = m }
                in
                reduce_projections' term ms name
            | entry ->
                (* First lookup ended with an entry that cannot be used in a
                   contextual LF term projection. *)
                let location = Identifier.location m in
                raise
                  (Expected_term_constant
                     { location; actual_binding = entry })
                (* TODO: Misleading, module, term variable, meta-variable are
                   allowed *)
            | exception Disambiguation_state.Unbound_identifier _ ->
                (* Immediately looked up a free variable. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let term =
                  Synext.CLF.Term.Variable { location; identifier = m }
                in
                reduce_projections' term ms name))
    | Synprs.CLF.Object.Raw_application { objects; _ } -> (
        match disambiguate_application state objects with
        | `Typ typ ->
            let location = Synext.location_of_clf_typ typ in
            raise (Expected_term location)
        | `Term term -> term)
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let parameter_type' =
          Option.map (disambiguate_as_typ state) parameter_sort
        in
        match parameter_identifier with
        | Option.None ->
            let body' = disambiguate_as_term state body in
            Synext.CLF.Term.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              }
        | Option.Some name ->
            let state' =
              Disambiguation_state.add_lf_term_variable name state
            in
            let body' = disambiguate_as_term state' body in
            Synext.CLF.Term.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })
    | Synprs.CLF.Object.Raw_hole { location; variant } ->
        Synext.CLF.Term.Hole { location; variant }
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let elements' = List1.map (disambiguate_as_term state) elements in
        Synext.CLF.Term.Tuple { location; terms = elements' }
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let term' = disambiguate_as_term state object_ in
        Synext.CLF.Term.Projection { location; term = term'; projection }
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let term' = disambiguate_as_term state object_ in
        let substitution' =
          disambiguate_as_substitution state substitution
        in
        Synext.CLF.Term.Substitution
          { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let term' = disambiguate_as_term state object_
        and typ' = disambiguate_as_typ state sort in
        Synext.CLF.Term.TypeAnnotated { location; term = term'; typ = typ' }

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
              raise (Illegal_subtitution_term_label location))
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
              let closure' = disambiguate_as_substitution state closure in
              ( Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              , xs )
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              ( Synext.CLF.Substitution.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              , xs )
          | _ ->
              ( Synext.CLF.Substitution.Head.None { location = head_location }
              , objects' )
        in
        let terms' = List.map (disambiguate_as_term state) objects'' in
        { Synext.CLF.Substitution.location; head = head'; terms = terms' }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let terms' = List.map (disambiguate_as_term state) objects' in
        { Synext.CLF.Substitution.location
        ; head =
            Synext.CLF.Substitution.Head.Identity
              { location = head_location }
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
              raise (Illegal_context_parameter_variable_binding location)
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Dollar; _ } )
          (* Substitution variables may only occur in meta-contexts *) ->
              let location = Identifier.location identifier in
              raise (Illegal_context_substitution_variable_binding location)
          | Option.None, typ (* Binding identifier missing *) ->
              let location = Synprs.location_of_clf_object typ in
              raise (Illegal_context_missing_binding_identifier location))
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
        raise (Illegal_context_identity location)
    | Synprs.CLF.Context_object.Head.None { location = head_location } -> (
        match objects with
        | ( Option.None
          , Synprs.CLF.Object.Raw_hole
              { variant = `Underscore; location = head_location } )
            (* Hole as context head *)
          :: xs ->
            let head' =
              Synext.CLF.Context.Head.Hole { location = head_location }
            and state', bindings' = disambiguate_context_bindings state xs in
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
                  disambiguate_context_bindings state xs
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
                and state', bindings' =
                  disambiguate_context_bindings state objects
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
            and state', bindings' =
              disambiguate_context_bindings state objects
            in
            let context' =
              { Synext.CLF.Context.location
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
          let applicand' = disambiguate_as_term state applicand in
          let arguments' =
            List1.map
              (disambiguate_as_term state)
              (List1.unsafe_of_list arguments)
          in
          `Term
            (Synext.CLF.Term.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
      | `Typ applicand ->
          let applicand' = disambiguate_as_typ state applicand in
          let arguments' =
            List1.map
              (disambiguate_as_term state)
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
        (CLF_operator)
        (struct
          (** [disambiguate_argument argument] disambiguates [argument] to an
              LF term.

              @raise Expected_term *)
          let disambiguate_argument argument =
            match argument with
            | CLF_operand.External_term term -> term
            | CLF_operand.External_typ typ ->
                let location = Synext.location_of_clf_typ typ in
                raise (Expected_term location)
            | CLF_operand.Parser_object object_ ->
                disambiguate_as_term state object_
            | CLF_operand.Application { applicand; arguments } -> (
                match disambiguate_juxtaposition applicand arguments with
                | `Term term -> term
                | `Typ typ ->
                    let location = Synext.location_of_clf_typ typ in
                    raise (Expected_term location))

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
                let applicand' = disambiguate_as_typ state applicand in
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
                let applicand' = disambiguate_as_term state applicand in
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
    fun objects ->
      try
        match Shunting_yard.shunting_yard (prepare_objects objects) with
        | CLF_operand.External_typ t -> `Typ t
        | CLF_operand.External_term t -> `Term t
        | CLF_operand.Application { applicand; arguments } ->
            disambiguate_juxtaposition applicand arguments
        | CLF_operand.Parser_object _ ->
            Error.violation
              "[CLF.disambiguate_application] unexpectedly did not \
               disambiguate LF operands in rewriting"
      with
      | Shunting_yard.Empty_expression ->
          Error.violation
            "[CLF.disambiguate_application] unexpectedly ended with an \
             empty expression"
      | Shunting_yard.Leftover_expressions _ ->
          Error.violation
            "[CLF.disambiguate_application] unexpectedly ended with \
             leftover expressions"
      | Shunting_yard.Misplaced_operator { operator; operands } ->
          let operator_location = CLF_operator.location operator
          and operand_locations = List.map CLF_operand.location operands in
          raise (Misplaced_operator { operator_location; operand_locations })
      | Shunting_yard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
          let operator_identifier = CLF_operator.identifier left_operator
          and left_operator_location = CLF_operator.location left_operator
          and right_operator_location =
            CLF_operator.location right_operator
          in
          raise
            (Ambiguous_operator_placement
               { operator_identifier
               ; left_operator_location
               ; right_operator_location
               })
      | Shunting_yard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
          let operator_identifier = CLF_operator.identifier left_operator
          and left_operator_location = CLF_operator.location left_operator
          and right_operator_location =
            CLF_operator.location right_operator
          in
          raise
            (Consecutive_non_associative_operators
               { operator_identifier
               ; left_operator_location
               ; right_operator_location
               })
      | Shunting_yard.Arity_mismatch { operator; operator_arity; operands }
        ->
          let operator_identifier = CLF_operator.identifier operator
          and operator_location = CLF_operator.location operator
          and actual_argument_locations =
            List.map CLF_operand.location operands
          in
          raise
            (Arity_mismatch
               { operator_identifier
               ; operator_location
               ; operator_arity
               ; actual_argument_locations
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
    | Synprs.CLF.Object.Raw_pi { location; _ } ->
        raise (Illegal_pi_term_pattern location)
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        raise (Illegal_forward_arrow_term_pattern location)
    | Synprs.CLF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        raise (Illegal_backward_arrow_term_pattern location)
    | Synprs.CLF.Object.Raw_block { location; _ } ->
        raise (Illegal_block_term_pattern location)
    | Synprs.CLF.Object.Raw_hole
        { location; variant = `Unlabelled | `Labelled _ } ->
        raise (Illegal_labellable_hole_term_pattern location)
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Hash; _ } ->
        Synext.CLF.Term.Pattern.Parameter_variable { location; identifier }
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, `Dollar; _ } ->
        Synext.CLF.Term.Pattern.Substitution_variable
          { location; identifier }
    | Synprs.CLF.Object.Raw_identifier
        { location; identifier = identifier, _modifier; quoted; _ } -> (
        (* As an LF term pattern, plain identifiers are either term-level
           constants, variables already present in the pattern, or new
           pattern variables. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        match Disambiguation_state.lookup qualified_identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            Synext.CLF.Term.Pattern.Constant
              { location
              ; identifier = qualified_identifier
              ; operator
              ; quoted
              }
        | _ -> Synext.CLF.Term.Pattern.Variable { location; identifier })
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
                      (Disambiguation_state.Module { entries = state' } as
                      entry) -> (
                      match remaining_identifiers with
                      | [] ->
                          (* Lookups ended with a module. *)
                          raise
                            (Expected_term_constant
                               { location; actual_binding = entry })
                      | next_identifier' :: remaining_identifiers' ->
                          let looked_up_identifiers' =
                            next_identifier :: looked_up_identifiers
                          in
                          helper state' looked_up_identifiers'
                            next_identifier' remaining_identifiers')
                  | Option.Some
                      (Disambiguation_state.LF_term_constant { operator })
                    -> (
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
                  | Option.Some entry ->
                      (* Lookups ended with an entry that cannot be used in a
                         contextual LF term projection. *)
                      let location =
                        Location.join_all1_contramap Identifier.location
                          (List1.from next_identifier looked_up_identifiers)
                      in
                      raise
                        (Expected_term_constant
                           { location; actual_binding = entry })
                  | Option.None -> (
                      match remaining_identifiers with
                      | [] ->
                          raise
                            (Unbound_term_constant { location; identifier })
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
                helper
                  (Disambiguation_state.get_bindings state)
                  [] m (ms @ [ name ])
            | Disambiguation_state.LF_term_constant { operator } ->
                (* Immediately looked up an LF term constant. The remaining
                   identifiers are named projections. *)
                let location = Identifier.location m in
                let identifier = Qualified_identifier.make_simple m in
                let term =
                  Synext.CLF.Term.Pattern.Constant
                    { identifier; location; operator; quoted = false }
                in
                reduce_projections' term ms name
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
                reduce_projections' term ms name
            | entry ->
                (* First lookup ended with an entry that cannot be used in a
                   contextual LF term projection. *)
                let location = Identifier.location m in
                raise
                  (Expected_term_constant
                     { location; actual_binding = entry })
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
                reduce_projections' term ms name))
    | Synprs.CLF.Object.Raw_application { objects; _ } -> (
        match disambiguate_application_pattern state objects with
        | `Typ typ ->
            let location = Synext.location_of_clf_typ typ in
            raise (Expected_term_pattern location)
        | `Term_pattern term_pattern -> term_pattern)
    | Synprs.CLF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let parameter_type' =
          Option.map (disambiguate_as_typ state) parameter_sort
        in
        match parameter_identifier with
        | Option.None ->
            let body' = disambiguate_as_term_pattern state body in
            Synext.CLF.Term.Pattern.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              }
        | Option.Some name ->
            let state' =
              Disambiguation_state.add_lf_term_variable name state
            in
            let body' = disambiguate_as_term_pattern state' body in
            Synext.CLF.Term.Pattern.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })
    | Synprs.CLF.Object.Raw_hole { location; variant = `Underscore } ->
        Synext.CLF.Term.Pattern.Wildcard { location }
    | Synprs.CLF.Object.Raw_tuple { location; elements } ->
        let elements' =
          List1.map (disambiguate_as_term_pattern state) elements
        in
        Synext.CLF.Term.Pattern.Tuple { location; terms = elements' }
    | Synprs.CLF.Object.Raw_projection { location; object_; projection } ->
        let term' = disambiguate_as_term_pattern state object_ in
        Synext.CLF.Term.Pattern.Projection
          { location; term = term'; projection }
    | Synprs.CLF.Object.Raw_substitution { location; object_; substitution }
      ->
        let term' = disambiguate_as_term_pattern state object_ in
        let substitution' =
          disambiguate_as_substitution state substitution
        in
        Synext.CLF.Term.Pattern.Substitution
          { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.Raw_annotated { location; object_; sort } ->
        let term' = disambiguate_as_term_pattern state object_
        and typ' = disambiguate_as_typ state sort in
        Synext.CLF.Term.Pattern.TypeAnnotated
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
              raise (Illegal_subtitution_pattern_term_label location))
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
              let closure' = disambiguate_as_substitution state closure in
              ( Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                  { location; identifier; closure = Option.some closure' }
              , xs )
          | Synprs.CLF.Object.Raw_identifier
              { location; identifier = identifier, `Dollar; _ }
              (* A substitution variable *)
            :: xs ->
              ( Synext.CLF.Substitution.Pattern.Head.Substitution_variable
                  { location; identifier; closure = Option.none }
              , xs )
          | _ ->
              ( Synext.CLF.Substitution.Pattern.Head.None
                  { location = head_location }
              , objects' )
        in
        let terms' =
          List.map (disambiguate_as_term_pattern state) objects''
        in
        { Synext.CLF.Substitution.Pattern.location
        ; head = head'
        ; terms = terms'
        }
    | Synprs.CLF.Context_object.Head.Identity { location = head_location } ->
        let terms' =
          List.map (disambiguate_as_term_pattern state) objects'
        in
        { Synext.CLF.Substitution.Pattern.location
        ; head =
            Synext.CLF.Substitution.Pattern.Head.Identity
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
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Plain; _ } ) ->
              let location = Identifier.location identifier in
              raise (Illegal_context_pattern_missing_binding_type location)
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Hash; _ } ) ->
              let location = Identifier.location identifier in
              raise
                (Illegal_context_pattern_parameter_variable_binding location)
          | ( Option.None
            , Synprs.CLF.Object.Raw_identifier
                { identifier = identifier, `Dollar; _ } ) ->
              let location = Identifier.location identifier in
              raise
                (Illegal_context_pattern_substitution_variable_binding
                   location)
          | Option.None, typ ->
              let location = Synprs.location_of_clf_object typ in
              raise
                (Illegal_context_pattern_missing_binding_identifier location))
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
        raise (Illegal_context_pattern_identity location)
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
            and bindings' = disambiguate_context_pattern_bindings state xs in
            { Synext.CLF.Context.Pattern.location
            ; head = head'
            ; bindings = bindings'
            }
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
                  disambiguate_context_pattern_bindings state xs
                in
                { Synext.CLF.Context.Pattern.location
                ; head = head'
                ; bindings = bindings'
                }
            | _
            | (exception Disambiguation_state.Unbound_identifier _) ->
                let head' =
                  Synext.CLF.Context.Pattern.Head.None
                    { location = head_location }
                and bindings' =
                  disambiguate_context_pattern_bindings state objects
                in
                { Synext.CLF.Context.Pattern.location
                ; head = head'
                ; bindings = bindings'
                })
        | _ ->
            let head' =
              Synext.CLF.Context.Pattern.Head.None
                { location = head_location }
            and bindings' =
              disambiguate_context_pattern_bindings state objects
            in
            { Synext.CLF.Context.Pattern.location
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
          let applicand' = disambiguate_as_term_pattern state applicand in
          let arguments' =
            List1.map
              (disambiguate_as_term_pattern state)
              (List1.unsafe_of_list arguments)
          in
          `Term_pattern
            (Synext.CLF.Term.Pattern.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
      | `Typ applicand ->
          let applicand' = disambiguate_as_typ state applicand in
          let arguments' =
            List1.map
              (disambiguate_as_term state)
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
        (CLF_pattern_operator)
        (struct
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
                raise (Expected_term location)
            | CLF_pattern_operand.External_typ typ ->
                let location = Synext.location_of_clf_typ typ in
                raise (Expected_term_pattern location)
            | CLF_pattern_operand.Parser_object object_ ->
                disambiguate_as_term state object_
            | CLF_pattern_operand.Application { applicand; arguments } -> (
                match disambiguate_juxtaposition applicand arguments with
                | `Term_pattern term_pattern ->
                    let location =
                      Synext.location_of_clf_term_pattern term_pattern
                    in
                    raise (Expected_term location)
                | `Typ typ ->
                    let location = Synext.location_of_clf_typ typ in
                    raise (Expected_term location))

          (** [disambiguate_argument_pattern argument] disambiguates
              [argument] to an LF term pattern.

              @raise Expected_term_pattern *)
          let disambiguate_argument_pattern argument =
            match argument with
            | CLF_pattern_operand.External_term_pattern term_pattern ->
                term_pattern
            | CLF_pattern_operand.External_typ typ ->
                let location = Synext.location_of_clf_typ typ in
                raise (Expected_term_pattern location)
            | CLF_pattern_operand.Parser_object object_ ->
                disambiguate_as_term_pattern state object_
            | CLF_pattern_operand.Application { applicand; arguments } -> (
                match disambiguate_juxtaposition applicand arguments with
                | `Term_pattern term_pattern -> term_pattern
                | `Typ typ ->
                    let location = Synext.location_of_clf_typ typ in
                    raise (Expected_term_pattern location))

          let write operator arguments =
            let application_location =
              Location.join_all_contramap CLF_pattern_operand.location
                (CLF_pattern_operator.location operator)
                arguments
            in
            match operator with
            | CLF_pattern_operator.Type_constant { applicand; _ } ->
                let applicand' = disambiguate_as_typ state applicand in
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
                  disambiguate_as_term_pattern state applicand
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
    fun objects ->
      try
        match Shunting_yard.shunting_yard (prepare_objects objects) with
        | CLF_pattern_operand.External_typ t -> `Typ t
        | CLF_pattern_operand.External_term_pattern t -> `Term_pattern t
        | CLF_pattern_operand.Application { applicand; arguments } ->
            disambiguate_juxtaposition applicand arguments
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
          raise (Misplaced_operator { operator_location; operand_locations })
      | Shunting_yard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
          let operator_identifier =
            CLF_pattern_operator.identifier left_operator
          and left_operator_location =
            CLF_pattern_operator.location left_operator
          and right_operator_location =
            CLF_pattern_operator.location right_operator
          in
          raise
            (Ambiguous_operator_placement
               { operator_identifier
               ; left_operator_location
               ; right_operator_location
               })
      | Shunting_yard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
          let operator_identifier =
            CLF_pattern_operator.identifier left_operator
          and left_operator_location =
            CLF_pattern_operator.location left_operator
          and right_operator_location =
            CLF_pattern_operator.location right_operator
          in
          raise
            (Consecutive_non_associative_operators
               { operator_identifier
               ; left_operator_location
               ; right_operator_location
               })
      | Shunting_yard.Arity_mismatch { operator; operator_arity; operands }
        ->
          let operator_identifier = CLF_pattern_operator.identifier operator
          and operator_location = CLF_pattern_operator.location operator
          and actual_argument_locations =
            List.map CLF_pattern_operand.location operands
          in
          raise
            (Arity_mismatch
               { operator_identifier
               ; operator_location
               ; operator_arity
               ; actual_argument_locations
               })
end
