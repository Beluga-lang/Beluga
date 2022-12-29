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
      ; identifier : Qualified_identifier.t
      }

  (** {2 Exceptions for LF term disambiguation} *)

  exception Illegal_type_kind_term of Location.t

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

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

  (** {1 Disambiguation} *)

  val disambiguate_as_kind :
    disambiguation_state -> Synprs.lf_object -> Synext.lf_kind

  val disambiguate_as_typ :
    disambiguation_state -> Synprs.lf_object -> Synext.lf_typ

  val disambiguate_as_term :
    disambiguation_state -> Synprs.lf_object -> Synext.lf_term
end

(** Disambiguation of LF kinds, types and terms from the parser syntax to the
    external syntax.

    This disambiguation does not perform normalization nor validation. *)
module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
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
      ; identifier : Qualified_identifier.t
      }

  (** {2 Exceptions for LF term disambiguation} *)

  exception Illegal_type_kind_term of Location.t

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

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

  (** {2 Exception Printing} *)

  (* TODO: Extract exception printer definition to a functor (over
     LF_DISAMBIGUATOR) with the side-effect of registering that printer. Use
     located errors. *)

  let pp_exception ppf = function
    | Illegal_identifier_kind location ->
        Format.fprintf ppf "Identifiers may not appear as LF kinds: %a@."
          Location.pp location
    | Illegal_qualified_identifier_kind location ->
        Format.fprintf ppf
          "Qualified identifiers may not appear as LF kinds: %a@."
          Location.pp location
    | Illegal_backward_arrow_kind location ->
        Format.fprintf ppf "Backward arrows may not appear as LF kinds: %a@."
          Location.pp location
    | Illegal_hole_kind location ->
        Format.fprintf ppf "Holes may not appear as LF kinds: %a@."
          Location.pp location
    | Illegal_lambda_kind location ->
        Format.fprintf ppf "Lambdas may not appear as LF kinds: %a@."
          Location.pp location
    | Illegal_annotated_kind location ->
        Format.fprintf ppf
          "Type ascriptions to terms may not appear as LF kinds: %a@."
          Location.pp location
    | Illegal_application_kind location ->
        Format.fprintf ppf
          "Term applications may not appear as LF kinds: %a@." Location.pp
          location
    | Illegal_untyped_pi_kind location ->
        Format.fprintf ppf
          "The LF Pi kind is missing its parameter type annotation: %a@."
          Location.pp location
    | Illegal_type_kind_type location ->
        Format.fprintf ppf "The kind `type' may not appear as LF types: %a@."
          Location.pp location
    | Illegal_hole_type location ->
        Format.fprintf ppf "Holes may not appear as LF types: %a@."
          Location.pp location
    | Illegal_lambda_type location ->
        Format.fprintf ppf "Lambdas may not appear as LF types: %a@."
          Location.pp location
    | Illegal_annotated_type location ->
        Format.fprintf ppf
          "Type ascriptions may not appear as LF types: %a@." Location.pp
          location
    | Illegal_untyped_pi_type location ->
        Format.fprintf ppf
          "The LF Pi type is missing its parameter type annotation: %a@."
          Location.pp location
    | Unbound_type_constant { location; identifier } ->
        Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
          Qualified_identifier.pp identifier Location.pp location
    | Illegal_type_kind_term location ->
        Format.fprintf ppf "The kind `type' may not appear as LF terms: %a@."
          Location.pp location
    | Illegal_pi_term location ->
        Format.fprintf ppf
          "Pi kinds or types may not appear as LF terms: %a@." Location.pp
          location
    | Illegal_forward_arrow_term location ->
        Format.fprintf ppf "Forward arrows may not appear as LF terms: %a@."
          Location.pp location
    | Illegal_backward_arrow_term location ->
        Format.fprintf ppf "Backward arrows may not appear as LF terms: %a@."
          Location.pp location
    | Unbound_term_constant { location; identifier } ->
        Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
          Qualified_identifier.pp identifier Location.pp location
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
           term constructor constant instead: %a@."
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
           type destructor constant instead: %a@."
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
        { location; actual_binding = Disambiguation_state.Query } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a logic programming \
           query identifier instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location; actual_binding = Disambiguation_state.MQuery } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a logic programming \
           meta-query identifier instead: %a@."
          Location.pp location
    | Expected_type_constant
        { location; actual_binding = Disambiguation_state.Module _ } ->
        Format.fprintf ppf
          "Expected an LF type-level constant but found a module instead: \
           %a@."
          Location.pp location
    | Expected_term location ->
        Format.fprintf ppf
          "Expected an LF term but found an LF type instead: %a@."
          Location.pp location
    | Expected_type location ->
        Format.fprintf ppf
          "Expected an LF type but found an LF term instead: %a@."
          Location.pp location
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
          "Ambiguous occurrences of the LF term-level or type-level \
           operator %a after rewriting: %a and %a@."
          Qualified_identifier.pp operator_identifier Location.pp
          left_operator_location Location.pp right_operator_location
    | Consecutive_non_associative_operators
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
        Format.fprintf ppf
          "Consecutive occurrences of the LF term-level or type-level \
           operator %a after rewriting: %a and %a@."
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
    | Synprs.LF.Object.Raw_identifier { identifier; quoted; _ } ->
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        resolve_lf_operator state ~quoted qualified_identifier
    | Synprs.LF.Object.Raw_qualified_identifier { identifier; quoted; _ } ->
        resolve_lf_operator state ~quoted identifier
    | _ -> `Not_an_operator

  (** LF term-level or type-level operands for rewriting of prefix, infix and
      postfix operators using {!Shunting_yard}. *)
  module LF_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext.LF.Typ.t  (** A disambiguated LF type. *)
      | External_term of Synext.LF.Term.t  (** A disambiguated LF term. *)
      | Parser_object of Synprs.lf_object
          (** An LF object that has yet to be disambiguated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.lf_object | `Term of Synprs.lf_object ]
          ; arguments : Synprs.lf_object List.t
          }  (** An LF type-level or term-level application. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext.location_of_lf_typ t
      | External_term t -> Synext.location_of_lf_term t
      | Parser_object t -> Synprs.location_of_lf_object t
      | Application { applicand; arguments } ->
          let applicand_location =
            match applicand with
            | `Typ applicand
            | `Term applicand ->
                Synprs.location_of_lf_object applicand
          in
          Location.join_all_contramap Synprs.location_of_lf_object
            applicand_location arguments
  end

  (** LF term-level or type-level operators for rewriting of prefix, infix
      and postfix operators using {!Shunting_yard}. *)
  module LF_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : Qualified_identifier.t
          ; operator : Operator.t
          ; applicand : Synprs.lf_object
          }
          (** An LF type-level constant with its operator definition in the
              disambiguation context, and its corresponding AST. *)
      | Term_constant of
          { identifier : Qualified_identifier.t
          ; operator : Operator.t
          ; applicand : Synprs.lf_object
          }
          (** An LF term-level constant with its operator definition in the
              disambiguation context, and its corresponding AST. *)

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

    let location = Fun.(applicand >> Synprs.location_of_lf_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module Qualified_identifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [disambiguate_as_kind state object_] is [object_] rewritten as an LF
      kind with respect to the disambiguation context [state].

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from raw LF objects to LF kinds, see the Beluga language specification. *)
  let rec disambiguate_as_kind state object_ =
    match object_ with
    | Synprs.LF.Object.Raw_identifier { location; _ } ->
        raise (Illegal_identifier_kind location)
    | Synprs.LF.Object.Raw_qualified_identifier { location; _ } ->
        raise (Illegal_qualified_identifier_kind location)
    | Synprs.LF.Object.Raw_hole { location; _ } ->
        raise (Illegal_hole_kind location)
    | Synprs.LF.Object.Raw_lambda { location; _ } ->
        raise (Illegal_lambda_kind location)
    | Synprs.LF.Object.Raw_annotated { location; _ } ->
        raise (Illegal_annotated_kind location)
    | Synprs.LF.Object.Raw_application { location; _ } ->
        raise (Illegal_application_kind location)
    | Synprs.LF.Object.Raw_type { location } ->
        Synext.LF.Kind.Typ { location }
    | Synprs.LF.Object.Raw_arrow { location; domain; range; orientation }
      -> (
        match orientation with
        | `Backward -> raise (Illegal_backward_arrow_kind location)
        | `Forward ->
            let domain' = disambiguate_as_typ state domain
            and range' = disambiguate_as_kind state range in
            Synext.LF.Kind.Arrow
              { location; domain = domain'; range = range' })
    | Synprs.LF.Object.Raw_pi
        { location; parameter_identifier; parameter_sort; body } -> (
        match parameter_sort with
        | Option.None -> raise (Illegal_untyped_pi_kind location)
        | Option.Some parameter_type ->
            let parameter_type' = disambiguate_as_typ state parameter_type in
            let body' =
              match parameter_identifier with
              | Option.None -> disambiguate_as_kind state body
              | Option.Some identifier ->
                  let state' =
                    Disambiguation_state.add_lf_term_variable identifier
                      state
                  in
                  disambiguate_as_kind state' body
            in
            Synext.LF.Kind.Pi
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })

  (** [disambiguate_as_typ state object_] is [object_] rewritten as an LF
      type with respect to the disambiguation context [state].

      Type applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification. *)
  and disambiguate_as_typ state object_ =
    match object_ with
    | Synprs.LF.Object.Raw_type { location; _ } ->
        raise (Illegal_type_kind_type location)
    | Synprs.LF.Object.Raw_hole { location; _ } ->
        raise (Illegal_hole_type location)
    | Synprs.LF.Object.Raw_lambda { location; _ } ->
        raise (Illegal_lambda_type location)
    | Synprs.LF.Object.Raw_annotated { location; _ } ->
        raise (Illegal_annotated_type location)
    | Synprs.LF.Object.Raw_pi { location; parameter_sort = Option.None; _ }
      ->
        raise (Illegal_untyped_pi_type location)
    | Synprs.LF.Object.Raw_identifier { location; identifier; quoted } -> (
        (* As an LF type, plain identifiers are necessarily type-level
           constants. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            Synext.LF.Typ.Constant
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
    | Synprs.LF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As an LF type, identifiers of the form [(<identifier> `::')+
           <identifier>] are necessarily type-level constants. *)
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            Synext.LF.Typ.Constant { location; identifier; operator; quoted }
        | entry ->
            raise
              (Expected_type_constant { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            raise (Unbound_type_constant { location; identifier }))
    | Synprs.LF.Object.Raw_arrow { location; domain; range; orientation } ->
        let domain' = disambiguate_as_typ state domain
        and range' = disambiguate_as_typ state range in
        Synext.LF.Typ.Arrow
          { location; domain = domain'; range = range'; orientation }
    | Synprs.LF.Object.Raw_pi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
        let parameter_type' = disambiguate_as_typ state parameter_type in
        match parameter_identifier with
        | Option.None ->
            let body' = disambiguate_as_typ state body in
            Synext.LF.Typ.Pi
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
            Synext.LF.Typ.Pi
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })
    | Synprs.LF.Object.Raw_application { objects; _ } -> (
        match disambiguate_application state objects with
        | `Term term ->
            let location = Synext.location_of_lf_term term in
            raise (Expected_type location)
        | `Typ typ -> typ)

  (** [disambiguate_as_term state object_] is [object_] rewritten as an LF
      term with respect to the disambiguation context [state].

      Term applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification. *)
  and disambiguate_as_term state object_ =
    match object_ with
    | Synprs.LF.Object.Raw_type { location; _ } ->
        raise (Illegal_type_kind_term location)
    | Synprs.LF.Object.Raw_pi { location; _ } ->
        raise (Illegal_pi_term location)
    | Synprs.LF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        raise (Illegal_forward_arrow_term location)
    | Synprs.LF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        raise (Illegal_backward_arrow_term location)
    | Synprs.LF.Object.Raw_identifier { location; identifier; quoted } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            Synext.LF.Term.Constant
              { location
              ; identifier = qualified_identifier
              ; operator
              ; quoted
              }
        | Disambiguation_state.LF_term_variable ->
            (* Bound variable *)
            Synext.LF.Term.Variable { location; identifier }
        | entry ->
            raise
              (Expected_term_constant { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_identifier _ ->
            (* Free variable *)
            Synext.LF.Term.Variable { location; identifier })
    | Synprs.LF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As an LF term, identifiers of the form [(<identifier> `::')+
           <identifier>] are necessarily term-level constants. *)
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            Synext.LF.Term.Constant
              { location; identifier; operator; quoted }
        | entry ->
            raise
              (Expected_term_constant { location; actual_binding = entry })
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            raise (Unbound_term_constant { location; identifier }))
    | Synprs.LF.Object.Raw_application { objects; _ } -> (
        match disambiguate_application state objects with
        | `Typ typ ->
            let location = Synext.location_of_lf_typ typ in
            raise (Expected_term location)
        | `Term term -> term)
    | Synprs.LF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } -> (
        let parameter_type' =
          Option.map (disambiguate_as_typ state) parameter_sort
        in
        match parameter_identifier with
        | Option.None ->
            let body' = disambiguate_as_term state body in
            Synext.LF.Term.Abstraction
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
            Synext.LF.Term.Abstraction
              { location
              ; parameter_identifier
              ; parameter_type = parameter_type'
              ; body = body'
              })
    | Synprs.LF.Object.Raw_hole { location } ->
        Synext.LF.Term.Wildcard { location }
    | Synprs.LF.Object.Raw_annotated { location; object_; sort } ->
        let term' = disambiguate_as_term state object_
        and typ' = disambiguate_as_typ state sort in
        Synext.LF.Term.TypeAnnotated { location; term = term'; typ = typ' }

  (* TODO: Abstract *)

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
        | `Term applicand
        | `Typ applicand ->
            Synprs.location_of_lf_object applicand
      in
      let application_location =
        Location.join_all_contramap Synprs.location_of_lf_object
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
            (Synext.LF.Term.Application
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
            (Synext.LF.Typ.Application
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
            let location = Synext.location_of_lf_typ typ in
            raise (Expected_term location)
        | LF_operand.Parser_object object_ ->
            disambiguate_as_term state object_
        | LF_operand.Application { applicand; arguments } -> (
            match disambiguate_juxtaposition applicand arguments with
            | `Term term -> term
            | `Typ typ ->
                let location = Synext.location_of_lf_typ typ in
                raise (Expected_term location))

      let disambiguate_arguments arguments =
        List1.map disambiguate_argument arguments

      let write operator arguments =
        let application_location =
          Location.join_all_contramap LF_operand.location
            (LF_operator.location operator)
            arguments
        in
        match operator with
        | LF_operator.Type_constant { applicand; _ } ->
            let applicand' = disambiguate_as_typ state applicand in
            let arguments' =
              disambiguate_arguments (List1.unsafe_of_list arguments)
            in
            LF_operand.External_typ
              (Synext.LF.Typ.Application
                 { location = application_location
                 ; applicand = applicand'
                 ; arguments = arguments'
                 })
        | LF_operator.Term_constant { applicand; _ } ->
            let applicand' = disambiguate_as_term state applicand in
            let arguments' =
              disambiguate_arguments (List1.unsafe_of_list arguments)
            in
            LF_operand.External_term
              (Synext.LF.Term.Application
                 { location = application_location
                 ; applicand = applicand'
                 ; arguments = arguments'
                 })
    end in
    let module Shunting_yard =
      Centiparsec.Shunting_yard.Make (Associativity) (Fixity) (LF_operand)
        (LF_operator)
        (LF_application_writer)
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
                Shunting_yard.operand (LF_operand.Parser_object t)
                :: reduce_juxtapositions_and_identify_operators rest
            | arguments, rest
            (* [t] is an applicand in juxtaposition with [arguments] *) ->
                let arguments' = List.map Pair.snd arguments in
                Shunting_yard.operand
                  (LF_operand.Application
                     { applicand = `Term t; arguments = arguments' })
                :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            Shunting_yard.operand
              (LF_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            Shunting_yard.operand
              (LF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
            if Operator.is_prefix operator then
              let arguments, rest = List.take_while is_argument ts in
              let arguments' = List.map Pair.snd arguments in
              Shunting_yard.operand
                (LF_operand.Application
                   { applicand = `Typ t; arguments = arguments' })
              :: reduce_juxtapositions_and_identify_operators rest
            else
              Shunting_yard.operator
                (LF_operator.Type_constant
                   { identifier; operator; applicand = t })
              :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
            if Operator.is_prefix operator then
              let arguments, rest = List.take_while is_argument ts in
              let arguments' = List.map Pair.snd arguments in
              Shunting_yard.operand
                (LF_operand.Application
                   { applicand = `Term t; arguments = arguments' })
              :: reduce_juxtapositions_and_identify_operators rest
            else
              Shunting_yard.operator
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
        match Shunting_yard.shunting_yard (prepare_objects objects) with
        | LF_operand.External_typ t -> `Typ t
        | LF_operand.External_term t -> `Term t
        | LF_operand.Application { applicand; arguments } ->
            disambiguate_juxtaposition applicand arguments
        | LF_operand.Parser_object _ ->
            Error.violation
              "[LF.disambiguate_application] unexpectedly did not \
               disambiguate LF operands in rewriting"
      with
      | Shunting_yard.Empty_expression ->
          Error.violation
            "[LF.disambiguate_application] unexpectedly ended with an empty \
             expression"
      | Shunting_yard.Leftover_expressions _ ->
          Error.violation
            "[LF.disambiguate_application] unexpectedly ended with leftover \
             expressions"
      | Shunting_yard.Misplaced_operator { operator; operands } ->
          let operator_location = LF_operator.location operator
          and operand_locations = List.map LF_operand.location operands in
          raise (Misplaced_operator { operator_location; operand_locations })
      | Shunting_yard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
          let operator_identifier = LF_operator.identifier left_operator
          and left_operator_location = LF_operator.location left_operator
          and right_operator_location =
            LF_operator.location right_operator
          in
          raise
            (Ambiguous_operator_placement
               { operator_identifier
               ; left_operator_location
               ; right_operator_location
               })
      | Shunting_yard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
          let operator_identifier = LF_operator.identifier left_operator
          and left_operator_location = LF_operator.location left_operator
          and right_operator_location =
            LF_operator.location right_operator
          in
          raise
            (Consecutive_non_associative_operators
               { operator_identifier
               ; left_operator_location
               ; right_operator_location
               })
      | Shunting_yard.Arity_mismatch { operator; operator_arity; operands }
        ->
          let operator_identifier = LF_operator.identifier operator
          and operator_location = LF_operator.location operator
          and actual_argument_locations =
            List.map LF_operand.location operands
          in
          raise
            (Arity_mismatch
               { operator_identifier
               ; operator_location
               ; operator_arity
               ; actual_argument_locations
               })
end

module Register_exception_printer (Lf_disambiguation : LF_DISAMBIGUATION) =
struct end
