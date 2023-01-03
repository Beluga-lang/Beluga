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

(** {2 Exceptions for LF kind disambiguation} *)

exception Illegal_identifier_kind

exception Illegal_qualified_identifier_kind

exception Illegal_backward_arrow_kind

exception Illegal_hole_kind

exception Illegal_lambda_kind

exception Illegal_annotated_kind

exception Illegal_application_kind

(** {2 Exceptions for LF type disambiguation} *)

exception Illegal_type_kind_type

exception Illegal_hole_type

exception Illegal_lambda_type

exception Illegal_annotated_type

exception Unbound_type_constant of Qualified_identifier.t

(** {2 Exceptions for LF term disambiguation} *)

exception Illegal_type_kind_term

exception Illegal_pi_term

exception Illegal_forward_arrow_term

exception Illegal_backward_arrow_term

exception Unbound_term_constant of Qualified_identifier.t

(** {2 Exceptions for LF type-level and term-level application rewriting} *)

exception Expected_term_constant

exception Expected_type_constant

exception Expected_term

exception Expected_type

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

(** {1 Disambiguation} *)

module type LF_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

  (** {1 Disambiguation} *)

  val disambiguate_as_kind :
       Synprs.lf_object
    -> disambiguation_state
    -> disambiguation_state * Synext.lf_kind

  val disambiguate_as_typ :
       Synprs.lf_object
    -> disambiguation_state
    -> disambiguation_state * Synext.lf_typ

  val disambiguate_as_term :
       Synprs.lf_object
    -> disambiguation_state
    -> disambiguation_state * Synext.lf_term
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

  include State.Make (Disambiguation_state)

  (** {1 Disambiguation} *)

  module Lf_operand = struct
    type expression = Synprs.lf_object

    type t =
      | Atom of expression
      | Application of
          { applicand : expression
          ; arguments : t List1.t
          }

    let rec location operand =
      match operand with
      | Atom object_ -> Synprs.location_of_lf_object object_
      | Application { applicand; arguments } ->
          let applicand_location = Synprs.location_of_lf_object applicand in
          let arguments_location =
            Location.join_all1_contramap location arguments
          in
          Location.join applicand_location arguments_location
  end

  module Lf_operator = struct
    type associativity = Associativity.t

    type fixity = Fixity.t

    type operand = Lf_operand.t

    type t =
      { identifier : Qualified_identifier.t
      ; operator : Operator.t
      ; applicand : Synprs.lf_object
      }

    let[@inline] make ~identifier ~operator ~applicand =
      { identifier; operator; applicand }

    let[@inline] operator { operator; _ } = operator

    let[@inline] applicand { applicand; _ } = applicand

    let[@inline] identifier { identifier; _ } = identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(identifier >> Qualified_identifier.location)

    let write operator arguments =
      let applicand = applicand operator in
      let arguments = List1.unsafe_of_list arguments in
      Lf_operand.Application { applicand; arguments }

    include (
      (val Eq.contramap (module Qualified_identifier) identifier) :
        Eq.EQ with type t := t)
  end

  module Application_disambiguation_state = struct
    type t = state

    type operator = Lf_operator.t

    type expression = Synprs.lf_object

    let guard_identifier_operator identifier expression state =
      match Disambiguation_state.lookup identifier state with
      | Disambiguation_state.LF_type_constant { operator }
      | Disambiguation_state.LF_term_constant { operator } ->
          if Operator.is_nullary operator then Option.none
          else
            Option.some
              (Lf_operator.make ~identifier ~operator ~applicand:expression)
      | _
      | (exception Disambiguation_state.Unbound_identifier _) ->
          Option.none

    let guard_operator expression state =
      match expression with
      | Synprs.LF.Object.Raw_identifier { quoted; _ }
      | Synprs.LF.Object.Raw_qualified_identifier { quoted; _ }
        when quoted ->
          Option.none
      | Synprs.LF.Object.Raw_identifier { identifier; _ } ->
          let identifier = Qualified_identifier.make_simple identifier in
          guard_identifier_operator identifier expression state
      | Synprs.LF.Object.Raw_qualified_identifier { identifier; _ } ->
          guard_identifier_operator identifier expression state
      | _ -> Option.none
  end

  module Application_disambiguation =
    Application_disambiguation.Make (Associativity) (Fixity) (Lf_operand)
      (Lf_operator)
      (Application_disambiguation_state)

  let with_lf_term_variable_opt identifier_opt =
    match identifier_opt with
    | Option.None -> Fun.id
    | Option.Some identifier ->
        scoped
          ~set:(Disambiguation_state.add_lf_term_variable identifier)
          ~unset:(Disambiguation_state.pop_binding identifier)

  (** [disambiguate_as_kind object_ state] is [object_] rewritten as an LF
      kind with respect to the disambiguation context [state].

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from raw LF objects to LF kinds, see the Beluga language specification. *)
  let rec disambiguate_as_kind object_ =
    match object_ with
    | Synprs.LF.Object.Raw_identifier { location; _ } ->
        Error.raise_at1 location Illegal_identifier_kind
    | Synprs.LF.Object.Raw_qualified_identifier { location; _ } ->
        Error.raise_at1 location Illegal_qualified_identifier_kind
    | Synprs.LF.Object.Raw_hole { location; _ } ->
        Error.raise_at1 location Illegal_hole_kind
    | Synprs.LF.Object.Raw_lambda { location; _ } ->
        Error.raise_at1 location Illegal_lambda_kind
    | Synprs.LF.Object.Raw_annotated { location; _ } ->
        Error.raise_at1 location Illegal_annotated_kind
    | Synprs.LF.Object.Raw_application { location; _ } ->
        Error.raise_at1 location Illegal_application_kind
    | Synprs.LF.Object.Raw_type { location } ->
        return (Synext.LF.Kind.Typ { location })
    | Synprs.LF.Object.Raw_arrow { location; domain; range; orientation }
      -> (
        match orientation with
        | `Backward -> Error.raise_at1 location Illegal_backward_arrow_kind
        | `Forward ->
            let* domain' = disambiguate_as_typ domain in
            let* range' = disambiguate_as_kind range in
            return
              (Synext.LF.Kind.Arrow
                 { location; domain = domain'; range = range' }))
    | Synprs.LF.Object.Raw_pi
        { location; parameter_identifier; parameter_sort; body } ->
        let* parameter_type' = disambiguate_as_typ_opt parameter_sort in
        let* body' =
          with_lf_term_variable_opt parameter_identifier
            (disambiguate_as_kind body)
        in
        return
          (Synext.LF.Kind.Pi
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; body = body'
             })

  (** [disambiguate_as_typ object_ state] is [object_] rewritten as an LF
      type with respect to the disambiguation context [state].

      Type applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification. *)
  and disambiguate_as_typ object_ =
    match object_ with
    | Synprs.LF.Object.Raw_type { location; _ } ->
        Error.raise_at1 location Illegal_type_kind_type
    | Synprs.LF.Object.Raw_hole { location; _ } ->
        Error.raise_at1 location Illegal_hole_type
    | Synprs.LF.Object.Raw_lambda { location; _ } ->
        Error.raise_at1 location Illegal_lambda_type
    | Synprs.LF.Object.Raw_annotated { location; _ } ->
        Error.raise_at1 location Illegal_annotated_type
    | Synprs.LF.Object.Raw_identifier { location; identifier; quoted } -> (
        (* As an LF type, plain identifiers are necessarily type-level
           constants. *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        get >>= fun state ->
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            return
              (Synext.LF.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | _entry -> Error.raise_at1 location Expected_type_constant
        | exception Disambiguation_state.Unbound_identifier _ ->
            Error.raise_at1 location
              (Unbound_type_constant qualified_identifier))
    | Synprs.LF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As an LF type, identifiers of the form [(<identifier> `::')+
           <identifier>] are necessarily type-level constants. *)
        get >>= fun state ->
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.LF_type_constant { operator } ->
            return
              (Synext.LF.Typ.Constant
                 { location; identifier; operator; quoted })
        | _entry -> Error.raise_at1 location Expected_type_constant
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            Error.raise_at1 location (Unbound_type_constant identifier))
    | Synprs.LF.Object.Raw_arrow { location; domain; range; orientation } ->
        let* domain' = disambiguate_as_typ domain in
        let* range' = disambiguate_as_typ range in
        return
          (Synext.LF.Typ.Arrow
             { location; domain = domain'; range = range'; orientation })
    | Synprs.LF.Object.Raw_pi
        { location; parameter_identifier; parameter_sort; body } ->
        let* parameter_type' = disambiguate_as_typ_opt parameter_sort in
        let* body' =
          with_lf_term_variable_opt parameter_identifier
            (disambiguate_as_typ body)
        in
        return
          (Synext.LF.Typ.Pi
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; body = body'
             })
    | Synprs.LF.Object.Raw_application { objects; location } ->
        let* applicand, arguments = disambiguate_application objects in
        let* applicand' = disambiguate_as_typ applicand in
        let* arguments' = elaborate_lf_operand_list1 arguments in
        return
          (Synext.LF.Typ.Application
             { applicand = applicand'; arguments = arguments'; location })

  and disambiguate_as_typ_opt object_opt =
    match object_opt with
    | Option.None -> return Option.none
    | Option.Some object_ ->
        let* typ' = disambiguate_as_typ object_ in
        return (Option.some typ')

  (** [disambiguate_as_term object_ state] is [object_] rewritten as an LF
      term with respect to the disambiguation context [state].

      Term applications are rewritten with {!disambiguate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification. *)
  and disambiguate_as_term object_ =
    match object_ with
    | Synprs.LF.Object.Raw_type { location; _ } ->
        Error.raise_at1 location Illegal_type_kind_term
    | Synprs.LF.Object.Raw_pi { location; _ } ->
        Error.raise_at1 location Illegal_pi_term
    | Synprs.LF.Object.Raw_arrow { location; orientation = `Forward; _ } ->
        Error.raise_at1 location Illegal_forward_arrow_term
    | Synprs.LF.Object.Raw_arrow { location; orientation = `Backward; _ } ->
        Error.raise_at1 location Illegal_backward_arrow_term
    | Synprs.LF.Object.Raw_identifier { location; identifier; quoted } -> (
        (* As an LF term, plain identifiers are either term-level constants
           or variables (bound or free). *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        get >>= fun state ->
        (* Lookup the identifier in the current state *)
        match Disambiguation_state.lookup_toplevel identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            (* [identifier] appears as an LF term-level constant *)
            return
              (Synext.LF.Term.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 })
        | Disambiguation_state.LF_term_variable ->
            (* [identifier] appears as an LF bound variable *)
            return (Synext.LF.Term.Variable { location; identifier })
        | _entry ->
            (* [identifier] appears as a bound entry that is not an LF
               term-level constant or variable *)
            Error.raise_at1 location Expected_term_constant
        | exception Disambiguation_state.Unbound_identifier _ ->
            (* [identifier] does not appear in the state, so it is a free
               variable *)
            return (Synext.LF.Term.Variable { location; identifier }))
    | Synprs.LF.Object.Raw_qualified_identifier
        { location; identifier; quoted } -> (
        (* Qualified identifiers without modules were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.modules identifier) >= 1);
        (* As an LF term, identifiers of the form [(<identifier> `::')+
           <identifier>] are necessarily term-level constants. *)
        get >>= fun state ->
        (* Lookup the identifier in the current state *)
        match Disambiguation_state.lookup identifier state with
        | Disambiguation_state.LF_term_constant { operator } ->
            (* [identifier] appears as an LF term-level constant *)
            return
              (Synext.LF.Term.Constant
                 { location; identifier; operator; quoted })
        | _entry ->
            (* [identifier] appears as a bound entry that is not an LF
               term-level constant *)
            Error.raise_at1 location Expected_term_constant
        | exception Disambiguation_state.Unbound_qualified_identifier _ ->
            (* [identifier] does not appear in the state, and constants must
               be bound *)
            Error.raise_at1 location (Unbound_term_constant identifier))
    | Synprs.LF.Object.Raw_lambda
        { location; parameter_identifier; parameter_sort; body } ->
        let* parameter_type' = disambiguate_as_typ_opt parameter_sort in
        let* body' =
          with_lf_term_variable_opt parameter_identifier
            (disambiguate_as_term body)
        in
        return
          (Synext.LF.Term.Abstraction
             { location
             ; parameter_identifier
             ; parameter_type = parameter_type'
             ; body = body'
             })
    | Synprs.LF.Object.Raw_hole { location } ->
        return (Synext.LF.Term.Wildcard { location })
    | Synprs.LF.Object.Raw_annotated { location; object_; sort } ->
        let* term' = disambiguate_as_term object_ in
        let* typ' = disambiguate_as_typ sort in
        return
          (Synext.LF.Term.TypeAnnotated
             { location; term = term'; typ = typ' })
    | Synprs.LF.Object.Raw_application { objects; location } ->
        let* applicand, arguments = disambiguate_application objects in
        let* applicand' = disambiguate_as_term applicand in
        let* arguments' = elaborate_lf_operand_list1 arguments in
        return
          (Synext.LF.Term.Application
             { applicand = applicand'; arguments = arguments'; location })

  and disambiguate_application objects =
    Application_disambiguation.disambiguate_application objects >>= function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Application_disambiguation.Ambiguous_operator_placement
          { left_operator; right_operator }) ->
        let left_operator_location = Lf_operator.location left_operator in
        let right_operator_location = Lf_operator.location right_operator in
        let identifier = Lf_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_operator_placement identifier)
    | Result.Error
        (Application_disambiguation.Arity_mismatch
          { operator; operator_arity; operands }) ->
        let operator_identifier = Lf_operator.identifier operator in
        let operator_location = Lf_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations = List.map Lf_operand.location operands in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Application_disambiguation.Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier = Lf_operator.identifier left_operator in
        let left_operator_location = Lf_operator.location left_operator in
        let right_operator_location = Lf_operator.location right_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_operators
             operator_identifier)
    | Result.Error
        (Application_disambiguation.Misplaced_operator
          { operator; operands }) ->
        let operator_location = Lf_operator.location operator
        and operand_locations = List.map Lf_operand.location operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_operator
    | Result.Error cause -> raise cause

  and elaborate_lf_operand operand =
    match operand with
    | Lf_operand.Atom object_ -> disambiguate_as_term object_
    | Lf_operand.Application { applicand; arguments } ->
        let* applicand' = disambiguate_as_term applicand in
        let* arguments' = elaborate_lf_operand_list1 arguments in
        let location =
          Location.join_all1_contramap Synext.location_of_lf_term
            (List1.cons applicand' arguments')
        in
        return
          (Synext.LF.Term.Application
             { applicand = applicand'; arguments = arguments'; location })

  and elaborate_lf_operand_list operands =
    match operands with
    | [] -> return []
    | x :: xs ->
        let* y = elaborate_lf_operand x in
        let* ys = elaborate_lf_operand_list xs in
        return (y :: ys)

  and elaborate_lf_operand_list1 operands =
    let (List1.T (x, xs)) = operands in
    let* y = elaborate_lf_operand x in
    let* ys = elaborate_lf_operand_list xs in
    return (List1.from y ys)
end

(** {2 Exception Printing} *)

let pp_exception ppf = function
  | Illegal_identifier_kind ->
      Format.fprintf ppf "Identifiers may not appear as LF kinds."
  | Illegal_qualified_identifier_kind ->
      Format.fprintf ppf "Qualified identifiers may not appear as LF kinds."
  | Illegal_backward_arrow_kind ->
      Format.fprintf ppf "Backward arrows may not appear as LF kinds."
  | Illegal_hole_kind ->
      Format.fprintf ppf "Holes may not appear as LF kinds."
  | Illegal_lambda_kind ->
      Format.fprintf ppf "Lambdas may not appear as LF kinds."
  | Illegal_annotated_kind ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as LF kinds."
  | Illegal_application_kind ->
      Format.fprintf ppf "Term applications may not appear as LF kinds."
  | Illegal_type_kind_type ->
      Format.fprintf ppf "The kind `type' may not appear as LF types."
  | Illegal_hole_type ->
      Format.fprintf ppf "Holes may not appear as LF types."
  | Illegal_lambda_type ->
      Format.fprintf ppf "Lambdas may not appear as LF types."
  | Illegal_annotated_type ->
      Format.fprintf ppf "Type ascriptions may not appear as LF types."
  | Unbound_type_constant identifier ->
      Format.fprintf ppf "The LF type-level constant %a is unbound."
        Qualified_identifier.pp identifier
  | Illegal_type_kind_term ->
      Format.fprintf ppf "The kind `type' may not appear as LF terms."
  | Illegal_pi_term ->
      Format.fprintf ppf "Pi-kinds or types may not appear as LF terms."
  | Illegal_forward_arrow_term ->
      Format.fprintf ppf "Forward arrows may not appear as LF terms."
  | Illegal_backward_arrow_term ->
      Format.fprintf ppf "Backward arrows may not appear as LF terms."
  | Unbound_term_constant identifier ->
      Format.fprintf ppf "The LF term-level constant %a is unbound."
        Qualified_identifier.pp identifier
  | Expected_term_constant ->
      Format.fprintf ppf "Expected an LF term-level constant."
  | Expected_type_constant ->
      Format.fprintf ppf "Expected an LF type-level constant."
  | Expected_term ->
      Format.fprintf ppf "Expected an LF term but got an LF type instead."
  | Expected_type ->
      Format.fprintf ppf "Expected an LF type but got an LF term instead."
  | Misplaced_operator ->
      Format.fprintf ppf "Misplaced LF term-level or type-level operator."
  | Ambiguous_operator_placement operator_identifier ->
      Format.fprintf ppf
        "Ambiguous occurrences of the LF term-level or type-level operator \
         %a."
        Qualified_identifier.pp operator_identifier
  | Consecutive_applications_of_non_associative_operators operator_identifier
    ->
      Format.fprintf ppf
        "The consecutive application of the non-associative LF term-level \
         or type-level %a is illegal."
        Qualified_identifier.pp operator_identifier
  | Arity_mismatch
      { operator_identifier
      ; expected_arguments_count
      ; actual_arguments_count
      } ->
      Format.fprintf ppf "Operator %a expected %d arguments but got %d."
        Qualified_identifier.pp operator_identifier expected_arguments_count
        actual_arguments_count
  | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
