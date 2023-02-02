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

[@@@warning "-A-4-44"]

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

exception Misplaced_comp_typ_operator

exception Ambiguous_comp_typ_operator_placement of Qualified_identifier.t

exception
  Consecutive_applications_of_non_associative_comp_typ_operators of
    Qualified_identifier.t

exception
  Comp_typ_arity_mismatch of
    { operator_identifier : Qualified_identifier.t
    ; expected_arguments_count : Int.t
    ; actual_arguments_count : Int.t
    }

(** {2 Exceptions for computation-level expression disambiguation} *)

exception Expected_program_or_constructor_constant of Qualified_identifier.t

exception Unbound_comp_term_destructor_constant of Qualified_identifier.t

exception Illegal_duplicate_pattern_variables

(** {2 Exceptions for expression-level application rewriting} *)

exception Misplaced_comp_expression_operator

exception
  Ambiguous_comp_expression_operator_placement of Qualified_identifier.t

exception
  Consecutive_applications_of_non_associative_comp_expression_operators of
    Qualified_identifier.t

exception
  Comp_expression_arity_mismatch of
    { operator_identifier : Qualified_identifier.t
    ; expected_arguments_count : Int.t
    ; actual_arguments_count : Int.t
    }

(** {2 Exceptions for pattern-level application rewriting} *)

exception Misplaced_comp_pattern_operator

exception Ambiguous_comp_pattern_operator_placement of Qualified_identifier.t

exception
  Consecutive_applications_of_non_associative_comp_pattern_operators of
    Qualified_identifier.t

exception
  Comp_pattern_arity_mismatch of
    { operator_identifier : Qualified_identifier.t
    ; expected_arguments_count : Int.t
    ; actual_arguments_count : Int.t
    }

(** {2 Exceptions for computation-level context disambiguation} *)

exception Illegal_missing_comp_context_binding_type of Identifier.t

(** {2 Exceptions for computation-level pattern disambiguation} *)

exception Expected_constructor_constant of Qualified_identifier.t

exception Illegal_meta_annotated_comp_pattern_missing_identifier

exception Illegal_meta_annotated_comp_pattern_missing_type

(** {2 Exceptions for computation-level copattern disambiguation} *)

exception Expected_comp_term_destructor_constant

(** {1 Disambiguation} *)

module Comp_typ_operand = struct
  type expression = Synprs.comp_sort_object

  type t =
    | Atom of expression
    | Application of
        { applicand : expression
        ; arguments : t List1.t
        }

  let rec location operand =
    match operand with
    | Atom object_ -> Synprs.location_of_comp_sort_object object_
    | Application { applicand; arguments } ->
        let applicand_location =
          Synprs.location_of_comp_sort_object applicand
        in
        let arguments_location =
          Location.join_all1_contramap location arguments
        in
        Location.join applicand_location arguments_location
end

module Comp_typ_operator = struct
  type associativity = Associativity.t

  type fixity = Fixity.t

  type operand = Comp_typ_operand.t

  type t =
    { identifier : Qualified_identifier.t
    ; operator : Operator.t
    ; applicand : Synprs.comp_sort_object
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

  let location = Fun.(applicand >> Synprs.location_of_comp_sort_object)

  (** [write operator arguments] constructs the application of [operator]
      with [arguments] for the shunting yard algorithm. Since nullary
      operators are treated as arguments, it is always the case that
      [List.length arguments > 0]. *)
  let write operator arguments =
    let applicand = applicand operator in
    let arguments =
      List1.unsafe_of_list arguments (* [List.length arguments > 0] *)
    in
    Comp_typ_operand.Application { applicand; arguments }

  (** Instance of equality by operator identifier.

      Since applications do not introduce bound variables, occurrences of
      operators are equal by their identifier. That is, in an application
      like [a o1 a o2 a], the operators [o1] and [o2] are equal if and only
      if they are textually equal. *)
  include (
    (val Eq.contramap (module Qualified_identifier) identifier) :
      Eq.EQ with type t := t)
end

module Make_comp_typ_application_disambiguation_state
    (Bindings_state : BINDINGS_STATE) =
struct
  include Bindings_state

  type operator = Comp_typ_operator.t

  type expression = Comp_typ_operand.expression

  let guard_identifier_operator identifier expression =
    lookup identifier >>= function
    | Result.Ok
        ( Computation_inductive_type_constant
        , { operator = Option.Some operator; _ } )
    | Result.Ok
        ( Computation_stratified_type_constant
        , { operator = Option.Some operator; _ } )
    | Result.Ok
        ( Computation_abbreviation_type_constant
        , { operator = Option.Some operator; _ } )
    | Result.Ok
        ( Computation_coinductive_type_constant
        , { operator = Option.Some operator; _ } ) ->
        if Operator.is_nullary operator then return Option.none
        else
          return
            (Option.some
               (Comp_typ_operator.make ~identifier ~operator
                  ~applicand:expression))
    | Result.Ok _
    | Result.Error (Unbound_identifier _) ->
        return Option.none
    | Result.Error cause ->
        Error.raise_at1 (Qualified_identifier.location identifier) cause

  let guard_operator expression =
    match expression with
    | Synprs.Comp.Sort_object.Raw_identifier { prefixed; _ }
    | Synprs.Comp.Sort_object.Raw_qualified_identifier { prefixed; _ }
      when prefixed ->
        return Option.none
    | Synprs.Comp.Sort_object.Raw_identifier { identifier; _ } ->
        let identifier = Qualified_identifier.make_simple identifier in
        guard_identifier_operator identifier expression
    | Synprs.Comp.Sort_object.Raw_qualified_identifier { identifier; _ } ->
        guard_identifier_operator identifier expression
    | Synprs.Comp.Sort_object.Raw_ctype _
    | Synprs.Comp.Sort_object.Raw_pi _
    | Synprs.Comp.Sort_object.Raw_arrow _
    | Synprs.Comp.Sort_object.Raw_cross _
    | Synprs.Comp.Sort_object.Raw_box _
    | Synprs.Comp.Sort_object.Raw_application _ ->
        return Option.none
end

module Comp_expression_operand = struct
  type expression = Synprs.comp_expression_object

  type t =
    | Atom of expression
    | Application of
        { applicand : expression
        ; arguments : t List1.t
        }

  let rec location operand =
    match operand with
    | Atom object_ -> Synprs.location_of_comp_expression_object object_
    | Application { applicand; arguments } ->
        let applicand_location =
          Synprs.location_of_comp_expression_object applicand
        in
        let arguments_location =
          Location.join_all1_contramap location arguments
        in
        Location.join applicand_location arguments_location
end

module Comp_expression_operator = struct
  type associativity = Associativity.t

  type fixity = Fixity.t

  type operand = Comp_expression_operand.t

  type t =
    { identifier : Qualified_identifier.t
    ; operator : Operator.t
    ; applicand : Synprs.comp_expression_object
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

  let location = Fun.(applicand >> Synprs.location_of_comp_expression_object)

  (** [write operator arguments] constructs the application of [operator]
      with [arguments] for the shunting yard algorithm. Since nullary
      operators are treated as arguments, it is always the case that
      [List.length arguments > 0]. *)
  let write operator arguments =
    let applicand = applicand operator in
    let arguments =
      List1.unsafe_of_list arguments (* [List.length arguments > 0] *)
    in
    Comp_expression_operand.Application { applicand; arguments }

  (** Instance of equality by operator identifier.

      Since applications do not introduce bound variables, occurrences of
      operators are equal by their identifier. That is, in an application
      like [a o1 a o2 a], the operators [o1] and [o2] are equal if and only
      if they are textually equal. *)
  include (
    (val Eq.contramap (module Qualified_identifier) identifier) :
      Eq.EQ with type t := t)
end

module Make_comp_expression_application_disambiguation_state
    (Bindings_state : BINDINGS_STATE) =
struct
  include Bindings_state

  type operator = Comp_expression_operator.t

  type expression = Comp_expression_operand.expression

  let guard_identifier_operator identifier expression =
    lookup identifier >>= function
    | Result.Ok
        (Computation_term_constructor, { operator = Option.Some operator; _ })
    | Result.Ok (Program_constant, { operator = Option.Some operator; _ }) ->
        if Operator.is_nullary operator then return Option.none
        else
          return
            (Option.some
               (Comp_expression_operator.make ~identifier ~operator
                  ~applicand:expression))
    | Result.Ok _
    | Result.Error (Unbound_identifier _) ->
        return Option.none
    | Result.Error cause ->
        Error.raise_at1 (Qualified_identifier.location identifier) cause

  let guard_operator expression =
    match expression with
    | Synprs.Comp.Expression_object.Raw_identifier { prefixed; _ }
    | Synprs.Comp.Expression_object.Raw_qualified_identifier { prefixed; _ }
      when prefixed ->
        return Option.none
    | Synprs.Comp.Expression_object.Raw_identifier { identifier; _ } ->
        let identifier = Qualified_identifier.make_simple identifier in
        guard_identifier_operator identifier expression
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { identifier; _ } ->
        guard_identifier_operator identifier expression
    | Synprs.Comp.Expression_object.Raw_fn _
    | Synprs.Comp.Expression_object.Raw_mlam _
    | Synprs.Comp.Expression_object.Raw_fun _
    | Synprs.Comp.Expression_object.Raw_box _
    | Synprs.Comp.Expression_object.Raw_let _
    | Synprs.Comp.Expression_object.Raw_impossible _
    | Synprs.Comp.Expression_object.Raw_case _
    | Synprs.Comp.Expression_object.Raw_tuple _
    | Synprs.Comp.Expression_object.Raw_hole _
    | Synprs.Comp.Expression_object.Raw_box_hole _
    | Synprs.Comp.Expression_object.Raw_application _
    | Synprs.Comp.Expression_object.Raw_annotated _
    | Synprs.Comp.Expression_object.Raw_observation _ ->
        return Option.none
end

module Comp_pattern_operand = struct
  type expression = Synprs.comp_pattern_object

  type t =
    | Atom of expression
    | Application of
        { applicand : expression
        ; arguments : t List1.t
        }

  let rec location operand =
    match operand with
    | Atom object_ -> Synprs.location_of_comp_pattern_object object_
    | Application { applicand; arguments } ->
        let applicand_location =
          Synprs.location_of_comp_pattern_object applicand
        in
        let arguments_location =
          Location.join_all1_contramap location arguments
        in
        Location.join applicand_location arguments_location
end

module Comp_pattern_operator = struct
  type associativity = Associativity.t

  type fixity = Fixity.t

  type operand = Comp_pattern_operand.t

  type t =
    { identifier : Qualified_identifier.t
    ; operator : Operator.t
    ; applicand : Synprs.comp_pattern_object
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

  let location = Fun.(applicand >> Synprs.location_of_comp_pattern_object)

  (** [write operator arguments] constructs the application of [operator]
      with [arguments] for the shunting yard algorithm. Since nullary
      operators are treated as arguments, it is always the case that
      [List.length arguments > 0]. *)
  let write operator arguments =
    let applicand = applicand operator in
    let arguments =
      List1.unsafe_of_list arguments (* [List.length arguments > 0] *)
    in
    Comp_pattern_operand.Application { applicand; arguments }

  (** Instance of equality by operator identifier.

      Since applications do not introduce bound variables, occurrences of
      operators are equal by their identifier. That is, in an application
      like [a o1 a o2 a], the operators [o1] and [o2] are equal if and only
      if they are textually equal. *)
  include (
    (val Eq.contramap (module Qualified_identifier) identifier) :
      Eq.EQ with type t := t)
end

module Make_comp_pattern_application_disambiguation_state
    (Bindings_state : BINDINGS_STATE) =
struct
  include Bindings_state

  type operator = Comp_pattern_operator.t

  type expression = Comp_pattern_operand.expression

  let guard_identifier_operator identifier pattern =
    lookup identifier >>= function
    | Result.Ok
        (Computation_term_constructor, { operator = Option.Some operator; _ })
    | Result.Ok (Program_constant, { operator = Option.Some operator; _ }) ->
        if Operator.is_nullary operator then return Option.none
        else
          return
            (Option.some
               (Comp_pattern_operator.make ~identifier ~operator
                  ~applicand:pattern))
    | Result.Ok _
    | Result.Error (Unbound_identifier _) ->
        return Option.none
    | Result.Error cause ->
        Error.raise_at1 (Qualified_identifier.location identifier) cause

  let guard_operator pattern =
    match pattern with
    | Synprs.Comp.Pattern_object.Raw_identifier { prefixed; _ }
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier { prefixed; _ }
      when prefixed ->
        return Option.none
    | Synprs.Comp.Pattern_object.Raw_identifier { identifier; _ } ->
        let identifier = Qualified_identifier.make_simple identifier in
        guard_identifier_operator identifier pattern
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier { identifier; _ }
      ->
        guard_identifier_operator identifier pattern
    | Synprs.Comp.Pattern_object.Raw_box _
    | Synprs.Comp.Pattern_object.Raw_tuple _
    | Synprs.Comp.Pattern_object.Raw_application _
    | Synprs.Comp.Pattern_object.Raw_annotated _
    | Synprs.Comp.Pattern_object.Raw_observation _
    | Synprs.Comp.Pattern_object.Raw_meta_annotated _
    | Synprs.Comp.Pattern_object.Raw_wildcard _ ->
        return Option.none
end

module type COMP_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind : Synprs.comp_sort_object -> Synext.comp_kind t

  val disambiguate_comp_typ : Synprs.comp_sort_object -> Synext.comp_typ t

  val disambiguate_comp_expression :
    Synprs.comp_expression_object -> Synext.comp_expression t

  val with_disambiguated_comp_context :
    Synprs.comp_context_object -> (Synext.comp_context -> 'a t) -> 'a t
end

module type COMP_PATTERN_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_pattern :
    Synprs.comp_pattern_object -> Synext.comp_pattern t

  val disambiguate_comp_copattern :
    Synprs.comp_pattern_object -> Synext.comp_copattern t
end

module Make
    (Bindings_state : BINDINGS_STATE)
    (Pattern_disambiguation_state : PATTERN_DISAMBGUATION_STATE
                                      with module S = Bindings_state)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Bindings_state.state)
    (Comp_pattern_disambiguator : COMP_PATTERN_DISAMBIGUATION
                                    with type state =
                                      Pattern_disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Bindings_state.state = struct
  include Bindings_state
  include Meta_disambiguator

  (** {1 Disambiguation State Helpers} *)

  let with_parameter_binding identifier modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        with_context_variable identifier
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        with_meta_variable identifier
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        with_parameter_variable identifier
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        with_substitution_variable identifier
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

  let with_context_variable_opt = function
    | Option.Some identifier -> with_context_variable identifier
    | Option.None -> Fun.id

  let with_meta_variable_opt = function
    | Option.Some identifier -> with_meta_variable identifier
    | Option.None -> Fun.id

  let with_parameter_variable_opt = function
    | Option.Some identifier -> with_parameter_variable identifier
    | Option.None -> Fun.id

  let with_substitution_variable_opt = function
    | Option.Some identifier -> with_substitution_variable identifier
    | Option.None -> Fun.id

  let with_parameter_binding_opt identifier_opt modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        with_context_variable_opt identifier_opt
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        with_meta_variable_opt identifier_opt
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        with_parameter_variable_opt identifier_opt
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        with_substitution_variable_opt identifier_opt
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

  let with_computation_variable_opt = function
    | Option.Some identifier -> with_comp_variable identifier
    | Option.None -> Fun.id

  let rec with_function_parameters_list parameters f =
    match parameters with
    | [] -> f
    | x :: xs ->
        with_computation_variable_opt x (with_function_parameters_list xs f)

  let with_function_parameters_list1 parameters f =
    let (List1.T (x, xs)) = parameters in
    with_computation_variable_opt x (with_function_parameters_list xs f)

  let with_function_parameters = with_function_parameters_list1

  let with_meta_parameter = function
    | Option.Some identifier, `Plain -> with_meta_variable identifier
    | Option.Some identifier, `Hash -> with_parameter_variable identifier
    | Option.Some identifier, `Dollar ->
        with_substitution_variable identifier
    | Option.None, _ -> Fun.id

  let rec with_meta_function_parameters_list parameters f =
    match parameters with
    | [] -> f
    | x :: xs ->
        with_meta_parameter x (with_meta_function_parameters_list xs f)

  let with_meta_function_parameters_list1 parameters f =
    let (List1.T (x, xs)) = parameters in
    with_meta_parameter x (with_meta_function_parameters_list xs f)

  let with_meta_function_parameters = with_meta_function_parameters_list1

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
    | Option.None -> Error.raise_violation "[pop_binding]"
    | Option.Some (List1.T (_head, [])) ->
        Identifier.Hamt.remove identifier bindings
    | Option.Some (List1.T (_head, x :: xs)) ->
        Identifier.Hamt.add identifier (List1.from x xs) bindings

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

  and disambiguate_comp_typ = function
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Error.raise_at1 location Illegal_ctype_comp_type
    | Synprs.Comp.Sort_object.Raw_pi
        { parameter_sort = Option.None; location; _ } ->
        Error.raise_at1 location Illegal_untyped_comp_pi_type
    | Synprs.Comp.Sort_object.Raw_identifier
        { location; identifier; prefixed } -> (
        (* As a computation-level type, plain identifiers are necessarily
           computation-level type constants *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok
            ( Computation_inductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Inductive_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
                 })
        | Result.Ok
            ( Computation_stratified_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Stratified_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
                 })
        | Result.Ok
            ( Computation_abbreviation_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Abbreviation_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
                 })
        | Result.Ok
            ( Computation_coinductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Coinductive_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
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
        { location; identifier; prefixed } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As a computation-level type, identifiers of the form [<identifier>
           <dot-identifier>+] are necessarily computation-level type
           constants. *)
        lookup identifier >>= function
        | Result.Ok
            ( Computation_inductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Inductive_typ_constant
                 { location; identifier; operator; prefixed })
        | Result.Ok
            ( Computation_stratified_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Stratified_typ_constant
                 { location; identifier; operator; prefixed })
        | Result.Ok
            ( Computation_abbreviation_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Abbreviation_typ_constant
                 { location; identifier; operator; prefixed })
        | Result.Ok
            ( Computation_coinductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Coinductive_typ_constant
                 { location; identifier; operator; prefixed })
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
        let* applicand, arguments =
          disambiguate_comp_typ_application objects
        in
        let* applicand' = disambiguate_comp_typ applicand in
        let* arguments' =
          traverse_list1 elaborate_comp_typ_operand arguments
        in
        return
          (Synext.Comp.Typ.Application
             { applicand = applicand'; arguments = arguments'; location })

  and elaborate_comp_typ_operand operand =
    match operand with
    | Comp_typ_operand.Atom object_ -> (
        match object_ with
        | Synprs.Comp.Sort_object.Raw_box { boxed; _ } ->
            disambiguate_meta_object boxed
        | _ ->
            Error.raise_at1
              (Synprs.location_of_comp_sort_object object_)
              Expected_meta_object)
    | Comp_typ_operand.Application { applicand; arguments } ->
        let location =
          Location.join
            (Synprs.location_of_comp_sort_object applicand)
            (Location.join_all1_contramap Comp_typ_operand.location arguments)
        in
        Error.raise_at1 location Expected_meta_object

  and disambiguate_comp_typ_application =
    let open
      Application_disambiguation.Make (Associativity) (Fixity)
        (Comp_typ_operand)
        (Comp_typ_operator)
        (Make_comp_typ_application_disambiguation_state (Bindings_state)) in
    disambiguate_application >=> function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Ambiguous_operator_placement { left_operator; right_operator }) ->
        let left_operator_location =
          Comp_typ_operator.location left_operator
        in
        let right_operator_location =
          Comp_typ_operator.location right_operator
        in
        let identifier = Comp_typ_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_comp_typ_operator_placement identifier)
    | Result.Error (Arity_mismatch { operator; operator_arity; operands }) ->
        let operator_identifier = Comp_typ_operator.identifier operator in
        let operator_location = Comp_typ_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations =
          List.map Comp_typ_operand.location operands
        in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Comp_typ_arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier =
          Comp_typ_operator.identifier left_operator
        in
        let left_operator_location =
          Comp_typ_operator.location left_operator
        in
        let right_operator_location =
          Comp_typ_operator.location right_operator
        in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_comp_typ_operators
             operator_identifier)
    | Result.Error (Misplaced_operator { operator; operands }) ->
        let operator_location = Comp_typ_operator.location operator
        and operand_locations =
          List.map Comp_typ_operand.location operands
        in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_comp_typ_operator
    | Result.Error cause -> Error.raise cause

  and disambiguate_comp_expression = function
    | Synprs.Comp.Expression_object.Raw_identifier
        { location; identifier; prefixed } -> (
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok
            ( Computation_term_constructor
            , { operator = Option.Some operator; _ } ) ->
            (* [identifier] appears as a bound computation-level
               constructor *)
            return
              (Synext.Comp.Expression.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; prefixed
                 ; operator = Option.some operator
                 })
        | Result.Ok (Program_constant, { operator; _ }) ->
            (* [identifier] appears as a bound computation-level program *)
            return
              (Synext.Comp.Expression.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; prefixed
                 ; operator
                 })
        | Result.Ok (Computation_variable _, _) ->
            (* [identifier] appears as a bound computation-level variable *)
            return (Synext.Comp.Expression.Variable { location; identifier })
        | Result.Ok entry ->
            (* [identifier] appears as a bound entry that is not a
               computation-level variable, constructor or program constant *)
            Error.raise_at1 location
              (Error.composite_exception2
                 (Expected_program_or_constructor_constant
                    qualified_identifier)
                 (actual_binding_exn qualified_identifier entry))
        | Result.Error (Unbound_identifier _) ->
            (* [identifier] does not appear in the state, so it is a free
               variable. *)
            return (Synext.Comp.Expression.Variable { location; identifier })
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { location; identifier; prefixed } -> (
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
        partial_lookup identifier >>= function
        | `Totally_unbound (List1.T (free_variable, rest))
        (* A free computation-level variable with (possibly) trailing
           observations *) -> (
            let location = Identifier.location free_variable in
            let scrutinee =
              Synext.Comp.Expression.Variable
                { location; identifier = free_variable }
            in
            match rest with
            | [] -> return scrutinee
            | x :: xs ->
                disambiguate_trailing_observations scrutinee
                  (List1.from x xs))
        | `Partially_bound (bound_segments, unbound_segments) -> (
            match bound_segments with
            | List1.T ((variable, (Computation_variable, _)), [])
            (* A bound computation-level variable with trailing
               observations *) ->
                let location = Identifier.location variable in
                let scrutinee =
                  Synext.Comp.Expression.Variable
                    { location; identifier = variable }
                in
                disambiguate_trailing_observations scrutinee unbound_segments
            | bound_segments -> (
                let bound_segments_identifier =
                  Qualified_identifier.from_list1
                    (List1.map Pair.fst bound_segments)
                in
                match List1.last bound_segments with
                | ( _identifier
                  , ( (Computation_term_constructor | Program_constant)
                    , { operator; _ } ) )
                (* [bound_segments] forms a valid constant *) ->
                    let location =
                      Qualified_identifier.location bound_segments_identifier
                    in
                    let scrutinee =
                      Synext.Comp.Expression.Constant
                        { location
                        ; identifier = bound_segments_identifier
                        ; operator
                        ; prefixed =
                            false
                            (* [unbound_segments] is non-empty, so the
                               parentheses do not force the constant to be
                               prefixed *)
                        }
                    in
                    disambiguate_trailing_observations scrutinee
                      unbound_segments
                | ( _identifier
                  , entry (* [bound_segments] forms an invalid constant *) )
                  ->
                    Error.raise_at1 location
                      (Error.composite_exception2
                         (Expected_program_or_constructor_constant
                            bound_segments_identifier)
                         (actual_binding_exn bound_segments_identifier entry))
                ))
        | `Totally_bound bound_segments (* A constant *) -> (
            match List1.last bound_segments with
            | ( _identifier
              , ( (Computation_term_constructor | Program_constant)
                , { operator; _ } ) ) ->
                return
                  (Synext.Comp.Expression.Constant
                     { location; identifier; operator; prefixed })
            | _identifier, entry ->
                Error.raise_at1 location
                  (Error.composite_exception2
                     (Expected_program_or_constructor_constant identifier)
                     (actual_binding_exn identifier entry))))
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
          traverse_list1
            (fun (copatterns, body) ->
              let* copatterns', body' =
                Pattern_disambiguation_state.with_pattern_variables
                  ~pattern:
                    Comp_pattern_disambiguator.(
                      traverse_list1 disambiguate_comp_copattern copatterns)
                  ~expression:(disambiguate_comp_expression body)
              in
              let location =
                Location.join
                  (Location.join_all1_contramap
                     Synext.location_of_comp_copattern copatterns')
                  (Synext.location_of_comp_expression body')
              in
              return
                { Synext.Comp.Cofunction_branch.location
                ; copatterns = copatterns'
                ; body = body'
                })
            branches
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
          Pattern_disambiguation_state.with_pattern_variables
            ~pattern:
              (Comp_pattern_disambiguator.disambiguate_comp_pattern pattern)
            ~expression:(disambiguate_comp_expression body)
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
        let* branches' =
          traverse_list1
            (fun (pattern, body) ->
              let* pattern', body' =
                Pattern_disambiguation_state.with_pattern_variables
                  ~pattern:
                    (Comp_pattern_disambiguator.disambiguate_comp_pattern
                       pattern)
                  ~expression:(disambiguate_comp_expression body)
              in
              let location =
                Location.join
                  (Synext.location_of_comp_pattern pattern')
                  (Synext.location_of_comp_expression body')
              in
              return
                { Synext.Comp.Case_branch.location
                ; pattern = pattern'
                ; body = body'
                })
            branches
        in
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
        return (Synext.Comp.Expression.Box_hole { location })
    | Synprs.Comp.Expression_object.Raw_application { location; expressions }
      ->
        (* We don't have to disambiguate the qualified identifiers in
           [objects] before we disambiguate applications. It is always the
           case that actual projections and actual observations that were
           parsed as qualified identifiers are not totally bound in the
           disambiguation state, so the application disambiguation identifies
           them as operands. *)
        let* applicand, arguments =
          disambiguate_comp_expression_application expressions
        in
        let* applicand' = disambiguate_comp_expression applicand in
        let* arguments' =
          traverse_list1 elaborate_comp_expression_operand arguments
        in
        return
          (Synext.Comp.Expression.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.Comp.Expression_object.Raw_annotated
        { location; expression; typ } ->
        let* expression' = disambiguate_comp_expression expression in
        let* typ' = disambiguate_comp_typ typ in
        return
          (Synext.Comp.Expression.Type_annotated
             { location; expression = expression'; typ = typ' })
    | Synprs.Comp.Expression_object.Raw_observation
        { scrutinee; destructor; _ } ->
        (* Observations of variables or constants is handled in the
           disambiguation of qualified identifiers. *)
        let* scrutinee' = disambiguate_comp_expression scrutinee in
        disambiguate_trailing_observations scrutinee'
          (Qualified_identifier.to_list1 destructor)

  and disambiguate_trailing_observations scrutinee trailing_identifiers =
    partial_lookup' trailing_identifiers >>= function
    | `Totally_unbound _ ->
        let qualified_identifier =
          Qualified_identifier.from_list1 trailing_identifiers
        in
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Unbound_comp_term_destructor_constant qualified_identifier)
    | `Partially_bound (bound_segments, unbound_segments) -> (
        let bound_segments_identifier =
          Qualified_identifier.from_list1 (List1.map Pair.fst bound_segments)
        in
        match List1.last bound_segments with
        | _identifier, (Computation_term_destructor, _)
        (* [bound_segments] forms a destructor *) ->
            let destructor = bound_segments_identifier in
            let location =
              Location.join
                (Synext.location_of_comp_expression scrutinee)
                (Qualified_identifier.location destructor)
            in
            let scrutinee' =
              Synext.Comp.Expression.Observation
                { scrutinee; destructor; location }
            in
            disambiguate_trailing_observations scrutinee' unbound_segments
        | _identifier, _entry
        (* [bound_segments] forms an invalid constant *) ->
            Error.raise_at1
              (Qualified_identifier.location bound_segments_identifier)
              Expected_comp_term_destructor_constant)
    | `Totally_bound bound_segments -> (
        let bound_segments_identifier =
          Qualified_identifier.from_list1 (List1.map Pair.fst bound_segments)
        in
        match List1.last bound_segments with
        | _identifier, (Computation_term_destructor, _)
        (* [bound_segments] forms a destructor *) ->
            let destructor = bound_segments_identifier in
            let location =
              Location.join
                (Synext.location_of_comp_expression scrutinee)
                (Qualified_identifier.location destructor)
            in
            return
              (Synext.Comp.Expression.Observation
                 { scrutinee; destructor; location })
        | _identifier, _entry
        (* [bound_segments] forms an invalid constant *) ->
            Error.raise_at1
              (Qualified_identifier.location bound_segments_identifier)
              Expected_comp_term_destructor_constant)

  and elaborate_comp_expression_operand operand =
    match operand with
    | Comp_expression_operand.Atom object_ ->
        disambiguate_comp_expression object_
    | Comp_expression_operand.Application { applicand; arguments } ->
        let* applicand' = disambiguate_comp_expression applicand in
        let* arguments' =
          traverse_list1 elaborate_comp_expression_operand arguments
        in
        let location =
          Location.join_all1_contramap Synext.location_of_comp_expression
            (List1.cons applicand' arguments')
        in
        return
          (Synext.Comp.Expression.Application
             { applicand = applicand'; arguments = arguments'; location })

  and disambiguate_comp_expression_application =
    let open
      Application_disambiguation.Make (Associativity) (Fixity)
        (Comp_expression_operand)
        (Comp_expression_operator)
        (Make_comp_expression_application_disambiguation_state
           (Bindings_state)) in
    disambiguate_application >=> function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Ambiguous_operator_placement { left_operator; right_operator }) ->
        let left_operator_location =
          Comp_expression_operator.location left_operator
        in
        let right_operator_location =
          Comp_expression_operator.location right_operator
        in
        let identifier = Comp_expression_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_comp_expression_operator_placement identifier)
    | Result.Error (Arity_mismatch { operator; operator_arity; operands }) ->
        let operator_identifier =
          Comp_expression_operator.identifier operator
        in
        let operator_location = Comp_expression_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations =
          List.map Comp_expression_operand.location operands
        in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Comp_expression_arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier =
          Comp_expression_operator.identifier left_operator
        in
        let left_operator_location =
          Comp_expression_operator.location left_operator
        in
        let right_operator_location =
          Comp_expression_operator.location right_operator
        in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_comp_expression_operators
             operator_identifier)
    | Result.Error (Misplaced_operator { operator; operands }) ->
        let operator_location = Comp_expression_operator.location operator
        and operand_locations =
          List.map Comp_expression_operand.location operands
        in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_comp_expression_operator
    | Result.Error cause -> Error.raise cause

  and with_disambiguated_comp_context context_object f =
    let { Synprs.Comp.Context_object.location; bindings } = context_object in
    (* Computation contexts are dependent, meaning that bound variables on
       the left of a declaration may appear in the type of a binding on the
       right. Bindings may not recursively refer to themselves. *)
    with_disambiguated_context_bindings_list bindings (fun bindings' ->
        f { Synext.Comp.Context.location; bindings = bindings' })

  and with_disambiguated_context_binding binding f =
    match binding with
    | identifier, Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Illegal_missing_comp_context_binding_type identifier)
    | identifier, Option.Some typ ->
        let* typ' = disambiguate_comp_typ typ in
        with_comp_variable identifier (f (identifier, typ'))

  and with_disambiguated_context_bindings_list bindings f =
    match bindings with
    | [] -> f []
    | x :: xs ->
        with_disambiguated_context_binding x (fun y ->
            with_disambiguated_context_bindings_list xs (fun ys ->
                f (y :: ys)))
end

module Make_pattern_disambiguator
    (Bindings_state : BINDINGS_STATE)
    (Pattern_disambiguation_state : PATTERN_DISAMBGUATION_STATE
                                      with module S = Bindings_state)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Bindings_state.state)
    (Meta_pattern_disambiguator : Meta_disambiguation
                                  .META_PATTERN_DISAMBIGUATION
                                    with type state =
                                      Pattern_disambiguation_state.state) :
  COMP_PATTERN_DISAMBIGUATION
    with type state = Pattern_disambiguation_state.state = struct
  include Pattern_disambiguation_state
  include Meta_pattern_disambiguator

  let lookup_toplevel identifier =
    with_wrapped_state (Bindings_state.lookup_toplevel identifier)

  let lookup identifier =
    with_wrapped_state (Bindings_state.lookup identifier)

  let comp_variable_adder identifier =
    { run = (fun m -> Bindings_state.with_comp_variable identifier m) }

  let add_pattern_comp_variable identifier =
    add_pattern_variable identifier (comp_variable_adder identifier)

  let with_context_variable_opt = function
    | Option.Some identifier -> with_context_variable identifier
    | Option.None -> Fun.id

  let with_meta_variable_opt = function
    | Option.Some identifier -> with_meta_variable identifier
    | Option.None -> Fun.id

  let with_parameter_variable_opt = function
    | Option.Some identifier -> with_parameter_variable identifier
    | Option.None -> Fun.id

  let with_substitution_variable_opt = function
    | Option.Some identifier -> with_substitution_variable identifier
    | Option.None -> Fun.id

  let with_parameter_binding identifier modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        with_context_variable identifier
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        with_meta_variable identifier
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        with_parameter_variable identifier
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        with_substitution_variable identifier
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

  let with_parameter_binding_opt identifier_opt modifier typ =
    match (modifier, typ) with
    | `Plain, Synext.Meta.Typ.Context_schema _ ->
        with_context_variable_opt identifier_opt
    | `Plain, Synext.Meta.Typ.Contextual_typ _ ->
        with_meta_variable_opt identifier_opt
    | `Hash, Synext.Meta.Typ.Parameter_typ _ ->
        with_parameter_variable_opt identifier_opt
    | ( `Dollar
      , ( Synext.Meta.Typ.Plain_substitution_typ _
        | Synext.Meta.Typ.Renaming_substitution_typ _ ) ) ->
        with_substitution_variable_opt identifier_opt
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

  let actual_binding_exn = Bindings_state.actual_binding_exn

  let rec disambiguate_comp_typ = function
    | Synprs.Comp.Sort_object.Raw_ctype { location } ->
        Error.raise_at1 location Illegal_ctype_comp_type
    | Synprs.Comp.Sort_object.Raw_pi
        { parameter_sort = Option.None; location; _ } ->
        Error.raise_at1 location Illegal_untyped_comp_pi_type
    | Synprs.Comp.Sort_object.Raw_identifier
        { location; identifier; prefixed } -> (
        (* As a computation-level type, plain identifiers are necessarily
           computation-level type constants *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok
            ( Computation_inductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Inductive_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
                 })
        | Result.Ok
            ( Computation_stratified_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Stratified_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
                 })
        | Result.Ok
            ( Computation_abbreviation_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Abbreviation_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
                 })
        | Result.Ok
            ( Computation_coinductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Coinductive_typ_constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; prefixed
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
        { location; identifier; prefixed } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As a computation-level type, identifiers of the form [<identifier>
           <dot-identifier>+] are necessarily computation-level type
           constants. *)
        lookup identifier >>= function
        | Result.Ok
            ( Computation_inductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Inductive_typ_constant
                 { location; identifier; operator; prefixed })
        | Result.Ok
            ( Computation_stratified_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Stratified_typ_constant
                 { location; identifier; operator; prefixed })
        | Result.Ok
            ( Computation_abbreviation_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Abbreviation_typ_constant
                 { location; identifier; operator; prefixed })
        | Result.Ok
            ( Computation_coinductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Coinductive_typ_constant
                 { location; identifier; operator; prefixed })
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
        let* applicand, arguments =
          with_wrapped_state (disambiguate_comp_typ_application objects)
        in
        let* applicand' = disambiguate_comp_typ applicand in
        let* arguments' =
          traverse_list1 elaborate_comp_typ_operand arguments
        in
        return
          (Synext.Comp.Typ.Application
             { applicand = applicand'; arguments = arguments'; location })

  and elaborate_comp_typ_operand operand =
    match operand with
    | Comp_typ_operand.Atom object_ -> (
        match object_ with
        | Synprs.Comp.Sort_object.Raw_box { boxed; _ } ->
            disambiguate_meta_object boxed
        | _ ->
            Error.raise_at1
              (Synprs.location_of_comp_sort_object object_)
              Expected_meta_object)
    | Comp_typ_operand.Application { applicand; arguments } ->
        let location =
          Location.join
            (Synprs.location_of_comp_sort_object applicand)
            (Location.join_all1_contramap Comp_typ_operand.location arguments)
        in
        Error.raise_at1 location Expected_meta_object

  and disambiguate_comp_typ_application =
    let open
      Application_disambiguation.Make (Associativity) (Fixity)
        (Comp_typ_operand)
        (Comp_typ_operator)
        (Make_comp_typ_application_disambiguation_state (Bindings_state)) in
    disambiguate_application >=> function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Ambiguous_operator_placement { left_operator; right_operator }) ->
        let left_operator_location =
          Comp_typ_operator.location left_operator
        in
        let right_operator_location =
          Comp_typ_operator.location right_operator
        in
        let identifier = Comp_typ_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_comp_typ_operator_placement identifier)
    | Result.Error (Arity_mismatch { operator; operator_arity; operands }) ->
        let operator_identifier = Comp_typ_operator.identifier operator in
        let operator_location = Comp_typ_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations =
          List.map Comp_typ_operand.location operands
        in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Comp_typ_arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier =
          Comp_typ_operator.identifier left_operator
        in
        let left_operator_location =
          Comp_typ_operator.location left_operator
        in
        let right_operator_location =
          Comp_typ_operator.location right_operator
        in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_comp_typ_operators
             operator_identifier)
    | Result.Error (Misplaced_operator { operator; operands }) ->
        let operator_location = Comp_typ_operator.location operator
        and operand_locations =
          List.map Comp_typ_operand.location operands
        in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_comp_typ_operator
    | Result.Error cause -> Error.raise cause

  and disambiguate_comp_pattern = function
    | Synprs.Comp.Pattern_object.Raw_identifier
        { location; identifier; prefixed } -> (
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok
            ( Computation_term_constructor
            , { operator = Option.Some operator; _ } ) ->
            (* [identifier] appears as a bound computation-level program *)
            return
              (Synext.Comp.Pattern.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; prefixed
                 ; operator
                 })
        | Result.Ok entry ->
            (* [identifier] appears as a bound entry that is not a
               computation-level constructor *)
            (* There are no computation-level patterns under
               [fn]-abstractions, so no need to check that [identifier] is
               not inner-bound. *)
            let* () = add_pattern_comp_variable identifier in
            return (Synext.Comp.Pattern.Variable { location; identifier })
        | Result.Error (Unbound_identifier _) ->
            (* [identifier] does not appear in the state, so it is a free
               variable. *)
            let* () = add_pattern_comp_variable identifier in
            return (Synext.Comp.Pattern.Variable { location; identifier })
        | Result.Error cause -> Error.raise_at1 location cause)
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { location; identifier; prefixed } ->
        Obj.magic () (* TODO: *)
    | Synprs.Comp.Pattern_object.Raw_box { location; pattern } ->
        let* pattern' = disambiguate_meta_pattern pattern in
        return
          (Synext.Comp.Pattern.Meta_object
             { location; meta_pattern = pattern' })
    | Synprs.Comp.Pattern_object.Raw_tuple { location; elements } ->
        let* elements' = traverse_list2 disambiguate_comp_pattern elements in
        return (Synext.Comp.Pattern.Tuple { location; elements = elements' })
    | Synprs.Comp.Pattern_object.Raw_application { location; patterns } ->
        (* We don't have to disambiguate the qualified identifiers in
           [objects] before we disambiguate applications. It is always the
           case that actual projections and actual observations that were
           parsed as qualified identifiers are not totally bound in the
           disambiguation state, so the application disambiguation identifies
           them as operands. *)
        let* applicand, arguments =
          with_wrapped_state (disambiguate_comp_pattern_application patterns)
        in
        let* applicand' = disambiguate_comp_pattern applicand in
        let* arguments' =
          traverse_list1 elaborate_comp_pattern_operand arguments
        in
        return
          (Synext.Comp.Pattern.Application
             { applicand = applicand'; arguments = arguments'; location })
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } ->
        Obj.magic () (* TODO: *)
    | Synprs.Comp.Pattern_object.Raw_annotated { location; pattern; typ } ->
        let* pattern' = disambiguate_comp_pattern pattern in
        let* typ' = disambiguate_comp_typ typ in
        return
          (Synext.Comp.Pattern.Type_annotated
             { location; pattern = pattern'; typ = typ' })
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location
        ; parameter_identifier = identifier, modifier
        ; parameter_typ
        ; pattern
        } -> (
        match (identifier, parameter_typ) with
        | Option.None, _ ->
            Error.raise_at1 location
              Illegal_meta_annotated_comp_pattern_missing_identifier
        | _, Option.None ->
            Error.raise_at1 location
              Illegal_meta_annotated_comp_pattern_missing_type
        | Option.Some identifier, Option.Some parameter_typ ->
            let* parameter_typ = disambiguate_meta_typ parameter_typ in
            Obj.magic ()
            (* TODO: Add the identifier as inner binding and pattern
               variable *))
    | Synprs.Comp.Pattern_object.Raw_wildcard { location } ->
        return (Synext.Comp.Pattern.Wildcard { location })

  and disambiguate_comp_copattern = function
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { location; identifier; prefixed } ->
        (* TODO: Can be a variable pattern or constant together with an
           observation *)
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } -> (
        lookup constant >>= function
        | Result.Ok (Computation_term_destructor, _) ->
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
      | Synprs.Comp.Pattern_object.Raw_wildcard _ ) as pattern ->
        let* pattern' = disambiguate_comp_pattern pattern in
        return (Synext.Comp.Copattern.Pattern pattern')

  and elaborate_comp_pattern_operand operand =
    match operand with
    | Comp_pattern_operand.Atom object_ -> disambiguate_comp_pattern object_
    | Comp_pattern_operand.Application { applicand; arguments } ->
        let* applicand' = disambiguate_comp_pattern applicand in
        let* arguments' =
          traverse_list1 elaborate_comp_pattern_operand arguments
        in
        let location =
          Location.join_all1_contramap Synext.location_of_comp_pattern
            (List1.cons applicand' arguments')
        in
        return
          (Synext.Comp.Pattern.Application
             { applicand = applicand'; arguments = arguments'; location })

  and disambiguate_comp_pattern_application =
    let open
      Application_disambiguation.Make (Associativity) (Fixity)
        (Comp_pattern_operand)
        (Comp_pattern_operator)
        (Make_comp_pattern_application_disambiguation_state (Bindings_state)) in
    disambiguate_application >=> function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Ambiguous_operator_placement { left_operator; right_operator }) ->
        let left_operator_location =
          Comp_pattern_operator.location left_operator
        in
        let right_operator_location =
          Comp_pattern_operator.location right_operator
        in
        let identifier = Comp_pattern_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_comp_pattern_operator_placement identifier)
    | Result.Error (Arity_mismatch { operator; operator_arity; operands }) ->
        let operator_identifier =
          Comp_pattern_operator.identifier operator
        in
        let operator_location = Comp_pattern_operator.location operator in
        let expected_arguments_count = operator_arity in
        let operand_locations =
          List.map Comp_pattern_operand.location operands
        in
        let actual_arguments_count = List.length operands in
        Error.raise_at
          (List1.from operator_location operand_locations)
          (Comp_pattern_arity_mismatch
             { operator_identifier
             ; expected_arguments_count
             ; actual_arguments_count
             })
    | Result.Error
        (Consecutive_non_associative_operators
          { left_operator; right_operator }) ->
        let operator_identifier =
          Comp_pattern_operator.identifier left_operator
        in
        let left_operator_location =
          Comp_pattern_operator.location left_operator
        in
        let right_operator_location =
          Comp_pattern_operator.location right_operator
        in
        Error.raise_at2 left_operator_location right_operator_location
          (Consecutive_applications_of_non_associative_comp_pattern_operators
             operator_identifier)
    | Result.Error (Misplaced_operator { operator; operands }) ->
        let operator_location = Comp_pattern_operator.location operator
        and operand_locations =
          List.map Comp_pattern_operand.location operands
        in
        Error.raise_at
          (List1.from operator_location operand_locations)
          Misplaced_comp_pattern_operator
    | Result.Error cause -> Error.raise cause
end

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Illegal_identifier_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "An identifier may not appear as a computation-level kind."
    | Illegal_qualified_identifier_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "A qualified identifier may not appear as a computation-level \
           kind."
    | Illegal_backward_arrow_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "Backward arrows may not appear as computation-level kinds."
    | Illegal_cross_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "Cross operators may not appear as computation-level kinds."
    | Illegal_box_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "Boxed types or objects may not appear as computation-level kinds."
    | Illegal_application_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "Applications may not appear as computation-level kinds."
    | Illegal_untyped_comp_pi_kind_parameter ->
        Format.dprintf "%a" Format.pp_print_text
          "Computation-level Pi kind parameters must be annotated with a \
           meta-type."
    | Illegal_comp_typ_domain_pi_comp_kind ->
        Format.dprintf "%a" Format.pp_print_text
          "Computation-level Pi kind parameters may only be annotated with \
           a meta-type, not a computation-level type."
    | Illegal_ctype_comp_type ->
        Format.dprintf "%a" Format.pp_print_text
          "The computation-level kind `ctype' may not appear as a \
           computation-level type."
    | Expected_comp_type_constant qualified_identifier ->
        Format.dprintf "Expected %a to be a computation-level type constant."
          Qualified_identifier.pp qualified_identifier
    | Unbound_comp_type_constant qualified_identifier ->
        Format.dprintf "The computation-level constant %a is unbound."
          Qualified_identifier.pp qualified_identifier
    | Illegal_untyped_comp_pi_type ->
        Format.dprintf "%a" Format.pp_print_text
          "Computation-level Pi type parameters must be annotated with a \
           meta-type."
    | Expected_meta_object ->
        Format.dprintf "%a" Format.pp_print_text "Expected a meta-object."
    | Ambiguous_comp_typ_operator_placement operator_identifier ->
        Format.dprintf
          "Ambiguous occurrences of the computation-level type operator %a \
           after rewriting."
          Qualified_identifier.pp operator_identifier
    | Misplaced_comp_typ_operator ->
        Format.dprintf "%a" Format.pp_print_text
          "Misplaced contextual computation-level type operator."
    | Consecutive_applications_of_non_associative_comp_typ_operators
        operator_identifier ->
        Format.dprintf
          "Consecutive occurrences of the computation-level type operator \
           %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Comp_typ_arity_mismatch
        { operator_identifier
        ; expected_arguments_count
        ; actual_arguments_count
        } ->
        Format.dprintf
          "Computation-level type operator %a expected %d argument(s) but \
           got %d."
          Qualified_identifier.pp operator_identifier
          expected_arguments_count actual_arguments_count
    | Expected_program_or_constructor_constant qualified_identifier ->
        Format.dprintf
          "Expected %a to be a program constant or computation-level \
           constructor."
          Qualified_identifier.pp qualified_identifier
    | Illegal_duplicate_pattern_variables ->
        Format.dprintf "%a" Format.pp_print_text
          "Illegal duplicate pattern variables."
    | Ambiguous_comp_expression_operator_placement operator_identifier ->
        Format.dprintf
          "Ambiguous occurrences of the computation-level expression \
           operator %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Misplaced_comp_expression_operator ->
        Format.dprintf "%a" Format.pp_print_text
          "Misplaced contextual computation-level expression operator."
    | Consecutive_applications_of_non_associative_comp_expression_operators
        operator_identifier ->
        Format.dprintf
          "Consecutive occurrences of the computation-level expressionn \
           operator %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Comp_expression_arity_mismatch
        { operator_identifier
        ; expected_arguments_count
        ; actual_arguments_count
        } ->
        Format.dprintf
          "Computation-level expression operator %a expected %d argument(s) \
           but got %d."
          Qualified_identifier.pp operator_identifier
          expected_arguments_count actual_arguments_count
    | Ambiguous_comp_pattern_operator_placement operator_identifier ->
        Format.dprintf
          "Ambiguous occurrences of the computation-level pattern operator \
           %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Misplaced_comp_pattern_operator ->
        Format.dprintf "%a" Format.pp_print_text
          "Misplaced contextual computation-level pattern operator."
    | Consecutive_applications_of_non_associative_comp_pattern_operators
        operator_identifier ->
        Format.dprintf
          "Consecutive occurrences of the computation-level patternn \
           operator %a after rewriting."
          Qualified_identifier.pp operator_identifier
    | Comp_pattern_arity_mismatch
        { operator_identifier
        ; expected_arguments_count
        ; actual_arguments_count
        } ->
        Format.dprintf
          "Computation-level pattern operator %a expected %d argument(s) \
           but got %d."
          Qualified_identifier.pp operator_identifier
          expected_arguments_count actual_arguments_count
    | Illegal_missing_comp_context_binding_type identifier ->
        Format.dprintf
          "Missing computation-level context type for binding for %a."
          Identifier.pp identifier
    | Expected_constructor_constant qualified_identifier ->
        Format.dprintf "Expected %a to be a computation-level constructor."
          Qualified_identifier.pp qualified_identifier
    | Illegal_meta_annotated_comp_pattern_missing_identifier ->
        Format.dprintf "%a" Format.pp_print_text
          "This meta-annotated pattern is missing its identifier."
    | Illegal_meta_annotated_comp_pattern_missing_type ->
        Format.dprintf "%a" Format.pp_print_text
          "This meta-annotated pattern is missing its meta-type."
    | Expected_comp_term_destructor_constant ->
        Format.dprintf "%a" Format.pp_print_text
          "Expected a computation-level term destructor constant."
    | exn -> Error.raise_unsupported_exception_printing exn)
