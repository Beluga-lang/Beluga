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

[@@@warning "-A-4-44"]

(** {1 Exceptions} *)

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

exception Illegal_duplicate_pattern_variables

(** {2 Exceptions for computation-level context disambiguation} *)

exception Illegal_missing_comp_context_binding_type

(** {2 Exceptions for computation-level pattern disambiguation} *)

exception Illegal_meta_annotated_comp_pattern_missing_identifier

exception Illegal_meta_annotated_comp_pattern_missing_type

(** {2 Exceptions for computation-level copattern disambiguation} *)

exception Expected_comp_term_destructor_constant

(** {1 Disambiguation} *)

module type COMP_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind :
    Synprs.Comp.Sort_object.t -> Synext.Comp.Kind.t t

  val disambiguate_comp_typ :
    Synprs.Comp.Sort_object.t -> Synext.Comp.Typ.t t

  val disambiguate_comp_expression :
    Synprs.Comp.Expression_object.t -> Synext.Comp.Expression.t t

  val with_disambiguated_comp_context :
    Synprs.Comp.Context_object.t -> (Synext.Comp.Context.t -> 'a t) -> 'a t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Disambiguation_state.state = struct
  include Disambiguation_state
  include Meta_disambiguation

  exception Plain_modifier_typ_mismatch

  exception Hash_modifier_typ_mismatch

  exception Dollar_modifier_typ_mismatch

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

  let rec with_meta_function_parameters_list1 parameters f =
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
    | Option.None -> Error.violation "[pop_binding]"
    | Option.Some (List1.T (_head, [])) ->
        Identifier.Hamt.remove identifier bindings
    | Option.Some (List1.T (_head, x :: xs)) ->
        Identifier.Hamt.add identifier (List1.from x xs) bindings

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

  module Comp_typ_application_disambiguation_state = struct
    include Disambiguation_state

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
      | Synprs.Comp.Sort_object.Raw_identifier { quoted; _ }
      | Synprs.Comp.Sort_object.Raw_qualified_identifier { quoted; _ }
        when quoted ->
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

  module Comp_typ_application_disambiguation =
    Application_disambiguation.Make (Associativity) (Fixity)
      (Comp_typ_operand)
      (Comp_typ_operator)
      (Comp_typ_application_disambiguation_state)

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
        | Synext.Comp.Typ.Constant _
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
    | Synprs.Comp.Sort_object.Raw_identifier { location; identifier; quoted }
      -> (
        (* As a computation-level type, plain identifiers are necessarily
           type constants *)
        let qualified_identifier =
          Qualified_identifier.make_simple identifier
        in
        lookup_toplevel identifier >>= function
        | Result.Ok
            ( Computation_inductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Inductive
                 })
        | Result.Ok
            ( Computation_stratified_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Stratified
                 })
        | Result.Ok
            ( Computation_abbreviation_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Abbreviation
                 })
        | Result.Ok
            ( Computation_coinductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier = qualified_identifier
                 ; operator
                 ; quoted
                 ; variant = `Coinductive
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
        { location; identifier; quoted } -> (
        (* Qualified identifiers without namespaces were parsed as plain
           identifiers *)
        assert (List.length (Qualified_identifier.namespaces identifier) >= 1);
        (* As a computation-level type, identifiers of the form
           [(<identifier> `::')+ <identifier>] are necessarily type
           constants. *)
        lookup identifier >>= function
        | Result.Ok
            ( Computation_inductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Inductive
                 })
        | Result.Ok
            ( Computation_stratified_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Stratified
                 })
        | Result.Ok
            ( Computation_abbreviation_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Abbreviation
                 })
        | Result.Ok
            ( Computation_coinductive_type_constant
            , { operator = Option.Some operator; _ } ) ->
            return
              (Synext.Comp.Typ.Constant
                 { location
                 ; identifier
                 ; operator
                 ; quoted
                 ; variant = `Coinductive
                 })
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
        let* applicand, arguments = disambiguate_clf_application objects in
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

  and disambiguate_clf_application objects =
    Comp_typ_application_disambiguation.disambiguate_application objects
    >>= function
    | Result.Ok (applicand, arguments) -> return (applicand, arguments)
    | Result.Error
        (Comp_typ_application_disambiguation.Ambiguous_operator_placement
          { left_operator; right_operator }) ->
        let left_operator_location =
          Comp_typ_operator.location left_operator
        in
        let right_operator_location =
          Comp_typ_operator.location right_operator
        in
        let identifier = Comp_typ_operator.identifier left_operator in
        Error.raise_at2 left_operator_location right_operator_location
          (Ambiguous_comp_typ_operator_placement identifier)
    | Result.Error
        (Comp_typ_application_disambiguation.Arity_mismatch
          { operator; operator_arity; operands }) ->
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
        (Comp_typ_application_disambiguation
         .Consecutive_non_associative_operators
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
    | Result.Error
        (Comp_typ_application_disambiguation.Misplaced_operator
          { operator; operands }) ->
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
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_qualified_identifier
        { location; identifier; quoted } ->
        (* TODO: Can be the observation(s) of a variable *)
        Obj.magic ()
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
          traverse_list1 disambiguate_cofunction_branch branches
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
        let* pattern', body' = disambiguate_case_branch (pattern, body) in
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
        let* branches' = traverse_list1 disambiguate_case_branch branches in
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
        return (Synext.Comp.Expression.BoxHole { location })
    | Synprs.Comp.Expression_object.Raw_application { location; expressions }
      ->
        Obj.magic ()
    | Synprs.Comp.Expression_object.Raw_annotated
        { location; expression; typ } ->
        let* expression' = disambiguate_comp_expression expression in
        let* typ' = disambiguate_comp_typ typ in
        return
          (Synext.Comp.Expression.Type_annotated
             { location; expression = expression'; typ = typ' })
    | Synprs.Comp.Expression_object.Raw_observation
        { location; scrutinee; destructor } ->
        (* TODO: Can be observation(s) *)
        Obj.magic ()

  and disambiguate_case_branch (pattern_object, body_object) =
    with_disambiguated_comp_pattern pattern_object Identifier.Hamt.empty []
      (fun pattern' _inner_bindings' pattern_variables' ->
        match Identifier.find_duplicates pattern_variables' with
        | Option.None ->
            let* body' = disambiguate_comp_expression body_object in
            return (pattern', body')
        | Option.Some duplicate_pattern_variables ->
            Error.raise_at
              (List2.to_list1
                 (List2.map Identifier.location duplicate_pattern_variables))
              Illegal_duplicate_pattern_variables)

  and disambiguate_cofunction_branch (copattern_objects, body_object) =
    with_disambiguated_comp_copatterns_list1 copattern_objects
      Identifier.Hamt.empty []
      (fun copattern' _inner_bindings' pattern_variables' ->
        match Identifier.find_duplicates pattern_variables' with
        | Option.None ->
            let* body' = disambiguate_comp_expression body_object in
            return (copattern', body')
        | Option.Some duplicate_pattern_variables ->
            Error.raise_at
              (List2.to_list1
                 (List2.map Identifier.location duplicate_pattern_variables))
              Illegal_duplicate_pattern_variables)

  and with_disambiguated_comp_patterns_list objects inner_bindings
      pattern_variables f =
    match objects with
    | [] -> f [] inner_bindings pattern_variables
    | x :: xs ->
        with_disambiguated_comp_pattern x inner_bindings pattern_variables
          (fun y inner_bindings' pattern_variables' ->
            with_disambiguated_comp_patterns_list xs inner_bindings'
              pattern_variables'
              (fun ys inner_bindings'' pattern_variables'' ->
                f (y :: ys) inner_bindings'' pattern_variables''))

  and with_disambiguated_comp_pattern :
      type a.
         Synprs.comp_pattern_object
      -> Identifier.t List1.t Identifier.Hamt.t
      -> Identifier.t list
      -> (   Synext.comp_pattern
          -> Identifier.t List1.t Identifier.Hamt.t
          -> Identifier.t list
          -> a t)
      -> a t =
   fun object_ inner_bindings pattern_variables f ->
    match object_ with
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_identifier = Option.None, _; _ } ->
        Error.raise_at1 location
          Illegal_meta_annotated_comp_pattern_missing_identifier
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location; parameter_typ = Option.None; _ } ->
        Error.raise_at1 location
          Illegal_meta_annotated_comp_pattern_missing_type
    | Synprs.Comp.Pattern_object.Raw_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier
        { location; identifier; quoted } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_box { location; pattern } ->
        with_disambiguated_meta_pattern pattern inner_bindings
          pattern_variables
          (fun pattern' inner_bindings' pattern_variables' ->
            f
              (Synext.Comp.Pattern.MetaObject
                 { location; meta_pattern = pattern' })
              inner_bindings' pattern_variables')
    | Synprs.Comp.Pattern_object.Raw_tuple { location; elements } ->
        (* TODO: Use the same [inner_bindings] for each argument and
           applicand, but carry the pattern variables *)
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_application { location; patterns } ->
        (* TODO: Use the same [inner_bindings] for each argument and
           applicand, but carry the pattern variables *)
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } ->
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_annotated { location; pattern; typ } ->
        let* typ' = disambiguate_comp_typ typ in
        with_disambiguated_comp_pattern pattern inner_bindings
          pattern_variables
          (fun pattern' inner_bindings' pattern_variables' ->
            f
              (Synext.Comp.Pattern.Type_annotated
                 { location; pattern = pattern'; typ = typ' })
              inner_bindings' pattern_variables')
    | Synprs.Comp.Pattern_object.Raw_meta_annotated
        { location
        ; parameter_identifier = Option.Some parameter_identifier, modifier
        ; parameter_typ = Option.Some parameter_typ
        ; pattern
        } ->
        let* parameter_typ' = disambiguate_meta_typ parameter_typ in
        (with_parameter_binding parameter_identifier modifier parameter_typ')
          (with_disambiguated_comp_pattern pattern
             (push_binding parameter_identifier inner_bindings)
             pattern_variables
             (fun pattern' inner_bindings' pattern_variables' ->
               f
                 (Synext.Comp.Pattern.MetaTypeAnnotated
                    { location
                    ; annotation_identifier = parameter_identifier
                    ; annotation_type = parameter_typ'
                    ; body = pattern'
                    })
                 (pop_binding parameter_identifier inner_bindings')
                 pattern_variables'))
    | Synprs.Comp.Pattern_object.Raw_wildcard { location } ->
        f
          (Synext.Comp.Pattern.Wildcard { location })
          inner_bindings pattern_variables

  and with_disambiguated_comp_copatterns_list objects inner_bindings
      pattern_variables f =
    match objects with
    | [] -> f [] inner_bindings pattern_variables
    | x :: xs ->
        with_disambiguated_comp_copattern x inner_bindings pattern_variables
          (fun y inner_bindings' pattern_variables' ->
            with_disambiguated_comp_copatterns_list xs inner_bindings'
              pattern_variables'
              (fun ys inner_bindings'' pattern_variables'' ->
                f (y :: ys) inner_bindings'' pattern_variables''))

  and with_disambiguated_comp_copatterns_list1 objects inner_bindings
      pattern_variables f =
    let (List1.T (x, xs)) = objects in
    with_disambiguated_comp_copattern x inner_bindings pattern_variables
      (fun y inner_bindings' pattern_variables' ->
        with_disambiguated_comp_copatterns_list xs inner_bindings'
          pattern_variables' (fun ys inner_bindings'' pattern_variables'' ->
            f (List1.from y ys) inner_bindings'' pattern_variables''))

  and with_disambiguated_comp_copattern object_ inner_bindings
      pattern_variables f =
    match object_ with
    | Synprs.Comp.Pattern_object.Raw_qualified_identifier _ ->
        (* TODO: Can be a variable pattern or constant together with an
           observation *)
        Obj.magic ()
    | Synprs.Comp.Pattern_object.Raw_observation
        { location; constant; arguments } -> (
        lookup constant >>= function
        | Result.Ok (Computation_term_destructor, _) ->
            with_disambiguated_comp_patterns_list arguments inner_bindings
              pattern_variables
              (fun arguments' inner_bindings' pattern_variables' ->
                f
                  (Synext.Comp.Copattern.Observation
                     { location
                     ; observation = constant
                     ; arguments = arguments'
                     })
                  inner_bindings' pattern_variables')
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
      | Synprs.Comp.Pattern_object.Raw_wildcard _ ) as pattern_object ->
        with_disambiguated_comp_pattern pattern_object inner_bindings
          pattern_variables
          (fun pattern' inner_bindings' pattern_variables' ->
            f (Synext.Comp.Copattern.Pattern pattern') inner_bindings'
              pattern_variables')

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
          Illegal_missing_comp_context_binding_type
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
