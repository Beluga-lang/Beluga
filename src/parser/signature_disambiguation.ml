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

(** {2 Exceptions for pragma applications} *)

exception Invalid_prefix_pragma of { actual_arity : Int.t }

exception Invalid_infix_pragma of { actual_arity : Int.t }

exception Invalid_postfix_pragma of { actual_arity : Int.t }

exception Expected_module of Qualified_identifier.t

(** {2 Exceptions for declaration disambiguation} *)

exception
  Old_style_lf_constant_declaration_error of
    { as_type_constant : exn
    ; as_term_constant : exn
    }

(** {2 Exceptions for recursive declaration disambiguation} *)

exception Identifiers_bound_several_times_in_recursive_declaration

module type SIGNATURE_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_pragma :
    Synprs.signature_pragma -> Synext.signature_pragma t

  val disambiguate_global_pragma :
    Synprs.signature_global_pragma -> Synext.signature_global_pragma t

  val disambiguate_totality_declaration :
       Synprs.signature_totality_declaration
    -> Synext.signature_totality_declaration t

  val disambiguate_numeric_totality_order :
       Int.t Synprs.signature_totality_order
    -> Int.t Synext.signature_totality_order t

  val disambiguate_named_totality_order :
       Identifier.t Synprs.signature_totality_order
    -> Identifier.t Synext.signature_totality_order t

  val disambiguate_declaration :
    Synprs.signature_declaration -> Synext.signature_declaration t

  val disambiguate_signature : Synprs.signature -> Synext.signature t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Lf_disambiguation : Lf_disambiguation.LF_DISAMBIGUATION
                           with type state = Disambiguation_state.state)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Harpoon_disambiguation : Harpoon_disambiguation.HARPOON_DISAMBIGUATION
                                with type state = Disambiguation_state.state) :
  SIGNATURE_DISAMBIGUATION with type state = Disambiguation_state.state =
struct
  include Disambiguation_state
  include Lf_disambiguation
  include Meta_disambiguation
  include Comp_disambiguation
  include Harpoon_disambiguation

  (** {1 Disambiguation Helpers} *)

  let add_query_opt = function
    | Option.None -> return ()
    | Option.Some identifier -> add_query identifier

  let add_declaration_opt = function
    | Option.None -> return ()
    | Option.Some identifier -> add_declaration identifier

  let explicit_arguments_lf_kind =
    let rec explicit_arguments_lf_kind_tl kind acc =
      match kind with
      | Synprs.LF.Object.Raw_arrow { range; _ } ->
          explicit_arguments_lf_kind_tl range (1 + acc)
      | Synprs.LF.Object.Raw_pi { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_lf_kind_tl body (1 + acc)
      | Synprs.LF.Object.Raw_pi { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_lf_kind_tl body acc
      | _ -> acc
    in
    fun kind -> explicit_arguments_lf_kind_tl kind 0

  let explicit_arguments_lf_kind' =
    let rec explicit_arguments_lf_kind_tl' kind' acc =
      match kind' with
      | Synext.LF.Kind.Arrow { range; _ } ->
          explicit_arguments_lf_kind_tl' range (1 + acc)
      | Synext.LF.Kind.Pi { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_lf_kind_tl' body (1 + acc)
      | Synext.LF.Kind.Pi { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_lf_kind_tl' body acc
      | _ -> acc
    in
    fun kind' -> explicit_arguments_lf_kind_tl' kind' 0

  let explicit_arguments_lf_typ =
    let rec explicit_arguments_lf_typ_tl typ acc =
      match typ with
      | Synprs.LF.Object.Raw_arrow { range; _ } ->
          explicit_arguments_lf_typ_tl range (1 + acc)
      | Synprs.LF.Object.Raw_pi { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_lf_typ_tl body (1 + acc)
      | Synprs.LF.Object.Raw_pi { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_lf_typ_tl body acc
      | _ -> acc
    in
    fun typ -> explicit_arguments_lf_typ_tl typ 0

  let explicit_arguments_lf_typ' =
    let rec explicit_arguments_lf_typ_tl' typ' acc =
      match typ' with
      | Synext.LF.Typ.Arrow { range; _ } ->
          explicit_arguments_lf_typ_tl' range (1 + acc)
      | Synext.LF.Typ.Pi { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_lf_typ_tl' body (1 + acc)
      | Synext.LF.Typ.Pi { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_lf_typ_tl' body acc
      | _ -> acc
    in
    fun typ' -> explicit_arguments_lf_typ_tl' typ' 0

  let explicit_arguments_comp_kind =
    let rec explicit_arguments_comp_kind_tl kind acc =
      match kind with
      | Synprs.Comp.Sort_object.Raw_arrow { range; _ } ->
          explicit_arguments_comp_kind_tl range (1 + acc)
      | Synprs.Comp.Sort_object.Raw_pi
          { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_comp_kind_tl body (1 + acc)
      | Synprs.Comp.Sort_object.Raw_pi
          { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_comp_kind_tl body acc
      | _ -> acc
    in
    fun kind -> explicit_arguments_comp_kind_tl kind 0

  let explicit_arguments_comp_kind' =
    let rec explicit_arguments_comp_kind_tl' kind' acc =
      match kind' with
      | Synext.Comp.Kind.Arrow { range; _ } ->
          explicit_arguments_comp_kind_tl' range (1 + acc)
      | Synext.Comp.Kind.Pi { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_comp_kind_tl' body (1 + acc)
      | Synext.Comp.Kind.Pi { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_comp_kind_tl' body acc
      | _ -> acc
    in
    fun kind' -> explicit_arguments_comp_kind_tl' kind' 0

  let explicit_arguments_comp_typ =
    let rec explicit_arguments_comp_typ_tl typ acc =
      match typ with
      | Synprs.Comp.Sort_object.Raw_arrow { range; _ } ->
          explicit_arguments_comp_typ_tl range (1 + acc)
      | Synprs.Comp.Sort_object.Raw_pi
          { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_comp_typ_tl body (1 + acc)
      | Synprs.Comp.Sort_object.Raw_pi
          { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_comp_typ_tl body acc
      | _ -> acc
    in
    fun typ -> explicit_arguments_comp_typ_tl typ 0

  let explicit_arguments_comp_typ' =
    let rec explicit_arguments_comp_typ_tl' typ' acc =
      match typ' with
      | Synext.Comp.Typ.Arrow { range; _ } ->
          explicit_arguments_comp_typ_tl' range (1 + acc)
      | Synext.Comp.Typ.Pi { body; plicity = Plicity.Explicit; _ } ->
          explicit_arguments_comp_typ_tl' body (1 + acc)
      | Synext.Comp.Typ.Pi { body; plicity = Plicity.Implicit; _ } ->
          explicit_arguments_comp_typ_tl' body acc
      | _ -> acc
    in
    fun typ' -> explicit_arguments_comp_typ_tl' typ' 0

  let default_precedence = 0

  let make_default_prefix_operator ~arity =
    Operator.make_prefix ~arity ~precedence:default_precedence

  let make_default_lf_type_constant_operator lf_kind =
    let explicit_arguments = explicit_arguments_lf_kind lf_kind in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_lf_type_constant_operator' lf_kind' =
    let explicit_arguments = explicit_arguments_lf_kind' lf_kind' in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_lf_term_constant_operator lf_typ =
    let explicit_arguments = explicit_arguments_lf_typ lf_typ in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_lf_term_constant_operator' lf_typ' =
    let explicit_arguments = explicit_arguments_lf_typ' lf_typ' in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_comp_typ_constant_operator comp_kind =
    let explicit_arguments = explicit_arguments_comp_kind comp_kind in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_comp_typ_constant_operator' comp_kind' =
    let explicit_arguments = explicit_arguments_comp_kind' comp_kind' in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_comp_constructor_operator comp_typ =
    let explicit_arguments = explicit_arguments_comp_typ comp_typ in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_comp_constructor_operator' comp_typ' =
    let explicit_arguments = explicit_arguments_comp_typ' comp_typ' in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_program_constant_operator comp_typ =
    let explicit_arguments = explicit_arguments_comp_typ comp_typ in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_program_constant_operator' comp_typ' =
    let explicit_arguments = explicit_arguments_comp_typ' comp_typ' in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_comp_destructor_operator comp_typ =
    let explicit_arguments = explicit_arguments_comp_typ comp_typ in
    make_default_prefix_operator ~arity:explicit_arguments

  let make_default_comp_destructor_operator' comp_typ' =
    let explicit_arguments = explicit_arguments_comp_typ' comp_typ' in
    make_default_prefix_operator ~arity:explicit_arguments

  let add_default_lf_type_constant identifier kind =
    let operator = make_default_lf_type_constant_operator kind in
    add_lf_type_constant operator identifier

  let add_default_lf_type_constant' identifier kind' =
    let operator = make_default_lf_type_constant_operator' kind' in
    add_lf_type_constant operator identifier

  let add_default_lf_term_constant identifier typ =
    let operator = make_default_lf_term_constant_operator typ in
    add_lf_term_constant operator identifier

  let add_default_lf_term_constant' identifier typ' =
    let operator = make_default_lf_term_constant_operator' typ' in
    add_lf_term_constant operator identifier

  let add_default_inductive_comp_typ_constant identifier kind =
    let operator = make_default_comp_typ_constant_operator kind in
    add_inductive_computation_type_constant operator identifier

  let add_default_inductive_comp_typ_constant' identifier kind' =
    let operator = make_default_comp_typ_constant_operator' kind' in
    add_inductive_computation_type_constant operator identifier

  let add_default_stratified_comp_typ_constant identifier kind =
    let operator = make_default_comp_typ_constant_operator kind in
    add_stratified_computation_type_constant operator identifier

  let add_default_stratified_comp_typ_constant' identifier kind' =
    let operator = make_default_comp_typ_constant_operator' kind' in
    add_stratified_computation_type_constant operator identifier

  let add_default_abbreviation_comp_typ_constant identifier kind =
    let operator = make_default_comp_typ_constant_operator kind in
    add_abbreviation_computation_type_constant operator identifier

  let add_default_abbreviation_comp_typ_constant' identifier kind' =
    let operator = make_default_comp_typ_constant_operator' kind' in
    add_abbreviation_computation_type_constant operator identifier

  let add_default_coinductive_comp_typ_constant identifier kind =
    let operator = make_default_comp_typ_constant_operator kind in
    add_coinductive_computation_type_constant operator identifier

  let add_default_coinductive_comp_typ_constant' identifier kind' =
    let operator = make_default_comp_typ_constant_operator' kind' in
    add_coinductive_computation_type_constant operator identifier

  let add_default_comp_constructor_constant identifier typ =
    let operator = make_default_comp_constructor_operator typ in
    add_computation_term_constructor operator identifier

  let add_default_comp_constructor_constant' identifier typ' =
    let operator = make_default_comp_constructor_operator' typ' in
    add_computation_term_constructor operator identifier

  let add_default_program_constant ?typ identifier =
    match typ with
    | Option.Some typ ->
        let operator = make_default_program_constant_operator typ in
        add_program_constant ~operator identifier
    | Option.None -> add_program_constant identifier

  let add_default_program_constant' ?typ' identifier =
    match typ' with
    | Option.Some typ' ->
        let operator = make_default_program_constant_operator' typ' in
        add_program_constant ~operator identifier
    | Option.None -> add_program_constant identifier

  let rec add_recursive_declaration declaration =
    match declaration with
    | Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant _
    (* Old style LF declarations can't be disambiguated without knowing the
       identifiers in scope and their sort, and the sort of an old style LF
       declaration cannot be determined unless it is disambiguated. The
       parser does not support old style LF declarations in mutually
       recursive declarations. *)
    | Synprs.Signature.Declaration.Raw_module _
    (* Adding a module as a recursive declaration adds its declarations to
       the current scope, but old style LF declarations prevent inferring the
       sort of the declarations in the module. As such, recursive modules
       need an explicit module type. The parser does not support modules in
       mutually recursive declarations. *)
    | Synprs.Signature.Declaration.Raw_recursive_declarations _
    (* The parser does not support nested recursive groups in mutually
       recursive declarations. *) ->
        Error.raise_violation
          "[Signature.add_recursive_declaration] unsupported declaration in \
           mutually recursive declarations group"
    | Synprs.Signature.Declaration.Raw_lf_typ_constant
        { identifier; kind; _ } ->
        add_default_lf_type_constant identifier kind
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_lf_term_constant
        { identifier; typ; _ } ->
        add_default_lf_term_constant identifier typ
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant
        { identifier; kind; _ } ->
        add_default_inductive_comp_typ_constant identifier kind
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant
        { identifier; kind; _ } ->
        add_default_stratified_comp_typ_constant identifier kind
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_comp_expression_constructor
        { identifier; typ; _ } ->
        add_default_comp_constructor_constant identifier typ
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
        { identifier; kind; _ } ->
        add_default_coinductive_comp_typ_constant identifier kind
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_comp_expression_destructor
        { identifier; _ } ->
        add_computation_term_destructor identifier
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_schema { identifier; _ } ->
        add_schema_constant identifier <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_theorem { identifier; typ; _ } ->
        add_default_program_constant identifier ~typ
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_proof { identifier; typ; _ } ->
        add_default_program_constant identifier ~typ
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { identifier; kind; _ } ->
        add_default_abbreviation_comp_typ_constant identifier kind
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_val { identifier; typ; _ } ->
        add_default_program_constant ?typ identifier
        <& add_declaration identifier
    | Synprs.Signature.Declaration.Raw_query { identifier; _ } ->
        add_query_opt identifier <& add_declaration_opt identifier

  (** [make_operator_prefix ?precedence operator_identifier state] is the
      disambiguation state derived from [state] where the operator with
      identifier [operator_identifier] is set as a prefix operator with
      [precedence]. *)
  let make_operator_prefix ?precedence operator_identifier =
    modify_operator operator_identifier (fun operator ->
        let arity = Operator.arity operator
        and precedence =
          Option.value ~default:default_precedence precedence
        in
        if arity >= 0 then Operator.make_prefix ~arity ~precedence
        else
          Error.raise_at1
            (Qualified_identifier.location operator_identifier)
            (Invalid_prefix_pragma { actual_arity = arity }))

  let get_default_associativity_opt = function
    | Option.Some associativity -> return associativity
    | Option.None -> get_default_associativity

  (** [make_operator_infix ?precedence ?associativity operator_identifier state]
      is the disambiguation state derived from [state] where the operator
      with identifier [operator_identifier] is set as an infix operator with
      [precedence] and [associativity]. If [associativity = Option.None],
      then the default associativity as found [state] is used instead.

      Only operators with arity [2] may be converted to infix operators. *)
  let make_operator_infix ?precedence ?associativity operator_identifier =
    let* associativity = get_default_associativity_opt associativity in
    modify_operator operator_identifier (fun operator ->
        let arity = Operator.arity operator
        and precedence =
          Option.value ~default:default_precedence precedence
        in
        if arity = 2 then Operator.make_infix ~associativity ~precedence
        else
          Error.raise_at1
            (Qualified_identifier.location operator_identifier)
            (Invalid_infix_pragma { actual_arity = arity }))

  (** [make_operator_postfix ?precedence operator_identifier state] is the
      disambiguation state derived from [state] where the operator with
      identifier [operator_identifier] is set as a postifx operator with
      [precedence].

      Only operators with arity [1] may be converted to postfix operators. *)
  let make_operator_postfix ?precedence operator_identifier =
    modify_operator operator_identifier (fun operator ->
        let arity = Operator.arity operator
        and precedence =
          Option.value ~default:default_precedence precedence
        in
        if arity = 1 then Operator.make_postfix ~precedence
        else
          Error.raise_at1
            (Qualified_identifier.location operator_identifier)
            (Invalid_postfix_pragma { actual_arity = arity }))

  (** [add_module_abbreviation module_identifier abbreviation state] is the
      disambiguation state derived from [state] with the addition of
      [abbreviation] as a synonym for the module with identifier
      [module_identifier] currently in scope. *)
  let add_module_abbreviation module_identifier abbreviation =
    lookup module_identifier >>= function
    | Result.Ok (Module, _) -> add_synonym module_identifier abbreviation
    | Result.Ok entry ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          (Error.composite_exception2 (Expected_module module_identifier)
             (actual_binding_exn module_identifier entry))
    | Result.Error cause ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          cause

  (** {1 Disambiguation} *)

  let rec disambiguate_pragma = function
    | Synprs.Signature.Pragma.Name
        { location; constant; meta_variable_base; computation_variable_base }
      ->
        return
          (Synext.Signature.Pragma.Name
             { location
             ; constant
             ; meta_variable_base
             ; computation_variable_base
             })
    | Synprs.Signature.Pragma.Default_associativity
        { location; associativity } ->
        let* () = set_default_associativity associativity in
        return
          (Synext.Signature.Pragma.Default_associativity
             { location; associativity })
    | Synprs.Signature.Pragma.Prefix_fixity
        { location; constant; precedence } ->
        let* () = make_operator_prefix ?precedence constant in
        let* () =
          is_inner_bound_declaration constant >>= function
          | true -> update_declaration constant
          | false -> return ()
        in
        return
          (Synext.Signature.Pragma.Prefix_fixity
             { location; constant; precedence })
    | Synprs.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity } ->
        let* () = make_operator_infix ?precedence ?associativity constant in
        let* () =
          is_inner_bound_declaration constant >>= function
          | true -> update_declaration constant
          | false -> return ()
        in
        return
          (Synext.Signature.Pragma.Infix_fixity
             { location; constant; precedence; associativity })
    | Synprs.Signature.Pragma.Postfix_fixity
        { location; constant; precedence } ->
        let* () = make_operator_postfix ?precedence constant in
        let* () =
          is_inner_bound_declaration constant >>= function
          | true -> update_declaration constant
          | false -> return ()
        in
        return
          (Synext.Signature.Pragma.Postfix_fixity
             { location; constant; precedence })
    | Synprs.Signature.Pragma.Not { location } ->
        return (Synext.Signature.Pragma.Not { location })
    | Synprs.Signature.Pragma.Open_module { location; module_identifier } ->
        let* () = open_module module_identifier in
        return
          (Synext.Signature.Pragma.Open_module
             { location; module_identifier })
    | Synprs.Signature.Pragma.Abbreviation
        { location; module_identifier; abbreviation } ->
        let* () = add_module_abbreviation module_identifier abbreviation in
        return
          (Synext.Signature.Pragma.Abbreviation
             { location; module_identifier; abbreviation })

  and disambiguate_global_pragma = function
    | Synprs.Signature.Global_pragma.No_strengthening { location } ->
        return (Synext.Signature.Global_pragma.No_strengthening { location })
    | Synprs.Signature.Global_pragma.Warn_on_coverage_error { location } ->
        return
          (Synext.Signature.Global_pragma.Warn_on_coverage_error { location })
    | Synprs.Signature.Global_pragma.Raise_error_on_coverage_error
        { location } ->
        return
          (Synext.Signature.Global_pragma.Raise_error_on_coverage_error
             { location })

  and disambiguate_totality_declaration = function
    | Synprs.Signature.Totality.Declaration.Trust { location } ->
        return (Synext.Signature.Totality.Declaration.Trust { location })
    | Synprs.Signature.Totality.Declaration.Numeric { location; order } ->
        let* order' =
          traverse_option disambiguate_numeric_totality_order order
        in
        return
          (Synext.Signature.Totality.Declaration.Numeric
             { location; order = order' })
    | Synprs.Signature.Totality.Declaration.Named
        { location; order; program; argument_labels } ->
        let* order' =
          traverse_option disambiguate_named_totality_order order
        in
        return
          (Synext.Signature.Totality.Declaration.Named
             { location; order = order'; program; argument_labels })

  and disambiguate_numeric_totality_order = function
    | Synprs.Signature.Totality.Order.Argument { location; argument } ->
        return
          (Synext.Signature.Totality.Order.Argument { location; argument })
    | Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments } ->
        let* arguments' =
          traverse_list1 disambiguate_numeric_totality_order arguments
        in
        return
          (Synext.Signature.Totality.Order.Lexical_ordering
             { location; arguments = arguments' })
    | Synprs.Signature.Totality.Order.Simultaneous_ordering
        { location; arguments } ->
        let* arguments' =
          traverse_list1 disambiguate_numeric_totality_order arguments
        in
        return
          (Synext.Signature.Totality.Order.Simultaneous_ordering
             { location; arguments = arguments' })

  and disambiguate_named_totality_order = function
    | Synprs.Signature.Totality.Order.Argument { location; argument } ->
        return
          (Synext.Signature.Totality.Order.Argument { location; argument })
    | Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments } ->
        let* arguments' =
          traverse_list1 disambiguate_named_totality_order arguments
        in
        return
          (Synext.Signature.Totality.Order.Lexical_ordering
             { location; arguments = arguments' })
    | Synprs.Signature.Totality.Order.Simultaneous_ordering
        { location; arguments } ->
        let* arguments' =
          traverse_list1 disambiguate_named_totality_order arguments
        in
        return
          (Synext.Signature.Totality.Order.Simultaneous_ordering
             { location; arguments = arguments' })

  and disambiguate_mutually_recursive_declarations declarations =
    let* () = traverse_list1_void add_recursive_declaration declarations in
    let* state = get in
    let* declarations =
      traverse_list1 disambiguate_declaration declarations
    in
    let* () = put state in
    return declarations

  and disambiguate_declaration = function
    | Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant
        { location; identifier; typ_or_const }
    (* Old style LF type or term constant declaration *) ->
        let disambiguate_as_lf_typ_declaration =
          lazy
            (let* kind' = disambiguate_lf_kind typ_or_const in
             let* () = add_default_lf_type_constant' identifier kind' in
             let* () = add_declaration identifier in
             return
               (Synext.Signature.Declaration.Typ
                  { location; identifier; kind = kind' }))
        and disambiguate_as_lf_const_declaration =
          lazy
            (let* typ' = disambiguate_lf_typ typ_or_const in
             let* () = add_default_lf_term_constant' identifier typ' in
             let* () = add_declaration identifier in
             return
               (Synext.Signature.Declaration.Const
                  { location; identifier; typ = typ' }))
        in
        try_catch disambiguate_as_lf_typ_declaration ~on_exn:(fun typ_exn ->
            try_catch disambiguate_as_lf_const_declaration
              ~on_exn:(fun const_exn ->
                if typ_exn <> const_exn then
                  (* Disambiguation as an LF type or term constant
                     declaration failed for different reasons *)
                  Error.raise_at1 location
                    (Old_style_lf_constant_declaration_error
                       { as_type_constant = typ_exn
                       ; as_term_constant = const_exn
                       })
                else
                  (* Disambiguation as an LF type or term constant
                     declaration failed for the same reason *)
                  Error.raise typ_exn))
    | Synprs.Signature.Declaration.Raw_lf_typ_constant
        { location; identifier; kind } ->
        let* kind' = disambiguate_lf_kind kind in
        let* () = add_default_lf_type_constant' identifier kind' in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.Typ
             { location; identifier; kind = kind' })
    | Synprs.Signature.Declaration.Raw_lf_term_constant
        { location; identifier; typ } ->
        let* typ' = disambiguate_lf_typ typ in
        let* () = add_default_lf_term_constant' identifier typ' in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.Const
             { location; identifier; typ = typ' })
    | Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant
        { location; identifier; kind } ->
        let* kind' = disambiguate_comp_kind kind in
        let* () =
          add_default_inductive_comp_typ_constant' identifier kind'
        in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.CompTyp
             { location
             ; identifier
             ; kind = kind'
             ; datatype_flavour = `Inductive
             })
    | Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant
        { location; identifier; kind } ->
        let* kind' = disambiguate_comp_kind kind in
        let* () =
          add_default_stratified_comp_typ_constant' identifier kind'
        in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.CompTyp
             { location
             ; identifier
             ; kind = kind'
             ; datatype_flavour = `Stratified
             })
    | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
        { location; identifier; kind } ->
        let* kind' = disambiguate_comp_kind kind in
        let* () =
          add_default_coinductive_comp_typ_constant' identifier kind'
        in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.CompCotyp
             { location; identifier; kind = kind' })
    | Synprs.Signature.Declaration.Raw_comp_expression_constructor
        { location; identifier; typ } ->
        let* typ' = disambiguate_comp_typ typ in
        let* () = add_default_comp_constructor_constant' identifier typ' in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.CompConst
             { location; identifier; typ = typ' })
    | Synprs.Signature.Declaration.Raw_comp_expression_destructor
        { location; identifier; observation_type; return_type } ->
        let* observation_type' = disambiguate_comp_typ observation_type in
        let* return_type' = disambiguate_comp_typ return_type in
        let* () = add_computation_term_destructor identifier in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.CompDest
             { location
             ; identifier
             ; observation_type = observation_type'
             ; return_type = return_type'
             })
    | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { location; identifier; kind; typ } ->
        let* kind' = disambiguate_comp_kind kind in
        let* typ' = disambiguate_comp_typ typ in
        let* () =
          add_default_abbreviation_comp_typ_constant' identifier kind'
        in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.CompTypAbbrev
             { location; identifier; kind = kind'; typ = typ' })
    | Synprs.Signature.Declaration.Raw_schema
        { location; identifier; schema } ->
        let* schema' = disambiguate_schema schema in
        let* () = add_schema_constant identifier in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.Schema
             { location; identifier; schema = schema' })
    | Synprs.Signature.Declaration.Raw_recursive_declarations
        { location; declarations } ->
        let* declarations' =
          disambiguate_mutually_recursive_declarations declarations
        in
        return
          (Synext.Signature.Declaration.Recursive_declarations
             { location; declarations = declarations' })
    | Synprs.Signature.Declaration.Raw_theorem
        { location; identifier; typ; order; body } ->
        let* typ' = disambiguate_comp_typ typ in
        let* order' =
          traverse_option disambiguate_totality_declaration order
        in
        let* () = add_program_constant identifier in
        let* () = add_declaration identifier in
        let* body' = disambiguate_comp_expression body in
        return
          (Synext.Signature.Declaration.Theorem
             { location
             ; identifier
             ; typ = typ'
             ; order = order'
             ; body = body'
             })
    | Synprs.Signature.Declaration.Raw_proof
        { location; identifier; typ; order; body } ->
        let* typ' = disambiguate_comp_typ typ in
        let* order' =
          traverse_option disambiguate_totality_declaration order
        in
        let* () = add_program_constant identifier in
        let* () = add_declaration identifier in
        let* body' = with_scope (disambiguate_harpoon_proof body) in
        return
          (Synext.Signature.Declaration.Proof
             { location
             ; identifier
             ; typ = typ'
             ; order = order'
             ; body = body'
             })
    | Synprs.Signature.Declaration.Raw_val
        { location; identifier; typ; expression } ->
        let* typ' = traverse_option disambiguate_comp_typ typ in
        let* expression' = disambiguate_comp_expression expression in
        let* () = add_program_constant identifier in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.Val
             { location; identifier; typ = typ'; expression = expression' })
    | Synprs.Signature.Declaration.Raw_query
        { location
        ; identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        } ->
        let* meta_context', typ' =
          with_disambiguated_meta_context meta_context (fun meta_context' ->
              let* typ' = disambiguate_lf_typ typ in
              return (meta_context', typ'))
        in
        let* () = add_query_opt identifier in
        let* () = add_declaration_opt identifier in
        return
          (Synext.Signature.Declaration.Query
             { location
             ; identifier
             ; meta_context = meta_context'
             ; typ = typ'
             ; expected_solutions
             ; maximum_tries
             })
    | Synprs.Signature.Declaration.Raw_module
        { location; identifier; declarations } ->
        let* entries' =
          with_module_inner_declarations
            ~declarations:(traverse_list disambiguate_entry declarations)
            ~module_identifier:identifier
        in
        let* () = add_declaration identifier in
        return
          (Synext.Signature.Declaration.Module
             { location; identifier; entries = entries' })

  and disambiguate_entry = function
    | Synprs.Signature.Entry.Raw_pragma { pragma; location } ->
        let* pragma' = disambiguate_pragma pragma in
        return (Synext.Signature.Entry.Pragma { pragma = pragma'; location })
    | Synprs.Signature.Entry.Raw_declaration { declaration; location } ->
        let* declaration' = disambiguate_declaration declaration in
        return
          (Synext.Signature.Entry.Declaration
             { declaration = declaration'; location })
    | Synprs.Signature.Entry.Raw_comment { location; content } ->
        return (Synext.Signature.Entry.Comment { location; content })

  (** [disambiguate_signature state signature] is [state', signature'], where
      [signature'] is [signature] disambiguated with respect to [state], and
      [state'] is [state] with all the declarations in [signature']
      applied/added to it.

      - When disambiguating the signature in the first file of a Beluga
        project, use {!empty} as initial disambiguation state.
      - When disambiguating a signature spread across multiple files, make
        sure to disambiguate the files in the order configured by the
        end-user, and pass [state'] to subsequent calls to
        {!disambiguate_signature}.

      The very last [state'] after disambiguating an entire Beluga project
      may be discarded. *)
  and disambiguate_signature = function
    | { Synprs.Signature.global_pragmas; entries } ->
        let* global_pragmas' =
          traverse_list disambiguate_global_pragma global_pragmas
        in
        let* entries' = traverse_list disambiguate_entry entries in
        return
          { Synext.Signature.global_pragmas = global_pragmas'
          ; entries = entries'
          }
end

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Invalid_prefix_pragma { actual_arity } ->
        Format.dprintf "Can't make an operator with arity %d prefix."
          actual_arity
    | Invalid_infix_pragma { actual_arity } ->
        Format.dprintf "Can't make an operator with arity %d infix."
          actual_arity
    | Invalid_postfix_pragma { actual_arity } ->
        Format.dprintf "Can't make an operator with arity %d postfix."
          actual_arity
    | Expected_module qualified_identifier ->
        Format.dprintf "Expected %a to be a module." Qualified_identifier.pp
          qualified_identifier
    | Old_style_lf_constant_declaration_error
        { as_type_constant; as_term_constant } ->
        let as_type_constant_printer = Error.find_printer as_type_constant in
        let as_term_constant_printer = Error.find_printer as_term_constant in
        Format.dprintf
          "@[<v 0>@[<hov 0>Failed@ to@ disambiguate@ old-style@ LF@ \
           type-level@ or@ term-level@ constant@ declaration.@]@,\
           - @[<hov 0>As@ an@ LF@ type:@ %t@]@,\
           - @[<hov 0>As@ an@ LF@ term:@ %t@]@]" as_type_constant_printer
          as_term_constant_printer
    | Identifiers_bound_several_times_in_recursive_declaration ->
        Format.dprintf
          "Identifiers may not be bound several times in a mutually \
           recursive declaration."
    | exn -> Error.raise_unsupported_exception_printing exn)
