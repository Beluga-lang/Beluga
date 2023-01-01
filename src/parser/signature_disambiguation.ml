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

[@@@warning "-A"]

module type SIGNATURE_DISAMBIGUATION = sig
  type disambiguation_state

  type disambiguation_state_entry

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

  (** {1 Disambiguation} *)

  val disambiguate_as_pragma :
       Synprs.signature_pragma
    -> disambiguation_state
    -> disambiguation_state * Synext.signature_pragma

  val disambiguate_as_global_pragma :
       Synprs.signature_global_pragma
    -> disambiguation_state
    -> disambiguation_state * Synext.signature_global_pragma

  val disambiguate_as_totality_declaration :
       Synprs.signature_totality_declaration
    -> disambiguation_state
    -> disambiguation_state * Synext.signature_totality_declaration

  val disambiguate_as_numeric_totality_order :
       Int.t Synprs.signature_totality_order
    -> disambiguation_state
    -> disambiguation_state * Int.t Synext.signature_totality_order

  val disambiguate_as_named_totality_order :
       Identifier.t Synprs.signature_totality_order
    -> disambiguation_state
    -> disambiguation_state * Identifier.t Synext.signature_totality_order

  val disambiguate_as_declaration :
       Synprs.signature_declaration
    -> disambiguation_state
    -> disambiguation_state * Synext.signature_declaration

  val disambiguate_as_signature :
       Synprs.signature
    -> disambiguation_state
    -> disambiguation_state * Synext.signature
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (LF_disambiguation : Lf_disambiguation.LF_DISAMBIGUATION
                           with type disambiguation_state =
                             Disambiguation_state.t
                            and type disambiguation_state_entry =
                             Disambiguation_state.entry)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type disambiguation_state =
                               Disambiguation_state.t
                              and type disambiguation_state_entry =
                               Disambiguation_state.entry)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type disambiguation_state =
                               Disambiguation_state.t
                              and type disambiguation_state_entry =
                               Disambiguation_state.entry)
    (Harpoon_disambiguation : Harpoon_disambiguation.HARPOON_DISAMBIGUATION
                                with type disambiguation_state =
                                  Disambiguation_state.t
                                 and type disambiguation_state_entry =
                                  Disambiguation_state.entry) :
  SIGNATURE_DISAMBIGUATION
    with type disambiguation_state = Disambiguation_state.t
     and type disambiguation_state_entry = Disambiguation_state.entry =
struct
  type disambiguation_state = Disambiguation_state.t

  type disambiguation_state_entry = Disambiguation_state.entry

  include State.Make (Disambiguation_state)

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

  (** {1 Disambiguation Helpers} *)

  let default_precedence = 0

  let rec explicit_arguments_lf_kind kind =
    match kind with
    | Synprs.LF.Object.Raw_arrow { range; _ } ->
        1 + explicit_arguments_lf_kind range
    | Synprs.LF.Object.Raw_pi { body; _ } ->
        1 + explicit_arguments_lf_kind body
    | _ -> 0

  let rec explicit_arguments_lf_kind' kind' =
    match kind' with
    | Synext.LF.Kind.Arrow { range; _ } ->
        1 + explicit_arguments_lf_kind' range
    | Synext.LF.Kind.Pi { body; _ } -> 1 + explicit_arguments_lf_kind' body
    | _ -> 0

  let rec explicit_arguments_lf_typ typ =
    match typ with
    | Synprs.LF.Object.Raw_arrow { range; _ } ->
        1 + explicit_arguments_lf_typ range
    | Synprs.LF.Object.Raw_pi { body; _ } ->
        1 + explicit_arguments_lf_typ body
    | _ -> 0

  let rec explicit_arguments_lf_typ' typ' =
    match typ' with
    | Synext.LF.Typ.Arrow { range; _ } ->
        1 + explicit_arguments_lf_typ' range
    | Synext.LF.Typ.Pi { body; _ } -> 1 + explicit_arguments_lf_typ' body
    | _ -> 0

  let rec explicit_arguments_comp_kind kind =
    match kind with
    | Synprs.Comp.Sort_object.Raw_arrow { range; _ } ->
        1 + explicit_arguments_comp_kind range
    | Synprs.Comp.Sort_object.Raw_pi { body; plicity = Plicity.Explicit; _ }
      ->
        1 + explicit_arguments_comp_kind body
    | Synprs.Comp.Sort_object.Raw_pi { body; plicity = Plicity.Implicit; _ }
      ->
        explicit_arguments_comp_kind body
    | _ -> 0

  let rec explicit_arguments_comp_kind' kind' =
    match kind' with
    | Synext.Comp.Kind.Arrow { range; _ } ->
        1 + explicit_arguments_comp_kind' range
    | Synext.Comp.Kind.Pi { body; plicity = Plicity.Explicit; _ } ->
        1 + explicit_arguments_comp_kind' body
    | Synext.Comp.Kind.Pi { body; plicity = Plicity.Implicit; _ } ->
        explicit_arguments_comp_kind' body
    | _ -> 0

  let rec explicit_arguments_comp_typ typ =
    match typ with
    | Synprs.Comp.Sort_object.Raw_arrow { range; _ } ->
        1 + explicit_arguments_comp_typ range
    | Synprs.Comp.Sort_object.Raw_pi { body; plicity = Plicity.Explicit; _ }
      ->
        1 + explicit_arguments_comp_typ body
    | Synprs.Comp.Sort_object.Raw_pi { body; plicity = Plicity.Implicit; _ }
      ->
        explicit_arguments_comp_typ body
    | _ -> 0

  let rec explicit_arguments_comp_typ' typ' =
    match typ' with
    | Synext.Comp.Typ.Arrow { range; _ } ->
        1 + explicit_arguments_comp_typ' range
    | Synext.Comp.Typ.Pi { body; plicity = Plicity.Explicit; _ } ->
        1 + explicit_arguments_comp_typ' body
    | Synext.Comp.Typ.Pi { body; plicity = Plicity.Implicit; _ } ->
        explicit_arguments_comp_typ' body
    | _ -> 0

  (** [add_recursive_declaration_to_disambiguation_state declaration state additions]
      is [(state', additions')], where [state'] is the disambiguation state
      derived from [state'] with the addition of [declaration], and
      [additions'] is the list derived from [additions] of identifiers
      introduced in scope by [declaration].

      This function works on declarations that have yet to be disambiguated,
      and is used solely for adding the declarations to the disambiguate
      state in a mutually recursive group of declarations. [additions] is
      used to ensure that no identifier in a recursive declaration is bound
      several times. *)
  let rec add_recursive_declaration_to_disambiguation_state declaration state
      additions =
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
    | Synprs.Signature.Declaration.Raw_pragma _
    (* It is ambiguous where exactly a pragma should be applied in a
       recursive group of declarations. The parser does not support pragmas
       in mutually recursive declarations. *)
    | Synprs.Signature.Declaration.Raw_global_pragma _
    (* The parser does not support global pragmas in mutually recursive
       declarations. *)
    | Synprs.Signature.Declaration.Raw_recursive_declarations _
    (* The parser does not support nested recursive groups in mutually
       recursive declarations. *) ->
        Error.violation
          "[Signature.add_recursive_declaration_to_disambiguation_state] \
           unsupported declaration in mutually recursive declarations group"
    | Synprs.Signature.Declaration.Raw_lf_typ_constant
        { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_lf_kind kind in
        let state' =
          Disambiguation_state.add_prefix_lf_type_constant
            ~arity:explicit_arguments ~precedence:default_precedence
            identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_lf_term_constant
        { identifier; typ; _ } ->
        let explicit_arguments = explicit_arguments_lf_typ typ in
        let state' =
          Disambiguation_state.add_prefix_lf_term_constant
            ~arity:explicit_arguments ~precedence:default_precedence
            identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_comp_typ_constant
        { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_comp_kind kind in
        let state' =
          Disambiguation_state.add_prefix_computation_type_constant
            ~arity:explicit_arguments ~precedence:default_precedence
            identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_comp_expression_constructor
        { identifier; typ; _ } ->
        let explicit_arguments = explicit_arguments_comp_typ typ in
        let state' =
          Disambiguation_state.add_prefix_computation_term_constructor
            ~arity:explicit_arguments ~precedence:default_precedence
            identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
        { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_comp_kind kind in
        let state' =
          Disambiguation_state.add_prefix_computation_cotype_constant
            ~arity:explicit_arguments ~precedence:default_precedence
            identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_comp_expression_destructor
        { identifier; _ } ->
        let state' =
          Disambiguation_state.add_computation_term_destructor identifier
            state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_schema { identifier; _ } ->
        let state' =
          Disambiguation_state.add_schema_constant identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_theorem { identifier; _ } ->
        let state' =
          Disambiguation_state.add_computation_variable identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_proof { identifier; _ } ->
        let state' =
          Disambiguation_state.add_computation_variable identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_comp_kind kind in
        let state' =
          Disambiguation_state.add_prefix_computation_type_constant
            ~arity:explicit_arguments ~precedence:default_precedence
            identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_val { identifier; _ } ->
        let state' =
          Disambiguation_state.add_computation_variable identifier state
        and additions' = identifier :: additions in
        (state', additions')
    | Synprs.Signature.Declaration.Raw_query { identifier; _ } -> (
        match identifier with
        | Option.Some identifier ->
            let state' = Disambiguation_state.add_query identifier state
            and additions' = identifier :: additions in
            (state', additions')
        | Option.None -> (state, additions))
    | Synprs.Signature.Declaration.Raw_mquery { identifier; _ } -> (
        match identifier with
        | Option.Some identifier ->
            let state' = Disambiguation_state.add_mquery identifier state
            and additions' = identifier :: additions in
            (state', additions')
        | Option.None -> (state, additions))
    | Synprs.Signature.Declaration.Raw_comment _ -> (state, additions)

  (** [add_inner_module_declaration_to_disambiguation_state declaration' state]
      is the disambiguation state derived from [state] with the addition of
      [declaration']. This is used to collect the inner declarations of a
      module after it has been disambiguated. *)
  let rec add_inner_module_declaration_to_disambiguation_state declaration'
      state =
    match declaration' with
    | Synext.Signature.Declaration.Typ { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_lf_kind' kind in
        Disambiguation_state.add_prefix_lf_type_constant
          ~arity:explicit_arguments ~precedence:default_precedence identifier
          state
    | Synext.Signature.Declaration.Const { identifier; typ; _ } ->
        let explicit_arguments = explicit_arguments_lf_typ' typ in
        Disambiguation_state.add_prefix_lf_term_constant
          ~arity:explicit_arguments ~precedence:default_precedence identifier
          state
    | Synext.Signature.Declaration.CompTyp { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_comp_kind' kind in
        Disambiguation_state.add_prefix_computation_type_constant
          ~arity:explicit_arguments ~precedence:default_precedence identifier
          state
    | Synext.Signature.Declaration.CompCotyp { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_comp_kind' kind in
        Disambiguation_state.add_prefix_computation_cotype_constant
          ~arity:explicit_arguments ~precedence:default_precedence identifier
          state
    | Synext.Signature.Declaration.CompConst { identifier; typ; _ } ->
        let explicit_arguments = explicit_arguments_comp_typ' typ in
        Disambiguation_state.add_prefix_computation_term_constructor
          ~arity:explicit_arguments ~precedence:default_precedence identifier
          state
    | Synext.Signature.Declaration.CompDest { identifier; _ } ->
        Disambiguation_state.add_computation_term_destructor identifier state
    | Synext.Signature.Declaration.Schema { identifier; _ } ->
        Disambiguation_state.add_schema_constant identifier state
    | Synext.Signature.Declaration.Recursive_declarations { declarations; _ }
      ->
        List.fold_left
          (fun state declaration ->
            add_inner_module_declaration_to_disambiguation_state declaration
              state)
          state
          (List1.to_list declarations)
    | Synext.Signature.Declaration.Theorem { identifier; _ } ->
        Disambiguation_state.add_computation_variable identifier state
    | Synext.Signature.Declaration.Proof { identifier; _ } ->
        Disambiguation_state.add_computation_variable identifier state
    | Synext.Signature.Declaration.CompTypAbbrev { identifier; kind; _ } ->
        let explicit_arguments = explicit_arguments_comp_kind' kind in
        Disambiguation_state.add_prefix_computation_type_constant
          ~arity:explicit_arguments ~precedence:default_precedence identifier
          state
    | Synext.Signature.Declaration.Val { identifier; _ } ->
        Disambiguation_state.add_computation_variable identifier state
    | Synext.Signature.Declaration.Query { identifier; _ } -> (
        match identifier with
        | Option.Some identifier ->
            Disambiguation_state.add_query identifier state
        | Option.None -> state)
    | Synext.Signature.Declaration.MQuery { identifier; _ } -> (
        match identifier with
        | Option.Some identifier ->
            Disambiguation_state.add_mquery identifier state
        | Option.None -> state)
    | Synext.Signature.Declaration.Module { identifier; declarations; _ } ->
        let sub_state =
          List.fold_left
            (fun state declaration ->
              add_inner_module_declaration_to_disambiguation_state
                declaration state)
            Disambiguation_state.empty declarations
        in
        Disambiguation_state.add_module
          (Disambiguation_state.get_bindings sub_state)
          identifier state
    | Synext.Signature.Declaration.Pragma _
    | Synext.Signature.Declaration.GlobalPragma _ ->
        (* Pragmas in a module only apply in the module. *) state
    | Synext.Signature.Declaration.Comment _ -> state

  (** [make_operator_prefix ?precedence operator_identifier state] is the
      disambiguation state derived from [state] where the operator with
      identifier [operator_identifier] is set as a prefix operator with
      [precedence]. *)
  let make_operator_prefix ?precedence operator_identifier state =
    Disambiguation_state.modify_operator
      (fun operator ->
        let arity = Operator.arity operator
        and precedence =
          Option.value ~default:default_precedence precedence
        in
        if arity >= 0 then Operator.make_prefix ~arity ~precedence
        else
          let location = Qualified_identifier.location operator_identifier in
          Error.raise_at1 location
            (Invalid_prefix_pragma { actual_arity = arity }))
      operator_identifier state

  (** [make_operator_infix ?precedence ?associativity operator_identifier state]
      is the disambiguation state derived from [state] where the operator
      with identifier [operator_identifier] is set as an infix operator with
      [precedence] and [associativity]. If [associativity = Option.None],
      then the default associativity as found [state] is used instead.

      Only operators with arity [2] may be converted to infix operators. *)
  let make_operator_infix ?precedence ?associativity operator_identifier
      state =
    let associativity =
      match associativity with
      | Option.Some associativity -> associativity
      | Option.None -> Disambiguation_state.get_default_associativity state
    in
    Disambiguation_state.modify_operator
      (fun operator ->
        let arity = Operator.arity operator
        and precedence =
          Option.value ~default:default_precedence precedence
        in
        if arity = 2 then Operator.make_infix ~associativity ~precedence
        else
          let location = Qualified_identifier.location operator_identifier in
          Error.raise_at1 location
            (Invalid_infix_pragma { actual_arity = arity }))
      operator_identifier state

  (** [make_operator_postfix ?precedence operator_identifier state] is the
      disambiguation state derived from [state] where the operator with
      identifier [operator_identifier] is set as a postifx operator with
      [precedence].

      Only operators with arity [1] may be converted to postfix operators. *)
  let make_operator_postfix ?precedence operator_identifier state =
    Disambiguation_state.modify_operator
      (fun operator ->
        let arity = Operator.arity operator
        and precedence =
          Option.value ~default:default_precedence precedence
        in
        if arity = 1 then Operator.make_postfix ~precedence
        else
          let location = Qualified_identifier.location operator_identifier in
          Error.raise_at1 location
            (Invalid_postfix_pragma { actual_arity = arity }))
      operator_identifier state

  (** [open_module module_identifier state] is the disambiguation state
      derived from [state] with the addition of the declarations in the
      module having identifier [module_identifier] currently in scope. *)
  let open_module module_identifier state =
    match Disambiguation_state.lookup module_identifier state with
    | Disambiguation_state.Module { entries = sub_state } ->
        Disambiguation_state.modify_bindings
          (fun bindings ->
            Identifier.Hamt.union
              (fun _key _original_binding new_binding -> new_binding)
              bindings sub_state
          )
          state
    | _entry ->
        let location = Qualified_identifier.location module_identifier in
        Error.raise_at1 location (Expected_module module_identifier)

  (** [add_module_abbreviation module_identifier abbreviation state] is the
      disambiguation state derived from [state] with the addition of
      [abbreviation] as a synonym for the module with identifier
      [module_identifier] currently in scope. *)
  let add_module_abbreviation module_identifier abbreviation state =
    match Disambiguation_state.lookup module_identifier state with
    | Disambiguation_state.Module { entries = sub_state } ->
        Disambiguation_state.add_module sub_state abbreviation state
    | _entry ->
        let location = Qualified_identifier.location module_identifier in
        Error.raise_at1 location (Expected_module module_identifier)

  (** {1 Disambiguation} *)

  let rec disambiguate_as_pragma pragma =
    match pragma with
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
        let* () =
          modify
            (Disambiguation_state.set_default_associativity associativity)
        in
        return
          (Synext.Signature.Pragma.Default_associativity
             { location; associativity })
    | Synprs.Signature.Pragma.Prefix_fixity
        { location; constant; precedence } ->
        let* () = modify (make_operator_prefix ?precedence constant) in
        return
          (Synext.Signature.Pragma.Prefix_fixity
             { location; constant; precedence })
    | Synprs.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity } ->
        let* () =
          modify (make_operator_infix ?precedence ?associativity constant)
        in
        return
          (Synext.Signature.Pragma.Infix_fixity
             { location; constant; precedence; associativity })
    | Synprs.Signature.Pragma.Postfix_fixity
        { location; constant; precedence } ->
        let* () = modify (make_operator_postfix ?precedence constant) in
        return
          (Synext.Signature.Pragma.Postfix_fixity
             { location; constant; precedence })
    | Synprs.Signature.Pragma.Not { location } ->
        return (Synext.Signature.Pragma.Not { location })
    | Synprs.Signature.Pragma.Open_module { location; module_identifier } ->
        let* () = modify (open_module module_identifier) in
        return
          (Synext.Signature.Pragma.Open_module
             { location; module_identifier })
    | Synprs.Signature.Pragma.Abbreviation
        { location; module_identifier; abbreviation } ->
        let* () =
          modify (add_module_abbreviation module_identifier abbreviation)
        in
        return
          (Synext.Signature.Pragma.Abbreviation
             { location; module_identifier; abbreviation })

  and disambiguate_as_global_pragma global_pragma =
    match global_pragma with
    | Synprs.Signature.Pragma.Global.No_strengthening { location } ->
        return (Synext.Signature.Pragma.Global.No_strengthening { location })
    | Synprs.Signature.Pragma.Global.Coverage { location; variant } ->
        return
          (Synext.Signature.Pragma.Global.Coverage { location; variant })

  and disambiguate_as_totality_declaration totality_declaration =
    match totality_declaration with
    | Synprs.Signature.Totality.Declaration.Trust { location } ->
        return (Synext.Signature.Totality.Declaration.Trust { location })
    | Synprs.Signature.Totality.Declaration.Numeric { location; order } ->
        let* order' =
          match order with
          | Option.None -> return Option.none
          | Option.Some order ->
              let* order' = disambiguate_as_numeric_totality_order order in
              return (Option.some order')
        in
        return
          (Synext.Signature.Totality.Declaration.Numeric
             { location; order = order' })
    | Synprs.Signature.Totality.Declaration.Named
        { location; order; program; argument_labels } ->
        let* order' =
          match order with
          | Option.None -> return Option.none
          | Option.Some order ->
              let* order' = disambiguate_as_named_totality_order order in
              return (Option.some order')
        in
        return
          (Synext.Signature.Totality.Declaration.Named
             { location; order = order'; program; argument_labels })

  and disambiguate_as_numeric_totality_order totality_order =
    match totality_order with
    | Synprs.Signature.Totality.Order.Argument { location; argument } ->
        return
          (Synext.Signature.Totality.Order.Argument { location; argument })
    | Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments } ->
        get >>= fun state ->
        let arguments' =
          List1.map
            (fun argument ->
              eval (disambiguate_as_numeric_totality_order argument) state)
            arguments
        in
        return
          (Synext.Signature.Totality.Order.Lexical_ordering
             { location; arguments = arguments' })
    | Synprs.Signature.Totality.Order.Simultaneous_ordering
        { location; arguments } ->
        get >>= fun state ->
        let arguments' =
          List1.map
            (fun argument ->
              eval (disambiguate_as_numeric_totality_order argument) state)
            arguments
        in
        return
          (Synext.Signature.Totality.Order.Simultaneous_ordering
             { location; arguments = arguments' })

  and disambiguate_as_named_totality_order totality_order =
    match totality_order with
    | Synprs.Signature.Totality.Order.Argument { location; argument } ->
        return
          (Synext.Signature.Totality.Order.Argument { location; argument })
    | Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments } ->
        get >>= fun state ->
        let arguments' =
          List1.map
            (fun argument ->
              eval (disambiguate_as_named_totality_order argument) state)
            arguments
        in
        return
          (Synext.Signature.Totality.Order.Lexical_ordering
             { location; arguments = arguments' })
    | Synprs.Signature.Totality.Order.Simultaneous_ordering
        { location; arguments } ->
        get >>= fun state ->
        let arguments' =
          List1.map
            (fun argument ->
              eval (disambiguate_as_named_totality_order argument) state)
            arguments
        in
        return
          (Synext.Signature.Totality.Order.Simultaneous_ordering
             { location; arguments = arguments' })

  (** [disambiguate_as_recursive_declarations declarations state] is
      [(state', declarations')] where [declarations'] is [declarations]
      disambiguated as mutually recursive declarations, and [state] is
      [state'] with the addition of [declarations'].

      An exception is raised if the identifiers for the declarations in
      [declarations] are not unique, in which case an identifier is bound
      multiple times in a group of recursive declarations. *)
  and disambiguate_as_recursive_declarations declarations state =
    let state', additions =
      declarations |> List1.to_list
      |> List.fold_left
           (fun (state, additions) declaration ->
             add_recursive_declaration_to_disambiguation_state declaration
               state additions)
           (state, [])
    in
    match Identifier.find_duplicates additions with
    | Option.Some duplicates ->
        let locations = List2.map Identifier.location duplicates in
        Error.raise_at
          (List2.to_list1 locations)
          Identifiers_bound_several_times_in_recursive_declaration
    | Option.None ->
        let _states', declarations' =
          declarations
          |> List1.map (fun declaration ->
                 disambiguate_as_declaration declaration state')
          |> List1.split
        in
        (state', declarations')

  and disambiguate_as_declaration declaration =
    match declaration with
    | Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant
        { location; identifier; typ_or_const }
    (* Old style LF type or term constant declaration *) -> (
        try
          let* kind' = LF_disambiguation.disambiguate_as_kind typ_or_const in
          let explicit_arguments = explicit_arguments_lf_kind' kind' in
          let* () =
            modify
              (Disambiguation_state.add_prefix_lf_type_constant
                 ~arity:explicit_arguments ~precedence:default_precedence
                 identifier)
          in
          return
            (Synext.Signature.Declaration.Typ
               { location; identifier; kind = kind' })
        with
        | typ_exn -> (
            try
              let* typ' =
                LF_disambiguation.disambiguate_as_typ typ_or_const
              in
              let explicit_arguments = explicit_arguments_lf_typ' typ' in
              let* () =
                modify
                  (Disambiguation_state.add_prefix_lf_term_constant
                     ~arity:explicit_arguments ~precedence:default_precedence
                     identifier)
              in
              return
                (Synext.Signature.Declaration.Const
                   { location; identifier; typ = typ' })
            with
            | const_exn ->
                if typ_exn <> const_exn then
                  (* Disambiguation as an LF type or term constant
                     declaration failed for different reasons *)
                  raise
                    (Old_style_lf_constant_declaration_error
                       { as_type_constant = typ_exn
                       ; as_term_constant = const_exn
                       })
                else
                  (* Disambiguation as an LF type or term constant
                     declaration failed for the same reason *) raise typ_exn)
        )
    | Synprs.Signature.Declaration.Raw_lf_typ_constant
        { location; identifier; kind } ->
        let* kind' = LF_disambiguation.disambiguate_as_kind kind in
        let explicit_arguments = explicit_arguments_lf_kind' kind' in
        let* () =
          modify
            (Disambiguation_state.add_prefix_lf_type_constant
               ~arity:explicit_arguments ~precedence:default_precedence
               identifier)
        in
        return
          (Synext.Signature.Declaration.Typ
             { location; identifier; kind = kind' })
    | Synprs.Signature.Declaration.Raw_lf_term_constant
        { location; identifier; typ } ->
        let* typ' = LF_disambiguation.disambiguate_as_typ typ in
        let explicit_arguments = explicit_arguments_lf_typ' typ' in
        let* () =
          modify
            (Disambiguation_state.add_prefix_lf_term_constant
               ~arity:explicit_arguments ~precedence:default_precedence
               identifier)
        in
        return
          (Synext.Signature.Declaration.Const
             { location; identifier; typ = typ' })
    | Synprs.Signature.Declaration.Raw_comp_typ_constant
        { location; identifier; kind; datatype_flavour } ->
        let* kind' = Comp_disambiguation.disambiguate_as_kind kind in
        let explicit_arguments = explicit_arguments_comp_kind' kind' in
        let* () =
          modify
            (Disambiguation_state.add_prefix_computation_type_constant
               ~arity:explicit_arguments ~precedence:default_precedence
               identifier)
        in
        return
          (Synext.Signature.Declaration.CompTyp
             { location; identifier; kind = kind'; datatype_flavour })
    | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
        { location; identifier; kind } ->
        let* kind' = Comp_disambiguation.disambiguate_as_kind kind in
        let explicit_arguments = explicit_arguments_comp_kind' kind' in
        let* () =
          modify
            (Disambiguation_state.add_prefix_computation_cotype_constant
               ~arity:explicit_arguments ~precedence:default_precedence
               identifier)
        in
        return
          (Synext.Signature.Declaration.CompCotyp
             { location; identifier; kind = kind' })
    | Synprs.Signature.Declaration.Raw_comp_expression_constructor
        { location; identifier; typ } ->
        let* typ' = Comp_disambiguation.disambiguate_as_typ typ in
        let explicit_arguments = explicit_arguments_comp_typ' typ' in
        let* () =
          modify
            (Disambiguation_state.add_prefix_computation_term_constructor
               ~arity:explicit_arguments ~precedence:default_precedence
               identifier)
        in
        return
          (Synext.Signature.Declaration.CompConst
             { location; identifier; typ = typ' })
    | Synprs.Signature.Declaration.Raw_comp_expression_destructor
        { location; identifier; observation_type; return_type } ->
        let* observation_type' =
          Comp_disambiguation.disambiguate_as_typ observation_type
        in
        let* return_type' =
          Comp_disambiguation.disambiguate_as_typ return_type
        in
        let* () =
          modify
            (Disambiguation_state.add_computation_term_destructor identifier)
        in
        return
          (Synext.Signature.Declaration.CompDest
             { location
             ; identifier
             ; observation_type = observation_type'
             ; return_type = return_type'
             })
    | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { location; identifier; kind; typ } ->
        let* kind' = Comp_disambiguation.disambiguate_as_kind kind in
        let* typ' = Comp_disambiguation.disambiguate_as_typ typ in
        let explicit_arguments = explicit_arguments_comp_kind' kind' in
        let* () =
          modify
            (Disambiguation_state.add_prefix_computation_type_constant
               ~arity:explicit_arguments ~precedence:default_precedence
               identifier)
        in
        return
          (Synext.Signature.Declaration.CompTypAbbrev
             { location; identifier; kind = kind'; typ = typ' })
    | Synprs.Signature.Declaration.Raw_schema
        { location; identifier; schema } ->
        let* schema' = Meta_disambiguation.disambiguate_as_schema schema in
        let* () =
          modify (Disambiguation_state.add_schema_constant identifier)
        in
        return
          (Synext.Signature.Declaration.Schema
             { location; identifier; schema = schema' })
    | Synprs.Signature.Declaration.Raw_pragma { location; pragma } ->
        let* pragma' = disambiguate_as_pragma pragma in
        return
          (Synext.Signature.Declaration.Pragma { location; pragma = pragma' })
    | Synprs.Signature.Declaration.Raw_global_pragma { location; pragma } ->
        let* pragma' = disambiguate_as_global_pragma pragma in
        return
          (Synext.Signature.Declaration.GlobalPragma
             { location; pragma = pragma' })
    | Synprs.Signature.Declaration.Raw_recursive_declarations
        { location; declarations } ->
        let* declarations' =
          disambiguate_as_recursive_declarations declarations
        in
        return
          (Synext.Signature.Declaration.Recursive_declarations
             { location; declarations = declarations' })
    | Synprs.Signature.Declaration.Raw_theorem
        { location; identifier; typ; order; body } ->
        let* typ' = Comp_disambiguation.disambiguate_as_typ typ in
        let* order' =
          match order with
          | Option.None -> return Option.none
          | Option.Some order ->
              let* order' = disambiguate_as_totality_declaration order in
              return (Option.some order')
        in
        let* body' = Comp_disambiguation.disambiguate_as_expression body in
        let* () =
          modify (Disambiguation_state.add_computation_variable identifier)
        in
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
        let* typ' = Comp_disambiguation.disambiguate_as_typ typ in
        let* order' =
          match order with
          | Option.None -> return Option.none
          | Option.Some order ->
              let* order' = disambiguate_as_totality_declaration order in
              return (Option.some order')
        in
        let* body' = Harpoon_disambiguation.disambiguate_as_proof body in
        let* () =
          modify (Disambiguation_state.add_computation_variable identifier)
        in
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
        let* typ' =
          match typ with
          | Option.None -> return Option.none
          | Option.Some typ ->
              let* typ' = Comp_disambiguation.disambiguate_as_typ typ in
              return (Option.some typ')
        in
        let* expression' =
          Comp_disambiguation.disambiguate_as_expression expression
        in
        let* () =
          modify (Disambiguation_state.add_computation_variable identifier)
        in
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
        get >>= fun state ->
        let* meta_context' =
          Meta_disambiguation.disambiguate_as_meta_context meta_context
        in
        let* typ' = LF_disambiguation.disambiguate_as_typ typ in
        let* () =
          put state (* Discard bindings introduced by [meta_context'] *)
        in
        let* () =
          match identifier with
          | Option.Some identifier ->
              modify (Disambiguation_state.add_query identifier)
          | Option.None -> return ()
        in
        return
          (Synext.Signature.Declaration.Query
             { location
             ; identifier
             ; meta_context = meta_context'
             ; typ = typ'
             ; expected_solutions
             ; maximum_tries
             })
    | Synprs.Signature.Declaration.Raw_mquery
        { location
        ; typ
        ; identifier
        ; expected_solutions
        ; search_tries
        ; search_depth
        } ->
        let* typ' = Comp_disambiguation.disambiguate_as_typ typ in
        let* () =
          match identifier with
          | Option.Some identifier ->
              modify (Disambiguation_state.add_mquery identifier)
          | Option.None -> return ()
        in
        return
          (Synext.Signature.Declaration.MQuery
             { location
             ; identifier
             ; typ = typ'
             ; expected_solutions
             ; search_tries
             ; search_depth
             })
    | Synprs.Signature.Declaration.Raw_module
        { location; identifier; declarations } ->
        (* Disambiguate inner declarations as if they were outside the
           module. *)
        let* declarations' = disambiguate_as_signature declarations in
        (* Collect the disambiguated inner declarations. *)
        let sub_state =
          List.fold_left
            (fun state declaration' ->
              add_inner_module_declaration_to_disambiguation_state
                declaration' state)
            Disambiguation_state.empty declarations'
        in
        (* Add the disambiguated inner declarations as nested in the
           module. *)
        let* () =
          modify
            (Disambiguation_state.add_module
               (Disambiguation_state.get_bindings sub_state)
               identifier)
        in
        return
          (Synext.Signature.Declaration.Module
             { location; identifier; declarations = declarations' })
    | Synprs.Signature.Declaration.Raw_comment { location; content } ->
        return (Synext.Signature.Declaration.Comment { location; content })

  (** [disambiguate_as_signature state signature] is [state', signature'],
      where [signature'] is [signature] disambiguated with respect to
      [state], and [state'] is [state] with all the declarations in
      [signature'] applied/added to it.

      - When disambiguating the signature in the first file of a Beluga
        project, use {!Disambiguation_state.empty} as initial disambiguation
        state.
      - When disambiguating a signature spread across multiple files, make
        sure to disambiguate the files in the order configured by the
        end-user, and pass [state'] to subsequent calls to
        {!disambiguate_as_signature}.

      The very last [state'] after disambiguating an entire Beluga project
      may be discarded. *)
  and disambiguate_as_signature declarations state =
    let state', declarations_rev' =
      List.fold_left
        (fun (state, declarations_rev') declaration ->
          let state', declaration' =
            disambiguate_as_declaration declaration state
          in
          (state', declaration' :: declarations_rev'))
        (state, []) declarations
    in
    let declarations' = List.rev declarations_rev' in
    (state', declarations')
end
