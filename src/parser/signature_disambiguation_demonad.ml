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

(** {1 Exceptions} *)

exception Duplicate_identifiers_recursive_declaration of Identifier.t List1.t

(** {2 Exceptions for declaration disambiguation} *)

exception
  Old_style_lf_constant_declaration_error of
    { as_type_constant : exn
    ; as_term_constant : exn
    }

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
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
    | Duplicate_identifiers_recursive_declaration duplicates ->
        Format.dprintf
          "@[<v 0>@[<hov 0>Illegal@ duplicate@ identifiers@ in@ mutually@ \
           recursive@ declaration.@ The@ following@ identifiers@ are@ in@ \
           conflict:@]@,\
           %a@]"
          (List1.pp ~pp_sep:Format.pp_print_cut (fun ppf identifier ->
               Format.fprintf ppf "@[<hov 0>- %a@]" Identifier.pp identifier))
          duplicates
    | exn -> Error.raise_unsupported_exception_printing exn)

module type SIGNATURE_DISAMBIGUATION = sig
  type state

  (** {1 Disambiguation} *)

  val disambiguate_pragma :
    state -> Synprs.signature_pragma -> Synext.signature_pragma

  val disambiguate_global_pragma :
    state -> Synprs.signature_global_pragma -> Synext.signature_global_pragma

  val disambiguate_totality_declaration :
       state
    -> Synprs.signature_totality_declaration
    -> Synext.signature_totality_declaration

  val disambiguate_numeric_totality_order :
       state
    -> Int.t Synprs.signature_totality_order
    -> Int.t Synext.signature_totality_order

  val disambiguate_named_totality_order :
       state
    -> Identifier.t Synprs.signature_totality_order
    -> Identifier.t Synext.signature_totality_order

  val disambiguate_declaration :
    state -> Synprs.signature_declaration -> Synext.signature_declaration

  val disambiguate_signature_file :
    state -> Synprs.signature_file -> Synext.signature_file

  val disambiguate_signature : state -> Synprs.signature -> Synext.signature
end

module Make
    (Disambiguation_state : Disambiguation_state_demonad.DISAMBIGUATION_STATE)
    (Lf_disambiguation : Lf_disambiguation_demonad.LF_DISAMBIGUATION
                           with type state = Disambiguation_state.state)
    (Clf_disambiguation : Clf_disambiguation_demonad.CLF_DISAMBIGUATION
                            with type state = Disambiguation_state.state)
    (Meta_disambiguation : Meta_disambiguation_demonad.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Comp_disambiguation : Comp_disambiguation_demonad.COMP_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Harpoon_disambiguation : Harpoon_disambiguation_demonad
                              .HARPOON_DISAMBIGUATION
                                with type state = Disambiguation_state.state) :
  SIGNATURE_DISAMBIGUATION with type state = Disambiguation_state.state =
struct
  include Disambiguation_state
  include Lf_disambiguation
  include Clf_disambiguation
  include Meta_disambiguation
  include Comp_disambiguation
  include Harpoon_disambiguation

  (** {1 Disambiguation Helpers} *)

  let with_bound_meta_level_variable = function
    | Synext.Meta.Typ.Context_schema _ -> with_bound_context_variable
    | Synext.Meta.Typ.Contextual_typ _ -> with_bound_meta_variable
    | Synext.Meta.Typ.Parameter_typ _ -> with_bound_parameter_variable
    | Synext.Meta.Typ.Plain_substitution_typ _
    | Synext.Meta.Typ.Renaming_substitution_typ _ ->
        with_bound_substitution_variable

  let with_bound_meta_level_variable_opt state identifier_opt typ f =
    match identifier_opt with
    | Option.None -> f state
    | Option.Some identifier ->
        with_bound_meta_level_variable typ state identifier f

  let add_default_lf_type_constant state ?location identifier kind =
    let arity = Synprs.explicit_arguments_lf_kind kind in
    add_lf_type_constant state ?location ~arity identifier

  let add_default_lf_type_constant' state ?location identifier kind' =
    let arity = Synext.explicit_arguments_lf_kind kind' in
    add_lf_type_constant state ?location ~arity identifier

  let add_default_lf_term_constant state ?location identifier typ =
    let arity = Synprs.explicit_arguments_lf_typ typ in
    add_lf_term_constant state ?location ~arity identifier

  let add_default_lf_term_constant' state ?location identifier typ' =
    let arity = Synext.explicit_arguments_lf_typ typ' in
    add_lf_term_constant state ?location ~arity identifier

  let add_default_inductive_comp_typ_constant state ?location identifier kind
      =
    let arity = Synprs.explicit_arguments_comp_kind kind in
    add_inductive_computation_type_constant state ?location ~arity identifier

  let add_default_inductive_comp_typ_constant' state ?location identifier
      kind' =
    let arity = Synext.explicit_arguments_comp_kind kind' in
    add_inductive_computation_type_constant state ?location ~arity identifier

  let add_default_stratified_comp_typ_constant state ?location identifier
      kind =
    let arity = Synprs.explicit_arguments_comp_kind kind in
    add_stratified_computation_type_constant state ?location ~arity
      identifier

  let add_default_stratified_comp_typ_constant' state ?location identifier
      kind' =
    let arity = Synext.explicit_arguments_comp_kind kind' in
    add_stratified_computation_type_constant state ?location ~arity
      identifier

  let add_default_abbreviation_comp_typ_constant state ?location identifier
      kind =
    let arity = Synprs.explicit_arguments_comp_kind kind in
    add_abbreviation_computation_type_constant state ?location ~arity
      identifier

  let add_default_abbreviation_comp_typ_constant' state ?location identifier
      kind' =
    let arity = Synext.explicit_arguments_comp_kind kind' in
    add_abbreviation_computation_type_constant state ?location ~arity
      identifier

  let add_default_coinductive_comp_typ_constant state ?location identifier
      kind =
    let arity = Synprs.explicit_arguments_comp_kind kind in
    add_coinductive_computation_type_constant state ?location ~arity
      identifier

  let add_default_coinductive_comp_typ_constant' state ?location identifier
      kind' =
    let arity = Synext.explicit_arguments_comp_kind kind' in
    add_coinductive_computation_type_constant state ?location ~arity
      identifier

  let add_default_comp_constructor_constant state ?location identifier typ =
    let arity = Synprs.explicit_arguments_comp_typ typ in
    add_computation_term_constructor state ?location ~arity identifier

  let add_default_comp_constructor_constant' state ?location identifier typ'
      =
    let arity = Synext.explicit_arguments_comp_typ typ' in
    add_computation_term_constructor state ?location ~arity identifier

  let add_default_program_constant state ?location ?typ identifier =
    let arity = Option.map Synprs.explicit_arguments_comp_typ typ in
    add_program_constant state ?location ?arity identifier

  let add_default_program_constant' state ?location ?typ' identifier =
    let arity = Option.map Synext.explicit_arguments_comp_typ typ' in
    add_program_constant state ?location ?arity identifier

  let add_declaration state = function
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
          (Format.asprintf
             "[%s] unsupported declaration in mutually recursive \
              declarations group"
             __FUNCTION__)
    | Synprs.Signature.Declaration.Raw_lf_typ_constant
        { identifier; kind; _ } ->
        add_default_lf_type_constant state identifier kind
    | Synprs.Signature.Declaration.Raw_lf_term_constant
        { identifier; typ; _ } ->
        add_default_lf_term_constant state identifier typ
    | Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant
        { identifier; kind; _ } ->
        add_default_inductive_comp_typ_constant state identifier kind
    | Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant
        { identifier; kind; _ } ->
        add_default_stratified_comp_typ_constant state identifier kind
    | Synprs.Signature.Declaration.Raw_comp_expression_constructor
        { identifier; typ; _ } ->
        add_default_comp_constructor_constant state identifier typ
    | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
        { identifier; kind; _ } ->
        add_default_coinductive_comp_typ_constant state identifier kind
    | Synprs.Signature.Declaration.Raw_comp_expression_destructor
        { identifier; _ } ->
        add_computation_term_destructor state identifier
    | Synprs.Signature.Declaration.Raw_schema { identifier; _ } ->
        add_schema_constant state identifier
    | Synprs.Signature.Declaration.Raw_theorem { identifier; typ; _ } ->
        add_default_program_constant state identifier ~typ
    | Synprs.Signature.Declaration.Raw_proof { identifier; typ; _ } ->
        add_default_program_constant state identifier ~typ
    | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { identifier; kind; _ } ->
        add_default_abbreviation_comp_typ_constant state identifier kind
    | Synprs.Signature.Declaration.Raw_val { identifier; typ; _ } ->
        add_default_program_constant state ?typ identifier

  let add_declaration' state = function
    | Synext.Signature.Declaration.Typ { identifier; kind; _ } ->
        add_default_lf_type_constant' state identifier kind
    | Synext.Signature.Declaration.Const { identifier; typ; _ } ->
        add_default_lf_term_constant' state identifier typ
    | Synext.Signature.Declaration.CompTyp
        { identifier; kind; datatype_flavour; _ } -> (
        match datatype_flavour with
        | `Inductive ->
            add_default_inductive_comp_typ_constant' state identifier kind
        | `Stratified ->
            add_default_stratified_comp_typ_constant' state identifier kind)
    | Synext.Signature.Declaration.CompCotyp { identifier; kind; _ } ->
        add_default_coinductive_comp_typ_constant' state identifier kind
    | Synext.Signature.Declaration.CompConst { identifier; typ; _ } ->
        add_default_comp_constructor_constant' state identifier typ
    | Synext.Signature.Declaration.CompDest { identifier; _ } ->
        add_computation_term_destructor state identifier
    | Synext.Signature.Declaration.Schema { identifier; _ } ->
        add_schema_constant state identifier
    | Synext.Signature.Declaration.Theorem { identifier; typ; _ } ->
        add_default_program_constant' state identifier ~typ':typ
    | Synext.Signature.Declaration.Proof { identifier; typ; _ } ->
        add_default_program_constant' state identifier ~typ':typ
    | Synext.Signature.Declaration.CompTypAbbrev { identifier; kind; _ } ->
        add_default_abbreviation_comp_typ_constant' state identifier kind
    | Synext.Signature.Declaration.Val { identifier; typ; _ } ->
        add_default_program_constant' state ?typ':typ identifier
    | Synext.Signature.Declaration.Recursive_declarations _ ->
        Error.raise_violation
          (Format.asprintf "[%s] unsupported recursive declarations"
             __FUNCTION__)
    | Synext.Signature.Declaration.Module _ ->
        Error.raise_violation
          (Format.asprintf "[%s] unsupported module declaration" __FUNCTION__)

  let declaration_identifiers declarations =
    List.fold_right
      (fun declaration accumulator ->
        match declaration with
        | Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_lf_typ_constant { identifier; _ }
        | Synprs.Signature.Declaration.Raw_lf_term_constant { identifier; _ }
        | Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_comp_expression_constructor
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_comp_expression_destructor
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
            { identifier; _ }
        | Synprs.Signature.Declaration.Raw_schema { identifier; _ }
        | Synprs.Signature.Declaration.Raw_theorem { identifier; _ }
        | Synprs.Signature.Declaration.Raw_proof { identifier; _ }
        | Synprs.Signature.Declaration.Raw_val { identifier; _ } ->
            identifier :: accumulator
        | Synprs.Signature.Declaration.Raw_recursive_declarations _ ->
            Error.raise_violation
              (Format.asprintf "[%s] unsupported recursive declarations"
                 __FUNCTION__)
        | Synprs.Signature.Declaration.Raw_module _ ->
            Error.raise_violation
              (Format.asprintf "[%s] unsupported module declaration"
                 __FUNCTION__))
      declarations []

  (** {1 Disambiguation} *)

  let rec disambiguate_pragma state = function
    | Synprs.Signature.Pragma.Name
        { location; constant; meta_variable_base; computation_variable_base }
      ->
        Synext.Signature.Pragma.Name
          { location
          ; constant
          ; meta_variable_base
          ; computation_variable_base
          }
    | Synprs.Signature.Pragma.Default_associativity
        { location; associativity } ->
        set_default_associativity state associativity;
        Synext.Signature.Pragma.Default_associativity
          { location; associativity }
    | Synprs.Signature.Pragma.Prefix_fixity
        { location; constant; precedence } ->
        add_prefix_notation state ?precedence constant;
        Synext.Signature.Pragma.Prefix_fixity
          { location; constant; precedence }
    | Synprs.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity } ->
        add_infix_notation state ?precedence ?associativity constant;
        Synext.Signature.Pragma.Infix_fixity
          { location; constant; precedence; associativity }
    | Synprs.Signature.Pragma.Postfix_fixity
        { location; constant; precedence } ->
        add_postfix_notation state ?precedence constant;
        Synext.Signature.Pragma.Postfix_fixity
          { location; constant; precedence }
    | Synprs.Signature.Pragma.Not { location } ->
        Synext.Signature.Pragma.Not { location }
    | Synprs.Signature.Pragma.Open_module { location; module_identifier } ->
        open_module state module_identifier;
        Synext.Signature.Pragma.Open_module { location; module_identifier }
    | Synprs.Signature.Pragma.Abbreviation
        { location; module_identifier; abbreviation } ->
        add_module_abbreviation state module_identifier abbreviation;
        Synext.Signature.Pragma.Abbreviation
          { location; module_identifier; abbreviation }
    | Synprs.Signature.Pragma.Raw_query
        { location
        ; identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        } ->
        with_disambiguated_meta_context state meta_context
          (fun state meta_context' ->
            let typ' = disambiguate_clf_typ state typ in
            Synext.Signature.Pragma.Query
              { location
              ; identifier
              ; meta_context = meta_context'
              ; typ = typ'
              ; expected_solutions
              ; maximum_tries
              })

  and disambiguate_global_pragma _state = function
    | Synprs.Signature.Global_pragma.No_strengthening { location } ->
        Synext.Signature.Global_pragma.No_strengthening { location }
    | Synprs.Signature.Global_pragma.Warn_on_coverage_error { location } ->
        Synext.Signature.Global_pragma.Warn_on_coverage_error { location }
    | Synprs.Signature.Global_pragma.Initiate_coverage_checking { location }
      ->
        Synext.Signature.Global_pragma.Initiate_coverage_checking
          { location }

  and disambiguate_totality_declaration state = function
    | Synprs.Signature.Totality.Declaration.Trust { location } ->
        Synext.Signature.Totality.Declaration.Trust { location }
    | Synprs.Signature.Totality.Declaration.Numeric { location; order } ->
        let order' =
          traverse_option state disambiguate_numeric_totality_order order
        in
        Synext.Signature.Totality.Declaration.Numeric
          { location; order = order' }
    | Synprs.Signature.Totality.Declaration.Named
        { location; order; program; argument_labels } ->
        let order' =
          traverse_option state disambiguate_named_totality_order order
        in
        Synext.Signature.Totality.Declaration.Named
          { location; order = order'; program; argument_labels }

  and disambiguate_numeric_totality_order state = function
    | Synprs.Signature.Totality.Order.Argument { location; argument } ->
        Synext.Signature.Totality.Order.Argument { location; argument }
    | Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments } ->
        let arguments' =
          traverse_list1 state disambiguate_numeric_totality_order arguments
        in
        Synext.Signature.Totality.Order.Lexical_ordering
          { location; arguments = arguments' }
    | Synprs.Signature.Totality.Order.Simultaneous_ordering
        { location; arguments } ->
        let arguments' =
          traverse_list1 state disambiguate_numeric_totality_order arguments
        in
        Synext.Signature.Totality.Order.Simultaneous_ordering
          { location; arguments = arguments' }

  and disambiguate_named_totality_order state = function
    | Synprs.Signature.Totality.Order.Argument { location; argument } ->
        Synext.Signature.Totality.Order.Argument { location; argument }
    | Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments } ->
        let arguments' =
          traverse_list1 state disambiguate_named_totality_order arguments
        in
        Synext.Signature.Totality.Order.Lexical_ordering
          { location; arguments = arguments' }
    | Synprs.Signature.Totality.Order.Simultaneous_ordering
        { location; arguments } ->
        let arguments' =
          traverse_list1 state disambiguate_named_totality_order arguments
        in
        Synext.Signature.Totality.Order.Simultaneous_ordering
          { location; arguments = arguments' }

  and disambiguate_mutually_recursive_declarations state declarations =
    traverse_list1_void state add_declaration declarations;
    let declarations =
      traverse_list1 state disambiguate_declaration declarations
    in
    declarations

  and disambiguate_declaration state = function
    | Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant
        { location; identifier; typ_or_const }
    (* Old style LF type or term constant declaration *) -> (
        try
          with_bindings_checkpoint state (fun state ->
              let kind' = disambiguate_lf_kind state typ_or_const in
              Synext.Signature.Declaration.Typ
                { location; identifier; kind = kind' })
        with
        | typ_exn -> (
            try
              with_bindings_checkpoint state (fun state ->
                  let typ' = disambiguate_lf_typ state typ_or_const in
                  Synext.Signature.Declaration.Const
                    { location; identifier; typ = typ' })
            with
            | const_exn ->
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
        let kind' = disambiguate_lf_kind state kind in
        Synext.Signature.Declaration.Typ
          { location; identifier; kind = kind' }
    | Synprs.Signature.Declaration.Raw_lf_term_constant
        { location; identifier; typ } ->
        let typ' = disambiguate_lf_typ state typ in
        Synext.Signature.Declaration.Const
          { location; identifier; typ = typ' }
    | Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant
        { location; identifier; kind } ->
        let kind' = disambiguate_comp_kind state kind in
        Synext.Signature.Declaration.CompTyp
          { location
          ; identifier
          ; kind = kind'
          ; datatype_flavour = `Inductive
          }
    | Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant
        { location; identifier; kind } ->
        let kind' = disambiguate_comp_kind state kind in
        Synext.Signature.Declaration.CompTyp
          { location
          ; identifier
          ; kind = kind'
          ; datatype_flavour = `Stratified
          }
    | Synprs.Signature.Declaration.Raw_comp_cotyp_constant
        { location; identifier; kind } ->
        let kind' = disambiguate_comp_kind state kind in
        Synext.Signature.Declaration.CompCotyp
          { location; identifier; kind = kind' }
    | Synprs.Signature.Declaration.Raw_comp_expression_constructor
        { location; identifier; typ } ->
        let typ' = disambiguate_comp_typ state typ in
        Synext.Signature.Declaration.CompConst
          { location; identifier; typ = typ' }
    | Synprs.Signature.Declaration.Raw_comp_expression_destructor
        { location; identifier; observation_type; return_type } ->
        let observation_type' =
          disambiguate_comp_typ state observation_type
        in
        let return_type' = disambiguate_comp_typ state return_type in
        Synext.Signature.Declaration.CompDest
          { location
          ; identifier
          ; observation_type = observation_type'
          ; return_type = return_type'
          }
    | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { location; identifier; kind; typ } ->
        let kind' = disambiguate_comp_kind state kind in
        let rec with_unrolled_kind state kind f =
          match kind with
          | Synext.Comp.Kind.Pi
              { parameter_identifier; parameter_type; body; _ } ->
              with_bound_meta_level_variable_opt state parameter_identifier
                parameter_type (fun state -> with_unrolled_kind state body f)
          | Synext.Comp.Kind.Arrow { range; _ } ->
              with_unrolled_kind state range f
          | Synext.Comp.Kind.Ctype _ -> f state
        in
        let typ' =
          with_unrolled_kind state kind' (fun state ->
              disambiguate_comp_typ state typ)
        in
        Synext.Signature.Declaration.CompTypAbbrev
          { location; identifier; kind = kind'; typ = typ' }
    | Synprs.Signature.Declaration.Raw_schema
        { location; identifier; schema } ->
        let schema' = disambiguate_schema state schema in
        Synext.Signature.Declaration.Schema
          { location; identifier; schema = schema' }
    | Synprs.Signature.Declaration.Raw_theorem
        { location; identifier; typ; order; body } ->
        let typ' = disambiguate_comp_typ state typ in
        let order' =
          traverse_option state disambiguate_totality_declaration order
        in
        let body' = disambiguate_comp_expression state body in
        Synext.Signature.Declaration.Theorem
          { location; identifier; typ = typ'; order = order'; body = body' }
    | Synprs.Signature.Declaration.Raw_proof
        { location; identifier; typ; order; body } ->
        let typ' = disambiguate_comp_typ state typ in
        let order' =
          traverse_option state disambiguate_totality_declaration order
        in
        let body' =
          with_scope state (fun state ->
              disambiguate_harpoon_proof state body)
        in
        Synext.Signature.Declaration.Proof
          { location; identifier; typ = typ'; order = order'; body = body' }
    | Synprs.Signature.Declaration.Raw_val
        { location; identifier; typ; expression } ->
        let typ' = traverse_option state disambiguate_comp_typ typ in
        let expression' = disambiguate_comp_expression state expression in
        Synext.Signature.Declaration.Val
          { location; identifier; typ = typ'; expression = expression' }
    | Synprs.Signature.Declaration.Raw_recursive_declarations _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] can't disambiguate mutually recursive declarations \
              without adding its entries to the state"
             __FUNCTION__)
    | Synprs.Signature.Declaration.Raw_module _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] can't disambiguate a module without adding its entries \
              to the state"
             __FUNCTION__)

  and disambiguate_and_add_declaration state = function
    | ( Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant _
      | Synprs.Signature.Declaration.Raw_lf_typ_constant _
      | Synprs.Signature.Declaration.Raw_lf_term_constant _
      | Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant _
      | Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant _
      | Synprs.Signature.Declaration.Raw_comp_cotyp_constant _
      | Synprs.Signature.Declaration.Raw_comp_expression_constructor _
      | Synprs.Signature.Declaration.Raw_comp_expression_destructor _
      | Synprs.Signature.Declaration.Raw_comp_typ_abbreviation _
      | Synprs.Signature.Declaration.Raw_schema _
      | Synprs.Signature.Declaration.Raw_theorem _
      | Synprs.Signature.Declaration.Raw_proof _
      | Synprs.Signature.Declaration.Raw_val _ ) as declaration ->
        let declaration' = disambiguate_declaration state declaration in
        add_declaration' state declaration';
        declaration'
    | Synprs.Signature.Declaration.Raw_recursive_declarations
        { location; declarations } -> (
        match
          Identifier.find_duplicates
            (declaration_identifiers (List1.to_list declarations))
        with
        | Option.Some duplicates ->
            Error.raise_at
              (List1.concat_map
                 (fun (_, duplicates) ->
                   List2.to_list1 (List2.map Identifier.location duplicates))
                 duplicates)
              (Duplicate_identifiers_recursive_declaration
                 (List1.map Pair.fst duplicates))
        | Option.None ->
            let declarations' =
              disambiguate_mutually_recursive_declarations state declarations
            in
            Synext.Signature.Declaration.Recursive_declarations
              { location; declarations = declarations' })
    | Synprs.Signature.Declaration.Raw_module
        { location; identifier; entries } ->
        add_module state ~location identifier (fun state ->
            let entries' = traverse_list state disambiguate_entry entries in
            Synext.Signature.Declaration.Module
              { location; identifier; entries = entries' })

  and disambiguate_entry state = function
    | Synprs.Signature.Entry.Raw_pragma { pragma; location } ->
        let pragma' = disambiguate_pragma state pragma in
        Synext.Signature.Entry.Pragma { pragma = pragma'; location }
    | Synprs.Signature.Entry.Raw_declaration { declaration; location } ->
        let declaration' =
          disambiguate_and_add_declaration state declaration
        in
        Synext.Signature.Entry.Declaration
          { declaration = declaration'; location }
    | Synprs.Signature.Entry.Raw_comment { location; content } ->
        Synext.Signature.Entry.Comment { location; content }

  and disambiguate_signature_file state
      { Synprs.Signature.location; global_pragmas; entries } =
    let global_pragmas' =
      traverse_list state disambiguate_global_pragma global_pragmas
    in
    let entries' = traverse_list state disambiguate_entry entries in
    { Synext.Signature.location
    ; global_pragmas = global_pragmas'
    ; entries = entries'
    }

  and disambiguate_signature state signature_files =
    traverse_list1 state disambiguate_signature_file signature_files
end
