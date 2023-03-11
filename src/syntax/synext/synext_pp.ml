open Support
open Synext_definition
open Common

exception Unsupported_implicit_lf_pi_kind

exception Unsupported_implicit_lf_pi_typ

exception Unsupported_implicit_clf_pi_typ

exception Unsupported_non_recursive_declaration

exception Unsupported_recursive_declaration

module type PRINTING_STATE = sig
  include State.STATE

  include Format_state.S with type state := state

  val add_binding : Identifier.t -> Unit.t t

  val with_module_declarations : Identifier.t -> 'a t -> 'a t

  val add_module_declaration : Identifier.t -> Unit.t t

  val open_module : Qualified_identifier.t -> Unit.t t

  val add_abbreviation : Qualified_identifier.t -> Identifier.t -> Unit.t t

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val set_default_precedence : Int.t -> Unit.t t

  val get_default_precedence : Int.t t

  val lookup_operator_precedence : Qualified_identifier.t -> Int.t Option.t t

  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t

  val make_prefix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  val make_infix :
       ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val make_postfix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t
end

module Printing_state : sig
  include PRINTING_STATE

  val initial : Format.formatter -> state

  val set_formatter : Format.formatter -> Unit.t t
end = struct
  type entry = { operator : Operator.t Option.t }

  type state =
    { bindings : entry Binding_tree.t
    ; formatter : Format.formatter
    ; default_precedence : Int.t
    ; default_associativity : Associativity.t
    ; declarations : entry Binding_tree.t
    }

  module S = State.Make (struct
    type t = state
  end)

  include (S : State.STATE with type state := state)

  let with_formatter f =
    let* { formatter; _ } = get in
    f formatter

  include (
    Format_state.Make (struct
      include S

      let with_formatter = with_formatter
    end) :
      Format_state.S with type state := state)

  let initial formatter =
    { bindings = Binding_tree.empty
    ; formatter
    ; default_precedence
    ; default_associativity
    ; declarations = Binding_tree.empty
    }

  let set_formatter formatter =
    modify (fun state -> { state with formatter })

  let get_bindings =
    let* state = get in
    return state.bindings

  let set_bindings bindings = modify (fun state -> { state with bindings })

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let add_module_declaration identifier =
    let* bindings = get_bindings in
    let entry, subtree = Binding_tree.lookup_toplevel identifier bindings in
    modify (fun state ->
        let declarations' =
          Binding_tree.add_toplevel identifier entry ~subtree
            state.declarations
        in
        { state with declarations = declarations' })

  let add_binding identifier =
    modify_bindings
      (Binding_tree.add_toplevel identifier { operator = Option.none })

  let lookup identifier =
    let* bindings = get_bindings in
    return (Binding_tree.lookup identifier bindings)

  let add_synonym qualified_identifier synonym =
    let* entry, subtree = lookup qualified_identifier in
    modify_bindings (Binding_tree.add_toplevel synonym entry ~subtree)

  let add_abbreviation = add_synonym

  let open_namespace qualified_identifier =
    modify_bindings (Binding_tree.open_namespace qualified_identifier)

  let open_module = open_namespace

  let with_module_declarations module_identifier declarations =
    let* state = get in
    let* () = put { state with declarations = Binding_tree.empty } in
    let* declarations' = declarations in
    let* state' = get in
    let* () = put state in
    let* () =
      modify_bindings
        (Binding_tree.add_toplevel module_identifier
           ~subtree:state'.declarations
           { operator = Option.none })
    in
    return declarations'

  let set_default_associativity default_associativity =
    modify (fun state -> { state with default_associativity })

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let[@warning "-32"] set_default_precedence default_precedence =
    modify (fun state -> { state with default_precedence })

  let get_default_associativity_opt = function
    | Option.None -> get_default_associativity
    | Option.Some associativity -> return associativity

  let get_default_precedence =
    let* state = get in
    return state.default_precedence

  let set_default_precedence default_precedence =
    modify (fun state -> { state with default_precedence })

  let get_default_precedence_opt = function
    | Option.None -> get_default_precedence
    | Option.Some precedence -> return precedence

  let lookup_operator constant =
    let* { operator; _ }, _subtree = lookup constant in
    return operator

  let lookup_operator_precedence constant =
    lookup_operator constant $> Option.map Operator.precedence

  let[@warning "-23"] make_prefix ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_bindings (fun bindings ->
        Binding_tree.replace constant
          (fun entry subtree ->
            let entry' =
              { entry with
                operator = Option.some (Operator.make_prefix ~precedence)
              }
            in
            (entry', subtree))
          bindings)

  let[@warning "-23"] make_infix ?precedence ?associativity constant =
    let* precedence = get_default_precedence_opt precedence in
    let* associativity = get_default_associativity_opt associativity in
    modify_bindings (fun bindings ->
        Binding_tree.replace constant
          (fun entry subtree ->
            let entry' =
              { entry with
                operator =
                  Option.some
                    (Operator.make_infix ~precedence ~associativity)
              }
            in
            (entry', subtree))
          bindings)

  let[@warning "-23"] make_postfix ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_bindings (fun bindings ->
        Binding_tree.replace constant
          (fun entry subtree ->
            let entry' =
              { entry with
                operator = Option.some (Operator.make_postfix ~precedence)
              }
            in
            (entry', subtree))
          bindings)
end

module type BELUGA_PRINTER = sig
  include State.STATE

  val pp_signature_file : signature_file -> Unit.t t
end

module Make_pretty_printer (Printing_state : PRINTING_STATE) :
  BELUGA_PRINTER with type state = Printing_state.state = struct
  include Printing_state

  let indent = 2

  let pp_double_cut = pp_cut ++ pp_cut

  let[@inline] pp_in_parens p = pp_char '(' ++ p ++ pp_char ')'

  let[@inline] pp_in_bracks p = pp_char '[' ++ p ++ pp_char ']'

  let[@inline] pp_in_braces p = pp_char '{' ++ p ++ pp_char '}'

  let[@inline] pp_in_angles p = pp_char '<' ++ p ++ pp_char '>'

  let[@inline] pp_in_hash_parens p = pp_string "#(" ++ p ++ pp_char ')'

  let[@inline] pp_in_dollar_parens p = pp_string "$(" ++ p ++ pp_char ')'

  let[@inline] [@warning "-32"] pp_in_hash_bracks p =
    pp_string "#[" ++ p ++ pp_char ']'

  let[@inline] pp_in_dollar_bracks p = pp_string "$[" ++ p ++ pp_char ']'

  let pp_right_arrow = pp_utf_8 "→"

  let pp_left_arrow = pp_utf_8 "←"

  let pp_thick_right_arrow = pp_utf_8 "⇒"

  let pp_turnstile = pp_utf_8 "⊢"

  let pp_hash = pp_char '#'

  let[@warning "-32"] pp_dollar = pp_char '$'

  let pp_hash_underscore = pp_string "#_"

  let pp_dollar_underscore = pp_string "$_"

  let pp_turnstile_hash = pp_turnstile ++ pp_hash

  let pp_dots = pp_utf_8 "…"

  let pp_underscore = pp_char '_'

  let pp_semicolon = pp_char ';'

  let pp_colon = pp_char ':'

  let pp_comma = pp_char ','

  let pp_dot = pp_char '.'

  let pp_star = pp_char '*'

  let pp_lambda = pp_char '\\'

  let pp_question_mark = pp_char '?'

  let pp_equal = pp_char '='

  let pp_pipe = pp_char '|'

  let pp_slash = pp_char '/'

  let pp_plus = pp_char '+'

  let pp_double_colon = pp_string "::"

  let pp_semicolon_space = pp_semicolon ++ pp_space

  let pp_comma_space = pp_comma ++ pp_space

  let pp_identifier identifier = pp_utf_8 (Identifier.name identifier)

  let pp_qualified_identifier identifier =
    let name = Qualified_identifier.name identifier in
    let namespaces = Qualified_identifier.namespaces identifier in
    match namespaces with
    | [] -> pp_identifier name
    | _ ->
        pp_hovbox ~indent
          (traverse_list_void
             (fun namespace -> pp_identifier namespace ++ pp_cut ++ pp_dot)
             namespaces
          ++ pp_identifier name)

  let pp_keyword x = pp_string x

  let pp_pragma _base x = x

  let pp_variable identifier = pp_identifier identifier

  let pp_lf_variable = pp_variable

  let pp_meta_variable = pp_variable

  let pp_parameter_variable = pp_variable

  let pp_substitution_variable = pp_variable

  let pp_context_variable = pp_variable

  let pp_computation_variable = pp_variable

  let pp_constant identifier = pp_identifier identifier

  let pp_constant_invoke identifier = pp_qualified_identifier identifier

  let pp_lf_type_constant = pp_constant

  let pp_lf_type_constant_invoke = pp_constant_invoke

  let pp_lf_term_constant = pp_constant

  let pp_lf_term_constant_invoke = pp_constant_invoke

  let pp_schema_constant = pp_constant

  let pp_schema_constant_invoke = pp_constant_invoke

  let pp_computation_inductive_constant = pp_constant

  let pp_computation_inductive_constant_invoke = pp_constant_invoke

  let pp_computation_stratified_constant = pp_constant

  let pp_computation_stratified_constant_invoke = pp_constant_invoke

  let pp_computation_coinductive_constant = pp_constant

  let pp_computation_coinductive_constant_invoke = pp_constant_invoke

  let pp_computation_abbreviation_constant = pp_constant

  let pp_computation_abbreviation_constant_invoke = pp_constant_invoke

  let pp_computation_constructor = pp_constant

  let pp_computation_constructor_invoke = pp_constant_invoke

  let pp_computation_destructor = pp_constant

  let pp_computation_destructor_invoke = pp_constant_invoke

  let pp_computation_program = pp_constant

  let pp_computation_program_invoke = pp_constant_invoke

  let pp_module_constant = pp_constant

  let[@warning "-32"] pp_module_constant_invoke = pp_constant_invoke

  let pp_and_keyword = pp_keyword "and"

  let pp_block_keyword = pp_keyword "block"

  let pp_case_keyword = pp_keyword "case"

  let[@warning "-32"] pp_if_keyword = pp_keyword "if"

  let[@warning "-32"] pp_then_keyword = pp_keyword "then"

  let[@warning "-32"] pp_else_keyword = pp_keyword "else"

  let pp_impossible_keyword = pp_keyword "impossible"

  let pp_let_keyword = pp_keyword "let"

  let pp_in_keyword = pp_keyword "in"

  let pp_of_keyword = pp_keyword "of"

  let pp_rec_keyword = pp_keyword "rec"

  let pp_schema_keyword = pp_keyword "schema"

  let pp_some_keyword = pp_keyword "some"

  let pp_fn_keyword = pp_keyword "fn"

  let pp_mlam_keyword = pp_keyword "mlam"

  let pp_module_keyword = pp_keyword "module"

  let pp_struct_keyword = pp_keyword "struct"

  let pp_end_keyword = pp_keyword "end"

  let pp_total_keyword = pp_keyword "total"

  let pp_trust_keyword = pp_keyword "trust"

  let pp_type_keyword = pp_keyword "type"

  let pp_ctype_keyword = pp_keyword "ctype"

  let[@warning "-32"] pp_prop_keyword = pp_keyword "prop"

  let pp_inductive_keyword = pp_keyword "inductive"

  let pp_coinductive_keyword = pp_keyword "coinductive"

  let pp_stratified_keyword = pp_keyword "stratified"

  let pp_lf_keyword = pp_keyword "LF"

  let pp_fun_keyword = pp_keyword "fun"

  let pp_typedef_keyword = pp_keyword "typedef"

  let pp_proof_keyword = pp_keyword "proof"

  let pp_as_keyword = pp_keyword "as"

  let pp_by_keyword = pp_keyword "by"

  let pp_suffices_keyword = pp_keyword "suffices"

  let pp_toshow_keyword = pp_keyword "toshow"

  let pp_unbox_keyword = pp_keyword "unbox"

  let pp_strengthen_keyword = pp_keyword "strengthen"

  let pp_head_keyword = pp_keyword "head"

  let pp_variable_keyword = pp_keyword "variable"

  let pp_empty_keyword = pp_keyword "empty"

  let pp_context_keyword = pp_keyword "context"

  let pp_extended_keyword = pp_keyword "extended"

  let pp_intros_keyword = pp_keyword "intros"

  let pp_solve_keyword = pp_keyword "solve"

  let pp_split_keyword = pp_keyword "split"

  open Synext_precedence.Make_precedences (Printing_state)

  (** {1 Pretty-Printing LF Syntax} *)

  let guard_lf_typ_operator = function
    | LF.Typ.Constant { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_lf_term_operator = function
    | LF.Term.Constant { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_lf_term_operator_application = function
    | LF.Term.Application
        { applicand = LF.Term.Constant { identifier; _ }; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator_application operator)
        | Option.None -> return `Operand)
    | term -> guard_lf_term_operator term

  let rec pp_lf_kind kind =
    let open Parenthesizer.Make (Printing_state) (Lf_precedence.Ord) in
    let* parent_precedence = precedence_of_lf_kind kind in
    match kind with
    | LF.Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative *)
        let pp_domain =
          parenthesize_left_argument_right_associative_operator
            precedence_of_lf_typ ~parent_precedence pp_lf_typ domain
        in
        let pp_range =
          parenthesize_right_argument_right_associative_operator
            precedence_of_lf_kind ~parent_precedence pp_lf_kind range
        in
        pp_hovbox ~indent
          (pp_domain ++ pp_non_breaking_space ++ pp_right_arrow ++ pp_space
         ++ pp_range)
    | LF.Kind.Typ _ -> pp_type_keyword
    | LF.Kind.Pi
        { parameter_identifier; parameter_type; body; plicity; location } ->
        let pp_parameter_identifier =
          pp_option ~none:pp_underscore pp_identifier parameter_identifier
        in
        let pp_parameter_type =
          pp_option
            (fun parameter_type ->
              pp_non_breaking_space ++ pp_colon ++ pp_space
              ++ pp_lf_typ parameter_type)
            parameter_type
        in
        let pp_declaration = pp_parameter_identifier ++ pp_parameter_type in
        let pp_binding =
          match plicity with
          | Plicity.Explicit -> pp_in_braces pp_declaration
          | Plicity.Implicit ->
              Error.raise_at1 location Unsupported_implicit_lf_pi_kind
        in
        pp_hovbox ~indent (pp_binding ++ pp_space ++ pp_lf_kind body)

  and pp_lf_typ typ =
    let open Parenthesizer.Make (Printing_state) (Lf_precedence.Ord) in
    let* parent_precedence = precedence_of_lf_typ typ in
    match typ with
    | LF.Typ.Constant { identifier; _ } ->
        pp_lf_type_constant_invoke identifier
    | LF.Typ.Application { applicand; arguments; _ } ->
        pp_application ~indent ~guard_operator:guard_lf_typ_operator
          ~guard_operator_application:guard_lf_term_operator_application
          ~precedence_of_applicand:precedence_of_lf_typ
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:pp_lf_typ ~pp_argument:pp_lf_term ~parent_precedence
          applicand arguments
    | LF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        let pp_domain =
          match domain with
          | LF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens (pp_lf_typ domain)
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ domain
        in
        let pp_range =
          match range with
          | LF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens (pp_lf_typ range)
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ range
        in
        pp_hovbox ~indent
          (pp_domain ++ pp_non_breaking_space ++ pp_right_arrow ++ pp_space
         ++ pp_range)
    | LF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        let pp_range =
          match range with
          | LF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens (pp_lf_typ range)
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ range
        in
        let pp_domain =
          match domain with
          | LF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens (pp_lf_typ domain)
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ domain
        in
        pp_hovbox ~indent
          (pp_range ++ pp_space ++ pp_left_arrow ++ pp_non_breaking_space
         ++ pp_domain)
    | LF.Typ.Pi
        { parameter_identifier; parameter_type; body; plicity; location } ->
        let pp_parameter_identifier =
          pp_option ~none:pp_underscore pp_identifier parameter_identifier
        in
        let pp_parameter_type =
          pp_option
            (fun parameter_type ->
              pp_non_breaking_space ++ pp_colon ++ pp_space
              ++ pp_lf_typ parameter_type)
            parameter_type
        in
        let pp_declaration = pp_parameter_identifier ++ pp_parameter_type in
        let pp_binding =
          match plicity with
          | Plicity.Explicit -> pp_in_braces pp_declaration
          | Plicity.Implicit ->
              Error.raise_at1 location Unsupported_implicit_lf_pi_typ
        in
        pp_hovbox ~indent (pp_binding ++ pp_space ++ pp_lf_typ body)

  and pp_lf_term term =
    let open Parenthesizer.Make (Printing_state) (Lf_precedence.Ord) in
    let* parent_precedence = precedence_of_lf_term term in
    match term with
    | LF.Term.Variable { identifier; _ } -> pp_lf_variable identifier
    | LF.Term.Constant { identifier; _ } ->
        pp_lf_term_constant_invoke identifier
    | LF.Term.Application { applicand; arguments; _ } ->
        pp_application ~indent ~guard_operator:guard_lf_term_operator
          ~guard_operator_application:guard_lf_term_operator_application
          ~precedence_of_applicand:precedence_of_lf_term
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:pp_lf_term ~pp_argument:pp_lf_term ~parent_precedence
          applicand arguments
    | LF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      ->
        (* Lambdas are weak prefix operators, so the body of the lambda never
           requires parentheses *)
        let pp_parameter_identifier =
          pp_option ~none:pp_underscore pp_identifier parameter_identifier
        in
        let pp_declaration =
          match parameter_type with
          | Option.Some parameter_type ->
              pp_in_parens
                (pp_parameter_identifier ++ pp_non_breaking_space ++ pp_colon
               ++ pp_space ++ pp_lf_typ parameter_type)
          | Option.None -> pp_parameter_identifier
        in
        pp_hovbox ~indent
          (pp_lambda ++ pp_declaration ++ pp_dot ++ pp_space
         ++ pp_lf_term body)
    | LF.Term.Wildcard _ -> pp_underscore
    | LF.Term.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_lf_term ~parent_precedence pp_lf_term term
        in
        pp_hovbox ~indent
          (pp_term ++ pp_space ++ pp_colon ++ pp_space ++ pp_lf_typ typ)

  (** {1 Pretty-Printing Contextual LF Syntax} *)

  let guard_clf_typ_operator = function
    | CLF.Typ.Constant { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_clf_term_operator = function
    | CLF.Term.Constant { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_clf_term_operator_application = function
    | CLF.Term.Application
        { applicand = CLF.Term.Constant { identifier; _ }; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator_application operator)
        | Option.None -> return `Operand)
    | term -> guard_clf_term_operator term

  let guard_clf_term_pattern_operator = function
    | CLF.Term.Pattern.Constant { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_clf_term_pattern_operator_application = function
    | CLF.Term.Pattern.Application
        { applicand = CLF.Term.Pattern.Constant { identifier; _ }; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator_application operator)
        | Option.None -> return `Operand)
    | term -> guard_clf_term_pattern_operator term

  let rec pp_clf_typ typ =
    let open Parenthesizer.Make (Printing_state) (Clf_precedence.Ord) in
    let* parent_precedence = precedence_of_clf_typ typ in
    match typ with
    | CLF.Typ.Constant { identifier; _ } ->
        pp_lf_type_constant_invoke identifier
    | CLF.Typ.Application { applicand; arguments; _ } ->
        pp_application ~indent ~guard_operator:guard_clf_typ_operator
          ~guard_operator_application:guard_clf_term_operator_application
          ~precedence_of_applicand:precedence_of_clf_typ
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:pp_clf_typ ~pp_argument:pp_clf_term
          ~parent_precedence applicand arguments
    | CLF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        let pp_domain =
          match domain with
          | CLF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens (pp_clf_typ domain)
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ domain
        in
        let pp_range =
          match range with
          | CLF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens (pp_clf_typ range)
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ range
        in
        pp_hovbox ~indent
          (pp_domain ++ pp_non_breaking_space ++ pp_right_arrow ++ pp_space
         ++ pp_range)
    | CLF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        let pp_range =
          match range with
          | CLF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens (pp_clf_typ range)
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ range
        in
        let pp_domain =
          match domain with
          | CLF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens (pp_clf_typ domain)
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ domain
        in
        pp_hovbox ~indent
          (pp_range ++ pp_space ++ pp_left_arrow ++ pp_non_breaking_space
         ++ pp_domain)
    | CLF.Typ.Pi
        { parameter_identifier; parameter_type; body; plicity; location } ->
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier =
          pp_option ~none:pp_underscore pp_identifier parameter_identifier
        in
        let pp_parameter_type =
          pp_non_breaking_space ++ pp_colon ++ pp_space
          ++ pp_clf_typ parameter_type
        in
        let pp_declaration = pp_parameter_identifier ++ pp_parameter_type in
        let pp_binding =
          match plicity with
          | Plicity.Explicit -> pp_in_braces pp_declaration
          | Plicity.Implicit ->
              Error.raise_at1 location Unsupported_implicit_clf_pi_typ
        in
        pp_hovbox ~indent (pp_binding ++ pp_space ++ pp_clf_typ body)
    | CLF.Typ.Block { elements = `Unnamed typ; _ } ->
        pp_hovbox ~indent
          (pp_block_keyword ++ pp_non_breaking_space
          ++ pp_in_parens (pp_clf_typ typ))
    | CLF.Typ.Block { elements = `Record nts; _ } ->
        let pp_binding (identifier, typ) =
          pp_hovbox ~indent
            (pp_identifier identifier ++ pp_non_breaking_space ++ pp_colon
           ++ pp_space ++ pp_clf_typ typ)
        in
        let pp_bindings bindings =
          pp_hvbox (pp_list1 ~sep:pp_comma_space pp_binding bindings)
        in
        pp_hovbox ~indent
          (pp_block_keyword ++ pp_non_breaking_space
          ++ pp_in_parens (pp_bindings nts))

  and pp_clf_term term =
    let open Parenthesizer.Make (Printing_state) (Clf_precedence.Ord) in
    let* parent_precedence = precedence_of_clf_term term in
    match term with
    | CLF.Term.Variable { identifier; _ } -> pp_lf_variable identifier
    | CLF.Term.Meta_variable { identifier; _ } -> pp_meta_variable identifier
    | CLF.Term.Parameter_variable { identifier; _ } ->
        pp_parameter_variable identifier
    | CLF.Term.Constant { identifier; _ } ->
        pp_lf_term_constant_invoke identifier
    | CLF.Term.Application { applicand; arguments; _ } ->
        pp_application ~indent ~guard_operator:guard_clf_term_operator
          ~guard_operator_application:guard_clf_term_operator_application
          ~precedence_of_applicand:precedence_of_clf_term
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:pp_clf_term ~pp_argument:pp_clf_term
          ~parent_precedence applicand arguments
    | CLF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      ->
        (* Lambdas are weak prefix operators, so the body of a lambda does
           not need to be parenthesized *)
        let pp_parameter_identifier =
          pp_option ~none:pp_underscore pp_identifier parameter_identifier
        in
        let pp_declaration =
          match parameter_type with
          | Option.Some parameter_type ->
              pp_in_parens
                (pp_parameter_identifier ++ pp_non_breaking_space ++ pp_colon
               ++ pp_space ++ pp_clf_typ parameter_type)
          | Option.None -> pp_parameter_identifier
        in
        pp_hovbox ~indent
          (pp_lambda ++ pp_declaration ++ pp_dot ++ pp_space
         ++ pp_clf_term body)
    | CLF.Term.Hole { variant = `Underscore; _ } -> pp_underscore
    | CLF.Term.Hole { variant = `Unlabelled; _ } -> pp_question_mark
    | CLF.Term.Hole { variant = `Labelled label; _ } ->
        pp_question_mark ++ pp_identifier label
    | CLF.Term.Substitution { term; substitution; _ } ->
        (* Substitutions are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_hovbox ~indent
          (pp_term ++ pp_in_bracks (pp_clf_substitution substitution))
    | CLF.Term.Tuple { terms; _ } ->
        pp_hovbox ~indent
          (pp_in_angles (pp_list1 ~sep:pp_semicolon_space pp_clf_term terms))
    | CLF.Term.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_hovbox ~indent (pp_term ++ pp_dot ++ pp_int i)
    | CLF.Term.Projection { term; projection = `By_identifier i; _ } ->
        (* Projections are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_term ++ pp_dot ++ pp_identifier i
    | CLF.Term.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_hovbox ~indent
          (pp_term ++ pp_non_breaking_space ++ pp_colon ++ pp_space
         ++ pp_clf_typ typ)

  and pp_clf_substitution substitution =
    match substitution with
    | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms = []; _ }
      ->
        pp_nop
    | { CLF.Substitution.head = CLF.Substitution.Head.Identity _
      ; terms = []
      ; _
      } ->
        pp_dots
    | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms; _ } ->
        pp_list ~sep:pp_comma_space pp_clf_term terms
    | { CLF.Substitution.head = CLF.Substitution.Head.Identity _; terms; _ }
      ->
        pp_dots ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_clf_term terms
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable identifier
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable identifier
        ++ pp_in_bracks (pp_clf_substitution closure)
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable identifier
        ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_clf_term terms
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable identifier
        ++ pp_in_bracks (pp_clf_substitution closure)
        ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_clf_term terms

  and pp_clf_context context =
    let pp_typing (identifier, typ_opt) =
      pp_lf_variable identifier
      ++ pp_option
           (fun typ ->
             pp_non_breaking_space ++ pp_colon ++ pp_space ++ pp_clf_typ typ)
           typ_opt
    in
    match context with
    | { CLF.Context.head = CLF.Context.Head.None _; bindings = []; _ } ->
        pp_nop
    | { CLF.Context.head = CLF.Context.Head.Hole _; bindings = []; _ } ->
        pp_underscore
    | { CLF.Context.head =
          CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        pp_context_variable identifier
    | { CLF.Context.head = CLF.Context.Head.None _; bindings; _ } ->
        pp_list ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.head = CLF.Context.Head.Hole _; bindings; _ } ->
        pp_underscore ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.head =
          CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        pp_context_variable identifier
        ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_typing bindings

  let rec pp_clf_term_pattern term =
    let open Parenthesizer.Make (Printing_state) (Clf_precedence.Ord) in
    let* parent_precedence = precedence_of_clf_term_pattern term in
    match term with
    | CLF.Term.Pattern.Variable { identifier; _ } ->
        pp_lf_variable identifier
    | CLF.Term.Pattern.Meta_variable { identifier; _ } ->
        pp_meta_variable identifier
    | CLF.Term.Pattern.Parameter_variable { identifier; _ } ->
        pp_parameter_variable identifier
    | CLF.Term.Pattern.Constant { identifier; _ } ->
        pp_lf_term_constant_invoke identifier
    | CLF.Term.Pattern.Application { applicand; arguments; _ } ->
        pp_application ~indent
          ~guard_operator:guard_clf_term_pattern_operator
          ~guard_operator_application:
            guard_clf_term_pattern_operator_application
          ~precedence_of_applicand:precedence_of_clf_term_pattern
          ~precedence_of_argument:precedence_of_clf_term_pattern
          ~pp_applicand:pp_clf_term_pattern ~pp_argument:pp_clf_term_pattern
          ~parent_precedence applicand arguments
    | CLF.Term.Pattern.Abstraction
        { parameter_identifier; parameter_type; body; _ } ->
        (* Lambdas are weak prefix operators, so the body of a lambda never
           requires parentheses. *)
        let pp_parameter_identifier =
          pp_option ~none:pp_underscore pp_identifier parameter_identifier
        in
        let pp_declaration =
          pp_parameter_identifier
          ++ pp_option
               (fun parameter_type ->
                 pp_in_parens
                   (pp_non_breaking_space ++ pp_colon ++ pp_space
                  ++ pp_clf_typ parameter_type))
               parameter_type
        in
        pp_hovbox ~indent
          (pp_lambda ++ pp_declaration ++ pp_dot ++ pp_space
         ++ pp_clf_term_pattern body)
    | CLF.Term.Pattern.Wildcard _ -> pp_underscore
    | CLF.Term.Pattern.Substitution { term; substitution; _ } ->
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_hovbox ~indent
          (pp_term ++ pp_in_bracks (pp_clf_substitution substitution))
    | CLF.Term.Pattern.Tuple { terms; _ } ->
        pp_hovbox ~indent
          (pp_in_angles
             (pp_list1 ~sep:pp_semicolon_space pp_clf_term_pattern terms))
    | CLF.Term.Pattern.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_term ++ pp_dot ++ pp_int i
    | CLF.Term.Pattern.Projection { term; projection = `By_identifier i; _ }
      ->
        (* Projections are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_term ++ pp_dot ++ pp_identifier i
    | CLF.Term.Pattern.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_term =
          parenthesize_left_argument_left_associative_operator
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_hovbox ~indent
          (pp_term ++ pp_non_breaking_space ++ pp_colon ++ pp_space
         ++ pp_clf_typ typ)

  and pp_clf_substitution_pattern substitution_pattern =
    match substitution_pattern with
    | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
      ; terms = []
      ; _
      } ->
        pp_nop
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Identity _
      ; terms = []
      ; _
      } ->
        pp_dots
    | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
      ; terms
      ; _
      } ->
        pp_list ~sep:pp_comma_space pp_clf_term_pattern terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Identity _
      ; terms
      ; _
      } ->
        pp_dots ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_clf_term_pattern terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable identifier
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable identifier
        ++ pp_in_bracks (pp_clf_substitution closure)
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable identifier
        ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_clf_term_pattern terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable identifier
        ++ pp_in_bracks (pp_clf_substitution closure)
        ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_clf_term_pattern terms

  and pp_clf_context_pattern context_pattern =
    let pp_typing (identifier, typ) =
      pp_lf_variable identifier ++ pp_non_breaking_space ++ pp_colon
      ++ pp_space ++ pp_clf_typ typ
    in
    match context_pattern with
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
      ; bindings = []
      ; _
      } ->
        pp_nop
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
      ; bindings = []
      ; _
      } ->
        pp_underscore
    | { CLF.Context.Pattern.head =
          CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        pp_context_variable identifier
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
      ; bindings
      ; _
      } ->
        pp_list ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
      ; bindings
      ; _
      } ->
        pp_underscore ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.Pattern.head =
          CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        pp_context_variable identifier
        ++ pp_comma_space
        ++ pp_list ~sep:pp_comma_space pp_typing bindings

  (** {1 Pretty-Printing Meta-Level Syntax} *)

  let rec pp_meta_typ typ =
    match typ with
    | Meta.Typ.Context_schema { schema; _ } ->
        pp_schema_constant_invoke schema
    | Meta.Typ.Contextual_typ { context; typ; _ } ->
        pp_hovbox ~indent
          (pp_in_parens
             (pp_clf_context context ++ pp_non_breaking_space ++ pp_turnstile
            ++ pp_space ++ pp_clf_typ typ))
    | Meta.Typ.Parameter_typ { context; typ; _ } ->
        pp_hovbox ~indent
          (pp_in_hash_parens
             (pp_clf_context context ++ pp_non_breaking_space ++ pp_turnstile
            ++ pp_space ++ pp_clf_typ typ))
    | Meta.Typ.Plain_substitution_typ { domain; range; _ } ->
        pp_hovbox ~indent
          (pp_in_dollar_parens
             (pp_clf_context domain ++ pp_non_breaking_space ++ pp_turnstile
            ++ pp_space ++ pp_clf_context range))
    | Meta.Typ.Renaming_substitution_typ { domain; range; _ } ->
        pp_hovbox ~indent
          (pp_in_dollar_parens
             (pp_clf_context domain ++ pp_non_breaking_space
            ++ pp_turnstile_hash ++ pp_space ++ pp_clf_context range))

  and pp_meta_object object_ =
    match object_ with
    | Meta.Object.Context { context; _ } ->
        pp_hovbox ~indent (pp_in_bracks (pp_clf_context context))
    | Meta.Object.Contextual_term { context; term; _ } ->
        pp_hovbox ~indent
          (pp_in_bracks
             (pp_clf_context context ++ pp_non_breaking_space ++ pp_turnstile
            ++ pp_space ++ pp_clf_term term))
    | Meta.Object.Plain_substitution { domain; range; _ } ->
        pp_hovbox ~indent
          (pp_in_dollar_bracks
             (pp_clf_context domain ++ pp_non_breaking_space ++ pp_turnstile
            ++ pp_space ++ pp_clf_substitution range))
    | Meta.Object.Renaming_substitution { domain; range; _ } ->
        pp_hovbox ~indent
          (pp_in_dollar_bracks
             (pp_clf_context domain ++ pp_non_breaking_space
            ++ pp_turnstile_hash ++ pp_space ++ pp_clf_substitution range))

  and pp_meta_pattern pattern =
    match pattern with
    | Meta.Pattern.Context { context; _ } ->
        pp_hovbox ~indent (pp_in_bracks (pp_clf_context_pattern context))
    | Meta.Pattern.Contextual_term { context; term; _ } ->
        pp_hovbox ~indent
          (pp_in_bracks
             (pp_clf_context_pattern context
             ++ pp_non_breaking_space ++ pp_turnstile ++ pp_space
             ++ pp_clf_term_pattern term))
    | Meta.Pattern.Plain_substitution { domain; range; _ } ->
        pp_hovbox ~indent
          (pp_in_dollar_bracks
             (pp_clf_context_pattern domain
             ++ pp_non_breaking_space ++ pp_turnstile ++ pp_space
             ++ pp_clf_substitution_pattern range))
    | Meta.Pattern.Renaming_substitution { domain; range; _ } ->
        pp_hovbox ~indent
          (pp_in_dollar_bracks
             (pp_clf_context_pattern domain
             ++ pp_non_breaking_space ++ pp_turnstile_hash ++ pp_space
             ++ pp_clf_substitution_pattern range))

  and pp_schema schema =
    let open Parenthesizer.Make (Printing_state) (Schema_precedence.Ord) in
    let* parent_precedence = precedence_of_schema schema in
    let pp_binding (identifier, typ) =
      pp_hovbox ~indent
        (pp_lf_variable identifier ++ pp_non_breaking_space ++ pp_colon
       ++ pp_space ++ pp_lf_typ typ)
    in
    let pp_bindings bindings =
      pp_hvbox (pp_list1 ~sep:pp_comma_space pp_binding bindings)
    in
    match schema with
    | Meta.Schema.Constant { identifier; _ } ->
        pp_schema_constant_invoke identifier
    | Meta.Schema.Alternation { schemas; _ } ->
        pp_list2
          ~sep:(pp_space ++ pp_plus ++ pp_non_breaking_space)
          (parenthesize_term_of_lesser_than_or_equal_precedence
             precedence_of_schema ~parent_precedence pp_schema)
          schemas
    | Meta.Schema.Element { some; block; _ } ->
        let pp_some_clause =
          pp_option
            (fun some_bindings ->
              pp_some_keyword ++ pp_non_breaking_space
              ++ pp_in_bracks (pp_bindings some_bindings)
              ++ pp_space)
            some
        in
        let pp_block_clause =
          match block with
          | `Unnamed t ->
              pp_block_keyword ++ pp_non_breaking_space ++ pp_lf_typ t
          | `Record block_bindings ->
              pp_block_keyword ++ pp_non_breaking_space
              ++ pp_in_parens (pp_bindings block_bindings)
        in
        pp_hvbox (pp_some_clause ++ pp_block_clause)

  (** {1 Pretty-Printing Computation-Level Syntax} *)

  (** [is_atomic_pattern pattern] is [true] if and only if [pattern] is an
      atomic pattern as defined in {!Parser}, meaning that it never requires
      additional enclosing parentheses during printing to avoid ambiguities. *)
  let is_atomic_pattern pattern =
    match pattern with
    | Comp.Pattern.Variable _
    | Comp.Pattern.Constructor _
    | Comp.Pattern.Meta_object _
    | Comp.Pattern.Tuple _
    | Comp.Pattern.Wildcard _ ->
        true
    | Comp.Pattern.Application _
    | Comp.Pattern.Type_annotated _ ->
        false

  let rec pp_comp_kind kind =
    match kind with
    | Comp.Kind.Ctype _ -> pp_ctype_keyword
    | Comp.Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative, but the precedence of
           meta-types is not comparable with the precedence of
           computation-level kinds *)
        pp_hovbox ~indent
          (pp_meta_typ domain ++ pp_non_breaking_space ++ pp_right_arrow
         ++ pp_space ++ pp_comp_kind range)
    | Comp.Kind.Pi { parameter_identifier; parameter_type; body; plicity; _ }
      ->
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier =
          match (parameter_identifier, parameter_type) with
          | Option.Some parameter_identifier, _ ->
              pp_meta_variable parameter_identifier
          | ( Option.None
            , (Meta.Typ.Context_schema _ | Meta.Typ.Contextual_typ _) ) ->
              pp_underscore
          | Option.None, Meta.Typ.Parameter_typ _ -> pp_hash_underscore
          | ( Option.None
            , ( Meta.Typ.Plain_substitution_typ _
              | Meta.Typ.Renaming_substitution_typ _ ) ) ->
              pp_dollar_underscore
        in
        let pp_binding =
          pp_parameter_identifier ++ pp_non_breaking_space ++ pp_colon
          ++ pp_space
          ++ pp_meta_typ parameter_type
        in
        let pp_declaration =
          match plicity with
          | Plicity.Implicit -> pp_in_parens pp_binding
          | Plicity.Explicit -> pp_in_braces pp_binding
        in
        pp_hovbox ~indent (pp_declaration ++ pp_space ++ pp_comp_kind body)

  and pp_comp_typ typ =
    let open Parenthesizer.Make (Printing_state) (Comp_sort_precedence.Ord) in
    let* parent_precedence = precedence_of_comp_typ typ in
    match typ with
    | Comp.Typ.Inductive_typ_constant { identifier; _ } ->
        pp_computation_inductive_constant_invoke identifier
    | Comp.Typ.Stratified_typ_constant { identifier; _ } ->
        pp_computation_stratified_constant_invoke identifier
    | Comp.Typ.Coinductive_typ_constant { identifier; _ } ->
        pp_computation_coinductive_constant_invoke identifier
    | Comp.Typ.Abbreviation_typ_constant { identifier; _ } ->
        pp_computation_abbreviation_constant_invoke identifier
    | Comp.Typ.Pi { parameter_identifier; plicity; parameter_type; body; _ }
      ->
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier =
          match (parameter_identifier, parameter_type) with
          | Option.Some parameter_identifier, _ ->
              pp_meta_variable parameter_identifier
          | ( Option.None
            , (Meta.Typ.Context_schema _ | Meta.Typ.Contextual_typ _) ) ->
              pp_underscore
          | Option.None, Meta.Typ.Parameter_typ _ -> pp_hash_underscore
          | ( Option.None
            , ( Meta.Typ.Plain_substitution_typ _
              | Meta.Typ.Renaming_substitution_typ _ ) ) ->
              pp_dollar_underscore
        in
        let pp_binding =
          pp_parameter_identifier ++ pp_non_breaking_space ++ pp_colon
          ++ pp_space
          ++ pp_meta_typ parameter_type
        in
        let pp_declaration =
          match plicity with
          | Plicity.Implicit -> pp_in_parens pp_binding
          | Plicity.Explicit -> pp_in_braces pp_binding
        in
        pp_hovbox ~indent (pp_declaration ++ pp_space ++ pp_comp_typ body)
    | Comp.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows *)
        let pp_domain =
          match domain with
          | Comp.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens (pp_comp_typ domain)
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_comp_typ domain
        in
        let pp_range =
          match range with
          | Comp.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens (pp_comp_typ range)
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_comp_typ range
        in
        pp_hovbox ~indent
          (pp_domain ++ pp_non_breaking_space ++ pp_right_arrow ++ pp_space
         ++ pp_range)
    | Comp.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows *)
        let pp_range =
          match range with
          | Comp.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens (pp_comp_typ range)
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_comp_typ range
        in
        let pp_domain =
          match domain with
          | Comp.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens (pp_comp_typ domain)
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_comp_typ domain
        in
        pp_hovbox ~indent
          (pp_range ++ pp_space ++ pp_left_arrow ++ pp_non_breaking_space
         ++ pp_domain)
    | Comp.Typ.Cross { types; _ } ->
        pp_list2
          ~sep:(pp_space ++ pp_star ++ pp_non_breaking_space)
          (parenthesize_term_of_lesser_than_or_equal_precedence
             precedence_of_comp_typ ~parent_precedence pp_comp_typ)
          types
    | Comp.Typ.Box { meta_type; _ } -> pp_meta_typ meta_type
    | Comp.Typ.Application { applicand; arguments; _ } -> (
        (* Override the behaviour of printing applications since the
           arguments are meta-object, which never need parentheses. *)
        match applicand with
        | Comp.Typ.Application
            { applicand =
                ( Comp.Typ.Inductive_typ_constant { identifier; _ }
                | Comp.Typ.Stratified_typ_constant { identifier; _ }
                | Comp.Typ.Coinductive_typ_constant { identifier; _ }
                | Comp.Typ.Abbreviation_typ_constant { identifier; _ } ) as
                applicand
            ; _
            } -> (
            lookup_operator identifier >>= function
            | Option.Some operator -> (
                match Operator.fixity operator with
                | Fixity.Prefix ->
                    pp_hovbox ~indent
                      (pp_comp_typ applicand ++ pp_space
                      ++ pp_list1 ~sep:pp_space pp_meta_object arguments)
                | Fixity.Infix ->
                    assert (
                      List1.compare_length_with arguments 2
                      = 0
                        (* Infix operators must be applied with exactly two
                           arguments. *));
                    let[@warning "-8"] (List1.T
                                         (left_argument, [ right_argument ]))
                        =
                      arguments
                    in
                    pp_hovbox ~indent
                      (pp_meta_object left_argument
                      ++ pp_space ++ pp_comp_typ applicand ++ pp_space
                      ++ pp_meta_object right_argument)
                | Fixity.Postfix ->
                    assert (
                      List1.compare_length_with arguments 1
                      = 0
                        (* Postfix operators must be applied with exactly one
                           argument. *));
                    let[@warning "-8"] (List1.T (argument, [])) =
                      arguments
                    in
                    pp_hovbox ~indent
                      (pp_meta_object argument ++ pp_space
                     ++ pp_comp_typ applicand))
            | Option.None ->
                let pp_applicand =
                  parenthesize_term_of_lesser_than_or_equal_precedence
                    precedence_of_comp_typ ~parent_precedence pp_comp_typ
                    applicand
                in
                let pp_arguments =
                  pp_list1 ~sep:pp_space pp_meta_object arguments
                in
                pp_hovbox ~indent (pp_applicand ++ pp_space ++ pp_arguments))
        | _ ->
            let pp_applicand =
              parenthesize_term_of_lesser_than_or_equal_precedence
                precedence_of_comp_typ ~parent_precedence pp_comp_typ
                applicand
            in
            let pp_arguments =
              pp_list1 ~sep:pp_space pp_meta_object arguments
            in
            pp_hovbox ~indent (pp_applicand ++ pp_space ++ pp_arguments))

  and pp_pattern_meta_context context =
    let pp_binding identifier typ =
      pp_identifier identifier ++ pp_non_breaking_space ++ pp_colon
      ++ pp_space ++ pp_meta_typ typ
    in
    let { Meta.Context.bindings; _ } = context in
    pp_list ~sep:pp_space
      (fun (identifier, typ) ->
        pp_hovbox ~indent (pp_in_braces (pp_binding identifier typ)))
      bindings

  let guard_comp_expression_operator = function
    | Comp.Expression.Program { identifier; _ }
    | Comp.Expression.Constructor { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_comp_expression_operator_application = function
    | Comp.Expression.Application
        { applicand =
            ( Comp.Expression.Program { identifier; _ }
            | Comp.Expression.Constructor { identifier; _ } )
        ; _
        } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator_application operator)
        | Option.None -> return `Operand)
    | expression -> guard_comp_expression_operator expression

  let guard_comp_pattern_operator = function
    | Comp.Pattern.Constructor { identifier; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator operator)
        | Option.None -> return `Operand)
    | _ -> return `Operand

  let guard_comp_pattern_operator_application = function
    | Comp.Pattern.Application
        { applicand = Comp.Pattern.Constructor { identifier; _ }; _ } -> (
        lookup_operator identifier >>= function
        | Option.Some operator -> return (`Operator_application operator)
        | Option.None -> return `Operand)
    | pattern -> guard_comp_pattern_operator pattern

  let rec comp_case_body_requires_parentheses = function
    | Comp.Expression.Type_annotated _ ->
        (* Type-annotated expressions are of lesser precedence than
           case-expressions *)
        true
    | Comp.Expression.Fn { body; _ }
    | Comp.Expression.Mlam { body; _ }
    | Comp.Expression.Let { body; _ } ->
        (* Parentheses are required if [body] contains a case analysis *)
        comp_case_body_requires_parentheses body
    | Comp.Expression.Fun _
    | Comp.Expression.Case _ ->
        (* Cofunction and case analyses have patterns, which would capture
           those of the parent case analysis *)
        true
    | Comp.Expression.Application _
    | Comp.Expression.Observation _
    | Comp.Expression.Impossible _
    | Comp.Expression.Box _
    | Comp.Expression.Box_hole _
    | Comp.Expression.Tuple _
    | Comp.Expression.Hole _
    | Comp.Expression.Variable _
    | Comp.Expression.Constructor _
    | Comp.Expression.Program _ ->
        (* These expressions are of greater precedence than
           case-expressions *)
        false

  let rec pp_comp_case_body expression =
    if comp_case_body_requires_parentheses expression then
      pp_in_parens (pp_comp_expression expression)
    else pp_comp_expression expression

  and pp_comp_expression expression =
    let open
      Parenthesizer.Make (Printing_state) (Comp_expression_precedence.Ord) in
    let* parent_precedence = precedence_of_comp_expression expression in
    match expression with
    | Comp.Expression.Variable { identifier; _ } ->
        pp_computation_variable identifier
    | Comp.Expression.Constructor { identifier; _ } ->
        pp_computation_constructor_invoke identifier
    | Comp.Expression.Program { identifier; _ } ->
        pp_computation_program_invoke identifier
    | Comp.Expression.Fn { parameters; body; _ } ->
        let pp_parameter (_location, parameter) =
          pp_option ~none:pp_underscore pp_computation_variable parameter
        in
        pp_fn_keyword ++ pp_non_breaking_space
        ++ pp_list1 ~sep:pp_space pp_parameter parameters
        ++ pp_non_breaking_space ++ pp_thick_right_arrow ++ pp_space
        ++ pp_comp_expression body
    | Comp.Expression.Mlam { parameters; body; _ } ->
        let pp_parameter (_location, (parameter, modifier)) =
          match (parameter, modifier) with
          | Option.Some parameter, (`Plain | `Hash | `Dollar) ->
              (* The hash or dollar prefix is part of [parameter] *)
              pp_meta_variable parameter
          | Option.None, `Plain -> pp_underscore
          | Option.None, `Hash -> pp_hash_underscore
          | Option.None, `Dollar -> pp_dollar_underscore
        in
        let pp_parameters = pp_list1 ~sep:pp_space pp_parameter parameters in
        pp_mlam_keyword ++ pp_non_breaking_space ++ pp_parameters
        ++ pp_non_breaking_space ++ pp_thick_right_arrow ++ pp_space
        ++ pp_comp_expression body
    | Comp.Expression.Fun { branches; _ } ->
        let pp_branch branch =
          let { Comp.Cofunction_branch.meta_context; copattern; body; _ } =
            branch
          in
          match meta_context with
          | Meta.Context.{ bindings = []; _ } ->
              pp_hovbox ~indent
                (pp_pipe ++ pp_non_breaking_space
                ++ pp_comp_copattern copattern
                ++ pp_non_breaking_space ++ pp_thick_right_arrow ++ pp_space
                ++ pp_comp_case_body body)
          | _ ->
              pp_hovbox ~indent
                (pp_pipe ++ pp_non_breaking_space
                ++ pp_pattern_meta_context meta_context
                ++ pp_space
                ++ pp_comp_copattern copattern
                ++ pp_non_breaking_space ++ pp_thick_right_arrow ++ pp_space
                ++ pp_comp_case_body body)
        in
        let pp_branches = pp_list1 ~sep:pp_cut pp_branch branches in
        pp_vbox ~indent:0 (pp_fun_keyword ++ pp_space ++ pp_branches)
    | Comp.Expression.Let { scrutinee; meta_context; pattern; body; _ } -> (
        match meta_context with
        | Meta.Context.{ bindings = []; _ } ->
            pp_hovbox ~indent
              (pp_let_keyword ++ pp_space ++ pp_comp_pattern pattern
             ++ pp_non_breaking_space ++ pp_equal ++ pp_space
              ++ pp_comp_expression scrutinee)
            ++ pp_space ++ pp_in_keyword ++ pp_space
            ++ pp_comp_expression body
        | _ ->
            pp_hovbox ~indent
              (pp_let_keyword ++ pp_space
              ++ pp_pattern_meta_context meta_context
              ++ pp_space ++ pp_comp_pattern pattern ++ pp_non_breaking_space
              ++ pp_equal ++ pp_space
              ++ pp_comp_expression scrutinee)
            ++ pp_space ++ pp_in_keyword ++ pp_space
            ++ pp_comp_expression body)
    | Comp.Expression.Box { meta_object; _ } -> pp_meta_object meta_object
    | Comp.Expression.Impossible { scrutinee; _ } ->
        (* [impossible (impossible (...))] is right-associative *)
        let pp_scrutinee =
          parenthesize_right_argument_right_associative_operator
            precedence_of_comp_expression ~parent_precedence
            pp_comp_expression scrutinee
        in
        pp_hovbox ~indent (pp_impossible_keyword ++ pp_space ++ pp_scrutinee)
    | Comp.Expression.Case { scrutinee; check_coverage; branches; _ } ->
        let pp_branch branch =
          let { Comp.Case_branch.meta_context; pattern; body; _ } = branch in
          match meta_context with
          | Meta.Context.{ bindings = []; _ } ->
              pp_hovbox ~indent
                (pp_pipe ++ pp_non_breaking_space ++ pp_comp_pattern pattern
               ++ pp_non_breaking_space ++ pp_thick_right_arrow ++ pp_space
               ++ pp_comp_case_body body)
          | _ ->
              pp_hovbox ~indent
                (pp_pipe ++ pp_non_breaking_space
                ++ pp_pattern_meta_context meta_context
                ++ pp_space ++ pp_comp_pattern pattern
                ++ pp_non_breaking_space ++ pp_thick_right_arrow ++ pp_space
                ++ pp_comp_case_body body)
        in
        let pp_branches = pp_list1 ~sep:pp_cut pp_branch branches in
        let pp_check_coverage_pragma_opt =
          if check_coverage then pp_nop
          else pp_space ++ pp_pragma "not" (pp_string "--not")
        in
        pp_vbox ~indent:0
          (pp_hovbox ~indent
             (pp_case_keyword ++ pp_space
             ++ pp_comp_expression scrutinee
             ++ pp_space ++ pp_of_keyword ++ pp_check_coverage_pragma_opt)
          ++ pp_cut ++ pp_branches)
    | Comp.Expression.Tuple { elements; _ } ->
        pp_hovbox ~indent
          (pp_in_parens
             (pp_list2 ~sep:pp_comma_space pp_comp_expression elements))
    | Comp.Expression.Hole { label; _ } ->
        pp_question_mark ++ pp_option pp_identifier label
    | Comp.Expression.Box_hole _ -> pp_underscore
    | Comp.Expression.Observation { scrutinee; destructor; _ } ->
        (* Observations are left-associative *)
        let pp_scrutinee =
          parenthesize_left_argument_left_associative_operator
            precedence_of_comp_expression ~parent_precedence
            pp_comp_expression scrutinee
        in
        pp_hovbox ~indent
          (pp_scrutinee ++ pp_space ++ pp_dot
          ++ pp_computation_destructor_invoke destructor)
    | Comp.Expression.Type_annotated { expression; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_expression =
          parenthesize_left_argument_left_associative_operator
            precedence_of_comp_expression ~parent_precedence
            pp_comp_expression expression
        in
        let pp_typ = pp_comp_typ typ in
        pp_hovbox ~indent
          (pp_expression ++ pp_non_breaking_space ++ pp_colon ++ pp_space
         ++ pp_typ)
    | Comp.Expression.Application { applicand; arguments; _ } ->
        pp_application ~indent ~guard_operator:guard_comp_expression_operator
          ~guard_operator_application:
            guard_comp_expression_operator_application
          ~precedence_of_applicand:precedence_of_comp_expression
          ~precedence_of_argument:precedence_of_comp_expression
          ~pp_applicand:pp_comp_expression ~pp_argument:pp_comp_expression
          ~parent_precedence applicand arguments

  and pp_comp_pattern pattern =
    let open
      Parenthesizer.Make (Printing_state) (Comp_pattern_precedence.Ord) in
    let* parent_precedence = precedence_of_comp_pattern pattern in
    match pattern with
    | Comp.Pattern.Variable { identifier; _ } ->
        pp_computation_variable identifier
    | Comp.Pattern.Constructor { identifier; _ } ->
        pp_computation_constructor_invoke identifier
    | Comp.Pattern.Meta_object { meta_pattern; _ } ->
        pp_meta_pattern meta_pattern
    | Comp.Pattern.Tuple { elements; _ } ->
        pp_hovbox ~indent
          (pp_in_parens
             (pp_list2 ~sep:pp_comma_space pp_comp_pattern elements))
    | Comp.Pattern.Type_annotated { pattern; typ; _ } ->
        (* The type annotation operator is left-associative *)
        let pp_pattern =
          parenthesize_left_argument_left_associative_operator
            precedence_of_comp_pattern ~parent_precedence pp_comp_pattern
            pattern
        in
        let pp_typ = pp_comp_typ typ in
        pp_hovbox ~indent
          (pp_pattern ++ pp_non_breaking_space ++ pp_colon ++ pp_space
         ++ pp_typ)
    | Comp.Pattern.Wildcard _ -> pp_underscore
    | Comp.Pattern.Application { applicand; arguments; _ } ->
        pp_application ~indent ~guard_operator:guard_comp_pattern_operator
          ~guard_operator_application:guard_comp_pattern_operator_application
          ~precedence_of_applicand:precedence_of_comp_pattern
          ~precedence_of_argument:precedence_of_comp_pattern
          ~pp_applicand:pp_comp_pattern ~pp_argument:pp_comp_pattern
          ~parent_precedence applicand arguments

  and pp_comp_copattern copattern =
    let pp_comp_pattern pattern =
      if is_atomic_pattern pattern then pp_comp_pattern pattern
      else pp_hovbox ~indent (pp_in_parens (pp_comp_pattern pattern))
    in
    let pp_comp_patterns patterns =
      pp_list ~sep:pp_space pp_comp_pattern patterns
    in
    let pp_observations observations =
      pp_list ~sep:pp_space
        (fun (destructor, arguments) ->
          match arguments with
          | [] -> pp_dot ++ pp_computation_destructor_invoke destructor
          | _ ->
              pp_dot
              ++ pp_computation_destructor_invoke destructor
              ++ pp_space
              ++ pp_comp_patterns arguments)
        observations
    in
    let { Comp.Copattern.patterns; observations; _ } = copattern in
    match (patterns, observations) with
    | [], [] -> pp_nop
    | [], observations -> pp_observations observations
    | patterns, [] -> pp_comp_patterns patterns
    | patterns, observations ->
        pp_comp_patterns patterns ++ pp_space ++ pp_observations observations

  (** {1 Pretty-Printing Harpoon Syntax} *)

  let rec pp_harpoon_proof proof =
    match proof with
    | Harpoon.Proof.Incomplete { label; _ } ->
        pp_option ~none:pp_question_mark pp_identifier label
    | Harpoon.Proof.Command { command; body; _ } ->
        pp_hovbox ~indent (pp_harpoon_command command)
        ++ pp_semicolon ++ pp_cut ++ pp_harpoon_proof body
    | Harpoon.Proof.Directive { directive; _ } ->
        pp_harpoon_directive directive

  and pp_harpoon_command command =
    match command with
    | Harpoon.Command.By { expression; assignee; _ } ->
        pp_hovbox ~indent
          (pp_by_keyword ++ pp_non_breaking_space
          ++ pp_comp_expression expression
          ++ pp_space ++ pp_as_keyword ++ pp_space ++ pp_identifier assignee
          )
    | Harpoon.Command.Unbox
        { expression; assignee; modifier = Option.None; _ } ->
        pp_hovbox ~indent
          (pp_unbox_keyword ++ pp_non_breaking_space
          ++ pp_comp_expression expression
          ++ pp_space ++ pp_as_keyword ++ pp_non_breaking_space
          ++ pp_identifier assignee)
    | Harpoon.Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
        pp_hovbox ~indent
          (pp_strengthen_keyword ++ pp_non_breaking_space
          ++ pp_comp_expression expression
          ++ pp_space ++ pp_as_keyword ++ pp_non_breaking_space
          ++ pp_identifier assignee)

  and pp_harpoon_directive directive =
    match directive with
    | Harpoon.Directive.Intros { hypothetical; _ } ->
        pp_vbox ~indent:0
          (pp_intros_keyword ++ pp_cut
          ++ pp_harpoon_hypothetical hypothetical)
    | Harpoon.Directive.Solve { solution; _ } ->
        pp_hovbox ~indent
          (pp_solve_keyword ++ pp_space ++ pp_comp_expression solution)
    | Harpoon.Directive.Split { scrutinee; branches; _ } ->
        pp_hovbox ~indent
          (pp_split_keyword ++ pp_space
          ++ pp_comp_expression scrutinee
          ++ pp_non_breaking_space ++ pp_as_keyword)
        ++ pp_cut
        ++ pp_vbox ~indent:0
             (pp_list1 ~sep:pp_cut pp_harpoon_split_branch branches)
    | Harpoon.Directive.Impossible { scrutinee; _ } ->
        pp_hovbox ~indent
          (pp_impossible_keyword ++ pp_space ++ pp_comp_expression scrutinee)
    | Harpoon.Directive.Suffices { scrutinee; branches; _ } ->
        pp_vbox ~indent:0
          (pp_hovbox ~indent pp_suffices_keyword
          ++ pp_non_breaking_space ++ pp_by_keyword ++ pp_space
          ++ pp_comp_expression scrutinee)
        ++ pp_non_breaking_space ++ pp_toshow_keyword ++ pp_cut
        ++ pp_list ~sep:pp_cut pp_harpoon_suffices_branch branches

  and pp_harpoon_split_branch branch =
    let { Harpoon.Split_branch.label; body; _ } = branch in
    pp_vbox ~indent:0
      (pp_case_keyword ++ pp_non_breaking_space
      ++ pp_harpoon_split_branch_label label
      ++ pp_colon ++ pp_cut
      ++ pp_harpoon_hypothetical body)

  and pp_harpoon_split_branch_label label =
    match label with
    | Harpoon.Split_branch.Label.Lf_constant { identifier; _ } ->
        pp_constant_invoke identifier
    | Harpoon.Split_branch.Label.Comp_constant { identifier; _ } ->
        pp_constant_invoke identifier
    | Harpoon.Split_branch.Label.Bound_variable _ ->
        pp_head_keyword ++ pp_non_breaking_space ++ pp_variable_keyword
    | Harpoon.Split_branch.Label.Empty_context _ ->
        pp_empty_keyword ++ pp_non_breaking_space ++ pp_context_keyword
    | Harpoon.Split_branch.Label.Extended_context { schema_element; _ } ->
        pp_extended_keyword ++ pp_non_breaking_space ++ pp_by_keyword
        ++ pp_space ++ pp_int schema_element
    | Harpoon.Split_branch.Label.Parameter_variable
        { schema_element; projection; _ } ->
        pp_int schema_element
        ++ pp_option
             (fun projection -> pp_dot ++ pp_int projection)
             projection

  and pp_harpoon_suffices_branch branch =
    let { Harpoon.Suffices_branch.goal; proof; _ } = branch in
    pp_vbox ~indent
      (pp_box (pp_comp_typ goal)
      ++ pp_non_breaking_space
      ++ pp_in_braces
           (pp_cut ++ pp_vbox ~indent:0 (pp_harpoon_proof proof) ++ pp_cut))

  and pp_harpoon_hypothetical hypothetical =
    let { Harpoon.Hypothetical.meta_context =
            { Meta.Context.bindings = meta_context_bindings; _ }
        ; comp_context = { Comp.Context.bindings = comp_context_bindings; _ }
        ; proof
        ; _
        } =
      hypothetical
    in
    let pp_meta_binding (identifier, typ) =
      pp_hovbox ~indent:2
        (pp_identifier identifier ++ pp_non_breaking_space ++ pp_colon
       ++ pp_space ++ pp_meta_typ typ)
    in
    let pp_comp_binding (identifier, typ) =
      pp_hovbox ~indent:2
        (pp_identifier identifier ++ pp_non_breaking_space ++ pp_colon
       ++ pp_space ++ pp_comp_typ typ)
    in
    let pp_meta_context =
      pp_hvbox ~indent:0
        (pp_list ~sep:pp_comma_space pp_meta_binding meta_context_bindings)
    in
    let pp_comp_context =
      pp_hvbox ~indent:0
        (pp_list ~sep:pp_comma_space pp_comp_binding comp_context_bindings)
    in
    pp_vbox ~indent:0
      (pp_in_braces
         (pp_non_breaking_space ++ pp_meta_context ++ pp_cut ++ pp_pipe
        ++ pp_non_breaking_space ++ pp_comp_context ++ pp_cut ++ pp_semicolon
        ++ pp_non_breaking_space
         ++ pp_vbox ~indent:0 (pp_harpoon_proof proof)
         ++ pp_cut))

  (** {1 Pretty-Printing Signature Syntax} *)

  let pp_associativity = function
    | Associativity.Left_associative -> pp_string "left"
    | Associativity.Right_associative -> pp_string "right"
    | Associativity.Non_associative -> pp_string "none"

  let rec pp_signature_pragma pragma =
    match pragma with
    | Signature.Pragma.Name
        { constant; meta_variable_base; computation_variable_base; _ } ->
        let pp_name_pragma =
          pp_hovbox ~indent
            (pp_string "--name" ++ pp_space
            ++ pp_constant_invoke constant
            ++ pp_space
            ++ pp_identifier meta_variable_base
            ++ pp_option
                 (fun computation_variable_base ->
                   pp_space ++ pp_identifier computation_variable_base)
                 computation_variable_base
            ++ pp_dot)
        in
        pp_pragma "name" pp_name_pragma
    | Signature.Pragma.Default_associativity { associativity; _ } ->
        let pp_associativity_pragma =
          pp_hovbox ~indent
            (pp_string "--assoc" ++ pp_space
            ++ pp_associativity associativity
            ++ pp_dot)
        in
        pp_pragma "assoc" pp_associativity_pragma
        <& set_default_associativity associativity
    | Signature.Pragma.Prefix_fixity { constant; precedence; _ } ->
        let pp_prefix_pragma =
          pp_hovbox ~indent
            (pp_string "--prefix" ++ pp_space
            ++ pp_constant_invoke constant
            ++ pp_option
                 (fun precedence -> pp_space ++ pp_int precedence)
                 precedence
            ++ pp_dot)
        in
        pp_pragma "prefix" pp_prefix_pragma
        <& make_prefix ?precedence constant
    | Signature.Pragma.Infix_fixity
        { constant; precedence; associativity; _ } ->
        let pp_infix_pragma =
          pp_hovbox ~indent
            (pp_string "--infix" ++ pp_space
            ++ pp_constant_invoke constant
            ++ pp_option
                 (fun precedence -> pp_space ++ pp_int precedence)
                 precedence
            ++ pp_option
                 (fun associativity ->
                   pp_space ++ pp_associativity associativity)
                 associativity
            ++ pp_dot)
        in
        pp_pragma "infix" pp_infix_pragma
        <& make_infix ?precedence ?associativity constant
    | Signature.Pragma.Postfix_fixity { constant; precedence; _ } ->
        let pp_postfix_pragma =
          pp_hovbox ~indent
            (pp_string "--postfix" ++ pp_space
            ++ pp_constant_invoke constant
            ++ pp_option
                 (fun precedence -> pp_space ++ pp_int precedence)
                 precedence
            ++ pp_dot)
        in
        pp_pragma "postfix" pp_postfix_pragma
        <& make_postfix ?precedence constant
    | Signature.Pragma.Not _ ->
        let pp_not_pragma = pp_string "--not" in
        pp_pragma "not" pp_not_pragma
    | Signature.Pragma.Open_module { module_identifier; _ } ->
        let pp_open_pragma =
          pp_hovbox ~indent
            (pp_string "--open" ++ pp_space
            ++ pp_constant_invoke module_identifier
            ++ pp_dot)
        in
        pp_pragma "open" pp_open_pragma <& open_module module_identifier
    | Signature.Pragma.Abbreviation { module_identifier; abbreviation; _ } ->
        let pp_abbrev_pragma =
          pp_hovbox ~indent
            (pp_string "--abbrev" ++ pp_space
            ++ pp_constant_invoke module_identifier
            ++ pp_space
            ++ pp_identifier abbreviation
            ++ pp_dot)
        in
        pp_pragma "abbrev" pp_abbrev_pragma
        <& add_abbreviation module_identifier abbreviation
    | Signature.Pragma.Query
        { identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        ; _
        } ->
        let pp_binding identifier typ =
          pp_identifier identifier ++ pp_non_breaking_space ++ pp_colon
          ++ pp_space ++ pp_meta_typ typ
        in
        let pp_declaration (identifier, typ) =
          pp_hovbox ~indent (pp_in_braces (pp_binding identifier typ))
        in
        let pp_meta_context meta_context =
          let { Meta.Context.bindings; _ } = meta_context in
          pp_list ~sep:pp_space pp_declaration bindings
        in
        let pp_query_argument =
          pp_option ~none:pp_star (fun argument -> pp_int argument)
        in
        pp_hovbox ~indent
          (pp_string "--query" ++ pp_space
          ++ pp_query_argument expected_solutions
          ++ pp_space
          ++ pp_query_argument maximum_tries
          ++ pp_space
          ++ pp_meta_context meta_context
          ++ pp_option
               (fun identifier -> pp_space ++ pp_identifier identifier)
               identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_lf_typ typ ++ pp_dot)

  and pp_signature_global_pragma global_pragma =
    match global_pragma with
    | Signature.Global_pragma.No_strengthening _ ->
        let pp_nostrengthen_pragma = pp_string "--nostrengthen" in
        pp_pragma "nostrengthen" pp_nostrengthen_pragma
    | Signature.Global_pragma.Warn_on_coverage_error _ ->
        let pp_warncoverage_pragma = pp_string "--warncoverage" in
        pp_pragma "warncoverage" pp_warncoverage_pragma
    | Signature.Global_pragma.Initiate_coverage_checking _ ->
        let pp_coverage_pragma = pp_string "--coverage" in
        pp_pragma "coverage" pp_coverage_pragma

  and pp_signature_totality_declaration totality_declaration =
    match totality_declaration with
    | Signature.Totality.Declaration.Trust _ -> pp_trust_keyword
    | Signature.Totality.Declaration.Named
        { order; program; argument_labels; _ } ->
        let pp_argument_label_opt =
          pp_option ~none:pp_underscore pp_identifier
        in
        let pp_order_opt =
          pp_option
            (fun order ->
              pp_space ++ pp_signature_totality_order pp_identifier order)
            order
        in
        let pp_argument_labels =
          match argument_labels with
          | [] -> pp_nop
          | _ ->
              pp_space
              ++ pp_list ~sep:pp_space pp_argument_label_opt argument_labels
        in
        pp_hovbox ~indent
          (pp_total_keyword ++ pp_order_opt ++ pp_space
          ++ pp_in_parens (pp_identifier program ++ pp_argument_labels))
    | Signature.Totality.Declaration.Numeric { order; _ } ->
        pp_option ~none:pp_total_keyword
          (fun order ->
            pp_hovbox ~indent
              (pp_total_keyword ++ pp_signature_totality_order pp_int order))
          order

  and pp_signature_totality_order :
        'a. ('a -> unit t) -> 'a signature_totality_order -> unit t =
   fun ppv totality_order ->
    match totality_order with
    | Signature.Totality.Order.Argument { argument; _ } -> ppv argument
    | Signature.Totality.Order.Lexical_ordering { arguments; _ } ->
        pp_hovbox ~indent
          (pp_in_braces
             (pp_list1 ~sep:pp_space
                (pp_signature_totality_order ppv)
                arguments))
    | Signature.Totality.Order.Simultaneous_ordering { arguments; _ } ->
        pp_hovbox ~indent
          (pp_in_bracks
             (pp_list1 ~sep:pp_space
                (pp_signature_totality_order ppv)
                arguments))

  and pp_signature_declaration declaration =
    match declaration with
    | Signature.Declaration.CompTyp _
    | Signature.Declaration.CompCotyp _
    | Signature.Declaration.CompConst _
    | Signature.Declaration.CompDest _
    | Signature.Declaration.Theorem _
    | Signature.Declaration.Proof _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration declaration)
          Unsupported_non_recursive_declaration
    | Signature.Declaration.Typ { identifier; kind; _ } ->
        let* () =
          pp_hovbox ~indent
            (pp_lf_type_constant identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space
            ++ pp_lf_kind kind ++ pp_dot)
        in
        let* () = add_binding identifier in
        add_module_declaration identifier
    | Signature.Declaration.Const { identifier; typ; _ } ->
        let* () =
          pp_hovbox ~indent
            (pp_lf_term_constant identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space ++ pp_lf_typ typ
            ++ pp_dot)
        in
        let* () = add_binding identifier in
        add_module_declaration identifier
    | Signature.Declaration.Schema { identifier; schema; _ } ->
        let* () =
          pp_hovbox ~indent
            (pp_schema_keyword ++ pp_non_breaking_space
            ++ pp_schema_constant identifier
            ++ pp_non_breaking_space ++ pp_equal ++ pp_space
            ++ pp_schema schema ++ pp_semicolon)
        in
        let* () = add_binding identifier in
        add_module_declaration identifier
    | Signature.Declaration.Recursive_declarations { declarations; _ } -> (
        let* () = traverse_list1_void pre_add_declaration declarations in
        match group_recursive_declarations declarations with
        | List1.T (first, []) ->
            pp_vbox ~indent:0
              (pp_grouped_declaration ~prepend_and:false first)
            ++ pp_semicolon
        | List1.T (first, rest) ->
            pp_vbox ~indent:0
              (pp_grouped_declaration ~prepend_and:false first
              ++ pp_double_cut
              ++ pp_list ~sep:pp_double_cut
                   (pp_grouped_declaration ~prepend_and:true)
                   rest)
            ++ pp_semicolon)
    | Signature.Declaration.CompTypAbbrev { identifier; kind; typ; _ } ->
        let* () =
          pp_hovbox ~indent
            (pp_typedef_keyword ++ pp_non_breaking_space
            ++ pp_computation_abbreviation_constant identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space
            ++ pp_comp_kind kind ++ pp_non_breaking_space ++ pp_equal
            ++ pp_space ++ pp_comp_typ typ ++ pp_semicolon)
        in
        let* () = add_binding identifier in
        add_module_declaration identifier
    | Signature.Declaration.Val { identifier; typ; expression; _ } ->
        let pp_typ_annotation =
          pp_option (fun typ -> pp_colon ++ pp_space ++ pp_comp_typ typ) typ
        in
        let pp_declaration =
          pp_computation_program identifier ++ pp_typ_annotation
        in
        let* () =
          pp_hovbox ~indent
            (pp_let_keyword ++ pp_space ++ pp_declaration ++ pp_space
           ++ pp_equal ++ pp_space
            ++ pp_comp_expression expression
            ++ pp_semicolon)
        in
        let* () = add_binding identifier in
        add_module_declaration identifier
    | Signature.Declaration.Module { identifier; entries; _ } ->
        with_module_declarations identifier
          (pp_module_keyword ++ pp_non_breaking_space
          ++ pp_module_constant identifier
          ++ pp_non_breaking_space ++ pp_equal ++ pp_non_breaking_space
          ++ pp_struct_keyword ++ pp_break 1 2
          ++ pp_vbox ~indent:0 (pp_module_entries entries)
          ++ pp_cut ++ pp_end_keyword)

  and pre_add_declaration declaration =
    match declaration with
    | Signature.Declaration.Typ { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.Const { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.CompTyp { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.CompCotyp { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.CompConst { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.CompDest { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.Schema { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.Theorem { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.Proof { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.CompTypAbbrev { identifier; _ } ->
        add_binding identifier
    | Signature.Declaration.Val { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.Module { identifier; _ } ->
        add_binding identifier <& add_module_declaration identifier
    | Signature.Declaration.Recursive_declarations { declarations; _ } ->
        traverse_list1_void pre_add_declaration declarations

  and pp_grouped_declaration ~prepend_and declaration =
    let pp_and_opt =
      if prepend_and then pp_and_keyword ++ pp_non_breaking_space else pp_nop
    in
    match declaration with
    | `Lf_typ (identifier, kind, constants) ->
        let pp_constant (identifier, typ) =
          pp_hovbox ~indent
            (pp_pipe ++ pp_non_breaking_space
            ++ pp_lf_term_constant identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space ++ pp_lf_typ typ
            )
        in
        let pp_constants =
          match constants with
          | [] -> pp_nop
          | _ -> pp_cut ++ pp_list ~sep:pp_cut pp_constant constants
        in
        pp_hovbox ~indent
          (pp_and_opt ++ pp_lf_keyword ++ pp_non_breaking_space
          ++ pp_lf_type_constant identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_space ++ pp_lf_kind kind
          ++ pp_non_breaking_space ++ pp_equal)
        ++ pp_constants
    | `Inductive_comp_typ (identifier, kind, constants) ->
        let pp_constant (identifier, typ) =
          pp_hovbox ~indent
            (pp_pipe ++ pp_non_breaking_space
            ++ pp_computation_constructor identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space
            ++ pp_comp_typ typ)
        in
        let pp_constants =
          match constants with
          | [] -> pp_nop
          | _ -> pp_cut ++ pp_list ~sep:pp_cut pp_constant constants
        in
        pp_hovbox ~indent
          (pp_and_opt ++ pp_inductive_keyword ++ pp_non_breaking_space
          ++ pp_computation_inductive_constant identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_space
          ++ pp_comp_kind kind ++ pp_non_breaking_space ++ pp_equal)
        ++ pp_constants
    | `Stratified_comp_typ (identifier, kind, constants) ->
        let pp_constant (identifier, typ) =
          pp_hovbox ~indent
            (pp_pipe ++ pp_non_breaking_space
            ++ pp_computation_constructor identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space
            ++ pp_comp_typ typ)
        in
        let pp_constants =
          match constants with
          | [] -> pp_nop
          | _ -> pp_cut ++ pp_list ~sep:pp_cut pp_constant constants
        in
        pp_hovbox ~indent
          (pp_and_opt ++ pp_stratified_keyword ++ pp_non_breaking_space
          ++ pp_computation_stratified_constant identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_space
          ++ pp_comp_kind kind ++ pp_non_breaking_space ++ pp_equal)
        ++ pp_constants
    | `Coinductive_comp_typ (identifier, kind, constants) ->
        let pp_constant (identifier, observation_typ, return_typ) =
          pp_hovbox ~indent
            (pp_pipe ++ pp_non_breaking_space
            ++ pp_computation_destructor identifier
            ++ pp_non_breaking_space ++ pp_colon ++ pp_space
            ++ pp_comp_typ observation_typ
            ++ pp_non_breaking_space ++ pp_double_colon ++ pp_space
            ++ pp_comp_typ return_typ)
        in
        let pp_constants =
          match constants with
          | [] -> pp_nop
          | _ -> pp_cut ++ pp_list ~sep:pp_cut pp_constant constants
        in
        pp_hovbox ~indent
          (pp_and_opt ++ pp_coinductive_keyword ++ pp_non_breaking_space
          ++ pp_computation_coinductive_constant identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_space
          ++ pp_comp_kind kind ++ pp_non_breaking_space ++ pp_equal)
        ++ pp_constants
    | `Theorem (identifier, typ, order, body) ->
        let pp_order =
          pp_option
            (fun order ->
              pp_cut ++ pp_slash ++ pp_non_breaking_space
              ++ pp_signature_totality_declaration order
              ++ pp_non_breaking_space ++ pp_slash)
            order
        in
        pp_hovbox ~indent
          (pp_and_opt ++ pp_rec_keyword ++ pp_non_breaking_space
          ++ pp_computation_program identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_space ++ pp_comp_typ typ
          ++ pp_non_breaking_space ++ pp_equal)
        ++ pp_order ++ pp_cut
        ++ pp_hovbox ~indent (pp_comp_expression body)
    | `Proof (identifier, typ, order, body) ->
        let pp_order =
          pp_option
            (fun order ->
              pp_cut ++ pp_slash ++ pp_non_breaking_space
              ++ pp_signature_totality_declaration order
              ++ pp_non_breaking_space ++ pp_slash)
            order
        in
        pp_hovbox ~indent
          (pp_and_opt ++ pp_proof_keyword ++ pp_non_breaking_space
          ++ pp_computation_program identifier
          ++ pp_non_breaking_space ++ pp_colon ++ pp_space ++ pp_comp_typ typ
          ++ pp_non_breaking_space ++ pp_equal)
        ++ pp_order ++ pp_cut
        ++ pp_hovbox ~indent (pp_harpoon_proof body)

  and group_recursive_declarations declarations =
    let (List1.T (first_declaration, declarations')) = declarations in
    match first_declaration with
    | Signature.Declaration.Typ _ ->
        group_recursive_lf_typ_declarations first_declaration declarations'
    | Signature.Declaration.Theorem _
    | Signature.Declaration.Proof _ ->
        group_recursive_theorem_declarations first_declaration declarations'
    | Signature.Declaration.CompTyp _
    | Signature.Declaration.CompCotyp _ ->
        group_recursive_comp_typ_declarations first_declaration declarations'
    | _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration
             first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_lf_typ_declarations first_declaration declarations =
    match first_declaration with
    | Signature.Declaration.Typ { identifier; kind; _ } -> (
        let lf_term_constant_declarations, declarations' =
          List.take_while_map
            (function
              | Signature.Declaration.Const { identifier; typ; _ } ->
                  Option.some (identifier, typ)
              | _ -> Option.none)
            declarations
        in
        let lf_typ_declaration =
          `Lf_typ (identifier, kind, lf_term_constant_declarations)
        in
        match declarations' with
        | [] -> List1.singleton lf_typ_declaration
        | first_declaration' :: declarations'' ->
            let lf_typ_declarations =
              group_recursive_lf_typ_declarations first_declaration'
                declarations''
            in
            List1.cons lf_typ_declaration lf_typ_declarations)
    | _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration
             first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_theorem_declarations first_declaration declarations =
    match first_declaration with
    | Signature.Declaration.Theorem { identifier; typ; order; body; _ } -> (
        let theorem_declaration = `Theorem (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton theorem_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons theorem_declaration theorem_declarations)
    | Signature.Declaration.Proof { identifier; typ; order; body; _ } -> (
        let proof_declaration = `Proof (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton proof_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons proof_declaration theorem_declarations)
    | _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration
             first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_comp_typ_declarations first_declaration declarations =
    match first_declaration with
    | Signature.Declaration.CompTyp { identifier; kind; datatype_flavour; _ }
      -> (
        let comp_constructor_declarations, declarations' =
          List.take_while_map
            (function
              | Signature.Declaration.CompConst { identifier; typ; _ } ->
                  Option.some (identifier, typ)
              | _ -> Option.none)
            declarations
        in
        let comp_typ_declaration =
          match datatype_flavour with
          | `Inductive ->
              `Inductive_comp_typ
                (identifier, kind, comp_constructor_declarations)
          | `Stratified ->
              `Stratified_comp_typ
                (identifier, kind, comp_constructor_declarations)
        in
        match declarations' with
        | [] -> List1.singleton comp_typ_declaration
        | first_declaration' :: declarations'' ->
            let comp_typ_declarations =
              group_recursive_comp_typ_declarations first_declaration'
                declarations''
            in
            List1.cons comp_typ_declaration comp_typ_declarations)
    | Signature.Declaration.CompCotyp { identifier; kind; _ } -> (
        let comp_destructor_declarations, declarations' =
          List.take_while_map
            (function
              | Signature.Declaration.CompDest
                  { identifier; observation_type; return_type; _ } ->
                  Option.some (identifier, observation_type, return_type)
              | _ -> Option.none)
            declarations
        in
        let comp_cotyp_declaration =
          `Coinductive_comp_typ
            (identifier, kind, comp_destructor_declarations)
        in
        match declarations' with
        | [] -> List1.singleton comp_cotyp_declaration
        | first_declaration' :: declarations'' ->
            let comp_typ_declarations =
              group_recursive_comp_typ_declarations first_declaration'
                declarations''
            in
            List1.cons comp_cotyp_declaration comp_typ_declarations)
    | _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration
             first_declaration)
          Unsupported_recursive_declaration

  and pp_module_entries entries =
    let groups = group_signature_entries entries in
    let pp_group = function
      | `Code group -> pp_list1 ~sep:pp_double_cut pp_signature_entry group
      | `Comment group ->
          pp_list1 ~sep:pp_double_cut pp_signature_entry group
    in
    let pp_groups groups = pp_list ~sep:pp_double_cut pp_group groups in
    pp_vbox ~indent:0 (pp_groups groups)

  and pp_signature_entry entry =
    match entry with
    | Signature.Entry.Declaration { declaration; _ } ->
        pp_signature_declaration declaration
    | Signature.Entry.Pragma { pragma; _ } -> pp_signature_pragma pragma
    | Signature.Entry.Comment { content; _ } ->
        pp_vbox
          (pp_string "%{{" ++ pp_cut ++ pp_string content ++ pp_cut
         ++ pp_string "}}%")

  and pp_signature_file signature_file =
    let { Signature.global_pragmas; entries; _ } = signature_file in
    let pp_global_pragmas_opt =
      match global_pragmas with
      | [] -> pp_nop
      | _ ->
          pp_list ~sep:pp_cut pp_signature_global_pragma global_pragmas
          ++ pp_cut
    in
    let groups = group_signature_entries entries in
    let pp_group = function
      | `Code group -> pp_list1 ~sep:pp_double_cut pp_signature_entry group
      | `Comment group ->
          pp_list1 ~sep:pp_double_cut pp_signature_entry group
    in
    let pp_groups groups = pp_list ~sep:pp_double_cut pp_group groups in
    pp_vbox ~indent:0 (pp_global_pragmas_opt ++ pp_groups groups)

  and group_signature_entries entries =
    match entries with
    | (Signature.Entry.Declaration _ as x) :: xs
    | (Signature.Entry.Pragma _ as x) :: xs ->
        let code_entries, rest =
          List.take_while
            (function
              | Signature.Entry.Declaration _
              | Signature.Entry.Pragma _ ->
                  true
              | Signature.Entry.Comment _ -> false)
            xs
        in
        `Code (List1.from x code_entries) :: group_signature_entries rest
    | (Signature.Entry.Comment _ as x) :: xs ->
        let comment_entries, rest =
          List.take_while
            (function
              | Signature.Entry.Declaration _
              | Signature.Entry.Pragma _ ->
                  false
              | Signature.Entry.Comment _ -> true)
            xs
        in
        `Comment (List1.from x comment_entries)
        :: group_signature_entries rest
    | [] -> []
end

let () =
  Error.register_exception_printer (function
    | Unsupported_implicit_lf_pi_kind ->
        Format.dprintf
          "Pretty-printing of implicit LF Pi kinds is unsupported."
    | Unsupported_implicit_lf_pi_typ ->
        Format.dprintf
          "Pretty-printing of implicit LF Pi types is unsupported."
    | Unsupported_implicit_clf_pi_typ ->
        Format.dprintf
          "Pretty-printing of implicit contextual LF Pi types is \
           unsupported."
    | Unsupported_non_recursive_declaration ->
        Format.dprintf
          "Unsupported pretty-printing for this declaration outside of a \
           recursive group of declarations."
    | Unsupported_recursive_declaration ->
        Format.dprintf
          "Unsupported pretty-printing for this declaration in a recursive \
           group of declarations."
    | exn -> Error.raise_unsupported_exception_printing exn)
