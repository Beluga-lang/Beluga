open Support
open Beluga_syntax
open Synext
open Synext_html_pp_state

exception Unsupported_implicit_lf_pi_kind

exception Unsupported_implicit_lf_pi_typ

exception Unsupported_implicit_clf_pi_typ

exception Markdown_rendering_error

exception Unsupported_non_recursive_declaration

exception Unsupported_recursive_declaration

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
    | Markdown_rendering_error ->
        Format.dprintf "Failed to render Markdown documentation comment."
    | Unsupported_non_recursive_declaration ->
        Format.dprintf
          "Unsupported pretty-printing for this declaration outside of a \
           recursive group of declarations."
    | Unsupported_recursive_declaration ->
        Format.dprintf
          "Unsupported pretty-printing for this declaration in a recursive \
           group of declarations."
    | exn -> Error.raise_unsupported_exception_printing exn)

module type HTML_PRINTER = sig
  include Imperative_state.IMPERATIVE_STATE

  val pp_signature_file : state -> Synext.signature_file -> Unit.t

  val pp_signature : state -> Synext.signature -> Unit.t
end

module Make_html_printer (Html_printing_state : HTML_PRINTING_STATE) = struct
  include Html_printing_state

  let indent = 2

  let pp_double_cut state =
    pp_cut state;
    pp_cut state

  let[@inline] pp_in_parens state p =
    pp_char state '(';
    p state;
    pp_char state ')'

  let[@inline] pp_in_bracks state p =
    pp_char state '[';
    p state;
    pp_char state ']'

  let[@inline] pp_in_braces state p =
    pp_char state '{';
    p state;
    pp_char state '}'

  let[@inline] pp_in_angles state p =
    pp_char state '<';
    p state;
    pp_char state '>'

  let[@inline] pp_in_hash_parens state p =
    pp_string state "#(";
    p state;
    pp_char state ')'

  let[@inline] pp_in_dollar_parens state p =
    pp_string state "$(";
    p state;
    pp_char state ')'

  let[@inline] [@warning "-32"] pp_in_hash_bracks state p =
    pp_string state "#[";
    p state;
    pp_char state ']'

  let[@inline] pp_in_dollar_bracks state p =
    pp_string state "$[";
    p state;
    pp_char state ']'

  let pp_right_arrow state = pp_utf_8 state "→"

  let pp_left_arrow state = pp_utf_8 state "←"

  let pp_thick_right_arrow state = pp_utf_8 state "⇒"

  let pp_turnstile state = pp_utf_8 state "⊢"

  let pp_hash state = pp_char state '#'

  let[@warning "-32"] pp_dollar state = pp_char state '$'

  let pp_hash_underscore state = pp_string state "#_"

  let pp_dollar_underscore state = pp_string state "$_"

  let pp_turnstile_hash state =
    pp_turnstile state;
    pp_hash state

  let pp_dots state = pp_utf_8 state "…"

  let pp_underscore state = pp_char state '_'

  let pp_semicolon state = pp_char state ';'

  let pp_colon state = pp_char state ':'

  let pp_comma state = pp_char state ','

  let pp_dot state = pp_char state '.'

  let pp_star state = pp_char state '*'

  let pp_lambda state = pp_char state '\\'

  let pp_question_mark state = pp_char state '?'

  let pp_equal state = pp_char state '='

  let pp_pipe state = pp_char state '|'

  let pp_slash state = pp_char state '/'

  let pp_plus state = pp_char state '+'

  let pp_double_colon state = pp_string state "::"

  let pp_semicolon_space state =
    pp_semicolon state;
    pp_space state

  let pp_comma_space state =
    pp_comma state;
    pp_space state

  let pp_identifier state identifier =
    pp_utf_8 state (Identifier.name identifier)

  let pp_qualified_identifier state identifier =
    let name = Qualified_identifier.name identifier in
    let namespaces = Qualified_identifier.namespaces identifier in
    match namespaces with
    | [] -> pp_identifier state name
    | _ ->
        pp_hovbox state ~indent (fun state ->
            iter_list state
              (fun state namespace ->
                pp_identifier state namespace;
                pp_cut state;
                pp_dot state)
              namespaces;
            pp_identifier state name)

  let[@inline] pp_in_html state ~start ~stop p =
    pp_as state 0 start;
    p state;
    pp_as state 0 stop

  let pp_toplevel_documentation_html =
    pp_in_html ~start:{|<div class="documentation">|} ~stop:{|</div>|}

  let pp_inner_documentation_html =
    pp_in_html ~start:{|<div class="inner-documentation">|} ~stop:{|</div>|}

  let pp_preformatted_code_html =
    pp_in_html ~start:{|<pre><code>|} ~stop:{|</code></pre>|}

  let pp_keyword state x =
    pp_in_html state
      ~start:(Format.asprintf {|<span class="keyword keyword-%s">|} x)
      ~stop:{|</span>|} (fun state -> pp_string state x)

  let pp_pragma state base =
    pp_in_html state
      ~start:(Format.asprintf {|<span class="pragma pragma-%s">|} base)
      ~stop:{|</span>|}

  let pp_variable state css_class identifier =
    pp_in_html state
      ~start:(Format.asprintf {|<span class="variable %s">|} css_class)
      ~stop:{|</span>|} (fun state -> pp_identifier state identifier)

  let pp_lf_variable state = pp_variable state "lf-variable"

  let pp_meta_variable state = pp_variable state "meta-variable"

  let pp_parameter_variable state = pp_variable state "parameter-variable"

  let pp_substitution_variable state =
    pp_variable state "substitution-variable"

  let pp_context_variable state = pp_variable state "context-variable"

  let pp_computation_variable state =
    pp_variable state "computation-variable"

  let pp_constant state ?css_class ~id identifier =
    let start =
      match css_class with
      | Option.Some css_class ->
          Format.asprintf {|<span id="%s" class="constant %s">|} id css_class
      | Option.None -> Format.asprintf {|<span id="%s" class="constant">|} id
    in
    pp_in_html state ~start ~stop:{|</span>|} (fun state ->
        pp_identifier state identifier)

  let pp_constant_invoke state ?css_class identifier =
    let reference = lookup_reference state identifier in
    let start =
      match css_class with
      | Option.Some css_class ->
          Format.asprintf {|<span class="constant %s"><a href="%s">|}
            css_class reference
      | Option.None ->
          Format.asprintf {|<span class="constant"><a href="%s">|} reference
    in
    pp_in_html state ~start ~stop:{|</a></span>|} (fun state ->
        pp_qualified_identifier state identifier)

  let lf_type_constant_css_class = "lf-type-constant"

  let pp_lf_type_constant = pp_constant ~css_class:lf_type_constant_css_class

  let pp_lf_type_constant_invoke =
    pp_constant_invoke ~css_class:lf_type_constant_css_class

  let lf_term_constant_css_class = "lf-term-constant"

  let pp_lf_term_constant = pp_constant ~css_class:lf_term_constant_css_class

  let pp_lf_term_constant_invoke =
    pp_constant_invoke ~css_class:lf_term_constant_css_class

  let context_schema_css_class = "context-schema"

  let pp_schema_constant = pp_constant ~css_class:context_schema_css_class

  let pp_schema_constant_invoke =
    pp_constant_invoke ~css_class:context_schema_css_class

  let computation_inductive_type_constant_css_class =
    "computation-inductive-type-constant"

  let pp_computation_inductive_constant =
    pp_constant ~css_class:computation_inductive_type_constant_css_class

  let pp_computation_inductive_constant_invoke =
    pp_constant_invoke
      ~css_class:computation_inductive_type_constant_css_class

  let computation_stratified_type_constant_css_class =
    "computation-stratified-type-constant"

  let pp_computation_stratified_constant =
    pp_constant ~css_class:computation_stratified_type_constant_css_class

  let pp_computation_stratified_constant_invoke =
    pp_constant_invoke
      ~css_class:computation_stratified_type_constant_css_class

  let computation_coinductive_type_constant_css_class =
    "computation-coinductive-type-constant"

  let pp_computation_coinductive_constant =
    pp_constant ~css_class:computation_coinductive_type_constant_css_class

  let pp_computation_coinductive_constant_invoke =
    pp_constant_invoke
      ~css_class:computation_coinductive_type_constant_css_class

  let computation_abbreviation_type_constant_css_class =
    "computation-abbreviation-type-constant"

  let pp_computation_abbreviation_constant =
    pp_constant ~css_class:computation_abbreviation_type_constant_css_class

  let pp_computation_abbreviation_constant_invoke =
    pp_constant_invoke
      ~css_class:computation_abbreviation_type_constant_css_class

  let computation_constructor_css_class = "computation-constructor"

  let pp_computation_constructor =
    pp_constant ~css_class:computation_constructor_css_class

  let pp_computation_constructor_invoke =
    pp_constant_invoke ~css_class:computation_constructor_css_class

  let computation_destructor_css_class = "computation-destructor"

  let pp_computation_destructor =
    pp_constant ~css_class:computation_destructor_css_class

  let pp_computation_destructor_invoke =
    pp_constant_invoke ~css_class:computation_destructor_css_class

  let computation_program_css_class = "computation-program"

  let pp_computation_program =
    pp_constant ~css_class:computation_program_css_class

  let pp_computation_program_invoke =
    pp_constant_invoke ~css_class:computation_program_css_class

  let module_css_class = "module"

  let pp_module_constant = pp_constant ~css_class:module_css_class

  let[@warning "-32"] pp_module_constant_invoke =
    pp_constant_invoke ~css_class:module_css_class

  let pp_and_keyword state = pp_keyword state "and"

  let pp_block_keyword state = pp_keyword state "block"

  let pp_case_keyword state = pp_keyword state "case"

  let[@warning "-32"] pp_if_keyword state = pp_keyword state "if"

  let[@warning "-32"] pp_then_keyword state = pp_keyword state "then"

  let[@warning "-32"] pp_else_keyword state = pp_keyword state "else"

  let pp_impossible_keyword state = pp_keyword state "impossible"

  let pp_let_keyword state = pp_keyword state "let"

  let pp_in_keyword state = pp_keyword state "in"

  let pp_of_keyword state = pp_keyword state "of"

  let pp_rec_keyword state = pp_keyword state "rec"

  let pp_schema_keyword state = pp_keyword state "schema"

  let pp_some_keyword state = pp_keyword state "some"

  let pp_fn_keyword state = pp_keyword state "fn"

  let pp_mlam_keyword state = pp_keyword state "mlam"

  let pp_module_keyword state = pp_keyword state "module"

  let pp_struct_keyword state = pp_keyword state "struct"

  let pp_end_keyword state = pp_keyword state "end"

  let pp_total_keyword state = pp_keyword state "total"

  let pp_trust_keyword state = pp_keyword state "trust"

  let pp_type_keyword state = pp_keyword state "type"

  let pp_ctype_keyword state = pp_keyword state "ctype"

  let[@warning "-32"] pp_prop_keyword state = pp_keyword state "prop"

  let pp_inductive_keyword state = pp_keyword state "inductive"

  let pp_coinductive_keyword state = pp_keyword state "coinductive"

  let pp_stratified_keyword state = pp_keyword state "stratified"

  let pp_lf_keyword state = pp_keyword state "LF"

  let pp_fun_keyword state = pp_keyword state "fun"

  let pp_typedef_keyword state = pp_keyword state "typedef"

  let pp_proof_keyword state = pp_keyword state "proof"

  let pp_as_keyword state = pp_keyword state "as"

  let pp_by_keyword state = pp_keyword state "by"

  let pp_suffices_keyword state = pp_keyword state "suffices"

  let pp_toshow_keyword state = pp_keyword state "toshow"

  let pp_unbox_keyword state = pp_keyword state "unbox"

  let pp_strengthen_keyword state = pp_keyword state "strengthen"

  let pp_head_keyword state = pp_keyword state "head"

  let pp_variable_keyword state = pp_keyword state "variable"

  let pp_empty_keyword state = pp_keyword state "empty"

  let pp_context_keyword state = pp_keyword state "context"

  let pp_extended_keyword state = pp_keyword state "extended"

  let pp_intros_keyword state = pp_keyword state "intros"

  let pp_solve_keyword state = pp_keyword state "solve"

  let pp_split_keyword state = pp_keyword state "split"

  let fresh_lf_type_id = fresh_id ~prefix:"lf-type-"

  let fresh_lf_term_id = fresh_id ~prefix:"lf-term-"

  let fresh_schema_id = fresh_id ~prefix:"schema-"

  let fresh_computation_inductive_type_id = fresh_id ~prefix:"ind-comp-type-"

  let fresh_computation_stratified_type_id =
    fresh_id ~prefix:"strat-comp-type-"

  let fresh_computation_coinductive_type_id = fresh_id ~prefix:"comp-cotype-"

  let fresh_computation_abbreviation_id = fresh_id ~prefix:"abbrev-"

  let fresh_computation_constructor_id = fresh_id ~prefix:"comp-const-"

  let fresh_computation_destructor_id = fresh_id ~prefix:"comp-dest-"

  let fresh_computation_value_id = fresh_id ~prefix:"val-"

  let fresh_theorem_id = fresh_id ~prefix:"theorem-"

  let fresh_proof_id = fresh_id ~prefix:"proof-"

  let fresh_module_id = fresh_id ~prefix:"module-"

  open Synext.Make_precedences (Html_printing_state)

  (** {1 Pretty-Printing LF Syntax} *)

  let guard_lf_typ_operator state = function
    | LF.Typ.Constant { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_lf_term_operator state = function
    | LF.Term.Constant { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_lf_term_operator_application state = function
    | LF.Term.Application
        { applicand = LF.Term.Constant { identifier; _ }; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator_application operator
        | Option.None -> `Operand)
    | term -> guard_lf_term_operator state term

  let rec pp_lf_kind state kind =
    let open Parenthesizer.Make (Html_printing_state) (Lf_precedence.Ord) in
    let parent_precedence = precedence_of_lf_kind state kind in
    match kind with
    | LF.Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative *)
        let pp_domain state =
          parenthesize_left_argument_right_associative_operator state
            precedence_of_lf_typ ~parent_precedence pp_lf_typ domain
        in
        let pp_range state =
          parenthesize_right_argument_right_associative_operator state
            precedence_of_lf_kind ~parent_precedence pp_lf_kind range
        in
        pp_hovbox state ~indent (fun state ->
            pp_domain state;
            pp_non_breaking_space state;
            pp_right_arrow state;
            pp_space state;
            pp_range state)
    | LF.Kind.Typ _ -> pp_type_keyword state
    | LF.Kind.Pi
        { parameter_identifier; parameter_type; body; plicity; location } ->
        let pp_parameter_identifier state =
          pp_option state ~none:pp_underscore pp_identifier
            parameter_identifier
        in
        let pp_parameter_type state =
          pp_option state
            (fun state parameter_type ->
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_lf_typ state parameter_type)
            parameter_type
        in
        let pp_declaration state =
          pp_parameter_identifier state;
          pp_parameter_type state
        in
        let pp_binding state =
          match plicity with
          | Plicity.Explicit -> pp_in_braces state pp_declaration
          | Plicity.Implicit ->
              Error.raise_at1 location Unsupported_implicit_lf_pi_kind
        in
        pp_hovbox state ~indent (fun state ->
            pp_binding state;
            pp_space state;
            pp_lf_kind state body)

  and pp_lf_typ state typ =
    let open Parenthesizer.Make (Html_printing_state) (Lf_precedence.Ord) in
    let parent_precedence = precedence_of_lf_typ state typ in
    match typ with
    | LF.Typ.Constant { identifier; _ } ->
        pp_lf_type_constant_invoke state identifier
    | LF.Typ.Application { applicand; arguments; _ } ->
        pp_application state ~indent ~guard_operator:guard_lf_typ_operator
          ~guard_operator_application:guard_lf_term_operator_application
          ~precedence_of_applicand:precedence_of_lf_typ
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:pp_lf_typ ~pp_argument:pp_lf_term ~parent_precedence
          applicand arguments
    | LF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        let pp_domain state =
          match domain with
          | LF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens state (fun state -> pp_lf_typ state domain)
          | _ ->
              parenthesize_left_argument_right_associative_operator state
                precedence_of_lf_typ ~parent_precedence pp_lf_typ domain
        in
        let pp_range state =
          match range with
          | LF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens state (fun state -> pp_lf_typ state range)
          | _ ->
              parenthesize_right_argument_right_associative_operator state
                precedence_of_lf_typ ~parent_precedence pp_lf_typ range
        in
        pp_hovbox state ~indent (fun state ->
            pp_domain state;
            pp_non_breaking_space state;
            pp_right_arrow state;
            pp_space state;
            pp_range state)
    | LF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        let pp_range state =
          match range with
          | LF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens state (fun state -> pp_lf_typ state range)
          | _ ->
              parenthesize_left_argument_left_associative_operator state
                precedence_of_lf_typ ~parent_precedence pp_lf_typ range
        in
        let pp_domain state =
          match domain with
          | LF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens state (fun state -> pp_lf_typ state domain)
          | _ ->
              parenthesize_right_argument_left_associative_operator state
                precedence_of_lf_typ ~parent_precedence pp_lf_typ domain
        in
        pp_hovbox state ~indent (fun state ->
            pp_range state;
            pp_space state;
            pp_left_arrow state;
            pp_non_breaking_space state;
            pp_domain state)
    | LF.Typ.Pi
        { parameter_identifier; parameter_type; body; plicity; location } ->
        let pp_parameter_identifier state =
          pp_option state ~none:pp_underscore pp_identifier
            parameter_identifier
        in
        let pp_parameter_type state =
          pp_option state
            (fun state parameter_type ->
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_lf_typ state parameter_type)
            parameter_type
        in
        let pp_declaration state =
          pp_parameter_identifier state;
          pp_parameter_type state
        in
        let pp_binding state =
          match plicity with
          | Plicity.Explicit -> pp_in_braces state pp_declaration
          | Plicity.Implicit ->
              Error.raise_at1 location Unsupported_implicit_lf_pi_typ
        in
        pp_hovbox state ~indent (fun state ->
            pp_binding state;
            pp_space state;
            pp_lf_typ state body)

  and pp_lf_term state term =
    let open Parenthesizer.Make (Html_printing_state) (Lf_precedence.Ord) in
    let parent_precedence = precedence_of_lf_term state term in
    match term with
    | LF.Term.Variable { identifier; _ } -> pp_lf_variable state identifier
    | LF.Term.Constant { identifier; _ } ->
        pp_lf_term_constant_invoke state identifier
    | LF.Term.Application { applicand; arguments; _ } ->
        pp_application state ~indent ~guard_operator:guard_lf_term_operator
          ~guard_operator_application:guard_lf_term_operator_application
          ~precedence_of_applicand:precedence_of_lf_term
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:pp_lf_term ~pp_argument:pp_lf_term ~parent_precedence
          applicand arguments
    | LF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      ->
        (* Lambdas are weak prefix operators, so the body of the lambda never
           requires parentheses *)
        let pp_parameter_identifier state =
          pp_option state ~none:pp_underscore pp_identifier
            parameter_identifier
        in
        let pp_declaration state =
          match parameter_type with
          | Option.Some parameter_type ->
              pp_in_parens state (fun state ->
                  pp_parameter_identifier state;
                  pp_non_breaking_space state;
                  pp_colon state;
                  pp_space state;
                  pp_lf_typ state parameter_type)
          | Option.None -> pp_parameter_identifier state
        in
        pp_hovbox state ~indent (fun state ->
            pp_lambda state;
            pp_declaration state;
            pp_dot state;
            pp_space state;
            pp_lf_term state body)
    | LF.Term.Wildcard _ -> pp_underscore state
    | LF.Term.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_lf_term ~parent_precedence pp_lf_term term
        in
        pp_hovbox state ~indent (fun state ->
            pp_term state;
            pp_space state;
            pp_colon state;
            pp_space state;
            pp_lf_typ state typ)

  (** {1 Pretty-Printing Contextual LF Syntax} *)

  let guard_clf_typ_operator state = function
    | CLF.Typ.Constant { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_clf_term_operator state = function
    | CLF.Term.Constant { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_clf_term_operator_application state = function
    | CLF.Term.Application
        { applicand = CLF.Term.Constant { identifier; _ }; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator_application operator
        | Option.None -> `Operand)
    | term -> guard_clf_term_operator state term

  let guard_clf_term_pattern_operator state = function
    | CLF.Term.Pattern.Constant { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_clf_term_pattern_operator_application state = function
    | CLF.Term.Pattern.Application
        { applicand = CLF.Term.Pattern.Constant { identifier; _ }; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator_application operator
        | Option.None -> `Operand)
    | term -> guard_clf_term_pattern_operator state term

  let rec pp_clf_typ state typ =
    let open Parenthesizer.Make (Html_printing_state) (Clf_precedence.Ord) in
    let parent_precedence = precedence_of_clf_typ state typ in
    match typ with
    | CLF.Typ.Constant { identifier; _ } ->
        pp_lf_type_constant_invoke state identifier
    | CLF.Typ.Application { applicand; arguments; _ } ->
        pp_application state ~indent ~guard_operator:guard_clf_typ_operator
          ~guard_operator_application:guard_clf_term_operator_application
          ~precedence_of_applicand:precedence_of_clf_typ
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:pp_clf_typ ~pp_argument:pp_clf_term
          ~parent_precedence applicand arguments
    | CLF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        let pp_domain state =
          match domain with
          | CLF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens state (fun state -> pp_clf_typ state domain)
          | _ ->
              parenthesize_left_argument_right_associative_operator state
                precedence_of_clf_typ ~parent_precedence pp_clf_typ domain
        in
        let pp_range state =
          match range with
          | CLF.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens state (fun state -> pp_clf_typ state range)
          | _ ->
              parenthesize_right_argument_right_associative_operator state
                precedence_of_clf_typ ~parent_precedence pp_clf_typ range
        in
        pp_hovbox state ~indent (fun state ->
            pp_domain state;
            pp_non_breaking_space state;
            pp_right_arrow state;
            pp_space state;
            pp_range state)
    | CLF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        let pp_range state =
          match range with
          | CLF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens state (fun state -> pp_clf_typ state range)
          | _ ->
              parenthesize_left_argument_left_associative_operator state
                precedence_of_clf_typ ~parent_precedence pp_clf_typ range
        in
        let pp_domain state =
          match domain with
          | CLF.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens state (fun state -> pp_clf_typ state domain)
          | _ ->
              parenthesize_right_argument_left_associative_operator state
                precedence_of_clf_typ ~parent_precedence pp_clf_typ domain
        in
        pp_hovbox state ~indent (fun state ->
            pp_range state;
            pp_space state;
            pp_left_arrow state;
            pp_non_breaking_space state;
            pp_domain state)
    | CLF.Typ.Pi
        { parameter_identifier; parameter_type; body; plicity; location } ->
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier state =
          pp_option state ~none:pp_underscore pp_identifier
            parameter_identifier
        in
        let pp_parameter_type state =
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_clf_typ state parameter_type
        in
        let pp_declaration state =
          pp_parameter_identifier state;
          pp_parameter_type state
        in
        let pp_binding state =
          match plicity with
          | Plicity.Explicit -> pp_in_braces state pp_declaration
          | Plicity.Implicit ->
              Error.raise_at1 location Unsupported_implicit_clf_pi_typ
        in
        pp_hovbox state ~indent (fun state ->
            pp_binding state;
            pp_space state;
            pp_clf_typ state body)
    | CLF.Typ.Block { elements = `Unnamed typ; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_block_keyword state;
            pp_non_breaking_space state;
            pp_in_parens state (fun state -> pp_clf_typ state typ))
    | CLF.Typ.Block { elements = `Record nts; _ } ->
        let pp_binding state (identifier, typ) =
          pp_hovbox state ~indent (fun state ->
              pp_identifier state identifier;
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_clf_typ state typ)
        in
        let pp_bindings state bindings =
          pp_hvbox state (fun state ->
              pp_list1 state ~sep:pp_comma_space pp_binding bindings)
        in
        pp_hovbox state ~indent (fun state ->
            pp_block_keyword state;
            pp_non_breaking_space state;
            pp_in_parens state (fun state -> pp_bindings state nts))

  and pp_clf_term state term =
    let open Parenthesizer.Make (Html_printing_state) (Clf_precedence.Ord) in
    let parent_precedence = precedence_of_clf_term state term in
    match term with
    | CLF.Term.Variable { identifier; _ } -> pp_lf_variable state identifier
    | CLF.Term.Meta_variable { identifier; _ } ->
        pp_meta_variable state identifier
    | CLF.Term.Parameter_variable { identifier; _ } ->
        pp_parameter_variable state identifier
    | CLF.Term.Constant { identifier; _ } ->
        pp_lf_term_constant_invoke state identifier
    | CLF.Term.Application { applicand; arguments; _ } ->
        pp_application state ~indent ~guard_operator:guard_clf_term_operator
          ~guard_operator_application:guard_clf_term_operator_application
          ~precedence_of_applicand:precedence_of_clf_term
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:pp_clf_term ~pp_argument:pp_clf_term
          ~parent_precedence applicand arguments
    | CLF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      ->
        (* Lambdas are weak prefix operators, so the body of a lambda does
           not need to be parenthesized *)
        let pp_parameter_identifier state =
          pp_option state ~none:pp_underscore pp_identifier
            parameter_identifier
        in
        let pp_declaration state =
          match parameter_type with
          | Option.Some parameter_type ->
              pp_in_parens state (fun state ->
                  pp_parameter_identifier state;
                  pp_non_breaking_space state;
                  pp_colon state;
                  pp_space state;
                  pp_clf_typ state parameter_type)
          | Option.None -> pp_parameter_identifier state
        in
        pp_hovbox state ~indent (fun state ->
            pp_lambda state;
            pp_declaration state;
            pp_dot state;
            pp_space state;
            pp_clf_term state body)
    | CLF.Term.Hole { variant = `Underscore; _ } -> pp_underscore state
    | CLF.Term.Hole { variant = `Unlabelled; _ } -> pp_question_mark state
    | CLF.Term.Hole { variant = `Labelled label; _ } ->
        pp_question_mark state;
        pp_identifier state label
    | CLF.Term.Substitution { term; substitution; _ } ->
        (* Substitutions are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_hovbox state ~indent (fun state ->
            pp_term state;
            pp_in_bracks state (fun state ->
                pp_clf_substitution state substitution))
    | CLF.Term.Tuple { terms; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_angles state (fun state ->
                pp_list1 state ~sep:pp_semicolon_space pp_clf_term terms))
    | CLF.Term.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_hovbox state ~indent (fun state ->
            pp_term state;
            pp_dot state;
            pp_int state i)
    | CLF.Term.Projection { term; projection = `By_identifier i; _ } ->
        (* Projections are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_term state;
        pp_dot state;
        pp_identifier state i
    | CLF.Term.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term ~parent_precedence pp_clf_term term
        in
        pp_hovbox state ~indent (fun state ->
            pp_term state;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_clf_typ state typ)

  and pp_clf_substitution state substitution =
    match substitution with
    | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms = []; _ }
      ->
        pp_nop state
    | { CLF.Substitution.head = CLF.Substitution.Head.Identity _
      ; terms = []
      ; _
      } ->
        pp_dots state
    | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms; _ } ->
        pp_list state ~sep:pp_comma_space pp_clf_term terms
    | { CLF.Substitution.head = CLF.Substitution.Head.Identity _; terms; _ }
      ->
        pp_dots state;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_clf_term terms
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable state identifier
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable state identifier;
        pp_in_bracks state (fun state -> pp_clf_substitution state closure)
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable state identifier;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_clf_term terms
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable state identifier;
        pp_in_bracks state (fun state -> pp_clf_substitution state closure);
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_clf_term terms

  and pp_clf_context state context =
    let pp_typing state (identifier, typ_opt) =
      pp_lf_variable state identifier;
      pp_option state
        (fun state typ ->
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_clf_typ state typ)
        typ_opt
    in
    match context with
    | { CLF.Context.head = CLF.Context.Head.None _; bindings = []; _ } ->
        pp_nop state
    | { CLF.Context.head = CLF.Context.Head.Hole _; bindings = []; _ } ->
        pp_underscore state
    | { CLF.Context.head =
          CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        pp_context_variable state identifier
    | { CLF.Context.head = CLF.Context.Head.None _; bindings; _ } ->
        pp_list state ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.head = CLF.Context.Head.Hole _; bindings; _ } ->
        pp_underscore state;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.head =
          CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        pp_context_variable state identifier;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_typing bindings

  let rec pp_clf_term_pattern state term =
    let open Parenthesizer.Make (Html_printing_state) (Clf_precedence.Ord) in
    let parent_precedence = precedence_of_clf_term_pattern state term in
    match term with
    | CLF.Term.Pattern.Variable { identifier; _ } ->
        pp_lf_variable state identifier
    | CLF.Term.Pattern.Meta_variable { identifier; _ } ->
        pp_meta_variable state identifier
    | CLF.Term.Pattern.Parameter_variable { identifier; _ } ->
        pp_parameter_variable state identifier
    | CLF.Term.Pattern.Constant { identifier; _ } ->
        pp_lf_term_constant_invoke state identifier
    | CLF.Term.Pattern.Application { applicand; arguments; _ } ->
        pp_application state ~indent
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
        let pp_parameter_identifier state =
          pp_option state ~none:pp_underscore pp_identifier
            parameter_identifier
        in
        let pp_declaration state =
          pp_parameter_identifier state;
          pp_option state
            (fun state parameter_type ->
              pp_in_parens state (fun state ->
                  pp_non_breaking_space state;
                  pp_colon state;
                  pp_space state;
                  pp_clf_typ state parameter_type))
            parameter_type
        in
        pp_hovbox state ~indent (fun state ->
            pp_lambda state;
            pp_declaration state;
            pp_dot state;
            pp_space state;
            pp_clf_term_pattern state body)
    | CLF.Term.Pattern.Wildcard _ -> pp_underscore state
    | CLF.Term.Pattern.Substitution { term; substitution; _ } ->
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_hovbox state ~indent (fun state ->
            pp_term state;
            pp_in_bracks state (fun state ->
                pp_clf_substitution state substitution))
    | CLF.Term.Pattern.Tuple { terms; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_angles state (fun state ->
                pp_list1 state ~sep:pp_semicolon_space pp_clf_term_pattern
                  terms))
    | CLF.Term.Pattern.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_term state;
        pp_dot state;
        pp_int state i
    | CLF.Term.Pattern.Projection { term; projection = `By_identifier i; _ }
      ->
        (* Projections are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_term state;
        pp_dot state;
        pp_identifier state i
    | CLF.Term.Pattern.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_term state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_clf_term_pattern ~parent_precedence
            pp_clf_term_pattern term
        in
        pp_hovbox state ~indent (fun state ->
            pp_term state;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_clf_typ state typ)

  and pp_clf_substitution_pattern state substitution_pattern =
    match substitution_pattern with
    | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
      ; terms = []
      ; _
      } ->
        pp_nop state
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Identity _
      ; terms = []
      ; _
      } ->
        pp_dots state
    | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
      ; terms
      ; _
      } ->
        pp_list state ~sep:pp_comma_space pp_clf_term_pattern terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Identity _
      ; terms
      ; _
      } ->
        pp_dots state;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_clf_term_pattern terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable state identifier
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        pp_substitution_variable state identifier;
        pp_in_bracks state (fun state -> pp_clf_substitution state closure)
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable state identifier;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_clf_term_pattern terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
        pp_substitution_variable state identifier;
        pp_in_bracks state (fun state -> pp_clf_substitution state closure);
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_clf_term_pattern terms

  and pp_clf_context_pattern state context_pattern =
    let pp_typing state (identifier, typ) =
      pp_lf_variable state identifier;
      pp_non_breaking_space state;
      pp_colon state;
      pp_space state;
      pp_clf_typ state typ
    in
    match context_pattern with
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
      ; bindings = []
      ; _
      } ->
        pp_nop state
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
      ; bindings = []
      ; _
      } ->
        pp_underscore state
    | { CLF.Context.Pattern.head =
          CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        pp_context_variable state identifier
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
      ; bindings
      ; _
      } ->
        pp_list state ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
      ; bindings
      ; _
      } ->
        pp_underscore state;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_typing bindings
    | { CLF.Context.Pattern.head =
          CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        pp_context_variable state identifier;
        pp_comma_space state;
        pp_list state ~sep:pp_comma_space pp_typing bindings

  (** {1 Pretty-Printing Meta-Level Syntax} *)

  let rec pp_meta_typ state typ =
    match typ with
    | Meta.Typ.Context_schema { schema; _ } ->
        pp_schema_constant_invoke state schema
    | Meta.Typ.Contextual_typ { context; typ; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_parens state (fun state ->
                pp_clf_context state context;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_typ state typ))
    | Meta.Typ.Parameter_typ { context; typ; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_hash_parens state (fun state ->
                pp_clf_context state context;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_typ state typ))
    | Meta.Typ.Plain_substitution_typ { domain; range; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_dollar_parens state (fun state ->
                pp_clf_context state domain;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_context state range))
    | Meta.Typ.Renaming_substitution_typ { domain; range; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_dollar_parens state (fun state ->
                pp_clf_context state domain;
                pp_non_breaking_space state;
                pp_turnstile_hash state;
                pp_space state;
                pp_clf_context state range))

  and pp_meta_object state object_ =
    match object_ with
    | Meta.Object.Context { context; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_bracks state (fun state -> pp_clf_context state context))
    | Meta.Object.Contextual_term { context; term; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_bracks state (fun state ->
                pp_clf_context state context;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_term state term))
    | Meta.Object.Plain_substitution { domain; range; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_dollar_bracks state (fun state ->
                pp_clf_context state domain;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_substitution state range))
    | Meta.Object.Renaming_substitution { domain; range; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_dollar_bracks state (fun state ->
                pp_clf_context state domain;
                pp_non_breaking_space state;
                pp_turnstile_hash state;
                pp_space state;
                pp_clf_substitution state range))

  and pp_meta_pattern state pattern =
    match pattern with
    | Meta.Pattern.Context { context; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_bracks state (fun state ->
                pp_clf_context_pattern state context))
    | Meta.Pattern.Contextual_term { context; term; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_bracks state (fun state ->
                pp_clf_context_pattern state context;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_term_pattern state term))
    | Meta.Pattern.Plain_substitution { domain; range; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_dollar_bracks state (fun state ->
                pp_clf_context_pattern state domain;
                pp_non_breaking_space state;
                pp_turnstile state;
                pp_space state;
                pp_clf_substitution_pattern state range))
    | Meta.Pattern.Renaming_substitution { domain; range; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_dollar_bracks state (fun state ->
                pp_clf_context_pattern state domain;
                pp_non_breaking_space state;
                pp_turnstile_hash state;
                pp_space state;
                pp_clf_substitution_pattern state range))

  and pp_schema state schema =
    let open Parenthesizer.Make (Html_printing_state) (Schema_precedence.Ord) in
    let parent_precedence = precedence_of_schema state schema in
    let pp_binding state (identifier, typ) =
      pp_hovbox state ~indent (fun state ->
          pp_lf_variable state identifier;
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_lf_typ state typ)
    in
    let pp_bindings state bindings =
      pp_hvbox state (fun state ->
          pp_list1 state ~sep:pp_comma_space pp_binding bindings)
    in
    match schema with
    | Meta.Schema.Constant { identifier; _ } ->
        pp_schema_constant_invoke state identifier
    | Meta.Schema.Alternation { schemas; _ } ->
        pp_list2 state
          ~sep:(fun state ->
            pp_space state;
            pp_plus state;
            pp_non_breaking_space state)
          (fun state ->
            parenthesize_term_of_lesser_than_or_equal_precedence state
              precedence_of_schema ~parent_precedence pp_schema)
          schemas
    | Meta.Schema.Element { some; block; _ } ->
        let pp_some_clause state =
          pp_option state
            (fun state some_bindings ->
              pp_some_keyword state;
              pp_non_breaking_space state;
              pp_in_bracks state (fun state ->
                  pp_bindings state some_bindings);
              pp_space state)
            some
        in
        let pp_block_clause state =
          match block with
          | `Unnamed t ->
              pp_block_keyword state;
              pp_non_breaking_space state;
              pp_lf_typ state t
          | `Record block_bindings ->
              pp_block_keyword state;
              pp_non_breaking_space state;
              pp_in_parens state (fun state ->
                  pp_bindings state block_bindings)
        in
        pp_hvbox state (fun state ->
            pp_some_clause state;
            pp_block_clause state)

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

  let rec pp_comp_kind state kind =
    match kind with
    | Comp.Kind.Ctype _ -> pp_ctype_keyword state
    | Comp.Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative, but the precedence of
           meta-types is not comparable with the precedence of
           computation-level kinds *)
        pp_hovbox state ~indent (fun state ->
            pp_meta_typ state domain;
            pp_non_breaking_space state;
            pp_right_arrow state;
            pp_space state;
            pp_comp_kind state range)
    | Comp.Kind.Pi { parameter_identifier; parameter_type; body; plicity; _ }
      ->
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier state =
          match (parameter_identifier, parameter_type) with
          | Option.Some parameter_identifier, _ ->
              pp_meta_variable state parameter_identifier
          | ( Option.None
            , (Meta.Typ.Context_schema _ | Meta.Typ.Contextual_typ _) ) ->
              pp_underscore state
          | Option.None, Meta.Typ.Parameter_typ _ -> pp_hash_underscore state
          | ( Option.None
            , ( Meta.Typ.Plain_substitution_typ _
              | Meta.Typ.Renaming_substitution_typ _ ) ) ->
              pp_dollar_underscore state
        in
        let pp_binding state =
          pp_parameter_identifier state;
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_meta_typ state parameter_type
        in
        let pp_declaration state =
          match plicity with
          | Plicity.Implicit -> pp_in_parens state pp_binding
          | Plicity.Explicit -> pp_in_braces state pp_binding
        in
        pp_hovbox state ~indent (fun state ->
            pp_declaration state;
            pp_space state;
            pp_comp_kind state body)

  and pp_comp_typ state typ =
    let open
      Parenthesizer.Make (Html_printing_state) (Comp_sort_precedence.Ord) in
    let parent_precedence = precedence_of_comp_typ state typ in
    match typ with
    | Comp.Typ.Inductive_typ_constant { identifier; _ } ->
        pp_computation_inductive_constant_invoke state identifier
    | Comp.Typ.Stratified_typ_constant { identifier; _ } ->
        pp_computation_stratified_constant_invoke state identifier
    | Comp.Typ.Coinductive_typ_constant { identifier; _ } ->
        pp_computation_coinductive_constant_invoke state identifier
    | Comp.Typ.Abbreviation_typ_constant { identifier; _ } ->
        pp_computation_abbreviation_constant_invoke state identifier
    | Comp.Typ.Pi { parameter_identifier; plicity; parameter_type; body; _ }
      ->
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier state =
          match (parameter_identifier, parameter_type) with
          | Option.Some parameter_identifier, _ ->
              pp_meta_variable state parameter_identifier
          | ( Option.None
            , (Meta.Typ.Context_schema _ | Meta.Typ.Contextual_typ _) ) ->
              pp_underscore state
          | Option.None, Meta.Typ.Parameter_typ _ -> pp_hash_underscore state
          | ( Option.None
            , ( Meta.Typ.Plain_substitution_typ _
              | Meta.Typ.Renaming_substitution_typ _ ) ) ->
              pp_dollar_underscore state
        in
        let pp_binding state =
          pp_parameter_identifier state;
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_meta_typ state parameter_type
        in
        let pp_declaration state =
          match plicity with
          | Plicity.Implicit -> pp_in_parens state pp_binding
          | Plicity.Explicit -> pp_in_braces state pp_binding
        in
        pp_hovbox state ~indent (fun state ->
            pp_declaration state;
            pp_space state;
            pp_comp_typ state body)
    | Comp.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows *)
        let pp_domain state =
          match domain with
          | Comp.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens state (fun state -> pp_comp_typ state domain)
          | _ ->
              parenthesize_left_argument_right_associative_operator state
                precedence_of_comp_typ ~parent_precedence pp_comp_typ domain
        in
        let pp_range state =
          match range with
          | Comp.Typ.Arrow { orientation = `Backward; _ } ->
              pp_in_parens state (fun state -> pp_comp_typ state range)
          | _ ->
              parenthesize_right_argument_right_associative_operator state
                precedence_of_comp_typ ~parent_precedence pp_comp_typ range
        in
        pp_hovbox state ~indent (fun state ->
            pp_domain state;
            pp_non_breaking_space state;
            pp_right_arrow state;
            pp_space state;
            pp_range state)
    | Comp.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows *)
        let pp_range state =
          match range with
          | Comp.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens state (fun state -> pp_comp_typ state range)
          | _ ->
              parenthesize_left_argument_left_associative_operator state
                precedence_of_comp_typ ~parent_precedence pp_comp_typ range
        in
        let pp_domain state =
          match domain with
          | Comp.Typ.Arrow { orientation = `Forward; _ } ->
              pp_in_parens state (fun state -> pp_comp_typ state domain)
          | _ ->
              parenthesize_right_argument_left_associative_operator state
                precedence_of_comp_typ ~parent_precedence pp_comp_typ domain
        in
        pp_hovbox state ~indent (fun state ->
            pp_range state;
            pp_space state;
            pp_left_arrow state;
            pp_non_breaking_space state;
            pp_domain state)
    | Comp.Typ.Cross { types; _ } ->
        pp_list2 state
          ~sep:(fun state ->
            pp_space state;
            pp_star state;
            pp_non_breaking_space state)
          (fun state ->
            parenthesize_term_of_lesser_than_or_equal_precedence state
              precedence_of_comp_typ ~parent_precedence pp_comp_typ)
          types
    | Comp.Typ.Box { meta_type; _ } -> pp_meta_typ state meta_type
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
            match lookup_operator state identifier with
            | Option.Some operator -> (
                match Operator.fixity operator with
                | Fixity.Prefix ->
                    pp_hovbox state ~indent (fun state ->
                        pp_comp_typ state applicand;
                        pp_space state;
                        pp_list1 state ~sep:pp_space pp_meta_object arguments)
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
                    pp_hovbox state ~indent (fun state ->
                        pp_meta_object state left_argument;
                        pp_space state;
                        pp_comp_typ state applicand;
                        pp_space state;
                        pp_meta_object state right_argument)
                | Fixity.Postfix ->
                    assert (
                      List1.compare_length_with arguments 1
                      = 0
                        (* Postfix operators must be applied with exactly one
                           argument. *));
                    let[@warning "-8"] (List1.T (argument, [])) =
                      arguments
                    in
                    pp_hovbox state ~indent (fun state ->
                        pp_meta_object state argument;
                        pp_space state;
                        pp_comp_typ state applicand))
            | Option.None ->
                let pp_applicand state =
                  parenthesize_term_of_lesser_than_or_equal_precedence state
                    precedence_of_comp_typ ~parent_precedence pp_comp_typ
                    applicand
                in
                let pp_arguments state =
                  pp_list1 state ~sep:pp_space pp_meta_object arguments
                in
                pp_hovbox state ~indent (fun state ->
                    pp_applicand state;
                    pp_space state;
                    pp_arguments state))
        | _ ->
            let pp_applicand state =
              parenthesize_term_of_lesser_than_or_equal_precedence state
                precedence_of_comp_typ ~parent_precedence pp_comp_typ
                applicand
            in
            let pp_arguments state =
              pp_list1 state ~sep:pp_space pp_meta_object arguments
            in
            pp_hovbox state ~indent (fun state ->
                pp_applicand state;
                pp_space state;
                pp_arguments state))

  and pp_pattern_meta_context state context =
    let pp_binding state identifier typ =
      pp_identifier state identifier;
      pp_non_breaking_space state;
      pp_colon state;
      pp_space state;
      pp_meta_typ state typ
    in
    let { Meta.Context.bindings; _ } = context in
    pp_list state ~sep:pp_space
      (fun state (identifier, typ) ->
        pp_hovbox state ~indent (fun state ->
            pp_in_braces state (fun state -> pp_binding state identifier typ)))
      bindings

  let guard_comp_expression_operator state = function
    | Comp.Expression.Program { identifier; _ }
    | Comp.Expression.Constructor { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_comp_expression_operator_application state = function
    | Comp.Expression.Application
        { applicand =
            ( Comp.Expression.Program { identifier; _ }
            | Comp.Expression.Constructor { identifier; _ } )
        ; _
        } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator_application operator
        | Option.None -> `Operand)
    | expression -> guard_comp_expression_operator state expression

  let guard_comp_pattern_operator state = function
    | Comp.Pattern.Constructor { identifier; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator operator
        | Option.None -> `Operand)
    | _ -> `Operand

  let guard_comp_pattern_operator_application state = function
    | Comp.Pattern.Application
        { applicand = Comp.Pattern.Constructor { identifier; _ }; _ } -> (
        match lookup_operator state identifier with
        | Option.Some operator -> `Operator_application operator
        | Option.None -> `Operand)
    | pattern -> guard_comp_pattern_operator state pattern

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

  let rec pp_comp_case_body state expression =
    if comp_case_body_requires_parentheses expression then
      pp_in_parens state (fun state -> pp_comp_expression state expression)
    else pp_comp_expression state expression

  and pp_comp_expression state expression =
    let open
      Parenthesizer.Make
        (Html_printing_state)
        (Comp_expression_precedence.Ord) in
    let parent_precedence = precedence_of_comp_expression state expression in
    match expression with
    | Comp.Expression.Variable { identifier; _ } ->
        pp_computation_variable state identifier
    | Comp.Expression.Constructor { identifier; _ } ->
        pp_computation_constructor_invoke state identifier
    | Comp.Expression.Program { identifier; _ } ->
        pp_computation_program_invoke state identifier
    | Comp.Expression.Fn { parameters; body; _ } ->
        let pp_parameter state (_location, parameter) =
          pp_option state ~none:pp_underscore pp_computation_variable
            parameter
        in
        pp_fn_keyword state;
        pp_non_breaking_space state;
        pp_list1 state ~sep:pp_space pp_parameter parameters;
        pp_non_breaking_space state;
        pp_thick_right_arrow state;
        pp_space state;
        pp_comp_expression state body
    | Comp.Expression.Mlam { parameters; body; _ } ->
        let pp_parameter state (_location, (parameter, modifier)) =
          match (parameter, modifier) with
          | Option.Some parameter, (`Plain | `Hash | `Dollar) ->
              (* The hash or dollar prefix is part of [parameter] *)
              pp_meta_variable state parameter
          | Option.None, `Plain -> pp_underscore state
          | Option.None, `Hash -> pp_hash_underscore state
          | Option.None, `Dollar -> pp_dollar_underscore state
        in
        let pp_parameters state =
          pp_list1 state ~sep:pp_space pp_parameter parameters
        in
        pp_mlam_keyword state;
        pp_non_breaking_space state;
        pp_parameters state;
        pp_non_breaking_space state;
        pp_thick_right_arrow state;
        pp_space state;
        pp_comp_expression state body
    | Comp.Expression.Fun { branches; _ } ->
        let pp_branch state branch =
          let { Comp.Cofunction_branch.meta_context; copattern; body; _ } =
            branch
          in
          match meta_context with
          | Meta.Context.{ bindings = []; _ } ->
              pp_hovbox state ~indent (fun state ->
                  pp_pipe state;
                  pp_non_breaking_space state;
                  pp_comp_copattern state copattern;
                  pp_non_breaking_space state;
                  pp_thick_right_arrow state;
                  pp_space state;
                  pp_comp_case_body state body)
          | _ ->
              pp_hovbox state ~indent (fun state ->
                  pp_pipe state;
                  pp_non_breaking_space state;
                  pp_pattern_meta_context state meta_context;
                  pp_space state;
                  pp_comp_copattern state copattern;
                  pp_non_breaking_space state;
                  pp_thick_right_arrow state;
                  pp_space state;
                  pp_comp_case_body state body)
        in
        let pp_branches state =
          pp_list1 state ~sep:pp_cut pp_branch branches
        in
        pp_vbox state ~indent:0 (fun state ->
            pp_fun_keyword state;
            pp_space state;
            pp_branches state)
    | Comp.Expression.Let { scrutinee; meta_context; pattern; body; _ } -> (
        match meta_context with
        | Meta.Context.{ bindings = []; _ } ->
            pp_hovbox state ~indent (fun state ->
                pp_let_keyword state;
                pp_space state;
                pp_comp_pattern state pattern;
                pp_non_breaking_space state;
                pp_equal state;
                pp_space state;
                pp_comp_expression state scrutinee);
            pp_space state;
            pp_in_keyword state;
            pp_space state;
            pp_comp_expression state body
        | _ ->
            pp_hovbox state ~indent (fun state ->
                pp_let_keyword state;
                pp_space state;
                pp_pattern_meta_context state meta_context;
                pp_space state;
                pp_comp_pattern state pattern;
                pp_non_breaking_space state;
                pp_equal state;
                pp_space state;
                pp_comp_expression state scrutinee);
            pp_space state;
            pp_in_keyword state;
            pp_space state;
            pp_comp_expression state body)
    | Comp.Expression.Box { meta_object; _ } ->
        pp_meta_object state meta_object
    | Comp.Expression.Impossible { scrutinee; _ } ->
        (* [impossible (impossible (...))] is right-associative *)
        let pp_scrutinee state =
          parenthesize_right_argument_right_associative_operator state
            precedence_of_comp_expression ~parent_precedence
            pp_comp_expression scrutinee
        in
        pp_hovbox state ~indent (fun state ->
            pp_impossible_keyword state;
            pp_space state;
            pp_scrutinee state)
    | Comp.Expression.Case { scrutinee; check_coverage; branches; _ } ->
        let pp_branch state branch =
          let { Comp.Case_branch.meta_context; pattern; body; _ } = branch in
          match meta_context with
          | Meta.Context.{ bindings = []; _ } ->
              pp_hovbox state ~indent (fun state ->
                  pp_pipe state;
                  pp_non_breaking_space state;
                  pp_comp_pattern state pattern;
                  pp_non_breaking_space state;
                  pp_thick_right_arrow state;
                  pp_space state;
                  pp_comp_case_body state body)
          | _ ->
              pp_hovbox state ~indent (fun state ->
                  pp_pipe state;
                  pp_non_breaking_space state;
                  pp_pattern_meta_context state meta_context;
                  pp_space state;
                  pp_comp_pattern state pattern;
                  pp_non_breaking_space state;
                  pp_thick_right_arrow state;
                  pp_space state;
                  pp_comp_case_body state body)
        in
        let pp_branches state =
          pp_list1 state ~sep:pp_cut pp_branch branches
        in
        let pp_check_coverage_pragma_opt state =
          if check_coverage then pp_nop state
          else (
            pp_space state;
            pp_pragma state "not" (fun state -> pp_string state "--not"))
        in
        pp_vbox state ~indent:0 (fun state ->
            pp_hovbox state ~indent (fun state ->
                pp_case_keyword state;
                pp_space state;
                pp_comp_expression state scrutinee;
                pp_space state;
                pp_of_keyword state;
                pp_check_coverage_pragma_opt state);
            pp_cut state;
            pp_branches state)
    | Comp.Expression.Tuple { elements; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_parens state (fun state ->
                pp_list2 state ~sep:pp_comma_space pp_comp_expression
                  elements))
    | Comp.Expression.Hole { label; _ } ->
        pp_question_mark state;
        pp_option state pp_identifier label
    | Comp.Expression.Box_hole _ -> pp_underscore state
    | Comp.Expression.Observation { scrutinee; destructor; _ } ->
        (* Observations are left-associative *)
        let pp_scrutinee state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_comp_expression ~parent_precedence
            pp_comp_expression scrutinee
        in
        pp_hovbox state ~indent (fun state ->
            pp_scrutinee state;
            pp_space state;
            pp_dot state;
            pp_computation_destructor_invoke state destructor)
    | Comp.Expression.Type_annotated { expression; typ; _ } ->
        (* Type ascriptions are left-associative *)
        let pp_expression state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_comp_expression ~parent_precedence
            pp_comp_expression expression
        in
        let pp_typ state = pp_comp_typ state typ in
        pp_hovbox state ~indent (fun state ->
            pp_expression state;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_typ state)
    | Comp.Expression.Application { applicand; arguments; _ } ->
        pp_application state ~indent
          ~guard_operator:guard_comp_expression_operator
          ~guard_operator_application:
            guard_comp_expression_operator_application
          ~precedence_of_applicand:precedence_of_comp_expression
          ~precedence_of_argument:precedence_of_comp_expression
          ~pp_applicand:pp_comp_expression ~pp_argument:pp_comp_expression
          ~parent_precedence applicand arguments

  and pp_comp_pattern state pattern =
    let open
      Parenthesizer.Make (Html_printing_state) (Comp_pattern_precedence.Ord) in
    let parent_precedence = precedence_of_comp_pattern state pattern in
    match pattern with
    | Comp.Pattern.Variable { identifier; _ } ->
        pp_computation_variable state identifier
    | Comp.Pattern.Constructor { identifier; _ } ->
        pp_computation_constructor_invoke state identifier
    | Comp.Pattern.Meta_object { meta_pattern; _ } ->
        pp_meta_pattern state meta_pattern
    | Comp.Pattern.Tuple { elements; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_parens state (fun state ->
                pp_list2 state ~sep:pp_comma_space pp_comp_pattern elements))
    | Comp.Pattern.Type_annotated { pattern; typ; _ } ->
        (* The type annotation operator is left-associative *)
        let pp_pattern state =
          parenthesize_left_argument_left_associative_operator state
            precedence_of_comp_pattern ~parent_precedence pp_comp_pattern
            pattern
        in
        let pp_typ state = pp_comp_typ state typ in
        pp_hovbox state ~indent (fun state ->
            pp_pattern state;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_typ state)
    | Comp.Pattern.Wildcard _ -> pp_underscore state
    | Comp.Pattern.Application { applicand; arguments; _ } ->
        pp_application state ~indent
          ~guard_operator:guard_comp_pattern_operator
          ~guard_operator_application:guard_comp_pattern_operator_application
          ~precedence_of_applicand:precedence_of_comp_pattern
          ~precedence_of_argument:precedence_of_comp_pattern
          ~pp_applicand:pp_comp_pattern ~pp_argument:pp_comp_pattern
          ~parent_precedence applicand arguments

  and pp_comp_copattern state copattern =
    let pp_comp_pattern state pattern =
      if is_atomic_pattern pattern then pp_comp_pattern state pattern
      else
        pp_hovbox state ~indent (fun state ->
            pp_in_parens state (fun state -> pp_comp_pattern state pattern))
    in
    let pp_comp_patterns state patterns =
      pp_list state ~sep:pp_space pp_comp_pattern patterns
    in
    let pp_observations state observations =
      pp_list state ~sep:pp_space
        (fun state (destructor, arguments) ->
          match arguments with
          | [] ->
              pp_dot state;
              pp_computation_destructor_invoke state destructor
          | _ ->
              pp_dot state;
              pp_computation_destructor_invoke state destructor;
              pp_space state;
              pp_comp_patterns state arguments)
        observations
    in
    let { Comp.Copattern.patterns; observations; _ } = copattern in
    match (patterns, observations) with
    | [], [] -> pp_nop state
    | [], observations -> pp_observations state observations
    | patterns, [] -> pp_comp_patterns state patterns
    | patterns, observations ->
        pp_comp_patterns state patterns;
        pp_space state;
        pp_observations state observations

  (** {1 Pretty-Printing Harpoon Syntax} *)

  let rec pp_harpoon_proof state proof =
    match proof with
    | Harpoon.Proof.Incomplete { label; _ } ->
        pp_option state ~none:pp_question_mark pp_identifier label
    | Harpoon.Proof.Command { command; body; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_harpoon_command state command);
        pp_semicolon state;
        pp_cut state;
        pp_harpoon_proof state body
    | Harpoon.Proof.Directive { directive; _ } ->
        pp_harpoon_directive state directive

  and pp_harpoon_command state command =
    match command with
    | Harpoon.Command.By { expression; assignee; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_by_keyword state;
            pp_non_breaking_space state;
            pp_comp_expression state expression;
            pp_space state;
            pp_as_keyword state;
            pp_space state;
            pp_identifier state assignee)
    | Harpoon.Command.Unbox
        { expression; assignee; modifier = Option.None; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_unbox_keyword state;
            pp_non_breaking_space state;
            pp_comp_expression state expression;
            pp_space state;
            pp_as_keyword state;
            pp_non_breaking_space state;
            pp_identifier state assignee)
    | Harpoon.Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_strengthen_keyword state;
            pp_non_breaking_space state;
            pp_comp_expression state expression;
            pp_space state;
            pp_as_keyword state;
            pp_non_breaking_space state;
            pp_identifier state assignee)

  and pp_harpoon_directive state directive =
    match directive with
    | Harpoon.Directive.Intros { hypothetical; _ } ->
        pp_vbox state ~indent:0 (fun state ->
            pp_intros_keyword state;
            pp_cut state;
            pp_harpoon_hypothetical state hypothetical)
    | Harpoon.Directive.Solve { solution; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_solve_keyword state;
            pp_space state;
            pp_comp_expression state solution)
    | Harpoon.Directive.Split { scrutinee; branches; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_split_keyword state;
            pp_space state;
            pp_comp_expression state scrutinee;
            pp_non_breaking_space state;
            pp_as_keyword state);
        pp_cut state;
        pp_vbox state ~indent:0 (fun state ->
            pp_list1 state ~sep:pp_cut pp_harpoon_split_branch branches)
    | Harpoon.Directive.Impossible { scrutinee; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_impossible_keyword state;
            pp_space state;
            pp_comp_expression state scrutinee)
    | Harpoon.Directive.Suffices { scrutinee; branches; _ } ->
        pp_vbox state ~indent:0 (fun state ->
            pp_hovbox state ~indent pp_suffices_keyword;
            pp_non_breaking_space state;
            pp_by_keyword state;
            pp_space state;
            pp_comp_expression state scrutinee);
        pp_non_breaking_space state;
        pp_toshow_keyword state;
        pp_cut state;
        pp_list state ~sep:pp_cut pp_harpoon_suffices_branch branches

  and pp_harpoon_split_branch state branch =
    let { Harpoon.Split_branch.label; body; _ } = branch in
    pp_vbox state ~indent:0 (fun state ->
        pp_case_keyword state;
        pp_non_breaking_space state;
        pp_harpoon_split_branch_label state label;
        pp_colon state;
        pp_cut state;
        pp_harpoon_hypothetical state body)

  and pp_harpoon_split_branch_label state label =
    match label with
    | Harpoon.Split_branch.Label.Lf_constant { identifier; _ } ->
        pp_constant_invoke state identifier
    | Harpoon.Split_branch.Label.Comp_constant { identifier; _ } ->
        pp_constant_invoke state identifier
    | Harpoon.Split_branch.Label.Bound_variable _ ->
        pp_head_keyword state;
        pp_non_breaking_space state;
        pp_variable_keyword state
    | Harpoon.Split_branch.Label.Empty_context _ ->
        pp_empty_keyword state;
        pp_non_breaking_space state;
        pp_context_keyword state
    | Harpoon.Split_branch.Label.Extended_context { schema_element; _ } ->
        pp_extended_keyword state;
        pp_non_breaking_space state;
        pp_by_keyword state;
        pp_space state;
        pp_int state schema_element
    | Harpoon.Split_branch.Label.Parameter_variable
        { schema_element; projection; _ } ->
        pp_hash state;
        pp_int state schema_element;
        pp_option state
          (fun state projection ->
            pp_dot state;
            pp_int state projection)
          projection

  and pp_harpoon_suffices_branch state branch =
    let { Harpoon.Suffices_branch.goal; proof; _ } = branch in
    pp_vbox state ~indent (fun state ->
        pp_box state (fun state -> pp_comp_typ state goal);
        pp_non_breaking_space state;
        pp_in_braces state (fun state ->
            pp_cut state;
            pp_vbox state ~indent:0 (fun state ->
                pp_harpoon_proof state proof);
            pp_cut state))

  and pp_harpoon_hypothetical state hypothetical =
    let { Harpoon.Hypothetical.meta_context =
            { Meta.Context.bindings = meta_context_bindings; _ }
        ; comp_context = { Comp.Context.bindings = comp_context_bindings; _ }
        ; proof
        ; _
        } =
      hypothetical
    in
    let pp_meta_binding state (identifier, typ) =
      pp_hovbox state ~indent:2 (fun state ->
          pp_identifier state identifier;
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_meta_typ state typ)
    in
    let pp_comp_binding state (identifier, typ) =
      pp_hovbox state ~indent:2 (fun state ->
          pp_identifier state identifier;
          pp_non_breaking_space state;
          pp_colon state;
          pp_space state;
          pp_comp_typ state typ)
    in
    let pp_meta_context state =
      pp_hvbox state ~indent:0 (fun state ->
          pp_list state ~sep:pp_comma_space pp_meta_binding
            meta_context_bindings)
    in
    let pp_comp_context state =
      pp_hvbox state ~indent:0 (fun state ->
          pp_list state ~sep:pp_comma_space pp_comp_binding
            comp_context_bindings)
    in
    pp_vbox state ~indent:0 (fun state ->
        pp_in_braces state (fun state ->
            pp_non_breaking_space state;
            pp_meta_context state;
            pp_cut state;
            pp_pipe state;
            pp_non_breaking_space state;
            pp_comp_context state;
            pp_cut state;
            pp_semicolon state;
            pp_non_breaking_space state;
            pp_vbox state ~indent:0 (fun state ->
                pp_harpoon_proof state proof);
            pp_cut state))

  (** {1 Pretty-Printing Signature Syntax} *)

  let pp_associativity state = function
    | Associativity.Left_associative -> pp_string state "left"
    | Associativity.Right_associative -> pp_string state "right"
    | Associativity.Non_associative -> pp_string state "none"

  let apply_signature_pragma state pragma =
    match pragma with
    | Signature.Pragma.Name _ -> ()
    | Signature.Pragma.Default_associativity { associativity; _ } ->
        set_default_associativity state associativity
    | Signature.Pragma.Prefix_fixity { constant; precedence; _ } ->
        add_prefix_notation state ?precedence constant
    | Signature.Pragma.Infix_fixity
        { constant; precedence; associativity; _ } ->
        add_infix_notation state ?precedence ?associativity constant
    | Signature.Pragma.Postfix_fixity { constant; precedence; _ } ->
        add_postfix_notation state ?precedence constant
    | Signature.Pragma.Not _ -> ()
    | Signature.Pragma.Open_module { module_identifier; _ } ->
        open_module state module_identifier
    | Signature.Pragma.Abbreviation { module_identifier; abbreviation; _ } ->
        add_abbreviation state module_identifier abbreviation
    | Signature.Pragma.Query _ -> ()

  let rec pp_signature_pragma state pragma =
    match pragma with
    | Signature.Pragma.Name
        { constant; meta_variable_base; computation_variable_base; _ } ->
        let pp_name_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--name";
              pp_space state;
              pp_constant_invoke state constant;
              pp_space state;
              pp_identifier state meta_variable_base;
              pp_option state
                (fun state computation_variable_base ->
                  pp_space state;
                  pp_identifier state computation_variable_base)
                computation_variable_base;
              pp_dot state)
        in
        pp_pragma state "name" pp_name_pragma
    | Signature.Pragma.Default_associativity { associativity; _ } ->
        let pp_associativity_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--assoc";
              pp_space state;
              pp_associativity state associativity;
              pp_dot state)
        in
        pp_pragma state "assoc" pp_associativity_pragma
    | Signature.Pragma.Prefix_fixity { constant; precedence; _ } ->
        let pp_prefix_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--prefix";
              pp_space state;
              pp_constant_invoke state constant;
              pp_option state
                (fun state precedence ->
                  pp_space state;
                  pp_int state precedence)
                precedence;
              pp_dot state)
        in
        pp_pragma state "prefix" pp_prefix_pragma
    | Signature.Pragma.Infix_fixity
        { constant; precedence; associativity; _ } ->
        let pp_infix_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--infix";
              pp_space state;
              pp_constant_invoke state constant;
              pp_option state
                (fun state precedence ->
                  pp_space state;
                  pp_int state precedence)
                precedence;
              pp_option state
                (fun state associativity ->
                  pp_space state;
                  pp_associativity state associativity)
                associativity;
              pp_dot state)
        in
        pp_pragma state "infix" pp_infix_pragma
    | Signature.Pragma.Postfix_fixity { constant; precedence; _ } ->
        let pp_postfix_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--postfix";
              pp_space state;
              pp_constant_invoke state constant;
              pp_option state
                (fun state precedence ->
                  pp_space state;
                  pp_int state precedence)
                precedence;
              pp_dot state)
        in
        pp_pragma state "postfix" pp_postfix_pragma
    | Signature.Pragma.Not _ ->
        let pp_not_pragma state = pp_string state "--not" in
        pp_pragma state "not" pp_not_pragma
    | Signature.Pragma.Open_module { module_identifier; _ } ->
        let pp_open_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--open";
              pp_space state;
              pp_constant_invoke state module_identifier;
              pp_dot state)
        in
        pp_pragma state "open" pp_open_pragma
    | Signature.Pragma.Abbreviation { module_identifier; abbreviation; _ } ->
        let pp_abbrev_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--abbrev";
              pp_space state;
              pp_constant_invoke state module_identifier;
              pp_space state;
              pp_identifier state abbreviation;
              pp_dot state)
        in
        pp_pragma state "abbrev" pp_abbrev_pragma
    | Signature.Pragma.Query
        { identifier; typ; expected_solutions; maximum_tries; _ } ->
        let pp_query_argument state argument_opt =
          pp_option state ~none:pp_star pp_int argument_opt
        in
        let pp_query_pragma state =
          pp_hovbox state ~indent (fun state ->
              pp_string state "--query";
              pp_space state;
              pp_query_argument state expected_solutions;
              pp_space state;
              pp_query_argument state maximum_tries;
              pp_option state
                (fun state identifier ->
                  pp_space state;
                  pp_identifier state identifier)
                identifier;
              pp_non_breaking_space state;
              pp_colon state;
              pp_lf_typ state typ;
              pp_dot state)
        in
        pp_pragma state "query" pp_query_pragma

  and pp_signature_global_pragma state global_pragma =
    match global_pragma with
    | Signature.Global_pragma.No_strengthening _ ->
        let pp_nostrengthen_pragma state =
          pp_string state "--nostrengthen"
        in
        pp_pragma state "nostrengthen" pp_nostrengthen_pragma
    | Signature.Global_pragma.Warn_on_coverage_error _ ->
        let pp_warncoverage_pragma state =
          pp_string state "--warncoverage"
        in
        pp_pragma state "warncoverage" pp_warncoverage_pragma
    | Signature.Global_pragma.Initiate_coverage_checking _ ->
        let pp_coverage_pragma state = pp_string state "--coverage" in
        pp_pragma state "coverage" pp_coverage_pragma

  and pp_signature_totality_declaration state totality_declaration =
    match totality_declaration with
    | Signature.Totality.Declaration.Trust _ -> pp_trust_keyword state
    | Signature.Totality.Declaration.Named
        { order; program; argument_labels; _ } ->
        let pp_argument_label_opt state =
          pp_option state ~none:pp_underscore pp_identifier
        in
        let pp_order_opt state =
          pp_option state
            (fun state order ->
              pp_space state;
              pp_signature_totality_order state pp_identifier order)
            order
        in
        let pp_argument_labels state =
          match argument_labels with
          | [] -> pp_nop state
          | _ ->
              pp_space state;
              pp_list state ~sep:pp_space pp_argument_label_opt
                argument_labels
        in
        pp_hovbox state ~indent (fun state ->
            pp_total_keyword state;
            pp_order_opt state;
            pp_space state;
            pp_in_parens state (fun state ->
                pp_identifier state program;
                pp_argument_labels state))
    | Signature.Totality.Declaration.Numeric { order; _ } ->
        pp_option state ~none:pp_total_keyword
          (fun state order ->
            pp_hovbox state ~indent (fun state ->
                pp_total_keyword state;
                pp_space state;
                pp_signature_totality_order state pp_int order))
          order

  and pp_signature_totality_order :
        'a.
        state -> (state -> 'a -> unit) -> 'a signature_totality_order -> unit
      =
   fun state ppv totality_order ->
    match totality_order with
    | Signature.Totality.Order.Argument { argument; _ } -> ppv state argument
    | Signature.Totality.Order.Lexical_ordering { arguments; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_braces state (fun state ->
                pp_list1 state ~sep:pp_space
                  (fun state -> pp_signature_totality_order state ppv)
                  arguments))
    | Signature.Totality.Order.Simultaneous_ordering { arguments; _ } ->
        pp_hovbox state ~indent (fun state ->
            pp_in_bracks state (fun state ->
                pp_list1 state ~sep:pp_space
                  (fun state -> pp_signature_totality_order state ppv)
                  arguments))

  and pp_signature_declaration state declaration =
    match declaration with
    | Signature.Declaration.CompTyp _
    | Signature.Declaration.CompCotyp _
    | Signature.Declaration.CompConst _
    | Signature.Declaration.CompDest _
    | Signature.Declaration.Theorem _
    | Signature.Declaration.Proof _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration declaration)
          Unsupported_non_recursive_declaration
    | Signature.Declaration.Typ { identifier; kind; _ } ->
        let id = fresh_lf_type_id state identifier in
        pp_hovbox state ~indent (fun state ->
            pp_lf_type_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_lf_kind state kind;
            pp_dot state);
        add_lf_type_constant state identifier ~id
    | Signature.Declaration.Const { identifier; typ; _ } ->
        let id = fresh_lf_term_id state identifier in
        pp_hovbox state ~indent (fun state ->
            pp_lf_term_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_lf_typ state typ;
            pp_dot state);
        add_lf_term_constant state identifier ~id
    | Signature.Declaration.Schema { identifier; schema; _ } ->
        let id = fresh_schema_id state identifier in
        pp_hovbox state ~indent (fun state ->
            pp_schema_keyword state;
            pp_non_breaking_space state;
            pp_schema_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_equal state;
            pp_space state;
            pp_schema state schema;
            pp_semicolon state);
        add_schema_constant state identifier ~id
    | Signature.Declaration.Recursive_declarations { declarations; _ } -> (
        iter_list1 state pre_add_declaration declarations;
        match group_recursive_declarations declarations with
        | List1.T (first, []) ->
            pp_vbox state ~indent:0 (fun state ->
                pp_grouped_declaration state ~prepend_and:false first);
            pp_semicolon state
        | List1.T (first, rest) ->
            pp_vbox state ~indent:0 (fun state ->
                pp_grouped_declaration state ~prepend_and:false first;
                pp_double_cut state;
                pp_list state ~sep:pp_double_cut
                  (fun state ->
                    pp_grouped_declaration state ~prepend_and:true)
                  rest);
            pp_semicolon state)
    | Signature.Declaration.CompTypAbbrev { identifier; kind; typ; _ } ->
        let id = fresh_computation_abbreviation_id state identifier in
        pp_hovbox state ~indent (fun state ->
            pp_typedef_keyword state;
            pp_non_breaking_space state;
            pp_computation_abbreviation_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_comp_kind state kind;
            pp_non_breaking_space state;
            pp_equal state;
            pp_space state;
            pp_comp_typ state typ;
            pp_semicolon state);
        add_abbreviation_computation_type_constant state identifier ~id
    | Signature.Declaration.Val { identifier; typ; expression; _ } ->
        let pp_typ_annotation state =
          pp_option state
            (fun state typ ->
              pp_colon state;
              pp_space state;
              pp_comp_typ state typ)
            typ
        in
        let id = fresh_computation_value_id state identifier in
        let pp_declaration state =
          pp_computation_program state ~id identifier;
          pp_typ_annotation state
        in
        pp_hovbox state ~indent (fun state ->
            pp_let_keyword state;
            pp_space state;
            pp_declaration state;
            pp_space state;
            pp_equal state;
            pp_space state;
            pp_comp_expression state expression;
            pp_semicolon state);
        add_program_constant state identifier ~id
    | Signature.Declaration.Module { identifier; entries; _ } ->
        let id = fresh_module_id state identifier in
        add_module state identifier ~id (fun state ->
            pp_module_keyword state;
            pp_non_breaking_space state;
            pp_module_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_equal state;
            pp_non_breaking_space state;
            pp_struct_keyword state;
            pp_break state 1 2;
            pp_vbox state ~indent:0 (fun state ->
                pp_module_entries state entries);
            pp_cut state;
            pp_end_keyword state)

  and pre_add_declaration state declaration =
    match declaration with
    | Signature.Declaration.Typ { identifier; _ } ->
        let id = fresh_lf_type_id state identifier in
        add_lf_type_constant state identifier ~id
    | Signature.Declaration.Const { identifier; _ } ->
        let id = fresh_lf_term_id state identifier in
        add_lf_term_constant state identifier ~id
    | Signature.Declaration.CompTyp
        { identifier; datatype_flavour = `Inductive; _ } ->
        let id = fresh_computation_inductive_type_id state identifier in
        add_inductive_computation_type_constant state identifier ~id
    | Signature.Declaration.CompTyp
        { identifier; datatype_flavour = `Stratified; _ } ->
        let id = fresh_computation_stratified_type_id state identifier in
        add_stratified_computation_type_constant state identifier ~id
    | Signature.Declaration.CompCotyp { identifier; _ } ->
        let id = fresh_computation_coinductive_type_id state identifier in
        add_coinductive_computation_type_constant state identifier ~id
    | Signature.Declaration.CompConst { identifier; _ } ->
        let id = fresh_computation_constructor_id state identifier in
        add_computation_term_constructor state identifier ~id
    | Signature.Declaration.CompDest { identifier; _ } ->
        let id = fresh_computation_destructor_id state identifier in
        add_computation_term_destructor state identifier ~id
    | Signature.Declaration.Schema { identifier; _ } ->
        let id = fresh_schema_id state identifier in
        add_schema_constant state identifier ~id
    | Signature.Declaration.Theorem { identifier; _ } ->
        let id = fresh_theorem_id state identifier in
        add_program_constant state identifier ~id
    | Signature.Declaration.Proof { identifier; _ } ->
        let id = fresh_proof_id state identifier in
        add_program_constant state identifier ~id
    | Signature.Declaration.CompTypAbbrev { identifier; _ } ->
        let id = fresh_computation_abbreviation_id state identifier in
        add_abbreviation_computation_type_constant state identifier ~id
    | Signature.Declaration.Val { identifier; _ } ->
        let id = fresh_computation_value_id state identifier in
        add_program_constant state identifier ~id
    | Signature.Declaration.Module { location; _ }
    | Signature.Declaration.Recursive_declarations { location; _ } ->
        Error.raise_at1 location Unsupported_recursive_declaration

  and pp_grouped_declaration state ~prepend_and declaration =
    let pp_and_opt state =
      if prepend_and then (
        pp_and_keyword state;
        pp_non_breaking_space state)
      else pp_nop state
    in
    match declaration with
    | `Lf_typ (identifier, kind, constants) ->
        let pp_constant state (identifier, typ) =
          let id =
            lookup_id state (Qualified_identifier.make_simple identifier)
          in
          pp_hovbox state ~indent (fun state ->
              pp_pipe state;
              pp_non_breaking_space state;
              pp_lf_term_constant state ~id identifier;
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_lf_typ state typ)
        in
        let pp_constants state =
          match constants with
          | [] -> pp_nop state
          | _ ->
              pp_cut state;
              pp_list state ~sep:pp_cut pp_constant constants
        in
        let id =
          lookup_id state (Qualified_identifier.make_simple identifier)
        in
        pp_hovbox state ~indent (fun state ->
            pp_and_opt state;
            pp_lf_keyword state;
            pp_non_breaking_space state;
            pp_lf_type_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_lf_kind state kind;
            pp_non_breaking_space state;
            pp_equal state);
        pp_constants state
    | `Inductive_comp_typ (identifier, kind, constants) ->
        let pp_constant state (identifier, typ) =
          let id =
            lookup_id state (Qualified_identifier.make_simple identifier)
          in
          pp_hovbox state ~indent (fun state ->
              pp_pipe state;
              pp_non_breaking_space state;
              pp_computation_constructor state ~id identifier;
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_comp_typ state typ)
        in
        let pp_constants state =
          match constants with
          | [] -> pp_nop state
          | _ ->
              pp_cut state;
              pp_list state ~sep:pp_cut pp_constant constants
        in
        let id =
          lookup_id state (Qualified_identifier.make_simple identifier)
        in
        pp_hovbox state ~indent (fun state ->
            pp_and_opt state;
            pp_inductive_keyword state;
            pp_non_breaking_space state;
            pp_computation_inductive_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_comp_kind state kind;
            pp_non_breaking_space state;
            pp_equal state);
        pp_constants state
    | `Stratified_comp_typ (identifier, kind, constants) ->
        let pp_constant state (identifier, typ) =
          let id =
            lookup_id state (Qualified_identifier.make_simple identifier)
          in
          pp_hovbox state ~indent (fun state ->
              pp_pipe state;
              pp_non_breaking_space state;
              pp_computation_constructor state ~id identifier;
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_comp_typ state typ)
        in
        let pp_constants state =
          match constants with
          | [] -> pp_nop state
          | _ ->
              pp_cut state;
              pp_list state ~sep:pp_cut pp_constant constants
        in
        let id =
          lookup_id state (Qualified_identifier.make_simple identifier)
        in
        pp_hovbox state ~indent (fun state ->
            pp_and_opt state;
            pp_stratified_keyword state;
            pp_non_breaking_space state;
            pp_computation_stratified_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_comp_kind state kind;
            pp_non_breaking_space state;
            pp_equal state);
        pp_constants state
    | `Coinductive_comp_typ (identifier, kind, constants) ->
        let pp_constant state (identifier, observation_typ, return_typ) =
          let id =
            lookup_id state (Qualified_identifier.make_simple identifier)
          in
          pp_hovbox state ~indent (fun state ->
              pp_pipe state;
              pp_non_breaking_space state;
              pp_computation_destructor state ~id identifier;
              pp_non_breaking_space state;
              pp_colon state;
              pp_space state;
              pp_comp_typ state observation_typ;
              pp_non_breaking_space state;
              pp_double_colon state;
              pp_space state;
              pp_comp_typ state return_typ)
        in
        let pp_constants state =
          match constants with
          | [] -> pp_nop state
          | _ ->
              pp_cut state;
              pp_list state ~sep:pp_cut pp_constant constants
        in
        let id =
          lookup_id state (Qualified_identifier.make_simple identifier)
        in
        pp_hovbox state ~indent (fun state ->
            pp_and_opt state;
            pp_coinductive_keyword state;
            pp_non_breaking_space state;
            pp_computation_coinductive_constant state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_comp_kind state kind;
            pp_non_breaking_space state;
            pp_equal state);
        pp_constants state
    | `Theorem (identifier, typ, order, body) ->
        let pp_order state =
          pp_option state
            (fun state order ->
              pp_cut state;
              pp_slash state;
              pp_non_breaking_space state;
              pp_signature_totality_declaration state order;
              pp_non_breaking_space state;
              pp_slash state)
            order
        in
        let id =
          lookup_id state (Qualified_identifier.make_simple identifier)
        in
        pp_hovbox state ~indent (fun state ->
            pp_and_opt state;
            pp_rec_keyword state;
            pp_non_breaking_space state;
            pp_computation_program state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_comp_typ state typ;
            pp_non_breaking_space state;
            pp_equal state);
        pp_order state;
        pp_cut state;
        pp_hovbox state ~indent (fun state -> pp_comp_expression state body)
    | `Proof (identifier, typ, order, body) ->
        let pp_order state =
          pp_option state
            (fun state order ->
              pp_cut state;
              pp_slash state;
              pp_non_breaking_space state;
              pp_signature_totality_declaration state order;
              pp_non_breaking_space state;
              pp_slash state)
            order
        in
        let id =
          lookup_id state (Qualified_identifier.make_simple identifier)
        in
        pp_hovbox state ~indent (fun state ->
            pp_and_opt state;
            pp_proof_keyword state;
            pp_non_breaking_space state;
            pp_computation_program state ~id identifier;
            pp_non_breaking_space state;
            pp_colon state;
            pp_space state;
            pp_comp_typ state typ;
            pp_non_breaking_space state;
            pp_equal state);
        pp_order state;
        pp_cut state;
        pp_hovbox state ~indent (fun state -> pp_harpoon_proof state body)

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
          (Synext.location_of_signature_declaration first_declaration)
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
          (Synext.location_of_signature_declaration first_declaration)
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
          (Synext.location_of_signature_declaration first_declaration)
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
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and render_markdown location content =
    try Omd.to_html (Omd.of_string content) with
    | cause ->
        Error.raise_at1 location
          (Error.composite_exception2 Markdown_rendering_error cause)

  and pp_module_entries state entries =
    let groups = group_signature_entries entries in
    let pp_group state = function
      | `Code group ->
          pp_list1 state ~sep:pp_double_cut pp_signature_entry group
      | `Comment group ->
          pp_inner_documentation_html state (fun state ->
              pp_list1 state ~sep:pp_double_cut pp_signature_entry group)
    in
    let pp_groups state groups =
      pp_list state ~sep:pp_double_cut pp_group groups
    in
    pp_vbox state ~indent:0 (fun state -> pp_groups state groups)

  and pp_signature_entry state entry =
    match entry with
    | Signature.Entry.Declaration { declaration; _ } ->
        pp_signature_declaration state declaration
    | Signature.Entry.Pragma { pragma; _ } ->
        pp_signature_pragma state pragma;
        apply_signature_pragma state pragma
    | Signature.Entry.Comment { location; content } ->
        let html = render_markdown location content in
        pp_string state html

  and pp_signature_file state signature_file =
    let { Signature.global_pragmas; entries; _ } = signature_file in
    let pp_global_pragmas_opt state =
      match global_pragmas with
      | [] -> pp_nop state
      | _ ->
          pp_preformatted_code_html state (fun state ->
              pp_list state ~sep:pp_cut pp_signature_global_pragma
                global_pragmas);
          pp_cut state
    in
    let groups = group_signature_entries entries in
    let pp_group state = function
      | `Code group ->
          pp_preformatted_code_html state (fun state ->
              pp_list1 state ~sep:pp_double_cut pp_signature_entry group)
      | `Comment group ->
          pp_toplevel_documentation_html state (fun state ->
              pp_list1 state ~sep:pp_double_cut pp_signature_entry group)
    in
    let pp_groups state groups =
      pp_list state ~sep:pp_double_cut pp_group groups
    in
    pp_vbox state ~indent:0 (fun state ->
        pp_global_pragmas_opt state;
        pp_groups state groups)

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

  and pp_signature state signature =
    pp_list1 state ~sep:pp_double_cut pp_signature_file signature
end

module Html_printer = struct
  include Html_printing_state
  include Make_html_printer (Html_printing_state)
end
