open Support
open Common
open Parenthesizer
open Beluga_syntax
open Synext

(* open Tyxml *)
[@@@warning "+A-4-44-32"]

(* https://github.com/ocaml/omd/tree/1.3.2 *)
(* view-source:https://hackage.haskell.org/package/base-4.17.0.0/docs/src/GHC.Base.html#%2B%2B *)
(* https://ocsigen.org/tyxml/latest/api/Html_sigs.T *)
(* https://ocamlpro.com/blog/2020_06_01_fr_tutoriel_format *)
(* https://highlightjs.readthedocs.io/en/latest/css-classes-reference.html *)

exception Unbound_identifier of Identifier.t

exception Unbound_qualified_identifier of Qualified_identifier.t

exception Markdown_rendering_error

exception Unsupported_non_recursive_declaration

exception Unsupported_recursive_declaration

module Persistent_html_state = struct
  type entry = { id : String.t }

  type state =
    { bindings : entry Binding_tree.t
    ; ids : String.Set.t
    ; max_suffix_by_id : Int.t String.Hamt.t
    }

  let empty =
    { bindings = Binding_tree.empty
    ; ids = String.Set.empty
    ; max_suffix_by_id = String.Hamt.empty
    }

  (** Regular expression for non-digit characters. *)
  let non_digit_regexp = Str.regexp "[^0-9]"

  (** [split_id s] is [(s', Option.Some n)] if [s = s' ^ string_of_int n],
      and [(s, Option.None)] if [s] does not end with digits. *)
  let split_id s =
    try
      let pos =
        Str.search_backward non_digit_regexp s (String.length s) + 1
      in
      (Str.string_before s pos, Some (int_of_string (Str.string_after s pos)))
    with
    | Not_found -> (s, Option.none)

  let fresh_id ?(prefix = "") identifier { ids; max_suffix_by_id; _ } =
    let id = Uri.pct_encode (prefix ^ Identifier.show identifier) in
    let base, suffix = split_id id in
    if String.Set.mem id ids then
      match String.Hamt.find_opt base max_suffix_by_id with
      | Option.Some max_suffix -> (id, base, Option.some (max_suffix + 1))
      | Option.None -> (id, base, Option.some 1)
    else (id, base, suffix)

  let add identifier ~id ~base suffix entry
      { bindings; ids; max_suffix_by_id } =
    let bindings' = Binding_tree.add_toplevel identifier entry bindings in
    let ids' = String.Set.add id ids in
    let max_suffix_by_id' =
      match suffix with
      | Option.Some suffix -> String.Hamt.add base suffix max_suffix_by_id
      | Option.None -> max_suffix_by_id
    in
    { bindings = bindings'
    ; ids = ids'
    ; max_suffix_by_id = max_suffix_by_id'
    }

  let add_fresh_id ?prefix identifier state =
    let id, base, suffix = fresh_id ?prefix identifier state in
    add identifier ~id ~base suffix (Obj.magic ()) state

  let lookup_toplevel identifier { bindings; _ } =
    Binding_tree.lookup_toplevel identifier bindings

  let lookup identifier { bindings; _ } =
    Binding_tree.lookup identifier bindings

  let lookup_toplevel_id identifier state =
    let id, _ = lookup_toplevel identifier state in
    id

  let lookup_id identifier state =
    let id, _ = lookup identifier state in
    id

  (* TODO: For modules, the first pass-through creates IDs as declarations
     get printed. Once the module is printed, backtrack to the state before
     printing the module, set the IDs set to the one after the first
     passthrough, then retraverse and add the declaration pairs.
     Alternatively, in the combinator for modules, keep track of added
     variables separately from namespace opens. *)
end

module type BELUGA_HTML = sig
  type state

  val pp_html_signature : Format.formatter -> signature -> unit
end

module Make (Html_state : sig
  type state

  val empty : state

  (* val open_module : Qualified_identifier.t -> state -> state *)

  val add_fresh_id : ?prefix:String.t -> Identifier.t -> state -> state

  val lookup_toplevel_id : Identifier.t -> state -> String.t

  val lookup_id : Qualified_identifier.t -> state -> String.t
end) : BELUGA_HTML with type state = Html_state.state = struct
  include Html_state

  type stag = Format.stag = ..

  (* Miscellaneous tags *)
  type stag +=
    | Keyword of { keyword : String.t }
    | Pragma of { pragma_keyword : String.t }
    | Toplevel_documentation_comment
    | Inner_documentation_comment
    | Preformatted_code

  (* Variables *)
  type stag +=
    | Lf_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Computation_variable

  (* Constant introductions *)
  type stag +=
    | Lf_type_constant of { id : String.t }
    | Lf_term_constant of { id : String.t }
    | Context_schema of { id : String.t }
    | Computation_stratified_type_constant of { id : String.t }
    | Computation_inductive_type_constant of { id : String.t }
    | Computation_abbreviation_type_constant of { id : String.t }
    | Computation_coinductive_type_constant of { id : String.t }
    | Computation_destructor of { id : String.t }
    | Computation_constructor of { id : String.t }

  (* Constant references *)
  type stag +=
    | Lf_type_constant_invoke of { id : String.t }
    | Lf_term_constant_invoke of { id : String.t }
    | Context_schema_invoke of { id : String.t }
    | Computation_inductive_type_constant_invoke of { id : String.t }
    | Computation_stratified_type_constant_invoke of { id : String.t }
    | Computation_abbreviation_type_constant_invoke of { id : String.t }
    | Computation_coinductive_type_constant_invoke of { id : String.t }
    | Computation_constructor_invoke of { id : String.t }
    | Computation_destructor_invoke of { id : String.t }

  let with_stag ppf stag f =
    Format.pp_open_stag ppf stag;
    let y = f ppf in
    Format.pp_close_stag ppf ();
    y

  let with_stag_identifier ppf stag identifier =
    with_stag ppf stag (fun ppf -> Identifier.pp ppf identifier)

  let with_stag_qualified_identifier ppf stag identifier =
    with_stag ppf stag (fun ppf -> Qualified_identifier.pp ppf identifier)

  let pp_keyword ppf keyword =
    with_stag ppf
      (Keyword { keyword })
      (fun ppf -> Format.pp_print_string ppf keyword)

  let with_pragma_stag _state pragma_keyword f ppf () =
    with_stag ppf (Pragma { pragma_keyword }) f

  let pp_toplevel_documentation_comment _state html ppf () =
    with_stag ppf Toplevel_documentation_comment (fun ppf ->
        Format.pp_print_string ppf html)

  let pp_inner_documentation_comment _state html ppf () =
    with_stag ppf Inner_documentation_comment (fun ppf ->
        Format.pp_print_string ppf html)

  let with_preformatted_code_stag _state f ppf () =
    with_stag ppf Preformatted_code f

  let pp_lf_variable _state ppf identifier =
    with_stag_identifier ppf Lf_variable identifier

  let pp_meta_variable _state ppf identifier =
    with_stag_identifier ppf Meta_variable identifier

  let pp_parameter_variable _state ppf identifier =
    with_stag_identifier ppf Parameter_variable identifier

  let pp_substitution_variable _state ppf identifier =
    with_stag_identifier ppf Substitution_variable identifier

  let pp_context_variable _state ppf identifier =
    with_stag_identifier ppf Context_variable identifier

  let pp_computation_variable _state ppf identifier =
    with_stag_identifier ppf Computation_variable identifier

  let pp_lf_type_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf (Lf_type_constant { id }) identifier

  let pp_lf_type_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Lf_type_constant_invoke { id })
      identifier

  let pp_lf_term_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf (Lf_term_constant { id }) identifier

  let pp_lf_term_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Lf_term_constant_invoke { id })
      identifier

  let pp_schema_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf (Context_schema { id }) identifier

  let pp_schema_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Context_schema_invoke { id })
      identifier

  let pp_computation_inductive_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf
      (Computation_inductive_type_constant { id })
      identifier

  let pp_computation_inductive_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Computation_inductive_type_constant_invoke { id })
      identifier

  let pp_computation_stratified_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf
      (Computation_stratified_type_constant { id })
      identifier

  let pp_computation_stratified_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Computation_stratified_type_constant_invoke { id })
      identifier

  let pp_computation_coinductive_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf
      (Computation_coinductive_type_constant { id })
      identifier

  let pp_computation_coinductive_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Computation_coinductive_type_constant_invoke { id })
      identifier

  let pp_computation_abbreviation_constant state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf
      (Computation_abbreviation_type_constant { id })
      identifier

  let pp_computation_abbreviation_constant_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Computation_abbreviation_type_constant_invoke { id })
      identifier

  let pp_computation_constructor state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf (Computation_constructor { id }) identifier

  let pp_computation_constructor_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Computation_constructor_invoke { id })
      identifier

  let pp_computation_destructor state ppf identifier =
    let id = lookup_toplevel_id identifier state in
    with_stag_identifier ppf (Computation_destructor { id }) identifier

  let pp_computation_destructor_invoke state ppf identifier =
    let id = lookup_id identifier state in
    with_stag_qualified_identifier ppf
      (Computation_destructor_invoke { id })
      identifier

  (** {1 Pretty-Printing LF Syntax} *)

  open Make_parenthesizer (Lf_precedence)

  let rec pp_lf_kind state ppf kind =
    let parent_precedence = precedence_of_lf_kind kind in
    match kind with
    | LF.Kind.Typ _ -> Format.fprintf ppf "type"
    | LF.Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative *)
        Format.fprintf ppf "@[<hov 2>%a →@ %a@]"
          (parenthesize_left_argument_right_associative_operator
             precedence_of_lf_typ ~parent_precedence (pp_lf_typ state))
          domain
          (parenthesize_right_argument_right_associative_operator
             precedence_of_lf_kind ~parent_precedence (pp_lf_kind state))
          range
    | LF.Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
        (* Pi-operators are weak prefix operators *)
        match (parameter_identifier, parameter_type) with
        | Option.Some parameter_identifier, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>{%a :@ %a}@ %a@]" Identifier.pp
              parameter_identifier (pp_lf_typ state) parameter_type
              (pp_lf_kind state) body
        | Option.Some parameter_identifier, Option.None ->
            Format.fprintf ppf "@[<hov 2>{%a}@ %a@]" Identifier.pp
              parameter_identifier (pp_lf_kind state) body
        | Option.None, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>{_ :@ %a}@ %a@]" (pp_lf_typ state)
              parameter_type (pp_lf_kind state) body
        | Option.None, Option.None ->
            Format.fprintf ppf "@[<hov 2>{_}@ %a@]" (pp_lf_kind state) body)

  and pp_lf_typ state ppf typ =
    let parent_precedence = precedence_of_lf_typ typ in
    match typ with
    | LF.Typ.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_lf_type_constant_invoke state)
            identifier
        else (pp_lf_type_constant_invoke state) ppf identifier
    | LF.Typ.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | LF.Typ.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | LF.Term.Application
                { applicand =
                    LF.Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_lf_typ
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:(pp_lf_typ state) ~pp_argument:(pp_lf_term state)
          ~parent_precedence ppf (applicand, arguments)
    | LF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<hov 2>%a →@ %a@]"
          (match domain with
          | LF.Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize (pp_lf_typ state)
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_lf_typ ~parent_precedence (pp_lf_typ state))
          domain
          (match range with
          | LF.Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize (pp_lf_typ state)
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_lf_typ ~parent_precedence (pp_lf_typ state))
          range
    | LF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<hov 2>%a@ ← %a@]"
          (match range with
          | LF.Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize (pp_lf_typ state)
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_lf_typ ~parent_precedence (pp_lf_typ state))
          range
          (match domain with
          | LF.Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize (pp_lf_typ state)
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_lf_typ ~parent_precedence (pp_lf_typ state))
          domain
    | LF.Typ.Pi { parameter_identifier; parameter_type; body; _ } -> (
        (* Pi-operators are weak prefix operators *)
        match (parameter_identifier, parameter_type) with
        | Option.Some parameter_identifier, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>{%a :@ %a}@ %a@]"
              (pp_lf_variable state) parameter_identifier (pp_lf_typ state)
              parameter_type (pp_lf_typ state) body
        | Option.Some parameter_identifier, Option.None ->
            Format.fprintf ppf "@[<hov 2>{%a}@ %a@]" (pp_lf_variable state)
              parameter_identifier (pp_lf_typ state) body
        | Option.None, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>{_ :@ %a}@ %a@]" (pp_lf_typ state)
              parameter_type (pp_lf_typ state) body
        | Option.None, Option.None ->
            Format.fprintf ppf "@[<hov 2>{_}@ %a@]" (pp_lf_typ state) body)

  and pp_lf_term state ppf term =
    let parent_precedence = precedence_of_lf_term term in
    match term with
    | LF.Term.Variable { identifier; _ } ->
        (pp_lf_variable state) ppf identifier
    | LF.Term.Constant { identifier; quoted = true; _ } ->
        Format.fprintf ppf "(%a)"
          (pp_lf_term_constant_invoke state)
          identifier
    | LF.Term.Constant { identifier; quoted = false; _ } ->
        (pp_lf_term_constant_invoke state) ppf identifier
    | LF.Term.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | LF.Term.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | LF.Term.Application
                { applicand =
                    LF.Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_lf_term
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:(pp_lf_term state) ~pp_argument:(pp_lf_term state)
          ~parent_precedence ppf (applicand, arguments)
    | LF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      -> (
        (* Lambdas are weak prefix operators, so the body of the lambda never
           requires parentheses *)
        match (parameter_identifier, parameter_type) with
        | Option.None, Option.None ->
            Format.fprintf ppf "@[<hov 2>\\_.@ %a@]" (pp_lf_term state) body
        | Option.None, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>\\_:%a.@ %a@]" (pp_lf_typ state)
              parameter_type (pp_lf_term state) body
        | Option.Some parameter_identifier, Option.None ->
            Format.fprintf ppf "@[<hov 2>\\%a.@ %a@]" (pp_lf_variable state)
              parameter_identifier (pp_lf_term state) body
        | Option.Some parameter_identifier, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>\\%a:%a.@ %a@]"
              (pp_lf_variable state) parameter_identifier (pp_lf_typ state)
              parameter_type (pp_lf_term state) body)
    | LF.Term.Wildcard _ -> Format.fprintf ppf "_"
    | LF.Term.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_lf_term ~parent_precedence (pp_lf_term state))
          term (pp_lf_typ state) typ

  (** {1 Pretty-Printing Contextual LF Syntax} *)

  open Make_parenthesizer (Clf_precedence)

  let rec pp_clf_typ state ppf typ =
    let parent_precedence = precedence_of_clf_typ typ in
    match typ with
    | CLF.Typ.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_lf_type_constant_invoke state)
            identifier
        else (pp_lf_type_constant_invoke state) ppf identifier
    | CLF.Typ.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | CLF.Typ.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | CLF.Term.Application
                { applicand =
                    CLF.Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_clf_typ
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:(pp_clf_typ state) ~pp_argument:(pp_clf_term state)
          ~parent_precedence ppf (applicand, arguments)
    | CLF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<hov 2>%a →@ %a@]"
          (match domain with
          | CLF.Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize (pp_clf_typ state)
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_clf_typ ~parent_precedence (pp_clf_typ state))
          domain
          (match range with
          | CLF.Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize (pp_clf_typ state)
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_clf_typ ~parent_precedence (pp_clf_typ state))
          range
    | CLF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<hov 2>%a@ ← %a@]"
          (match range with
          | CLF.Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize (pp_clf_typ state)
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_clf_typ ~parent_precedence (pp_clf_typ state))
          range
          (match domain with
          | CLF.Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize (pp_clf_typ state)
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_clf_typ ~parent_precedence (pp_clf_typ state))
          domain
    | CLF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
        (* Pi-operators are weak prefix operators *)
        Format.fprintf ppf "@[<hov 2>{%a :@ %a}@ %a@]"
          (fun ppf -> function
            | Option.Some parameter_identifier ->
                (pp_lf_variable state) ppf parameter_identifier
            | Option.None -> Format.fprintf ppf "_")
          parameter_identifier (pp_clf_typ state) parameter_type
          (pp_clf_typ state) body
    | CLF.Typ.Block { elements = `Unnamed typ; _ } ->
        Format.fprintf ppf "@[<hov 2>block (%a)]" (pp_clf_typ state) typ
    | CLF.Typ.Block { elements = `Record nts; _ } ->
        Format.fprintf ppf "@[<hov 2>block (%a)]"
          (List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
               Format.fprintf ppf "%a :@ %a" (pp_lf_variable state) i
                 (pp_clf_typ state) t))
          nts

  and pp_clf_term state ppf term =
    let parent_precedence = precedence_of_clf_term term in
    match term with
    | CLF.Term.Variable { identifier; _ } ->
        (pp_lf_variable state) ppf identifier
    | CLF.Term.Parameter_variable { identifier; _ } ->
        (pp_parameter_variable state) ppf identifier
    | CLF.Term.Substitution_variable { identifier; _ } ->
        (pp_substitution_variable state) ppf identifier
    | CLF.Term.Constant { identifier; quoted = true; _ } ->
        Format.fprintf ppf "(%a)"
          (pp_lf_term_constant_invoke state)
          identifier
    | CLF.Term.Constant { identifier; quoted = false; _ } ->
        (pp_lf_term_constant_invoke state) ppf identifier
    | CLF.Term.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | CLF.Term.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | CLF.Term.Application
                { applicand =
                    CLF.Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_clf_term
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:(pp_clf_term state) ~pp_argument:(pp_clf_term state)
          ~parent_precedence ppf (applicand, arguments)
    | CLF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      -> (
        (* Lambdas are weak prefix operators, so the body of a lambda does
           not need to be parenthesized *)
        match (parameter_identifier, parameter_type) with
        | Option.None, Option.None ->
            Format.fprintf ppf "@[<hov 2>\\_.@ %a@]" (pp_clf_term state) body
        | Option.None, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>\\_:%a.@ %a@]" (pp_clf_typ state)
              parameter_type (pp_clf_term state) body
        | Option.Some parameter_identifier, Option.None ->
            Format.fprintf ppf "@[<hov 2>\\%a.@ %a@]" (pp_lf_variable state)
              parameter_identifier (pp_clf_term state) body
        | Option.Some parameter_identifier, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>\\%a:%a.@ %a@]"
              (pp_lf_variable state) parameter_identifier (pp_clf_typ state)
              parameter_type (pp_clf_term state) body)
    | CLF.Term.Hole { variant = `Underscore; _ } -> Format.fprintf ppf "_"
    | CLF.Term.Hole { variant = `Unlabelled; _ } -> Format.fprintf ppf "?"
    | CLF.Term.Hole { variant = `Labelled label; _ } ->
        Format.fprintf ppf "?%a" Identifier.pp label
    | CLF.Term.Substitution { term; substitution; _ } ->
        (* Substitutions are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a[%a]@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence (pp_clf_term state))
          term
          (pp_clf_substitution state)
          substitution
    | CLF.Term.Tuple { terms; _ } ->
        Format.fprintf ppf "@[<hov 2><%a>@]"
          (List1.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
             (pp_clf_term state))
          terms
    | CLF.Term.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a.%d@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence (pp_clf_term state))
          term i
    | CLF.Term.Projection { term; projection = `By_identifier i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a.%a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence (pp_clf_term state))
          term Identifier.pp i
    | CLF.Term.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence (pp_clf_term state))
          term (pp_clf_typ state) typ

  and pp_clf_substitution state ppf substitution =
    match substitution with
    | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms = []; _ }
      ->
        Format.fprintf ppf "^"
    | { CLF.Substitution.head = CLF.Substitution.Head.Identity _
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "…"
    | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms; _ } ->
        Format.fprintf ppf "@[<hov 2>%a@]"
          (List.pp ~pp_sep:Format.comma (pp_clf_term state))
          terms
    | { CLF.Substitution.head = CLF.Substitution.Head.Identity _; terms; _ }
      ->
        Format.fprintf ppf "@[<hov 2>…,@ %a@]"
          (List.pp ~pp_sep:Format.comma (pp_clf_term state))
          terms
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a@]"
          (pp_substitution_variable state)
          identifier
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a[%a]@]"
          (pp_substitution_variable state)
          identifier
          (pp_clf_substitution state)
          closure
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a,@ %a@]"
          (pp_substitution_variable state)
          identifier
          (List.pp ~pp_sep:Format.comma (pp_clf_term state))
          terms
    | { CLF.Substitution.head =
          CLF.Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a[%a],@ %a@]"
          (pp_substitution_variable state)
          identifier
          (pp_clf_substitution state)
          closure
          (List.pp ~pp_sep:Format.comma (pp_clf_term state))
          terms

  and pp_clf_context state ppf context =
    let pp_typing ppf typing =
      match typing with
      | identifier, Option.None -> (pp_lf_variable state) ppf identifier
      | identifier, Option.Some typ ->
          Format.fprintf ppf "%a :@ %a" (pp_lf_variable state) identifier
            (pp_clf_typ state) typ
    in
    match context with
    | { CLF.Context.head = CLF.Context.Head.None _; bindings = []; _ } ->
        Format.fprintf ppf "^"
    | { CLF.Context.head = CLF.Context.Head.Hole _; bindings = []; _ } ->
        Format.fprintf ppf "_"
    | { CLF.Context.head =
          CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        (pp_context_variable state) ppf identifier
    | { CLF.Context.head = CLF.Context.Head.None _; bindings; _ } ->
        Format.fprintf ppf "@[<hov 2>%a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { CLF.Context.head = CLF.Context.Head.Hole _; bindings; _ } ->
        Format.fprintf ppf "@[<hov 2>_,@ %a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { CLF.Context.head =
          CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a,@ %a@]"
          (pp_context_variable state)
          identifier
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings

  let rec pp_clf_term_pattern state ppf term =
    let parent_precedence = precedence_of_clf_term_pattern term in
    match term with
    | CLF.Term.Pattern.Variable { identifier; _ } ->
        (pp_lf_variable state) ppf identifier
    | CLF.Term.Pattern.Parameter_variable { identifier; _ } ->
        (pp_parameter_variable state) ppf identifier
    | CLF.Term.Pattern.Substitution_variable { identifier; _ } ->
        (pp_substitution_variable state) ppf identifier
    | CLF.Term.Pattern.Constant { identifier; quoted = true; _ } ->
        Format.fprintf ppf "(%a)"
          (pp_lf_term_constant_invoke state)
          identifier
    | CLF.Term.Pattern.Constant { identifier; quoted = false; _ } ->
        (pp_lf_term_constant_invoke state) ppf identifier
    | CLF.Term.Pattern.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | CLF.Term.Pattern.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | CLF.Term.Pattern.Application
                { applicand =
                    CLF.Term.Pattern.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_clf_term_pattern
          ~precedence_of_argument:precedence_of_clf_term_pattern
          ~pp_applicand:(pp_clf_term_pattern state)
          ~pp_argument:(pp_clf_term_pattern state)
          ~parent_precedence ppf (applicand, arguments)
    | CLF.Term.Pattern.Abstraction
        { parameter_identifier; parameter_type; body; _ } -> (
        (* Lambdas are weak prefix operators, so the body of a lambda never
           requires parentheses. *)
        match (parameter_identifier, parameter_type) with
        | Option.None, Option.None ->
            Format.fprintf ppf "@[<hov 2>\\_.@ %a@]"
              (pp_clf_term_pattern state)
              body
        | Option.None, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>\\_:%a.@ %a@]" (pp_clf_typ state)
              parameter_type
              (pp_clf_term_pattern state)
              body
        | Option.Some parameter_identifier, Option.None ->
            Format.fprintf ppf "@[<hov 2>\\%a.@ %a@]" (pp_lf_variable state)
              parameter_identifier
              (pp_clf_term_pattern state)
              body
        | Option.Some parameter_identifier, Option.Some parameter_type ->
            Format.fprintf ppf "@[<hov 2>\\%a:%a.@ %a@]"
              (pp_lf_variable state) parameter_identifier (pp_clf_typ state)
              parameter_type
              (pp_clf_term_pattern state)
              body)
    | CLF.Term.Pattern.Wildcard _ -> Format.fprintf ppf "_"
    | CLF.Term.Pattern.Substitution { term; substitution; _ } ->
        Format.fprintf ppf "@[<hov 2>%a[%a]@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             (pp_clf_term_pattern state))
          term
          (pp_clf_substitution state)
          substitution
    | CLF.Term.Pattern.Tuple { terms; _ } ->
        Format.fprintf ppf "@[<hov 2><%a>@]"
          (List1.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
             (pp_clf_term_pattern state))
          terms
    | CLF.Term.Pattern.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a.%d@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             (pp_clf_term_pattern state))
          term i
    | CLF.Term.Pattern.Projection { term; projection = `By_identifier i; _ }
      ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a.%a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             (pp_clf_term_pattern state))
          term Identifier.pp i
    | CLF.Term.Pattern.Type_annotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             (pp_clf_term_pattern state))
          term (pp_clf_typ state) typ

  and pp_clf_substitution_pattern state ppf substitution_pattern =
    match substitution_pattern with
    | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "^"
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Identity _
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "…"
    | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a@]"
          (List.pp ~pp_sep:Format.comma (pp_clf_term_pattern state))
          terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Identity _
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>…,@ %a@]"
          (List.pp ~pp_sep:Format.comma (pp_clf_term_pattern state))
          terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a@]"
          (pp_substitution_variable state)
          identifier
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a[%a]@]"
          (pp_substitution_variable state)
          identifier
          (pp_clf_substitution state)
          closure
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a,@ %a@]"
          (pp_substitution_variable state)
          identifier
          (List.pp ~pp_sep:Format.comma (pp_clf_term_pattern state))
          terms
    | { CLF.Substitution.Pattern.head =
          CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a[%a],@ %a@]"
          (pp_substitution_variable state)
          identifier
          (pp_clf_substitution state)
          closure
          (List.pp ~pp_sep:Format.comma (pp_clf_term_pattern state))
          terms

  and pp_clf_context_pattern state ppf context_pattern =
    let pp_typing ppf (i, t) =
      Format.fprintf ppf "%a :@ %a" (pp_lf_variable state) i
        (pp_clf_typ state) t
    in
    match context_pattern with
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
      ; bindings = []
      ; _
      } ->
        Format.fprintf ppf "^"
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
      ; bindings = []
      ; _
      } ->
        Format.fprintf ppf "_"
    | { CLF.Context.Pattern.head =
          CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        (pp_context_variable state) ppf identifier
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
      ; bindings
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
      ; bindings
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>_,@ %a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { CLF.Context.Pattern.head =
          CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        Format.fprintf ppf "@[<hov 2>%a,@ %a@]"
          (pp_context_variable state)
          identifier
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings

  (** {1 Pretty-Printing Meta-Level Syntax} *)

  open Make_parenthesizer (Meta_precedence)

  let rec pp_meta_typ state ppf typ =
    match typ with
    | Meta.Typ.Context_schema { schema; _ } -> (pp_schema state) ppf schema
    | Meta.Typ.Contextual_typ { context; typ; _ } ->
        Format.fprintf ppf "@[<hov 2>(%a ⊢@ %a)@]" (pp_clf_context state)
          context (pp_clf_typ state) typ
    | Meta.Typ.Parameter_typ { context; typ; _ } ->
        Format.fprintf ppf "@[<hov 2>#(%a ⊢@ %a)@]" (pp_clf_context state)
          context (pp_clf_typ state) typ
    | Meta.Typ.Plain_substitution_typ { domain; range; _ } ->
        Format.fprintf ppf "@[<hov 2>$(%a ⊢@ %a)@]" (pp_clf_context state)
          domain (pp_clf_context state) range
    | Meta.Typ.Renaming_substitution_typ { domain; range; _ } ->
        Format.fprintf ppf "@[<hov 2>$(%a ⊢#@ %a)@]" (pp_clf_context state)
          domain (pp_clf_context state) range

  and pp_meta_object state ppf object_ =
    match object_ with
    | Meta.Object.Context { context; _ } ->
        Format.fprintf ppf "@[[%a]@]" (pp_clf_context state) context
    | Meta.Object.Contextual_term { context; term; _ } ->
        Format.fprintf ppf "@[<hov 2>[%a ⊢@ %a]@]" (pp_clf_context state)
          context (pp_clf_term state) term
    | Meta.Object.Plain_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<hov 2>$[%a ⊢@ %a]@]" (pp_clf_context state)
          domain
          (pp_clf_substitution state)
          range
    | Meta.Object.Renaming_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<hov 2>$[%a ⊢#@ %a]@]" (pp_clf_context state)
          domain
          (pp_clf_substitution state)
          range

  and pp_meta_pattern state ppf pattern =
    match pattern with
    | Meta.Pattern.Context { context; _ } ->
        Format.fprintf ppf "@[[%a]@]" (pp_clf_context_pattern state) context
    | Meta.Pattern.Contextual_term { context; term; _ } ->
        Format.fprintf ppf "@[<hov 2>[%a ⊢@ %a]@]"
          (pp_clf_context_pattern state)
          context
          (pp_clf_term_pattern state)
          term
    | Meta.Pattern.Plain_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<hov 2>$[%a ⊢@ %a]@]"
          (pp_clf_context_pattern state)
          domain
          (pp_clf_substitution_pattern state)
          range
    | Meta.Pattern.Renaming_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<hov 2>$[%a ⊢#@ %a]@]"
          (pp_clf_context_pattern state)
          domain
          (pp_clf_substitution_pattern state)
          range

  and pp_schema state ppf schema =
    let parent_precedence = precedence_of_schema schema in
    let pp_bindings =
      List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
          Format.fprintf ppf "@[%a :@ %a@]" (pp_lf_variable state) i
            (pp_clf_typ state) t)
    in
    match schema with
    | Meta.Schema.Constant { identifier; _ } ->
        (pp_schema_constant_invoke state) ppf identifier
    | Meta.Schema.Alternation { schemas; _ } ->
        List2.pp
          ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ + ")
          (parenthesize_term_of_lesser_than_or_equal_precedence
             precedence_of_schema ~parent_precedence (pp_schema state))
          ppf schemas
    | Meta.Schema.Element { some = Option.None; block = `Unnamed t; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a@]" pp_keyword "block"
          (pp_clf_typ state) t
    | Meta.Schema.Element { some = Option.None; block = `Record bindings; _ }
      ->
        Format.fprintf ppf "@[<hov 2>%a (%a)@]" pp_keyword "block"
          pp_bindings bindings
    | Meta.Schema.Element
        { some = Option.Some some_bindings; block = `Unnamed t; _ } ->
        Format.fprintf ppf "@[<hov 2>%a [%a]@ %a %a@]" pp_keyword "some"
          pp_bindings some_bindings pp_keyword "block" (pp_clf_typ state) t
    | Meta.Schema.Element
        { some = Option.Some some_bindings
        ; block = `Record block_bindings
        ; _
        } ->
        Format.fprintf ppf "@[<hov 2>%a [%a]@ %a (%a)@]" pp_keyword "some"
          pp_bindings some_bindings pp_keyword "block" pp_bindings
          block_bindings

  (** {1 Pretty-Printing Computation-Level Syntax} *)

  open Make_parenthesizer (Comp_precedence)

  (** [is_atomic_pattern pattern] is [true] if and only if [pattern] is an
      atomic pattern as defined in {!Parser}, meaning that it never requires
      additional enclosing parentheses during printing to avoid ambiguities. *)
  let is_atomic_pattern pattern =
    match pattern with
    | Comp.Pattern.Variable _
    | Comp.Pattern.Constant _
    | Comp.Pattern.MetaObject _
    | Comp.Pattern.Tuple _
    | Comp.Pattern.Wildcard _ ->
        true
    | _ -> false

  let is_atomic_copattern copattern =
    match copattern with
    | Comp.Copattern.Observation _ -> true
    | Comp.Copattern.Pattern pattern -> is_atomic_pattern pattern

  let rec pp_comp_kind state ppf kind =
    let[@warning "-26"] parent_precedence = precedence_of_comp_kind kind in
    match kind with
    | Comp.Kind.Ctype _ -> pp_keyword ppf "ctype"
    | Comp.Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative *)
        Format.fprintf ppf "@[<hov 2>%a →@ %a@]" (pp_meta_typ state) domain
          (pp_comp_kind state) range
    | Comp.Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
        (* Pi-operators are weak prefix operators *)
        match parameter_identifier with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>{_ :@ %a}@ %a@]" (pp_meta_typ state)
              parameter_type (pp_comp_kind state) body
        | Option.Some parameter_identifier ->
            Format.fprintf ppf "@[<hov 2>{%a :@ %a}@ %a@]"
              (pp_meta_variable state) parameter_identifier
              (pp_meta_typ state) parameter_type (pp_comp_kind state) body)

  and pp_comp_typ state ppf typ =
    let parent_precedence = precedence_of_comp_typ typ in
    match typ with
    | Comp.Typ.Constant
        { identifier; operator; quoted; variant = `Coinductive; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_computation_coinductive_constant_invoke state)
            identifier
        else
          (pp_computation_coinductive_constant_invoke state) ppf identifier
    | Comp.Typ.Constant
        { identifier; operator; quoted; variant = `Inductive; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_computation_inductive_constant_invoke state)
            identifier
        else (pp_computation_inductive_constant_invoke state) ppf identifier
    | Comp.Typ.Constant
        { identifier; operator; quoted; variant = `Abbreviation; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_computation_abbreviation_constant_invoke state)
            identifier
        else
          (pp_computation_abbreviation_constant_invoke state) ppf identifier
    | Comp.Typ.Constant
        { identifier; operator; quoted; variant = `Stratified; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_computation_stratified_constant_invoke state)
            identifier
        else (pp_computation_stratified_constant_invoke state) ppf identifier
    | Comp.Typ.Pi { parameter_identifier; plicity; parameter_type; body; _ }
      -> (
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier parameter_type ppf parameter_identifier =
          match (parameter_identifier, parameter_type) with
          | Option.Some parameter_identifier, _ ->
              (pp_meta_variable state) ppf parameter_identifier
          | ( Option.None
            , (Meta.Typ.Context_schema _ | Meta.Typ.Contextual_typ _) ) ->
              Format.pp_print_string ppf "_"
          | Option.None, Meta.Typ.Parameter_typ _ ->
              Format.pp_print_string ppf "#_"
          | ( Option.None
            , ( Meta.Typ.Plain_substitution_typ _
              | Meta.Typ.Renaming_substitution_typ _ ) ) ->
              Format.pp_print_string ppf "$_"
        in
        match plicity with
        | Plicity.Implicit ->
            Format.fprintf ppf "@[<hov 2>(%a :@ %a)@ %a@]"
              (pp_parameter_identifier parameter_type)
              parameter_identifier (pp_meta_typ state) parameter_type
              (pp_comp_typ state) body
        | Plicity.Explicit ->
            Format.fprintf ppf "@[<hov 2>{%a :@ %a}@ %a@]"
              (pp_parameter_identifier parameter_type)
              parameter_identifier (pp_meta_typ state) parameter_type
              (pp_comp_typ state) body)
    | Comp.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows *)
        Format.fprintf ppf "@[<hov 2>%a →@ %a@]"
          (match domain with
          | Comp.Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize (pp_comp_typ state)
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          domain
          (match range with
          | Comp.Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize (pp_comp_typ state)
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          range
    | Comp.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows *)
        Format.fprintf ppf "@[<hov 2>%a@ ← %a@]"
          (match range with
          | Comp.Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize (pp_comp_typ state)
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          range
          (match domain with
          | Comp.Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize (pp_comp_typ state)
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          domain
    | Comp.Typ.Cross { types; _ } ->
        List2.pp
          ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ * ")
          (parenthesize_term_of_lesser_than_or_equal_precedence
             precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          ppf types
    | Comp.Typ.Box { meta_type; _ } -> (pp_meta_typ state) ppf meta_type
    | Comp.Typ.Application { applicand; arguments; _ } -> (
        (* Override the behaviour of printing applications since the
           arguments are meta-object, which need no parentheses. *)
        match applicand with
        | Comp.Typ.Application
            { applicand =
                Comp.Typ.Constant { operator; quoted = false; _ } as
                applicand
            ; _
            } -> (
            match Operator.fixity operator with
            | Fixity.Prefix ->
                Format.fprintf ppf "@[<hov 2>%a@ %a@]" (pp_comp_typ state)
                  applicand
                  (List1.pp ~pp_sep:Format.pp_print_space
                     (pp_meta_object state))
                  arguments
            | Fixity.Infix ->
                assert (
                  List1.compare_length_with arguments 2
                  = 0
                    (* Infix operators must be applied with exactly two
                       arguments. *));
                let[@warning "-8"] (List1.T
                                     (left_argument, [ right_argument ])) =
                  arguments
                in
                Format.fprintf ppf "@[<hov 2>%a@ %a@ %a@]"
                  (pp_meta_object state) left_argument (pp_comp_typ state)
                  applicand (pp_meta_object state) right_argument
            | Fixity.Postfix ->
                assert (
                  List1.compare_length_with arguments 1
                  = 0
                    (* Postfix operators must be applied with exactly one
                       argument. *));
                let[@warning "-8"] (List1.T (argument, [])) = arguments in
                Format.fprintf ppf "@[<hov 2>%a@ %a@]" (pp_meta_object state)
                  argument (pp_comp_typ state) applicand)
        | _ ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@]"
              (parenthesize_term_of_lesser_than_or_equal_precedence
                 precedence_of_comp_typ ~parent_precedence
                 (pp_comp_typ state))
              applicand
              (List1.pp ~pp_sep:Format.pp_print_space (pp_meta_object state))
              arguments)

  and pp_comp_expression state ppf expression =
    let parent_precedence = precedence_of_comp_expression expression in
    match expression with
    | Comp.Expression.Variable { identifier; _ } ->
        (pp_computation_variable state) ppf identifier
    | Comp.Expression.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)"
            (pp_computation_constructor_invoke state)
            identifier
        else (pp_computation_constructor_invoke state) ppf identifier
    | Comp.Expression.Fn { parameters; body; _ } ->
        let pp_parameter ppf parameter =
          match parameter with
          | Option.None -> Format.pp_print_string ppf "_"
          | Option.Some parameter ->
              (pp_computation_variable state) ppf parameter
        in
        Format.fprintf ppf "@[<hov 2>%a %a ⇒@ %a@]" pp_keyword "fn"
          (List1.pp ~pp_sep:Format.pp_print_space pp_parameter)
          parameters
          (pp_comp_expression state)
          body
    | Comp.Expression.Mlam { parameters; body; _ } ->
        let pp_parameter ppf (parameter, modifier) =
          match (parameter, modifier) with
          | Option.Some parameter, (`Plain | `Hash | `Dollar) ->
              (* The hash or dollar prefix is part of [parameter] *)
              (pp_meta_variable state) ppf parameter
          | Option.None, `Plain -> Format.pp_print_string ppf "_"
          | Option.None, `Hash -> Format.pp_print_string ppf "#_"
          | Option.None, `Dollar -> Format.pp_print_string ppf "$_"
        in
        let pp_parameters =
          List1.pp ~pp_sep:Format.pp_print_space pp_parameter
        in
        Format.fprintf ppf "@[<hov 2>%a %a ⇒@ %a@]" pp_keyword "mlam"
          pp_parameters parameters
          (pp_comp_expression state)
          body
    | Comp.Expression.Fun { branches; _ } ->
        let pp_branch_pattern ppf copattern =
          if is_atomic_copattern copattern then
            (pp_comp_copattern state) ppf copattern
          else parenthesize (pp_comp_copattern state) ppf copattern
        in
        let pp_branch_patterns =
          List1.pp ~pp_sep:Format.pp_print_space pp_branch_pattern
        in
        let pp_branch ppf (patterns, expression) =
          Format.fprintf ppf "@[<hov 2>|@ %a ⇒@ %a@]" pp_branch_patterns
            patterns
            (pp_comp_expression state)
            expression
        in
        let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
        Format.fprintf ppf "@[<v 0>%a@;%a@]" pp_keyword "fun" pp_branches
          branches
    | Comp.Expression.Let { pattern; scrutinee; body; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a =@ %a@ %a@ %a@]" pp_keyword "let"
          (pp_comp_pattern state) pattern pp_keyword "in"
          (pp_comp_expression state)
          scrutinee
          (pp_comp_expression state)
          body
    | Comp.Expression.Box { meta_object; _ } ->
        (pp_meta_object state) ppf meta_object
    | Comp.Expression.Impossible { scrutinee; _ } ->
        (* [impossible (impossible (...))] is right-associative *)
        Format.fprintf ppf "@[<hov 2>%a@ %a@]" pp_keyword "impossible"
          (parenthesize_right_argument_right_associative_operator
             precedence_of_comp_expression ~parent_precedence
             (pp_comp_expression state))
          scrutinee
    | Comp.Expression.Case { scrutinee; check_coverage; branches; _ } ->
        let pp_branch ppf (pattern, expression) =
          Format.fprintf ppf "@[<hov 2>|@ %a ⇒@ %a@]" (pp_comp_pattern state)
            pattern
            (pp_comp_expression state)
            expression
        in
        let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
        if check_coverage then
          Format.fprintf ppf "@[<v 0>@[<hov 2>%a@ %a@ %a@ %a@]@,%a@]"
            pp_keyword "case"
            (pp_comp_expression state)
            scrutinee
            (with_pragma_stag state "not" (fun ppf ->
                 Format.pp_print_string ppf "--not"))
            () pp_keyword "of" pp_branches branches
        else
          Format.fprintf ppf "@[<v 0>@[%a@ %a@ %a@]@,%a@]" pp_keyword "case"
            (pp_comp_expression state)
            scrutinee pp_keyword "of" pp_branches branches
    | Comp.Expression.Tuple { elements; _ } ->
        Format.fprintf ppf "@[<hov 2>(%a)@]"
          (List2.pp ~pp_sep:Format.comma (pp_comp_expression state))
          elements
    | Comp.Expression.Hole { label; _ } -> (
        match label with
        | Option.None -> Format.pp_print_string ppf "?"
        | Option.Some label -> Format.fprintf ppf "?%a" Identifier.pp label)
    | Comp.Expression.BoxHole _ -> Format.pp_print_string ppf "_"
    | Comp.Expression.Observation { scrutinee; destructor; _ } ->
        (* Observations are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a@ .%a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_comp_expression ~parent_precedence
             (pp_comp_expression state))
          scrutinee
          (pp_computation_destructor_invoke state)
          destructor
    | Comp.Expression.Type_annotated { expression; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<hov 2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_comp_expression ~parent_precedence
             (pp_comp_expression state))
          expression
          (parenthesize_right_argument_left_associative_operator
             precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          typ
    | Comp.Expression.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Comp.Expression.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Comp.Expression.Application
                { applicand =
                    Comp.Expression.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_comp_expression
          ~precedence_of_argument:precedence_of_comp_expression
          ~pp_applicand:(pp_comp_expression state)
          ~pp_argument:(pp_comp_expression state)
          ~parent_precedence ppf (applicand, arguments)

  and pp_comp_pattern state ppf pattern =
    let parent_precedence = precedence_of_comp_pattern pattern in
    match pattern with
    | Comp.Pattern.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Comp.Pattern.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
        else Qualified_identifier.pp ppf identifier
    | Comp.Pattern.MetaObject { meta_pattern; _ } ->
        (pp_meta_pattern state) ppf meta_pattern
    | Comp.Pattern.Tuple { elements; _ } ->
        Format.fprintf ppf "@[<hov 2>(%a)@]"
          (List2.pp ~pp_sep:Format.comma (pp_comp_pattern state))
          elements
    | Comp.Pattern.Type_annotated { pattern; typ; _ } ->
        (* The type annotation operator is left-associative *)
        Format.fprintf ppf "@[<hov 2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_comp_pattern ~parent_precedence
             (pp_comp_pattern state))
          pattern
          (parenthesize_right_argument_left_associative_operator
             precedence_of_comp_typ ~parent_precedence (pp_comp_typ state))
          typ
    | Comp.Pattern.MetaTypeAnnotated
        { annotation_identifier; annotation_type; body; _ } ->
        Format.fprintf ppf "@[<hov 2>{%a :@ %a}@ %a@]" Identifier.pp
          annotation_identifier (pp_meta_typ state) annotation_type
          (pp_comp_pattern state) body
    | Comp.Pattern.Wildcard _ -> Format.pp_print_string ppf "_"
    | Comp.Pattern.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Comp.Pattern.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Comp.Pattern.Application
                { applicand =
                    Comp.Pattern.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_comp_pattern
          ~precedence_of_argument:precedence_of_comp_pattern
          ~pp_applicand:(pp_comp_pattern state)
          ~pp_argument:(pp_comp_pattern state) ~parent_precedence ppf
          (applicand, arguments)

  and pp_comp_copattern state ppf copattern =
    let[@warning "-26"] parent_precedence = precedence_of_comp_copattern in
    match copattern with
    | Comp.Copattern.Observation { observation; arguments; _ } -> (
        match List1.of_list arguments with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>.%a@]" Qualified_identifier.pp
              observation
        | Option.Some arguments ->
            Format.fprintf ppf "@[<hov 2>.%a@ %a@]" Qualified_identifier.pp
              observation
              (List1.pp ~pp_sep:Format.pp_print_space (pp_comp_pattern state))
              arguments)
    | Comp.Copattern.Pattern pattern -> (pp_comp_pattern state) ppf pattern

  (** {1 Pretty-Printing Harpoon Syntax} *)

  let rec pp_harpoon_proof state ppf proof =
    match proof with
    | Harpoon.Proof.Incomplete { label; _ } -> (
        match label with
        | Option.None -> Format.pp_print_string ppf "?"
        | Option.Some label -> Identifier.pp ppf label)
    | Harpoon.Proof.Command { command; body; _ } ->
        Format.fprintf ppf "@[%a@];@,%a"
          (pp_harpoon_command state)
          command (pp_harpoon_proof state) body
    | Harpoon.Proof.Directive { directive; _ } ->
        (pp_harpoon_directive state) ppf directive

  and pp_harpoon_command state ppf command =
    match command with
    | Harpoon.Command.By { expression; assignee; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a@ %a %a@]" pp_keyword "by"
          (pp_comp_expression state)
          expression pp_keyword "as" Identifier.pp assignee
    | Harpoon.Command.Unbox
        { expression; assignee; modifier = Option.None; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a@ %a %a@]" pp_keyword "unbox"
          (pp_comp_expression state)
          expression pp_keyword "as" Identifier.pp assignee
    | Harpoon.Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a@ %a %a@]" pp_keyword "strengthen"
          (pp_comp_expression state)
          expression pp_keyword "as" Identifier.pp assignee

  and pp_harpoon_directive state ppf directive =
    match directive with
    | Harpoon.Directive.Intros { hypothetical; _ } ->
        Format.fprintf ppf "@[<v 0>%a@,%a@]" pp_keyword "intros"
          (pp_harpoon_hypothetical state)
          hypothetical
    | Harpoon.Directive.Solve { solution; _ } ->
        Format.fprintf ppf "@[<hov 2>%a@ %a@]" pp_keyword "solve"
          (pp_comp_expression state)
          solution
    | Harpoon.Directive.Split { scrutinee; branches; _ } ->
        Format.fprintf ppf "@[%a@ %a as@]@,@[<v 0>%a@]" pp_keyword "split"
          (pp_comp_expression state)
          scrutinee
          (List1.pp ~pp_sep:Format.pp_print_cut
             (pp_harpoon_split_branch state))
          branches
    | Harpoon.Directive.Impossible { scrutinee; _ } ->
        Format.fprintf ppf "@[%a@ @[%a@]@]" pp_keyword "impossible"
          (pp_comp_expression state)
          scrutinee
    | Harpoon.Directive.Suffices { scrutinee; branches; _ } ->
        Format.fprintf ppf "@[<v 0>@[<hov 2>%a %a@ %a@] %a@,@[<v 0>%a@]@]"
          pp_keyword "suffices" pp_keyword "by"
          (pp_comp_expression state)
          scrutinee pp_keyword "toshow"
          (List.pp ~pp_sep:Format.pp_print_cut
             (pp_harpoon_suffices_branch state))
          branches

  and pp_harpoon_split_branch state ppf branch =
    let { Harpoon.Split_branch.label; body; _ } = branch in
    Format.fprintf ppf "@[<v 0>%a %a:@,%a@]" pp_keyword "case"
      (pp_harpoon_split_branch_label state)
      label
      (pp_harpoon_hypothetical state)
      body

  and pp_harpoon_split_branch_label _state ppf label =
    match label with
    | Harpoon.Split_branch.Label.Constant { identifier; _ } ->
        Qualified_identifier.pp ppf identifier
    | Harpoon.Split_branch.Label.Bound_variable _ ->
        Format.fprintf ppf "%a %a" pp_keyword "head" pp_keyword "variable"
    | Harpoon.Split_branch.Label.Empty_context _ ->
        Format.fprintf ppf "%a %a" pp_keyword "empty" pp_keyword "context"
    | Harpoon.Split_branch.Label.Extended_context { schema_element; _ } ->
        Format.fprintf ppf "%a %a %d" pp_keyword "extended" pp_keyword "by"
          schema_element
    | Harpoon.Split_branch.Label.Parameter_variable
        { schema_element; projection; _ } -> (
        match projection with
        | Option.None -> Format.fprintf ppf "%d" schema_element
        | Option.Some projection ->
            Format.fprintf ppf "%d.%d" schema_element projection)

  and pp_harpoon_suffices_branch state ppf branch =
    let { Harpoon.Suffices_branch.goal; proof; _ } = branch in
    Format.fprintf ppf "@[<v 2>@[%a@] {@,@[<v 0>%a@]@]@,}"
      (pp_comp_typ state) goal (pp_harpoon_proof state) proof

  and pp_harpoon_hypothetical state ppf hypothetical =
    let { Harpoon.Hypothetical.meta_context =
            { Meta.Context.bindings = meta_context_bindings; _ }
        ; comp_context = { Comp.Context.bindings = comp_context_bindings; _ }
        ; proof
        ; _
        } =
      hypothetical
    in
    Format.fprintf ppf
      "@[<v 0>{ @[<hv>%a@]@,| @[<hv>%a@]@,; @[<v 0>%a@]@,}@]"
      (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
           Format.fprintf ppf "@[<hov 2>%a :@ %a@]" Identifier.pp i
             (pp_meta_typ state) t))
      meta_context_bindings
      (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
           Format.fprintf ppf "@[<hov 2>%a :@ %a@]" Identifier.pp i
             (pp_comp_typ state) t))
      comp_context_bindings (pp_harpoon_proof state) proof

  (** {1 Pretty-Printing Signature Syntax} *)

  let pp_associativity ppf = function
    | Associativity.Left_associative -> Format.pp_print_string ppf "left"
    | Associativity.Right_associative -> Format.pp_print_string ppf "right"
    | Associativity.Non_associative -> Format.pp_print_string ppf "none"

  let rec pp_signature_pragma state ppf pragma =
    match pragma with
    | Signature.Pragma.Name
        { constant; meta_variable_base; computation_variable_base; _ } ->
        (match computation_variable_base with
        | Option.None ->
            (with_pragma_stag state "name" (fun ppf ->
                 Format.fprintf ppf "@[<hov 2>--name@ %a@ %a.@]"
                   Qualified_identifier.pp constant Identifier.pp
                   meta_variable_base))
              ppf ()
        | Option.Some computation_variable_base ->
            with_pragma_stag state "name"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--name@ %a@ %a@ %a.@]"
                  Qualified_identifier.pp constant Identifier.pp
                  meta_variable_base Identifier.pp computation_variable_base)
              ppf ());
        state
    | Signature.Pragma.Default_associativity { associativity; _ } ->
        with_pragma_stag state "assoc"
          (fun ppf ->
            Format.fprintf ppf "@[<hov 2>--assoc@ %a.@]" pp_associativity
              associativity)
          ppf ();
        state
    | Signature.Pragma.Prefix_fixity { constant; precedence; _ } ->
        (match precedence with
        | Option.None ->
            with_pragma_stag state "prefix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--prefix@ %a.@]"
                  Qualified_identifier.pp constant)
              ppf ()
        | Option.Some precedence ->
            with_pragma_stag state "prefix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--prefix@ %a@ %i.@]"
                  Qualified_identifier.pp constant precedence)
              ppf ());
        state
    | Signature.Pragma.Infix_fixity
        { constant; precedence; associativity; _ } ->
        (match (precedence, associativity) with
        | Option.Some precedence, Option.Some associativity ->
            with_pragma_stag state "infix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--infix@ %a@ %i@ %a.@]"
                  Qualified_identifier.pp constant precedence
                  pp_associativity associativity)
              ppf ()
        | Option.Some precedence, Option.None ->
            with_pragma_stag state "infix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--infix@ %a@ %i.@]"
                  Qualified_identifier.pp constant precedence)
              ppf ()
        | Option.None, Option.Some associativity ->
            with_pragma_stag state "infix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--infix@ %a@ %a.@]"
                  Qualified_identifier.pp constant pp_associativity
                  associativity)
              ppf ()
        | Option.None, Option.None ->
            with_pragma_stag state "infix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--infix@ %a.@]"
                  Qualified_identifier.pp constant)
              ppf ());
        state
    | Signature.Pragma.Postfix_fixity { constant; precedence; _ } ->
        (match precedence with
        | Option.None ->
            with_pragma_stag state "postfix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--postfix@ %a.@]"
                  Qualified_identifier.pp constant)
              ppf ()
        | Option.Some precedence ->
            with_pragma_stag state "postfix"
              (fun ppf ->
                Format.fprintf ppf "@[<hov 2>--postfix@ %a@ %i.@]"
                  Qualified_identifier.pp constant precedence)
              ppf ());
        state
    | Signature.Pragma.Not _ ->
        with_pragma_stag state "not"
          (fun ppf -> Format.pp_print_string ppf "--not")
          ppf ();
        state
    | Signature.Pragma.Open_module { module_identifier; _ } ->
        with_pragma_stag state "open"
          (fun ppf ->
            Format.fprintf ppf "@[<hov 2>--open@ %a.@]"
              Qualified_identifier.pp module_identifier)
          ppf ();
        state (* TODO: Open the module *)
    | Signature.Pragma.Abbreviation { module_identifier; abbreviation; _ } ->
        with_pragma_stag state "abbrev"
          (fun ppf ->
            Format.fprintf ppf "@[<hov 2>--abbrev@ %a@ %a.@]"
              Qualified_identifier.pp module_identifier Identifier.pp
              abbreviation)
          ppf ();
        state (* TODO: Add the abbreviation *)

  and pp_signature_global_pragma state ppf global_pragma =
    match global_pragma with
    | Signature.Global_pragma.No_strengthening _ ->
        with_pragma_stag state "nostrengthen"
          (fun ppf -> Format.pp_print_string ppf "--nostrengthen")
          ppf ()
    | Signature.Global_pragma.Warn_on_coverage_error _ ->
        with_pragma_stag state "warncoverage"
          (fun ppf -> Format.pp_print_string ppf "--warncoverage")
          ppf ()
    | Signature.Global_pragma.Raise_error_on_coverage_error _ ->
        with_pragma_stag state "coverage"
          (fun ppf -> Format.pp_print_string ppf "--coverage")
          ppf ()

  and pp_signature_totality_declaration state ppf totality_declaration =
    match totality_declaration with
    | Signature.Totality.Declaration.Trust _ -> pp_keyword ppf "trust"
    | Signature.Totality.Declaration.Named
        { order; program; argument_labels; _ } -> (
        let pp_identifier_option ppf = function
          | Option.None -> Format.pp_print_string ppf "_"
          | Option.Some identifier -> Identifier.pp ppf identifier
        in
        match order with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>%a@ (%a)@]" pp_keyword "total"
              (List.pp ~pp_sep:Format.pp_print_space pp_identifier_option)
              (Option.some program :: argument_labels)
        | Option.Some order ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@ (%a)@]" pp_keyword "total"
              ((pp_signature_totality_order state) Identifier.pp)
              order
              (List.pp ~pp_sep:Format.pp_print_space pp_identifier_option)
              (Option.some program :: argument_labels))
    | Signature.Totality.Declaration.Numeric { order; _ } -> (
        match order with
        | Option.None -> pp_keyword ppf "total"
        | Option.Some order ->
            Format.fprintf ppf "@[%a@ %a@]" pp_keyword "total"
              ((pp_signature_totality_order state) Int.pp)
              order)

  and pp_signature_totality_order :
      type a.
         state
      -> (Format.formatter -> a -> Unit.t)
      -> Format.formatter
      -> a Signature.Totality.Order.t
      -> Unit.t =
   fun state ppv ppf totality_order ->
    match totality_order with
    | Signature.Totality.Order.Argument { argument; _ } -> ppv ppf argument
    | Signature.Totality.Order.Lexical_ordering { arguments; _ } ->
        Format.fprintf ppf "@[<hov 2>{@ %a@ }@]"
          (List1.pp ~pp_sep:Format.pp_print_space
             ((pp_signature_totality_order state) ppv))
          arguments
    | Signature.Totality.Order.Simultaneous_ordering { arguments; _ } ->
        Format.fprintf ppf "@[<hov 2>[@ %a@ ]@]"
          (List1.pp ~pp_sep:Format.pp_print_space
             ((pp_signature_totality_order state) ppv))
          arguments

  and pp_signature_declaration state ppf declaration =
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
        Format.fprintf ppf "@[<hov 2>%a :@ %a.@]"
          (pp_lf_type_constant state)
          identifier (pp_lf_kind state) kind;
        add_fresh_id identifier state
    | Signature.Declaration.Const { identifier; typ; _ } ->
        Format.fprintf ppf "@[<hov 2>%a :@ %a.@]"
          (pp_lf_term_constant state)
          identifier (pp_lf_typ state) typ;
        add_fresh_id identifier state
    | Signature.Declaration.Schema { identifier; schema; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a =@ %a;@]" pp_keyword "schema"
          (pp_schema_constant state)
          identifier (pp_schema state) schema;
        add_fresh_id identifier state
    | Signature.Declaration.Recursive_declarations { declarations; _ } ->
        (pp_recursive_declarations state) ppf declarations
    | Signature.Declaration.CompTypAbbrev { identifier; kind; typ; _ } ->
        Format.fprintf ppf "@[<hov 2>%a %a :@ %a =@ %a;@]" pp_keyword
          "typedef"
          (pp_computation_abbreviation_constant state)
          identifier (pp_comp_kind state) kind (pp_comp_typ state) typ;
        add_fresh_id identifier state
    | Signature.Declaration.Val { identifier; typ; expression; _ } ->
        (match typ with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@ =@ %a@]" pp_keyword "let"
              (pp_computation_variable state)
              identifier
              (pp_comp_expression state)
              expression
        | Option.Some typ ->
            Format.fprintf ppf "@[<hov 2>%a@ %a :@ %a@ =@ %a@]" pp_keyword
              "let" Identifier.pp identifier (pp_comp_typ state) typ
              (pp_comp_expression state)
              expression);
        add_fresh_id identifier state
    | Signature.Declaration.Query
        { identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        ; _
        } -> (
        let pp_meta_context state ppf meta_context =
          let { Meta.Context.bindings; _ } = meta_context in
          List.pp ~pp_sep:Format.pp_print_space
            (fun ppf (i, t) ->
              Format.fprintf ppf "@[{@ %a :@ %a@ }@]" Identifier.pp i
                (pp_meta_typ state) t)
            ppf bindings
        in
        let pp_query_argument ppf = function
          | Option.None -> Format.pp_print_string ppf "*"
          | Option.Some argument -> Format.pp_print_int ppf argument
        in
        match identifier with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@ %a@ %a@ %a@]" pp_keyword
              "query" pp_query_argument expected_solutions pp_query_argument
              maximum_tries (pp_meta_context state) meta_context
              (pp_lf_typ state) typ;
            state
        | Option.Some identifier ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@ %a@ %a@ %a :@ %a@]"
              pp_keyword "query" pp_query_argument expected_solutions
              pp_query_argument maximum_tries (pp_meta_context state)
              meta_context Identifier.pp identifier (pp_lf_typ state) typ;
            add_fresh_id identifier state)
    | Signature.Declaration.MQuery
        { identifier
        ; typ
        ; expected_solutions
        ; search_tries
        ; search_depth
        ; _
        } -> (
        let pp_mquery_argument ppf = function
          | Option.None -> Format.pp_print_string ppf "*"
          | Option.Some argument -> Format.pp_print_int ppf argument
        in
        match identifier with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@ %a@ %a@ %a@]" pp_keyword
              "mquery" pp_mquery_argument expected_solutions
              pp_mquery_argument search_tries pp_mquery_argument search_depth
              (pp_comp_typ state) typ;
            state
        | Option.Some identifier ->
            Format.fprintf ppf "@[<hov 2>%a@ %a@ %a@ %a@ %a :@ %a@]"
              pp_keyword "mquery" pp_mquery_argument expected_solutions
              pp_mquery_argument search_tries pp_mquery_argument search_depth
              Identifier.pp identifier (pp_comp_typ state) typ;
            add_fresh_id identifier state)
    | Signature.Declaration.Module { identifier; entries; _ } ->
        Format.fprintf ppf "%a %a = %a@;<1 2>@[<v 0>%a@]@ %a" pp_keyword
          "module" Identifier.pp identifier pp_keyword "struct"
          (Obj.magic ()) entries pp_keyword "end";
        (* TODO: Carry the state through [pp_module_entry], or collect inner
           (identifier, IDs) pairs with a [with]-combinator *)
        add_fresh_id identifier state

  and pp_recursive_declarations state ppf declarations =
    let state' =
      List.fold_left add_signature_declaration_to_state state
        (List1.to_list declarations)
    in
    Format.fprintf ppf "@[<v 0>%a@];"
      (List1.pp
         ~pp_sep:(fun ppf () ->
           Format.fprintf ppf "@,@,%a@ " pp_keyword "and")
         (pp_grouped_declaration state'))
      (group_recursive_declarations declarations);
    state'

  and add_signature_declaration_to_state state = function
    | Signature.Declaration.Typ { identifier; _ }
    | Signature.Declaration.Const { identifier; _ }
    | Signature.Declaration.CompTyp { identifier; _ }
    | Signature.Declaration.CompCotyp { identifier; _ }
    | Signature.Declaration.CompConst { identifier; _ }
    | Signature.Declaration.CompDest { identifier; _ }
    | Signature.Declaration.Schema { identifier; _ }
    | Signature.Declaration.Theorem { identifier; _ }
    | Signature.Declaration.Proof { identifier; _ }
    | Signature.Declaration.CompTypAbbrev { identifier; _ }
    | Signature.Declaration.Val { identifier; _ }
    | Signature.Declaration.Query { identifier = Option.Some identifier; _ }
    | Signature.Declaration.MQuery { identifier = Option.Some identifier; _ }
      ->
        add_fresh_id identifier state
    | Signature.Declaration.Module { location; _ }
    | Signature.Declaration.Recursive_declarations { location; _ } ->
        Error.raise_at1 location Unsupported_recursive_declaration
    | Signature.Declaration.Query { identifier = Option.None; _ }
    | Signature.Declaration.MQuery { identifier = Option.None; _ } ->
        state

  and pp_grouped_declaration state ppf declaration =
    match declaration with
    | `Lf_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, typ) =
          Format.fprintf ppf "@[<h 0>| %a :@ %a@]@"
            (pp_lf_term_constant state)
            identifier (pp_lf_typ state) typ
        in
        Format.fprintf ppf "@[<v 0>@[%a %a :@ %a =@]@,%a@]" pp_keyword "LF"
          (pp_lf_type_constant state)
          identifier (pp_lf_kind state) kind
          (List.pp ~pp_sep:Format.pp_print_cut pp_constant)
          constants
    | `Inductive_comp_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, typ) =
          Format.fprintf ppf "@[<h 0>| %a :@ %a@]@"
            (pp_computation_constructor state)
            identifier (pp_comp_typ state) typ
        in
        Format.fprintf ppf "@[<v 0>@[%a %a :@ %a =@]@,%a@]" pp_keyword
          "inductive"
          (pp_computation_inductive_constant state)
          identifier (pp_comp_kind state) kind
          (List.pp ~pp_sep:Format.pp_print_cut pp_constant)
          constants
    | `Stratified_comp_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, typ) =
          Format.fprintf ppf "@[<h 0>| %a :@ %a@]@"
            (pp_computation_constructor state)
            identifier (pp_comp_typ state) typ
        in
        Format.fprintf ppf "@[<v 0>@[%a %a :@ %a =@]@,%a@]" pp_keyword
          "stratified"
          (pp_computation_stratified_constant state)
          identifier (pp_comp_kind state) kind
          (List.pp ~pp_sep:Format.pp_print_cut pp_constant)
          constants
    | `Coinductive_comp_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, observation_typ, return_typ) =
          Format.fprintf ppf "@[<h 0>| %a :@ %a ::@ %a@]@"
            (pp_computation_destructor state)
            identifier (pp_comp_typ state) observation_typ
            (pp_comp_typ state) return_typ
        in
        Format.fprintf ppf "@[<v 0>@[%a %a :@ %a =@]@,%a@]" pp_keyword
          "coinductive"
          (pp_computation_coinductive_constant state)
          identifier (pp_comp_kind state) kind
          (List.pp ~pp_sep:Format.pp_print_cut pp_constant)
          constants
    | `Theorem (identifier, typ, order, body) -> (
        match order with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>%a %a :@ %a =@ %a@]" pp_keyword
              "rec"
              (pp_computation_variable state)
              identifier (pp_comp_typ state) typ
              (pp_comp_expression state)
              body
        | Option.Some order ->
            Format.fprintf ppf "@[<hov 2>%a %a :@ %a =@,%a@,%a@]" pp_keyword
              "rec"
              (pp_computation_variable state)
              identifier (pp_comp_typ state) typ
              (pp_signature_totality_declaration state)
              order
              (pp_comp_expression state)
              body)
    | `Proof (identifier, typ, order, body) -> (
        match order with
        | Option.None ->
            Format.fprintf ppf "@[<hov 2>%a %a :@ %a =@ %a@]" pp_keyword
              "proof"
              (pp_computation_variable state)
              identifier (pp_comp_typ state) typ (pp_harpoon_proof state)
              body
        | Option.Some order ->
            Format.fprintf ppf "@[<hov 2>%a %a :@ %a =@,%a@,%a@]" pp_keyword
              "proof"
              (pp_computation_variable state)
              identifier (pp_comp_typ state) typ
              (pp_signature_totality_declaration state)
              order (pp_harpoon_proof state) body)

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

  and pp_module_entry state ppf entry =
    match entry with
    | Signature.Entry.Declaration _
    | Signature.Entry.Pragma _ ->
        pp_signature_entry state ppf entry
    | Signature.Entry.Comment { location; content } ->
        let html = render_markdown location content in
        (pp_inner_documentation_comment state html) ppf ();
        state

  and pp_signature_entry state ppf entry =
    match entry with
    | Signature.Entry.Declaration { declaration; _ } ->
        (pp_signature_declaration state) ppf declaration
    | Signature.Entry.Pragma { pragma; _ } ->
        (pp_signature_pragma state) ppf pragma
    | Signature.Entry.Comment { location; content } ->
        let html = render_markdown location content in
        (pp_toplevel_documentation_comment state html) ppf ();
        state

  and pp_signature state ppf signature =
    (* TODO: State management *)
    let { Signature.global_pragmas; entries } = signature in
    let groups = group_toplevel_signature_entries entries in
    match (global_pragmas, groups) with
    | [], _groups -> Obj.magic () (* TODO: *)
    | _global_pragmas, `Code _group1 :: _rest -> Obj.magic () (* TODO: *)
    | _global_pragmas, `Comment _group1 :: _rest -> Obj.magic () (* TODO: *)
    | global_pragmas, [] ->
        with_preformatted_code_stag state
          (fun ppf ->
            (List.pp ~pp_sep:Format.pp_print_cut
               (pp_signature_global_pragma state))
              ppf global_pragmas)
          ppf ();
        Format.pp_print_char ppf '\n'

  and group_toplevel_signature_entries entries =
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
        `Code (List1.from x code_entries)
        :: group_toplevel_signature_entries rest
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
        :: group_toplevel_signature_entries rest
    | [] -> []

  and pp_toplevel_signature_group _state _groups =
    (* TODO: Add the HTML tags depending on whether the group is [`Code] or
       [`Comment] *)
    Obj.magic ()

  let html_mark_open_stag = function
    | Toplevel_documentation_comment -> {|<div class="documentation">|}
    | Inner_documentation_comment -> {|<div class="inner-documentation">|}
    | Preformatted_code -> {|<pre><code>|}
    | Keyword { keyword } ->
        Format.asprintf {|<span class="keyword keyword-%s">|} keyword
    | Pragma { pragma_keyword } ->
        Format.asprintf {|<span class="pragma pragma-%s">|} pragma_keyword
    | Lf_variable -> {|<span class="variable lf-variable">|}
    | Meta_variable -> {|<span class="variable meta-variable">|}
    | Parameter_variable -> {|<span class="variable parameter-variable">|}
    | Substitution_variable ->
        {|<span class="variable substitution-variable">|}
    | Context_variable -> {|<span class="variable context-variable">|}
    | Computation_variable ->
        {|<span class="variable computation-variable">|}
    | Lf_type_constant { id } ->
        Format.asprintf {|<span id="%s" class="constant lf-type-constant">|}
          id
    | Lf_term_constant { id } ->
        Format.asprintf {|<span id="%s" class="constant lf-term-constant">|}
          id
    | Context_schema { id } ->
        Format.asprintf {|<span id="%s" class="constant context-schema">|} id
    | Computation_inductive_type_constant { id } ->
        Format.asprintf
          {|<span id="%s" class="constant computation-inductive-type-constant">|}
          id
    | Computation_stratified_type_constant { id } ->
        Format.asprintf
          {|<span id="%s" class="constant computation-stratified-type-constant">|}
          id
    | Computation_abbreviation_type_constant { id } ->
        Format.asprintf
          {|<span id="%s" class="constant computation-abbreviation-type-constant">|}
          id
    | Computation_coinductive_type_constant { id } ->
        Format.asprintf
          {|<span id="%s" class="constant computation-coinductive-type-constant">|}
          id
    | Computation_constructor { id } ->
        Format.asprintf
          {|<span id="%s" class="constant computation-constructor">|} id
    | Computation_destructor { id } ->
        Format.asprintf
          {|<span id="%s" class="constant computation-destructor">|} id
    | Lf_type_constant_invoke { id } ->
        Format.asprintf
          {|<span class="constant lf-type-constant"><a href="#%s">|} id
    | Lf_term_constant_invoke { id } ->
        Format.asprintf
          {|<span class="constant lf-term-constant"><a href="#%s">|} id
    | Context_schema_invoke { id } ->
        Format.asprintf
          {|<span class="constant schema-constant"><a href="#%s">|} id
    | Computation_inductive_type_constant_invoke { id } ->
        Format.asprintf
          {|<span class="constant comp-inductive-type-constant"><a href="#%s">|}
          id
    | Computation_stratified_type_constant_invoke { id } ->
        Format.asprintf
          {|<span class="constant comp-stratified-type-constant"><a href="#%s">|}
          id
    | Computation_abbreviation_type_constant_invoke { id } ->
        Format.asprintf
          {|<span class="constant comp-abbreviation-type-constant"><a href="#%s">|}
          id
    | Computation_coinductive_type_constant_invoke { id } ->
        Format.asprintf
          {|<span class="constant comp-coinductive-type-constant"><a href="#%s">|}
          id
    | Computation_constructor_invoke { id } ->
        Format.asprintf
          {|<span class="constant comp-constructor-constant"><a href="#%s">|}
          id
    | Computation_destructor_invoke { id } ->
        Format.asprintf
          {|<span class="constant comp-destructor-constant"><a href="#%s">|}
          id
    | _ -> Error.violation "Unsupported HTML stag"

  let html_mark_close_stag = function
    | Toplevel_documentation_comment
    | Inner_documentation_comment ->
        {|</div>|}
    | Preformatted_code -> {|</code></pre>|}
    | Keyword _
    | Pragma _
    | Lf_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Computation_variable
    | Lf_type_constant _
    | Lf_term_constant _
    | Context_schema _
    | Computation_inductive_type_constant _
    | Computation_stratified_type_constant _
    | Computation_abbreviation_type_constant _
    | Computation_coinductive_type_constant _
    | Computation_constructor _
    | Computation_destructor _ ->
        {|</span>|}
    | Lf_type_constant_invoke _
    | Lf_term_constant_invoke _
    | Context_schema_invoke _
    | Computation_inductive_type_constant_invoke _
    | Computation_stratified_type_constant_invoke _
    | Computation_abbreviation_type_constant_invoke _
    | Computation_coinductive_type_constant_invoke _
    | Computation_constructor_invoke _
    | Computation_destructor_invoke _ ->
        {|</a></span>|}
    | _ -> Error.violation "Unsupported HTML stag"

  let with_html_tags ppf f =
    (* Get the old stag-marking state *)
    let old_formatter_stag_functions =
      Format.pp_get_formatter_stag_functions ppf ()
    in
    let old_mark_tags = Format.pp_get_mark_tags ppf () in
    (* Print with stag-marking enabled *)
    Format.pp_set_formatter_stag_functions ppf
      { old_formatter_stag_functions with
        Format.mark_open_stag = html_mark_open_stag
      ; mark_close_stag = html_mark_close_stag
      };
    Format.pp_set_mark_tags ppf true;
    f ppf;
    (* Restore the stag-marking state *)
    Format.pp_set_mark_tags ppf old_mark_tags;
    Format.pp_set_formatter_stag_functions ppf old_formatter_stag_functions

  let pp_html_signature ppf signature =
    with_html_tags ppf (fun ppf -> pp_signature empty ppf signature)
end

let pp_exception ppf = function
  | Markdown_rendering_error ->
      Format.fprintf ppf "Failed to render Markdown documentation comment."
  | Unsupported_non_recursive_declaration ->
      Format.fprintf ppf
        "Unsupported pretty-printing for this declaration outside of a \
         recursive group of declarations."
  | Unsupported_recursive_declaration ->
      Format.fprintf ppf
        "Unsupported pretty-printing for this declaration in a recursive \
         group of declarations."
  | _ ->
      Error.raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
