(** Pretty-printing for the external syntax. *)

open Support
open Common
open Synext_definition
open Synext_precedence
open Parenthesizer

(** {1 Pretty-Printing LF Syntax} *)

open Make_parenthesizer (Lf_precedence)

let rec pp_lf_kind ppf kind =
  let parent_precedence = precedence_of_lf_kind kind in
  match kind with
  | LF.Kind.Typ _ -> Format.fprintf ppf "type"
  | LF.Kind.Arrow { domain; range; _ } ->
      (* Right arrows are right-associative *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
        (parenthesize_left_argument_right_associative_operator
           precedence_of_lf_typ ~parent_precedence pp_lf_typ)
        domain pp_lf_kind range
  | LF.Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
      (* Pi-operators are weak prefix operators *)
      match (parameter_identifier, parameter_type) with
      | Option.Some parameter_identifier, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
            parameter_identifier pp_lf_typ parameter_type pp_lf_kind body
      | Option.Some parameter_identifier, Option.None ->
          Format.fprintf ppf "@[<2>{@ %a@ }@ %a@]" Identifier.pp
            parameter_identifier pp_lf_kind body
      | Option.None, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>{@ _ :@ %a@ }@ %a@]" pp_lf_typ
            parameter_type pp_lf_kind body
      | Option.None, Option.None ->
          Format.fprintf ppf "@[<2>{@ _@ }@ %a@]" pp_lf_kind body)

and pp_lf_typ ppf typ =
  let parent_precedence = precedence_of_lf_typ typ in
  match typ with
  | LF.Typ.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
      else Qualified_identifier.pp ppf identifier
  | LF.Typ.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | LF.Typ.Constant { operator; quoted = false; _ } ->
              `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | LF.Term.Application
              { applicand = LF.Term.Constant { operator; quoted = false; _ }
              ; _
              } ->
              `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:precedence_of_lf_typ
        ~precedence_of_argument:precedence_of_lf_term ~pp_applicand:pp_lf_typ
        ~pp_argument:pp_lf_term ~parent_precedence ppf (applicand, arguments)
  | LF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows, so backward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
        (match domain with
        | LF.Typ.Arrow { orientation = `Backward; _ } ->
            parenthesize pp_lf_typ
        | _ ->
            parenthesize_left_argument_right_associative_operator
              precedence_of_lf_typ ~parent_precedence pp_lf_typ)
        domain
        (match range with
        | LF.Typ.Arrow { orientation = `Backward; _ } ->
            parenthesize pp_lf_typ
        | _ ->
            parenthesize_right_argument_right_associative_operator
              precedence_of_lf_typ ~parent_precedence pp_lf_typ)
        range
  | LF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows, so forward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a@ ← %a@]"
        (match range with
        | LF.Typ.Arrow { orientation = `Forward; _ } ->
            parenthesize pp_lf_typ
        | _ ->
            parenthesize_left_argument_left_associative_operator
              precedence_of_lf_typ ~parent_precedence pp_lf_typ)
        range
        (match domain with
        | LF.Typ.Arrow { orientation = `Forward; _ } ->
            parenthesize pp_lf_typ
        | _ ->
            parenthesize_right_argument_left_associative_operator
              precedence_of_lf_typ ~parent_precedence pp_lf_typ)
        domain
  | LF.Typ.Pi { parameter_identifier; parameter_type; body; _ } -> (
      (* Pi-operators are weak prefix operators *)
      match (parameter_identifier, parameter_type) with
      | Option.Some parameter_identifier, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
            parameter_identifier pp_lf_typ parameter_type pp_lf_typ body
      | Option.Some parameter_identifier, Option.None ->
          Format.fprintf ppf "@[<2>{@ %a@ }@ %a@]" Identifier.pp
            parameter_identifier pp_lf_typ body
      | Option.None, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>{@ _ :@ %a@ }@ %a@]" pp_lf_typ
            parameter_type pp_lf_typ body
      | Option.None, Option.None ->
          Format.fprintf ppf "@[<2>{@ _@ }@ %a@]" pp_lf_typ body)

and pp_lf_term ppf term =
  let parent_precedence = precedence_of_lf_term term in
  match term with
  | LF.Term.Variable { identifier; _ } -> Identifier.pp ppf identifier
  | LF.Term.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
  | LF.Term.Constant { identifier; quoted = false; _ } ->
      Qualified_identifier.pp ppf identifier
  | LF.Term.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | LF.Term.Constant { operator; quoted = false; _ } ->
              `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | LF.Term.Application
              { applicand = LF.Term.Constant { operator; quoted = false; _ }
              ; _
              } ->
              `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:precedence_of_lf_term
        ~precedence_of_argument:precedence_of_lf_term
        ~pp_applicand:pp_lf_term ~pp_argument:pp_lf_term ~parent_precedence
        ppf (applicand, arguments)
  | LF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
    -> (
      (* Lambdas are weak prefix operators, so the body of the lambda never
         requires parentheses *)
      match (parameter_identifier, parameter_type) with
      | Option.None, Option.None ->
          Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_lf_term body
      | Option.None, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_lf_typ parameter_type
            pp_lf_term body
      | Option.Some parameter_identifier, Option.None ->
          Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
            parameter_identifier pp_lf_term body
      | Option.Some parameter_identifier, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
            parameter_identifier pp_lf_typ parameter_type pp_lf_term body)
  | LF.Term.Wildcard _ -> Format.fprintf ppf "_"
  | LF.Term.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_lf_term ~parent_precedence pp_lf_term)
        term pp_lf_typ typ

(** {1 Pretty-Printing Contextual LF Syntax} *)

open Make_parenthesizer (Clf_precedence)

let rec pp_clf_typ ppf typ =
  let parent_precedence = precedence_of_clf_typ typ in
  match typ with
  | CLF.Typ.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
      else Qualified_identifier.pp ppf identifier
  | CLF.Typ.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | CLF.Typ.Constant { operator; quoted = false; _ } ->
              `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | CLF.Term.Application
              { applicand = CLF.Term.Constant { operator; quoted = false; _ }
              ; _
              } ->
              `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:precedence_of_clf_typ
        ~precedence_of_argument:precedence_of_clf_term
        ~pp_applicand:pp_clf_typ ~pp_argument:pp_clf_term ~parent_precedence
        ppf (applicand, arguments)
  | CLF.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows, so backward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
        (match domain with
        | CLF.Typ.Arrow { orientation = `Backward; _ } ->
            parenthesize pp_clf_typ
        | _ ->
            parenthesize_left_argument_right_associative_operator
              precedence_of_clf_typ ~parent_precedence pp_clf_typ)
        domain
        (match range with
        | CLF.Typ.Arrow { orientation = `Backward; _ } ->
            parenthesize pp_clf_typ
        | _ ->
            parenthesize_right_argument_right_associative_operator
              precedence_of_clf_typ ~parent_precedence pp_clf_typ)
        range
  | CLF.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows, so forward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a@ ← %a@]"
        (match range with
        | CLF.Typ.Arrow { orientation = `Forward; _ } ->
            parenthesize pp_clf_typ
        | _ ->
            parenthesize_left_argument_left_associative_operator
              precedence_of_clf_typ ~parent_precedence pp_clf_typ)
        range
        (match domain with
        | CLF.Typ.Arrow { orientation = `Forward; _ } ->
            parenthesize pp_clf_typ
        | _ ->
            parenthesize_right_argument_left_associative_operator
              precedence_of_clf_typ ~parent_precedence pp_clf_typ)
        domain
  | CLF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
      (* Pi-operators are weak prefix operators *)
      Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
        (fun ppf -> function
          | Option.Some parameter_identifier ->
              Identifier.pp ppf parameter_identifier
          | Option.None -> Format.fprintf ppf "_")
        parameter_identifier pp_clf_typ parameter_type pp_clf_typ body
  | CLF.Typ.Block { elements = `Unnamed typ; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]" pp_clf_typ typ
  | CLF.Typ.Block { elements = `Record nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
             Format.fprintf ppf "%a :@ %a" Identifier.pp i pp_clf_typ t))
        nts

and pp_clf_term ppf term =
  let parent_precedence = precedence_of_clf_term term in
  match term with
  | CLF.Term.Variable { identifier; _ } -> Identifier.pp ppf identifier
  | CLF.Term.Parameter_variable { identifier; _ } ->
      Identifier.pp ppf identifier
  | CLF.Term.Substitution_variable { identifier; _ } ->
      Identifier.pp ppf identifier
  | CLF.Term.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
  | CLF.Term.Constant { identifier; quoted = false; _ } ->
      Qualified_identifier.pp ppf identifier
  | CLF.Term.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | CLF.Term.Constant { operator; quoted = false; _ } ->
              `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | CLF.Term.Application
              { applicand = CLF.Term.Constant { operator; quoted = false; _ }
              ; _
              } ->
              `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:precedence_of_clf_term
        ~precedence_of_argument:precedence_of_clf_term
        ~pp_applicand:pp_clf_term ~pp_argument:pp_clf_term ~parent_precedence
        ppf (applicand, arguments)
  | CLF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
    -> (
      (* Lambdas are weak prefix operators, so the body of a lambda does not
         need to be parenthesized *)
      match (parameter_identifier, parameter_type) with
      | Option.None, Option.None ->
          Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_clf_term body
      | Option.None, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_clf_typ parameter_type
            pp_clf_term body
      | Option.Some parameter_identifier, Option.None ->
          Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
            parameter_identifier pp_clf_term body
      | Option.Some parameter_identifier, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
            parameter_identifier pp_clf_typ parameter_type pp_clf_term body)
  | CLF.Term.Hole { variant = `Underscore; _ } -> Format.fprintf ppf "_"
  | CLF.Term.Hole { variant = `Unlabelled; _ } -> Format.fprintf ppf "?"
  | CLF.Term.Hole { variant = `Labelled label; _ } ->
      Format.fprintf ppf "?%a" Identifier.pp label
  | CLF.Term.Substitution { term; substitution; _ } ->
      (* Substitutions are left-associative *)
      Format.fprintf ppf "@[<2>%a[%a]@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term ~parent_precedence pp_clf_term)
        term pp_clf_substitution substitution
  | CLF.Term.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
           pp_clf_term)
        terms
  | CLF.Term.Projection { term; projection = `By_position i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%d@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term ~parent_precedence pp_clf_term)
        term i
  | CLF.Term.Projection { term; projection = `By_identifier i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term ~parent_precedence pp_clf_term)
        term Identifier.pp i
  | CLF.Term.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term ~parent_precedence pp_clf_term)
        term pp_clf_typ typ

and pp_clf_substitution ppf substitution =
  match substitution with
  | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms = []; _ }
    ->
      Format.fprintf ppf "^"
  | { CLF.Substitution.head = CLF.Substitution.Head.Identity _
    ; terms = []
    ; _
    } ->
      Format.fprintf ppf ".."
  | { CLF.Substitution.head = CLF.Substitution.Head.None _; terms; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:Format.comma pp_clf_term)
        terms
  | { CLF.Substitution.head = CLF.Substitution.Head.Identity _; terms; _ } ->
      Format.fprintf ppf "@[<2>..,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_clf_term)
        terms
  | { CLF.Substitution.head =
        CLF.Substitution.Head.Substitution_variable
          { identifier; closure = Option.None; _ }
    ; terms = []
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a@]" Identifier.pp identifier
  | { CLF.Substitution.head =
        CLF.Substitution.Head.Substitution_variable
          { identifier; closure = Option.Some closure; _ }
    ; terms = []
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a[%a]@]" Identifier.pp identifier
        pp_clf_substitution closure
  | { CLF.Substitution.head =
        CLF.Substitution.Head.Substitution_variable
          { identifier; closure = Option.None; _ }
    ; terms
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:Format.comma pp_clf_term)
        terms
  | { CLF.Substitution.head =
        CLF.Substitution.Head.Substitution_variable
          { identifier; closure = Option.Some closure; _ }
    ; terms
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a[%a],@ %a@]" Identifier.pp identifier
        pp_clf_substitution closure
        (List.pp ~pp_sep:Format.comma pp_clf_term)
        terms

and pp_clf_context ppf context =
  let pp_typing ppf typing =
    match typing with
    | identifier, Option.None -> Identifier.pp ppf identifier
    | identifier, Option.Some typ ->
        Format.fprintf ppf "%a :@ %a" Identifier.pp identifier pp_clf_typ typ
  in
  match context with
  | { CLF.Context.head = CLF.Context.Head.None _; bindings = []; _ } ->
      Format.fprintf ppf "^"
  | { CLF.Context.head = CLF.Context.Head.Hole _; bindings = []; _ } ->
      Format.fprintf ppf "_"
  | { CLF.Context.head = CLF.Context.Head.Context_variable { identifier; _ }
    ; bindings = []
    ; _
    } ->
      Identifier.pp ppf identifier
  | { CLF.Context.head = CLF.Context.Head.None _; bindings; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
  | { CLF.Context.head = CLF.Context.Head.Hole _; bindings; _ } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
  | { CLF.Context.head = CLF.Context.Head.Context_variable { identifier; _ }
    ; bindings
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings

let rec pp_clf_term_pattern ppf term =
  let parent_precedence = precedence_of_clf_term_pattern term in
  match term with
  | CLF.Term.Pattern.Variable { identifier; _ } ->
      Identifier.pp ppf identifier
  | CLF.Term.Pattern.Parameter_variable { identifier; _ } ->
      Identifier.pp ppf identifier
  | CLF.Term.Pattern.Substitution_variable { identifier; _ } ->
      Identifier.pp ppf identifier
  | CLF.Term.Pattern.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
  | CLF.Term.Pattern.Constant { identifier; quoted = false; _ } ->
      Qualified_identifier.pp ppf identifier
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
        ~pp_applicand:pp_clf_term_pattern ~pp_argument:pp_clf_term_pattern
        ~parent_precedence ppf (applicand, arguments)
  | CLF.Term.Pattern.Abstraction
      { parameter_identifier; parameter_type; body; _ } -> (
      (* Lambdas are weak prefix operators, so the body of a lambda never
         requires parentheses. *)
      match (parameter_identifier, parameter_type) with
      | Option.None, Option.None ->
          Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_clf_term_pattern body
      | Option.None, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_clf_typ parameter_type
            pp_clf_term_pattern body
      | Option.Some parameter_identifier, Option.None ->
          Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
            parameter_identifier pp_clf_term_pattern body
      | Option.Some parameter_identifier, Option.Some parameter_type ->
          Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
            parameter_identifier pp_clf_typ parameter_type
            pp_clf_term_pattern body)
  | CLF.Term.Pattern.Wildcard _ -> Format.fprintf ppf "_"
  | CLF.Term.Pattern.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a[%a]@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term_pattern ~parent_precedence
           pp_clf_term_pattern)
        term pp_clf_substitution substitution
  | CLF.Term.Pattern.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
           pp_clf_term_pattern)
        terms
  | CLF.Term.Pattern.Projection { term; projection = `By_position i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%d@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term_pattern ~parent_precedence
           pp_clf_term_pattern)
        term i
  | CLF.Term.Pattern.Projection { term; projection = `By_identifier i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term_pattern ~parent_precedence
           pp_clf_term_pattern)
        term Identifier.pp i
  | CLF.Term.Pattern.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_clf_term_pattern ~parent_precedence
           pp_clf_term_pattern)
        term pp_clf_typ typ

and pp_clf_substitution_pattern ppf substitution_pattern =
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
      Format.fprintf ppf ".."
  | { CLF.Substitution.Pattern.head = CLF.Substitution.Pattern.Head.None _
    ; terms
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
        terms
  | { CLF.Substitution.Pattern.head =
        CLF.Substitution.Pattern.Head.Identity _
    ; terms
    ; _
    } ->
      Format.fprintf ppf "@[<2>..,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
        terms
  | { CLF.Substitution.Pattern.head =
        CLF.Substitution.Pattern.Head.Substitution_variable
          { identifier; closure = Option.None; _ }
    ; terms = []
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a@]" Identifier.pp identifier
  | { CLF.Substitution.Pattern.head =
        CLF.Substitution.Pattern.Head.Substitution_variable
          { identifier; closure = Option.Some closure; _ }
    ; terms = []
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a[%a]@]" Identifier.pp identifier
        pp_clf_substitution closure
  | { CLF.Substitution.Pattern.head =
        CLF.Substitution.Pattern.Head.Substitution_variable
          { identifier; closure = Option.None; _ }
    ; terms
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
        terms
  | { CLF.Substitution.Pattern.head =
        CLF.Substitution.Pattern.Head.Substitution_variable
          { identifier; closure = Option.Some closure; _ }
    ; terms
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a[%a],@ %a@]" Identifier.pp identifier
        pp_clf_substitution closure
        (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
        terms

and pp_clf_context_pattern ppf context_pattern =
  let pp_typing ppf (i, t) =
    Format.fprintf ppf "%a :@ %a" Identifier.pp i pp_clf_typ t
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
      Identifier.pp ppf identifier
  | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.None _
    ; bindings
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
  | { CLF.Context.Pattern.head = CLF.Context.Pattern.Head.Hole _
    ; bindings
    ; _
    } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
  | { CLF.Context.Pattern.head =
        CLF.Context.Pattern.Head.Context_variable { identifier; _ }
    ; bindings
    ; _
    } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings

(** {1 Pretty-Printing Meta-Level Syntax} *)

open Make_parenthesizer (Meta_precedence)

let rec pp_meta_typ ppf typ =
  match typ with
  | Meta.Typ.Context_schema { schema; _ } -> pp_schema ppf schema
  | Meta.Typ.Contextual_typ { context; typ; _ } ->
      Format.fprintf ppf "@[<2>(%a@ ⊢@ %a)@]" pp_clf_context context
        pp_clf_typ typ
  | Meta.Typ.Parameter_typ { context; typ; _ } ->
      Format.fprintf ppf "@[<2>#(%a@ ⊢@ %a)@]" pp_clf_context context
        pp_clf_typ typ
  | Meta.Typ.Plain_substitution_typ { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$(%a@ ⊢@ %a)@]" pp_clf_context domain
        pp_clf_context range
  | Meta.Typ.Renaming_substitution_typ { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$(%a@ ⊢#@ %a)@]" pp_clf_context domain
        pp_clf_context range

and pp_meta_object ppf object_ =
  match object_ with
  | Meta.Object.Context { context; _ } ->
      Format.fprintf ppf "@[[%a]@]" pp_clf_context context
  | Meta.Object.Contextual_term { context; term; _ } ->
      Format.fprintf ppf "@[<2>[%a@ ⊢@ %a]@]" pp_clf_context context
        pp_clf_term term
  | Meta.Object.Plain_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢@ %a]@]" pp_clf_context domain
        pp_clf_substitution range
  | Meta.Object.Renaming_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢#@ %a]@]" pp_clf_context domain
        pp_clf_substitution range

and pp_meta_pattern ppf pattern =
  match pattern with
  | Meta.Pattern.Context { context; _ } ->
      Format.fprintf ppf "@[[%a]@]" pp_clf_context_pattern context
  | Meta.Pattern.Contextual_term { context; term; _ } ->
      Format.fprintf ppf "@[<2>[%a@ ⊢@ %a]@]" pp_clf_context_pattern context
        pp_clf_term_pattern term
  | Meta.Pattern.Plain_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢@ %a]@]" pp_clf_context_pattern domain
        pp_clf_substitution_pattern range
  | Meta.Pattern.Renaming_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢#@ %a]@]" pp_clf_context_pattern domain
        pp_clf_substitution_pattern range

and pp_meta_context ppf context =
  let { Meta.Context.bindings; _ } = context in
  List.pp ~pp_sep:Format.comma
    (fun ppf (i, t) ->
      Format.fprintf ppf "@[%a :@ %a@]" Identifier.pp i pp_meta_typ t)
    ppf bindings

and pp_schema ppf schema =
  let parent_precedence = precedence_of_schema schema in
  let pp_bindings =
    List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
        Format.fprintf ppf "@[%a :@ %a@]" Identifier.pp i pp_clf_typ t)
  in
  match schema with
  | Meta.Schema.Constant { identifier; _ } ->
      Qualified_identifier.pp ppf identifier
  | Meta.Schema.Alternation { schemas; _ } ->
      List2.pp
        ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ +@ ")
        (parenthesize_term_of_lesser_than_or_equal_precedence
           precedence_of_schema ~parent_precedence pp_schema)
        ppf schemas
  | Meta.Schema.Element { some = Option.None; block = `Unnamed t; _ } ->
      Format.fprintf ppf "@[<2>block@ %a@]" pp_clf_typ t
  | Meta.Schema.Element { some = Option.None; block = `Record bindings; _ }
    ->
      Format.fprintf ppf "@[<2>block@ (%a)@]" pp_bindings bindings
  | Meta.Schema.Element
      { some = Option.Some some_bindings; block = `Unnamed t; _ } ->
      Format.fprintf ppf "@[<2>some@ [%a]@ block@ %a@]" pp_bindings
        some_bindings pp_clf_typ t
  | Meta.Schema.Element
      { some = Option.Some some_bindings; block = `Record block_bindings; _ }
    ->
      Format.fprintf ppf "@[<2>some@ [%a]@ block@ (%a)@]" pp_bindings
        some_bindings pp_bindings block_bindings

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

let rec pp_comp_kind ppf kind =
  let parent_precedence = precedence_of_comp_kind kind in
  match kind with
  | Comp.Kind.Ctype _ -> Format.pp_print_string ppf "ctype"
  | Comp.Kind.Arrow { domain; range; _ } ->
      (* Right arrows are right-associative *)
      Format.fprintf ppf "@[<2>%a@ →@ %a@]"
        (parenthesize_left_argument_right_associative_operator
           precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        domain pp_comp_kind range
  | Comp.Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
      (* Pi-operators are weak prefix operators *)
      match parameter_identifier with
      | Option.None ->
          Format.fprintf ppf "@[<2>{@ _ :@ %a@ }@ %a@]" pp_meta_typ
            parameter_type pp_comp_kind body
      | Option.Some parameter_identifier ->
          Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
            parameter_identifier pp_meta_typ parameter_type pp_comp_kind body
      )

and pp_comp_typ ppf typ =
  let parent_precedence = precedence_of_comp_typ typ in
  match typ with
  | Comp.Typ.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
      else Qualified_identifier.pp ppf identifier
  | Comp.Typ.Pi { parameter_identifier; plicity; parameter_type; body; _ }
    -> (
      (* Pi-operators are weak prefix operators *)
      let pp_parameter_identifier parameter_type ppf parameter_identifier =
        match (parameter_identifier, parameter_type) with
        | Option.Some parameter_identifier, _ ->
            Identifier.pp ppf parameter_identifier
        | Option.None, (Meta.Typ.Context_schema _ | Meta.Typ.Contextual_typ _)
          ->
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
          Format.fprintf ppf "@[<2>(@ %a :@ %a@ )@ %a@]"
            (pp_parameter_identifier parameter_type)
            parameter_identifier pp_meta_typ parameter_type pp_comp_typ body
      | Plicity.Explicit ->
          Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
            (pp_parameter_identifier parameter_type)
            parameter_identifier pp_meta_typ parameter_type pp_comp_typ body)
  | Comp.Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
        (match domain with
        | Comp.Typ.Arrow { orientation = `Backward; _ } ->
            parenthesize pp_comp_typ
        | _ ->
            parenthesize_left_argument_right_associative_operator
              precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        domain
        (match range with
        | Comp.Typ.Arrow { orientation = `Backward; _ } ->
            parenthesize pp_comp_typ
        | _ ->
            parenthesize_right_argument_right_associative_operator
              precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        range
  | Comp.Typ.Arrow { range; domain; orientation = `Backward; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      Format.fprintf ppf "@[<2>%a@ ← %a@]"
        (match range with
        | Comp.Typ.Arrow { orientation = `Forward; _ } ->
            parenthesize pp_comp_typ
        | _ ->
            parenthesize_left_argument_left_associative_operator
              precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        range
        (match domain with
        | Comp.Typ.Arrow { orientation = `Forward; _ } ->
            parenthesize pp_comp_typ
        | _ ->
            parenthesize_right_argument_left_associative_operator
              precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        domain
  | Comp.Typ.Cross { types; _ } ->
      List2.pp
        ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ * ")
        (parenthesize_term_of_lesser_than_or_equal_precedence
           precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        ppf types
  | Comp.Typ.Box { meta_type; _ } -> pp_meta_typ ppf meta_type
  | Comp.Typ.Application { applicand; arguments; _ } -> (
      match applicand with
      | Comp.Typ.Application
          { applicand =
              Comp.Typ.Constant { identifier; operator; quoted = false; _ }
          ; _
          } -> (
          match Operator.fixity operator with
          | Fixity.Prefix ->
              Format.fprintf ppf "@[<2>%a@ %a@]" Qualified_identifier.pp
                identifier
                (List1.pp ~pp_sep:Format.pp_print_space pp_meta_object)
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
              Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_meta_object
                left_argument Qualified_identifier.pp identifier
                pp_meta_object right_argument
          | Fixity.Postfix ->
              assert (
                List1.compare_length_with arguments 1
                = 0
                  (* Postfix operators must be applied with exactly one
                     argument. *));
              let[@warning "-8"] (List1.T (argument, [])) = arguments in
              Format.fprintf ppf "@[<2>%a@ %a@]" pp_meta_object argument
                Qualified_identifier.pp identifier)
      | _ ->
          Format.fprintf ppf "@[<2>%a@ %a@]"
            (parenthesize_term_of_lesser_than_or_equal_precedence
               precedence_of_comp_typ ~parent_precedence pp_comp_typ)
            applicand
            (List1.pp ~pp_sep:Format.pp_print_space pp_meta_object)
            arguments)

and pp_comp_expression ppf expression =
  let parent_precedence = precedence_of_comp_expression expression in
  match expression with
  | Comp.Expression.Variable { identifier; _ } ->
      Identifier.pp ppf identifier
  | Comp.Expression.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
      else Qualified_identifier.pp ppf identifier
  | Comp.Expression.Fn { parameters; body; _ } ->
      let pp_parameter ppf parameter =
        match parameter with
        | Option.None -> Format.pp_print_string ppf "_"
        | Option.Some parameter -> Identifier.pp ppf parameter
      in
      Format.fprintf ppf "@[<2>fn@ %a =>@ %a@]"
        (List1.pp ~pp_sep:Format.pp_print_space pp_parameter)
        parameters pp_comp_expression body
  | Comp.Expression.Mlam { parameters; body; _ } ->
      let pp_parameter ppf (parameter, modifier) =
        match (parameter, modifier) with
        | Option.Some parameter, (`Plain | `Hash | `Dollar) ->
            (* The hash or dollar prefix is part of [parameter] *)
            Identifier.pp ppf parameter
        | Option.None, `Plain -> Format.pp_print_string ppf "_"
        | Option.None, `Hash -> Format.pp_print_string ppf "#_"
        | Option.None, `Dollar -> Format.pp_print_string ppf "$_"
      in
      let pp_parameters =
        List1.pp ~pp_sep:Format.pp_print_space pp_parameter
      in
      Format.fprintf ppf "@[<2>mlam@ %a =>@ %a@]" pp_parameters parameters
        pp_comp_expression body
  | Comp.Expression.Fun { branches; _ } ->
      let pp_branch_pattern ppf copattern =
        if is_atomic_copattern copattern then pp_comp_copattern ppf copattern
        else parenthesize pp_comp_copattern ppf copattern
      in
      let pp_branch_patterns =
        List1.pp ~pp_sep:Format.pp_print_space pp_branch_pattern
      in
      let pp_branch ppf (patterns, expression) =
        Format.fprintf ppf "@[<hov 2>|@ %a =>@ %a@]" pp_branch_patterns
          patterns pp_comp_expression expression
      in
      let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
      Format.fprintf ppf "@[<2>fun@;%a@]" pp_branches branches
  | Comp.Expression.Let { pattern; scrutinee; body; _ } ->
      Format.fprintf ppf "@[<hov 2>let@ %a =@ %a@ in@ %a@]" pp_comp_pattern
        pattern pp_comp_expression scrutinee pp_comp_expression body
  | Comp.Expression.Box { meta_object; _ } -> pp_meta_object ppf meta_object
  | Comp.Expression.Impossible { scrutinee; _ } ->
      (* [impossible (impossible (...))] is right-associative *)
      Format.fprintf ppf "@[<2>impossible@ %a@]"
        (parenthesize_right_argument_right_associative_operator
           precedence_of_comp_expression ~parent_precedence
           pp_comp_expression)
        scrutinee
  | Comp.Expression.Case { scrutinee; check_coverage; branches; _ } ->
      let pp_branch ppf (pattern, expression) =
        Format.fprintf ppf "@[<hov 2>|@ %a =>@ %a@]" pp_comp_pattern pattern
          pp_comp_expression expression
      in
      let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
      if check_coverage then
        Format.fprintf ppf "@[case@ %a@ --not@ of@;%a@]" pp_comp_expression
          scrutinee pp_branches branches
      else
        Format.fprintf ppf "@[case@ %a@ of@;%a@]" pp_comp_expression
          scrutinee pp_branches branches
  | Comp.Expression.Tuple { elements; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]"
        (List2.pp ~pp_sep:Format.comma pp_comp_expression)
        elements
  | Comp.Expression.Hole { label; _ } -> (
      match label with
      | Option.None -> Format.pp_print_string ppf "?"
      | Option.Some label -> Format.fprintf ppf "?%a" Identifier.pp label)
  | Comp.Expression.BoxHole _ -> Format.pp_print_string ppf "_"
  | Comp.Expression.Observation { observation; arguments; _ } -> (
      match List1.of_list arguments with
      | Option.None ->
          Format.fprintf ppf ".%a" Qualified_identifier.pp observation
      | Option.Some arguments ->
          Format.fprintf ppf ".%a@ %a" Qualified_identifier.pp observation
            (List1.pp ~pp_sep:Format.pp_print_space
               (parenthesize_argument_prefix_operator
                  precedence_of_comp_expression ~parent_precedence
                  pp_comp_expression))
            arguments)
  | Comp.Expression.TypeAnnotated { expression; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_comp_expression ~parent_precedence
           pp_comp_expression)
        expression
        (parenthesize_right_argument_left_associative_operator
           precedence_of_comp_typ ~parent_precedence pp_comp_typ)
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
        ~pp_applicand:pp_comp_expression ~pp_argument:pp_comp_expression
        ~parent_precedence ppf (applicand, arguments)

and pp_comp_pattern ppf pattern =
  let parent_precedence = precedence_of_comp_pattern pattern in
  match pattern with
  | Comp.Pattern.Variable { identifier; _ } -> Identifier.pp ppf identifier
  | Comp.Pattern.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
      else Qualified_identifier.pp ppf identifier
  | Comp.Pattern.MetaObject { meta_pattern; _ } ->
      pp_meta_pattern ppf meta_pattern
  | Comp.Pattern.Tuple { elements; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]"
        (List2.pp ~pp_sep:Format.comma pp_comp_pattern)
        elements
  | Comp.Pattern.TypeAnnotated { pattern; typ; _ } ->
      (* The type annotation operator is left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_of_comp_pattern ~parent_precedence pp_comp_pattern)
        pattern
        (parenthesize_right_argument_left_associative_operator
           precedence_of_comp_typ ~parent_precedence pp_comp_typ)
        typ
  | Comp.Pattern.MetaTypeAnnotated
      { annotation_identifier; annotation_type; body; _ } ->
      Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
        annotation_identifier pp_meta_typ annotation_type pp_comp_pattern
        body
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
        ~pp_applicand:pp_comp_pattern ~pp_argument:pp_comp_pattern
        ~parent_precedence ppf (applicand, arguments)

and pp_comp_copattern ppf copattern =
  let[@warning "-26"] parent_precedence = precedence_of_comp_copattern in
  match copattern with
  | Comp.Copattern.Observation { observation; arguments; _ } -> (
      match List1.of_list arguments with
      | Option.None ->
          Format.fprintf ppf "@[<2>.%a@]" Qualified_identifier.pp observation
      | Option.Some arguments ->
          Format.fprintf ppf "@[<2>.%a@ %a@]" Qualified_identifier.pp
            observation
            (List1.pp ~pp_sep:Format.pp_print_space pp_comp_pattern)
            arguments)
  | Comp.Copattern.Pattern pattern -> pp_comp_pattern ppf pattern

and pp_comp_context ppf context =
  let pp_binding ppf (identifier, typ) =
    Format.fprintf ppf "%a :@ %a" Identifier.pp identifier pp_comp_typ typ
  in
  let { Comp.Context.bindings; _ } = context in
  List.pp ~pp_sep:Format.comma pp_binding ppf bindings

(** {1 Pretty-Printing Harpoon Syntax} *)

let rec pp_harpoon_proof ppf proof =
  match proof with
  | Harpoon.Proof.Incomplete { label; _ } -> (
      match label with
      | Option.None -> Format.pp_print_string ppf "?"
      | Option.Some label -> Identifier.pp ppf label)
  | Harpoon.Proof.Command { command; body; _ } ->
      Format.fprintf ppf "@[%a@];@,%a" pp_harpoon_command command
        pp_harpoon_proof body
  | Harpoon.Proof.Directive { directive; _ } ->
      pp_harpoon_directive ppf directive

and pp_harpoon_command ppf command =
  match command with
  | Harpoon.Command.By { expression; assignee; _ } ->
      Format.fprintf ppf "@[<2>by@ %a@ as@ %a@]" pp_comp_expression
        expression Identifier.pp assignee
  | Harpoon.Command.Unbox { expression; assignee; modifier = Option.None; _ }
    ->
      Format.fprintf ppf "@[<2>unbox@ %a@ as@ %a@]" pp_comp_expression
        expression Identifier.pp assignee
  | Harpoon.Command.Unbox
      { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
      Format.fprintf ppf "@[<2>strengthen@ %a@ as@ %a@]" pp_comp_expression
        expression Identifier.pp assignee

and pp_harpoon_directive ppf directive =
  match directive with
  | Harpoon.Directive.Intros { hypothetical; _ } ->
      Format.fprintf ppf "@[<v>intros@,%a@]" pp_harpoon_hypothetical
        hypothetical
  | Harpoon.Directive.Solve { solution; _ } ->
      Format.fprintf ppf "@[<hov 2>solve@ %a@]" pp_comp_expression solution
  | Harpoon.Directive.Split { scrutinee; branches; _ } ->
      Format.fprintf ppf "@[split@ %a as@]@,@[<v>%a@]" pp_comp_expression
        scrutinee
        (List1.pp ~pp_sep:Format.pp_print_cut pp_harpoon_split_branch)
        branches
  | Harpoon.Directive.Impossible { scrutinee; _ } ->
      Format.fprintf ppf "@[impossible@ @[%a@]@]" pp_comp_expression
        scrutinee
  | Harpoon.Directive.Suffices { scrutinee; branches; _ } ->
      Format.fprintf ppf "@[<v>@[<2>suffices by@ %a@] toshow@,@[<v>%a@]@]"
        pp_comp_expression scrutinee
        (List.pp ~pp_sep:Format.pp_print_cut pp_harpoon_suffices_branch)
        branches

and pp_harpoon_split_branch ppf branch =
  let { Harpoon.Split_branch.label; body; _ } = branch in
  Format.fprintf ppf "@[<v>case %a:@,%a@]" pp_harpoon_split_branch_label
    label pp_harpoon_hypothetical body

and pp_harpoon_split_branch_label ppf label =
  match label with
  | Harpoon.Split_branch.Label.Constant { identifier; _ } ->
      Qualified_identifier.pp ppf identifier
  | Harpoon.Split_branch.Label.Bound_variable _ ->
      Format.pp_print_string ppf "head variable"
  | Harpoon.Split_branch.Label.Empty_context _ ->
      Format.pp_print_string ppf "empty context"
  | Harpoon.Split_branch.Label.Extended_context { schema_element; _ } ->
      Format.fprintf ppf "extended by %d" schema_element
  | Harpoon.Split_branch.Label.Parameter_variable
      { schema_element; projection; _ } -> (
      match projection with
      | Option.None -> Format.fprintf ppf "%d" schema_element
      | Option.Some projection ->
          Format.fprintf ppf "%d.%d" schema_element projection)

and pp_harpoon_suffices_branch ppf branch =
  let { Harpoon.Suffices_branch.goal; proof; _ } = branch in
  Format.fprintf ppf "@[<v 2>@[%a@] {@,@[<v>%a@]@]@,}" pp_comp_typ goal
    pp_harpoon_proof proof

and pp_harpoon_hypothetical ppf hypothetical =
  let { Harpoon.Hypothetical.meta_context =
          { Meta.Context.bindings = meta_context_bindings; _ }
      ; comp_context = { Comp.Context.bindings = comp_context_bindings; _ }
      ; proof
      ; _
      } =
    hypothetical
  in
  Format.fprintf ppf "@[<v>{ @[<hv>%a@]@,| @[<hv>%a@]@,; @[<v>%a@]@,}@]"
    (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
         Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp i pp_meta_typ t))
    meta_context_bindings
    (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
         Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp i pp_comp_typ t))
    comp_context_bindings pp_harpoon_proof proof

and pp_harpoon_repl_command ppf repl_command =
  match repl_command with
  | Harpoon.Repl.Command.Rename { rename_from; rename_to; level = `comp; _ }
    ->
      Format.fprintf ppf "@[<2>rename@ comp@ %a@ %a@]" Identifier.pp
        rename_from Identifier.pp rename_to
  | Harpoon.Repl.Command.Rename { rename_from; rename_to; level = `meta; _ }
    ->
      Format.fprintf ppf "@[<2>rename@ meta@ %a@ %a@]" Identifier.pp
        rename_from Identifier.pp rename_to
  | Harpoon.Repl.Command.Toggle_automation { kind; change; _ } ->
      let pp_toggle_automation_kind ppf = function
        | `auto_intros -> Format.pp_print_string ppf "auto-intros"
        | `auto_solve_trivial ->
            Format.pp_print_string ppf "auto-solve-trivial"
      and pp_toggle_automation_change ppf = function
        | `on -> Format.pp_print_string ppf "on"
        | `off -> Format.pp_print_string ppf "off"
        | `toggle -> Format.pp_print_string ppf "toggle"
      in
      Format.fprintf ppf "@[<2>toggle-automation@ %a@ %a@]"
        pp_toggle_automation_kind kind pp_toggle_automation_change change
  | Harpoon.Repl.Command.Type { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>type@ %a@]" pp_comp_expression scrutinee
  | Harpoon.Repl.Command.Info { kind; object_identifier; _ } ->
      let pp_info_kind ppf = function
        | `prog -> Format.pp_print_string ppf "theorem"
      in
      Format.fprintf ppf "@[<2>info@ %a@ %a@]" pp_info_kind kind
        Qualified_identifier.pp object_identifier
  | Harpoon.Repl.Command.Select_theorem { theorem; _ } ->
      Format.fprintf ppf "@[<2>select@ %a@]" Qualified_identifier.pp theorem
  | Harpoon.Repl.Command.Theorem { subcommand; _ } ->
      let pp_theorem_subcommand ppf = function
        | `list -> Format.pp_print_string ppf "list"
        | `defer -> Format.fprintf ppf "defer"
        | `show_ihs -> Format.pp_print_string ppf "show-ihs"
        | `show_proof -> Format.pp_print_string ppf "show-proof"
        | `dump_proof path -> Format.fprintf ppf "dump-proof@ \"%s\"" path
      in
      Format.fprintf ppf "@[<2>theorem@ %a@]" pp_theorem_subcommand
        subcommand
  | Harpoon.Repl.Command.Session { subcommand; _ } ->
      let pp_session_subcommand ppf = function
        | `list -> Format.pp_print_string ppf "list"
        | `defer -> Format.pp_print_string ppf "defer"
        | `create -> Format.pp_print_string ppf "create"
        | `serialize -> Format.pp_print_string ppf "serialize"
      in
      Format.fprintf ppf "@[<2>session@ %a@]" pp_session_subcommand
        subcommand
  | Harpoon.Repl.Command.Subgoal { subcommand; _ } ->
      let pp_subgoal_subcommand ppf = function
        | `list -> Format.pp_print_string ppf "list"
        | `defer -> Format.pp_print_string ppf "defer"
      in
      Format.fprintf ppf "@[<2>subgoal@ %a@]" pp_subgoal_subcommand
        subcommand
  | Harpoon.Repl.Command.Undo _ -> Format.pp_print_string ppf "undo"
  | Harpoon.Repl.Command.Redo _ -> Format.pp_print_string ppf "redo"
  | Harpoon.Repl.Command.History _ -> Format.pp_print_string ppf "history"
  | Harpoon.Repl.Command.Translate { theorem; _ } ->
      Format.fprintf ppf "@[<2>translate@ %a@]" Qualified_identifier.pp
        theorem
  | Harpoon.Repl.Command.Intros { introduced_variables = Option.None; _ } ->
      Format.pp_print_string ppf "intros"
  | Harpoon.Repl.Command.Intros
      { introduced_variables = Option.Some variables; _ } ->
      Format.fprintf ppf "@[intros@ %a@]"
        (List1.pp ~pp_sep:Format.pp_print_space Identifier.pp)
        variables
  | Harpoon.Repl.Command.Split { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>split@ %a@]" pp_comp_expression scrutinee
  | Harpoon.Repl.Command.Invert { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>invert@ %a@]" pp_comp_expression scrutinee
  | Harpoon.Repl.Command.Impossible { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>impossible@ %a@]" pp_comp_expression scrutinee
  | Harpoon.Repl.Command.Msplit { identifier; _ } ->
      Format.fprintf ppf "@[<2>msplit@ %a@]" Identifier.pp identifier
  | Harpoon.Repl.Command.Solve { solution; _ } ->
      Format.fprintf ppf "@[<2>solve@ %a@]" pp_comp_expression solution
  | Harpoon.Repl.Command.Unbox { expression; assignee; modifier = None; _ }
    ->
      Format.fprintf ppf "@[<2>unbox@ %a@ as@ %a@]" pp_comp_expression
        expression Identifier.pp assignee
  | Harpoon.Repl.Command.Unbox
      { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
      Format.fprintf ppf "@[<2>strengthen@ %a@ as@ %a@]" pp_comp_expression
        expression Identifier.pp assignee
  | Harpoon.Repl.Command.By { expression; assignee; _ } ->
      Format.fprintf ppf "@[<2>by@ %a@ as@ %a@]" pp_comp_expression
        expression Identifier.pp assignee
  | Harpoon.Repl.Command.Suffices { implication; goal_premises; _ } ->
      Format.fprintf ppf "@[suffices@ by@ %a@ toshow@ %a@]"
        pp_comp_expression implication
        (List.pp ~pp_sep:Format.comma (fun ppf -> function
           | `exact typ -> pp_comp_typ ppf typ
           | `infer _ -> Format.pp_print_string ppf "_"))
        goal_premises
  | Harpoon.Repl.Command.Help _ -> Format.pp_print_string ppf "help"

(** {1 Pretty-Printing Signature Syntax} *)

exception Unsupported_non_recursive_declaration

exception Unsupported_recursive_declaration

let pp_associativity ppf = function
  | Associativity.Left_associative -> Format.pp_print_string ppf "left"
  | Associativity.Right_associative -> Format.pp_print_string ppf "right"
  | Associativity.Non_associative -> Format.pp_print_string ppf "none"

let rec pp_signature_pragma ppf pragma =
  match pragma with
  | Signature.Pragma.Name
      { constant; meta_variable_base; computation_variable_base; _ } -> (
      match computation_variable_base with
      | Option.None ->
          Format.fprintf ppf "@[<2>--name@ %a@ %a.@]" Qualified_identifier.pp
            constant Identifier.pp meta_variable_base
      | Option.Some computation_variable_base ->
          Format.fprintf ppf "@[<2>--name@ %a@ %a@ %a.@]"
            Qualified_identifier.pp constant Identifier.pp meta_variable_base
            Identifier.pp computation_variable_base)
  | Signature.Pragma.Default_associativity { associativity; _ } ->
      Format.fprintf ppf "@[<2>--assoc@ %a.@]" pp_associativity associativity
  | Signature.Pragma.Prefix_fixity { constant; precedence; _ } -> (
      match precedence with
      | Option.None ->
          Format.fprintf ppf "@[<2>--prefix@ %a.@]" Qualified_identifier.pp
            constant
      | Option.Some precedence ->
          Format.fprintf ppf "@[<2>--prefix@ %a@ %i.@]"
            Qualified_identifier.pp constant precedence)
  | Signature.Pragma.Infix_fixity { constant; precedence; associativity; _ }
    -> (
      match (precedence, associativity) with
      | Option.Some precedence, Option.Some associativity ->
          Format.fprintf ppf "@[<2>--infix@ %a@ %i@ %a.@]"
            Qualified_identifier.pp constant precedence pp_associativity
            associativity
      | Option.Some precedence, Option.None ->
          Format.fprintf ppf "@[<2>--infix@ %a@ %i.@]"
            Qualified_identifier.pp constant precedence
      | Option.None, Option.Some associativity ->
          Format.fprintf ppf "@[<2>--infix@ %a@ %a.@]"
            Qualified_identifier.pp constant pp_associativity associativity
      | Option.None, Option.None ->
          Format.fprintf ppf "@[<2>--infix@ %a.@]" Qualified_identifier.pp
            constant)
  | Signature.Pragma.Postfix_fixity { constant; precedence; _ } -> (
      match precedence with
      | Option.None ->
          Format.fprintf ppf "@[<2>--postfix@ %a.@]" Qualified_identifier.pp
            constant
      | Option.Some precedence ->
          Format.fprintf ppf "@[<2>--postfix@ %a@ %i.@]"
            Qualified_identifier.pp constant precedence)
  | Signature.Pragma.Not _ -> Format.pp_print_string ppf "--not"
  | Signature.Pragma.Open_module { module_identifier; _ } ->
      Format.fprintf ppf "@[<2>--open@ %a.@]" Qualified_identifier.pp
        module_identifier
  | Signature.Pragma.Abbreviation { module_identifier; abbreviation; _ } ->
      Format.fprintf ppf "@[<2>--abbrev@ %a@ %a.@]" Qualified_identifier.pp
        module_identifier Identifier.pp abbreviation

and pp_signature_global_pragma ppf global_pragma =
  match global_pragma with
  | Signature.Global_pragma.No_strengthening _ ->
      Format.pp_print_string ppf "--nostrengthen"
  | Signature.Global_pragma.Warn_on_coverage_error _ ->
      Format.pp_print_string ppf "--warncoverage"
  | Signature.Global_pragma.Raise_error_on_coverage_error _ ->
      Format.pp_print_string ppf "--coverage"

and pp_signature_totality_declaration ppf totality_declaration =
  match totality_declaration with
  | Signature.Totality.Declaration.Trust _ ->
      Format.pp_print_string ppf "trust"
  | Signature.Totality.Declaration.Named
      { order; program; argument_labels; _ } -> (
      let pp_identifier_option ppf = function
        | Option.None -> Format.pp_print_string ppf "_"
        | Option.Some identifier -> Identifier.pp ppf identifier
      in
      match order with
      | Option.None ->
          Format.fprintf ppf "@[<2>total@ (%a)@]"
            (List.pp ~pp_sep:Format.pp_print_space pp_identifier_option)
            (Option.some program :: argument_labels)
      | Option.Some order ->
          Format.fprintf ppf "@[<2>total@ %a@ (%a)@]"
            (pp_signature_totality_order Identifier.pp)
            order
            (List.pp ~pp_sep:Format.pp_print_space pp_identifier_option)
            (Option.some program :: argument_labels))
  | Signature.Totality.Declaration.Numeric { order; _ } -> (
      match order with
      | Option.None -> Format.pp_print_string ppf "total"
      | Option.Some order ->
          Format.fprintf ppf "@[total@ %a@]"
            (pp_signature_totality_order Int.pp)
            order)

and pp_signature_totality_order :
    type a.
       (Format.formatter -> a -> Unit.t)
    -> Format.formatter
    -> a Signature.Totality.Order.t
    -> Unit.t =
 fun ppv ppf totality_order ->
  match totality_order with
  | Signature.Totality.Order.Argument { argument; _ } -> ppv ppf argument
  | Signature.Totality.Order.Lexical_ordering { arguments; _ } ->
      Format.fprintf ppf "@[<2>{@ %a@ }@]"
        (List1.pp ~pp_sep:Format.pp_print_space
           (pp_signature_totality_order ppv))
        arguments
  | Signature.Totality.Order.Simultaneous_ordering { arguments; _ } ->
      Format.fprintf ppf "@[<2>[@ %a@ ]@]"
        (List1.pp ~pp_sep:Format.pp_print_space
           (pp_signature_totality_order ppv))
        arguments

and pp_signature_declaration ppf declaration =
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
      Format.fprintf ppf "@[<2>%a :@ %a.@]" Identifier.pp identifier
        pp_lf_kind kind
  | Signature.Declaration.Const { identifier; typ; _ } ->
      Format.fprintf ppf "@[<2>%a :@ %a.@]" Identifier.pp identifier
        pp_lf_typ typ
  | Signature.Declaration.Schema { identifier; schema; _ } ->
      Format.fprintf ppf "@[<2>schema %a =@ %a;@]" Identifier.pp identifier
        pp_schema schema
  | Signature.Declaration.Recursive_declarations { declarations; _ } ->
      pp_recursive_declarations ppf declarations
  | Signature.Declaration.CompTypAbbrev { identifier; kind; typ; _ } ->
      Format.fprintf ppf "@[<2>typedef %a :@ %a =@ %a;@]" Identifier.pp
        identifier pp_comp_kind kind pp_comp_typ typ
  | Signature.Declaration.Val { identifier; typ; expression; _ } -> (
      match typ with
      | Option.None ->
          Format.fprintf ppf "@[<2>let@ %a@ =@ %a@]" Identifier.pp identifier
            pp_comp_expression expression
      | Option.Some typ ->
          Format.fprintf ppf "@[<2>let@ %a :@ %a@ =@ %a@]" Identifier.pp
            identifier pp_comp_typ typ pp_comp_expression expression)
  | Signature.Declaration.Query
      { identifier; meta_context; typ; expected_solutions; maximum_tries; _ }
    -> (
      let pp_meta_context ppf meta_context =
        let { Meta.Context.bindings; _ } = meta_context in
        List.pp ~pp_sep:Format.pp_print_space
          (fun ppf (i, t) ->
            Format.fprintf ppf "@[{@ %a :@ %a@ }@]" Identifier.pp i
              pp_meta_typ t)
          ppf bindings
      in
      let pp_query_argument ppf = function
        | Option.None -> Format.pp_print_string ppf "*"
        | Option.Some argument -> Format.pp_print_int ppf argument
      in
      match identifier with
      | Option.None ->
          Format.fprintf ppf "@[<2>query@ %a@ %a@ %a@ %a@]" pp_query_argument
            expected_solutions pp_query_argument maximum_tries
            pp_meta_context meta_context pp_lf_typ typ
      | Option.Some identifier ->
          Format.fprintf ppf "@[<2>query@ %a@ %a@ %a@ %a :@ %a@]"
            pp_query_argument expected_solutions pp_query_argument
            maximum_tries pp_meta_context meta_context Identifier.pp
            identifier pp_lf_typ typ)
  | Signature.Declaration.MQuery
      { identifier; typ; expected_solutions; search_tries; search_depth; _ }
    -> (
      let pp_mquery_argument ppf = function
        | Option.None -> Format.pp_print_string ppf "*"
        | Option.Some argument -> Format.pp_print_int ppf argument
      in
      match identifier with
      | Option.None ->
          Format.fprintf ppf "@[<2>mquery@ %a@ %a@ %a@ %a@]"
            pp_mquery_argument expected_solutions pp_mquery_argument
            search_tries pp_mquery_argument search_depth pp_comp_typ typ
      | Option.Some identifier ->
          Format.fprintf ppf "@[<2>mquery@ %a@ %a@ %a@ %a :@ %a@]"
            pp_mquery_argument expected_solutions pp_mquery_argument
            search_tries pp_mquery_argument search_depth Identifier.pp
            identifier pp_comp_typ typ)
  | Signature.Declaration.Module { identifier; entries; _ } ->
      Format.fprintf ppf "module %a = struct@;<1 2>@[<v 0>%a@]@.end"
        Identifier.pp identifier
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.@.")
           pp_signature_entry)
        entries
  | Signature.Declaration.Comment { content; _ } ->
      (* Workaround format string errors when inputing the documentation
         comment delimiters *)
      let left_delimiter = "%{{"
      and right_delimiter = "}}%" in
      Format.fprintf ppf "%s%s%s" left_delimiter content right_delimiter

and pp_recursive_declarations ppf declarations =
  Format.fprintf ppf "@[<v 0>%a@];"
    (List1.pp
       ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.@.and ")
       pp_grouped_declaration)
    (group_recursive_declarations declarations)

and pp_grouped_declaration ppf declaration =
  match declaration with
  | `Lf_typ (identifier, kind, constants) ->
      let pp_constant ppf (identifier, typ) =
        Format.fprintf ppf "@[<h>| %a :@ %a@]@" Identifier.pp identifier
          pp_lf_typ typ
      in
      Format.fprintf ppf "@[<v 0>LF %a :@ %a =@,%a@]" Identifier.pp
        identifier pp_lf_kind kind
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.") pp_constant)
        constants
  | `Inductive_comp_typ (identifier, kind, constants) ->
      let pp_constant ppf (identifier, typ) =
        Format.fprintf ppf "@[<h>| %a :@ %a@]@" Identifier.pp identifier
          pp_comp_typ typ
      in
      Format.fprintf ppf "@[<v 0>inductive %a :@ %a =@,%a@]" Identifier.pp
        identifier pp_comp_kind kind
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.") pp_constant)
        constants
  | `Stratified_comp_typ (identifier, kind, constants) ->
      let pp_constant ppf (identifier, typ) =
        Format.fprintf ppf "@[<h>| %a :@ %a@]@" Identifier.pp identifier
          pp_comp_typ typ
      in
      Format.fprintf ppf "@[<v 0>stratified %a :@ %a =@,%a@]" Identifier.pp
        identifier pp_comp_kind kind
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.") pp_constant)
        constants
  | `Coinductive_comp_typ (identifier, kind, constants) ->
      let pp_constant ppf (identifier, observation_typ, return_typ) =
        Format.fprintf ppf "@[<h>| %a :@ %a ::@ %a@]@" Identifier.pp
          identifier pp_comp_typ observation_typ pp_comp_typ return_typ
      in
      Format.fprintf ppf "@[<v 0>coinductive %a :@ %a =@,%a@]" Identifier.pp
        identifier pp_comp_kind kind
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.") pp_constant)
        constants
  | `Theorem (identifier, typ, order, body) -> (
      match order with
      | Option.None ->
          Format.fprintf ppf "@[<v 0>rec %a :@ %a =@ @[<v 2>%a@]@]"
            Identifier.pp identifier pp_comp_typ typ pp_comp_expression body
      | Option.Some order ->
          Format.fprintf ppf "@[<v 0>rec %a :@ %a =@.%a@.@[<v 2>%a@]@]"
            Identifier.pp identifier pp_comp_typ typ
            pp_signature_totality_declaration order pp_comp_expression body)
  | `Proof (identifier, typ, order, body) -> (
      match order with
      | Option.None ->
          Format.fprintf ppf "@[<v 0>proof %a :@ %a =@ @[<v 2>%a@]@]"
            Identifier.pp identifier pp_comp_typ typ pp_harpoon_proof body
      | Option.Some order ->
          Format.fprintf ppf "@[<v 0>proof %a :@ %a =@.%a@.@[<v 2>%a@]@]"
            Identifier.pp identifier pp_comp_typ typ
            pp_signature_totality_declaration order pp_harpoon_proof body)

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
        (Synext_location.location_of_signature_declaration first_declaration)
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
        (Synext_location.location_of_signature_declaration first_declaration)
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
        (Synext_location.location_of_signature_declaration first_declaration)
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
        `Coinductive_comp_typ (identifier, kind, comp_destructor_declarations)
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
        (Synext_location.location_of_signature_declaration first_declaration)
        Unsupported_recursive_declaration

and pp_signature_entry ppf entry =
  match entry with
  | Signature.Entry.Declaration declaration ->
      pp_signature_declaration ppf declaration
  | Signature.Entry.Pragma pragma -> pp_signature_pragma ppf pragma

and pp_signature ppf signature =
  let { Signature.global_pragmas; entries } = signature in
  match global_pragmas with
  | [] ->
      Format.fprintf ppf "@[<v 0>%a@]@."
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.@.")
           pp_signature_entry)
        entries
  | global_pragmas ->
      Format.fprintf ppf "@[<v 0>%a@.@.%a@]@."
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.@.")
           pp_signature_global_pragma)
        global_pragmas
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.@.")
           pp_signature_entry)
        entries

let pp_exception ppf = function
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
