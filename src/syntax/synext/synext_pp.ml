(** Pretty-printing for the external syntax. *)

open Support
open Common
open Synext_definition
open Synext_precedence
open Parenthesizer

(** {1 Pretty-Printing LF Syntax} *)

module LF = struct
  open LF

  open Make_parenthesizer (Lf_precedence)

  let rec pp_lf_kind ppf kind =
    let parent_precedence = precedence_of_lf_kind kind in
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative *)
        Format.fprintf ppf "@[<2>%a →@ %a@]"
          (parenthesize_left_argument_right_associative_operator
             precedence_of_lf_typ ~parent_precedence pp_lf_typ)
          domain pp_lf_kind range
    | Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
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
    | Typ.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
        else Qualified_identifier.pp ppf identifier
    | Typ.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Typ.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Term.Application
                { applicand = Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_lf_typ
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:pp_lf_typ ~pp_argument:pp_lf_term ~parent_precedence
          ppf (applicand, arguments)
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<2>%a →@ %a@]"
          (match domain with
          | Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize pp_lf_typ
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ)
          domain
          (match range with
          | Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize pp_lf_typ
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ)
          range
    | Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<2>%a@ ← %a@]"
          (match range with
          | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_lf_typ
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ)
          range
          (match domain with
          | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_lf_typ
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_lf_typ ~parent_precedence pp_lf_typ)
          domain
    | Typ.Pi { parameter_identifier; parameter_type; body; _ } -> (
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
    | Term.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Term.Constant { identifier; quoted = true; _ } ->
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
    | Term.Constant { identifier; quoted = false; _ } ->
        Qualified_identifier.pp ppf identifier
    | Term.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Term.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Term.Application
                { applicand = Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_lf_term
          ~precedence_of_argument:precedence_of_lf_term
          ~pp_applicand:pp_lf_term ~pp_argument:pp_lf_term ~parent_precedence
          ppf (applicand, arguments)
    | Term.Abstraction { parameter_identifier; parameter_type; body; _ } -> (
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
    | Term.Wildcard _ -> Format.fprintf ppf "_"
    | Term.TypeAnnotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_lf_term ~parent_precedence pp_lf_term)
          term pp_lf_typ typ
end

(** {1 Pretty-Printing Contextual LF Syntax} *)

module CLF = struct
  open CLF

  open Make_parenthesizer (Clf_precedence)

  let rec pp_clf_typ ppf typ =
    let parent_precedence = precedence_of_clf_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
        else Qualified_identifier.pp ppf identifier
    | Typ.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Typ.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Term.Application
                { applicand = Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_clf_typ
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:pp_clf_typ ~pp_argument:pp_clf_term
          ~parent_precedence ppf (applicand, arguments)
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows, so backward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<2>%a →@ %a@]"
          (match domain with
          | Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize pp_clf_typ
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ)
          domain
          (match range with
          | Typ.Arrow { orientation = `Backward; _ } ->
              parenthesize pp_clf_typ
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ)
          range
    | Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows, so forward arrows have to be parenthesized *)
        Format.fprintf ppf "@[<2>%a@ ← %a@]"
          (match range with
          | Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize pp_clf_typ
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ)
          range
          (match domain with
          | Typ.Arrow { orientation = `Forward; _ } ->
              parenthesize pp_clf_typ
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_clf_typ ~parent_precedence pp_clf_typ)
          domain
    | Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
        (* Pi-operators are weak prefix operators *)
        Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
          (fun ppf -> function
            | Option.Some parameter_identifier ->
                Identifier.pp ppf parameter_identifier
            | Option.None -> Format.fprintf ppf "_")
          parameter_identifier pp_clf_typ parameter_type pp_clf_typ body
    | Typ.Block { elements = `Unnamed typ; _ } ->
        Format.fprintf ppf "@[<2>block (%a)]" pp_clf_typ typ
    | Typ.Block { elements = `Record nts; _ } ->
        Format.fprintf ppf "@[<2>block (%a)]"
          (List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
               Format.fprintf ppf "%a :@ %a" Identifier.pp i pp_clf_typ t))
          nts

  and pp_clf_term ppf term =
    let parent_precedence = precedence_of_clf_term term in
    match term with
    | Term.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Term.Parameter_variable { identifier; _ } ->
        Identifier.pp ppf identifier
    | Term.Substitution_variable { identifier; _ } ->
        Identifier.pp ppf identifier
    | Term.Constant { identifier; quoted = true; _ } ->
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
    | Term.Constant { identifier; quoted = false; _ } ->
        Qualified_identifier.pp ppf identifier
    | Term.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Term.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Term.Application
                { applicand = Term.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_clf_term
          ~precedence_of_argument:precedence_of_clf_term
          ~pp_applicand:pp_clf_term ~pp_argument:pp_clf_term
          ~parent_precedence ppf (applicand, arguments)
    | Term.Abstraction { parameter_identifier; parameter_type; body; _ } -> (
        (* Lambdas are weak prefix operators, so the body of a lambda does
           not need to be parenthesized *)
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
              parameter_identifier pp_clf_typ parameter_type pp_clf_term body
        )
    | Term.Hole { variant = `Underscore; _ } -> Format.fprintf ppf "_"
    | Term.Hole { variant = `Unlabelled; _ } -> Format.fprintf ppf "?"
    | Term.Hole { variant = `Labelled label; _ } ->
        Format.fprintf ppf "?%a" Identifier.pp label
    | Term.Substitution { term; substitution; _ } ->
        (* Substitutions are left-associative *)
        Format.fprintf ppf "@[<2>%a[%a]@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence pp_clf_term)
          term pp_clf_substitution substitution
    | Term.Tuple { terms; _ } ->
        Format.fprintf ppf "@[<2><%a>@]"
          (List1.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
             pp_clf_term)
          terms
    | Term.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<2>%a.%d@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence pp_clf_term)
          term i
    | Term.Projection { term; projection = `By_identifier i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<2>%a.%a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence pp_clf_term)
          term Identifier.pp i
    | Term.TypeAnnotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term ~parent_precedence pp_clf_term)
          term pp_clf_typ typ

  and pp_clf_substitution ppf substitution =
    match substitution with
    | { Substitution.head = Substitution.Head.None _; terms = []; _ } ->
        Format.fprintf ppf "^"
    | { Substitution.head = Substitution.Head.Identity _; terms = []; _ } ->
        Format.fprintf ppf ".."
    | { Substitution.head = Substitution.Head.None _; terms; _ } ->
        Format.fprintf ppf "@[<2>%a@]"
          (List.pp ~pp_sep:Format.comma pp_clf_term)
          terms
    | { Substitution.head = Substitution.Head.Identity _; terms; _ } ->
        Format.fprintf ppf "@[<2>..,@ %a@]"
          (List.pp ~pp_sep:Format.comma pp_clf_term)
          terms
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a@]" Identifier.pp identifier
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a[%a]@]" Identifier.pp identifier
          pp_clf_substitution closure
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
          (List.pp ~pp_sep:Format.comma pp_clf_term)
          terms
    | { Substitution.head =
          Substitution.Head.Substitution_variable
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
          Format.fprintf ppf "%a :@ %a" Identifier.pp identifier pp_clf_typ
            typ
    in
    match context with
    | { Context.head = Context.Head.None _; bindings = []; _ } ->
        Format.fprintf ppf "^"
    | { Context.head = Context.Head.Hole _; bindings = []; _ } ->
        Format.fprintf ppf "_"
    | { Context.head = Context.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        Identifier.pp ppf identifier
    | { Context.head = Context.Head.None _; bindings; _ } ->
        Format.fprintf ppf "@[<2>%a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { Context.head = Context.Head.Hole _; bindings; _ } ->
        Format.fprintf ppf "@[<2>_,@ %a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { Context.head = Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings

  let rec pp_clf_term_pattern ppf term =
    let parent_precedence = precedence_of_clf_term_pattern term in
    match term with
    | Term.Pattern.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Term.Pattern.Parameter_variable { identifier; _ } ->
        Identifier.pp ppf identifier
    | Term.Pattern.Substitution_variable { identifier; _ } ->
        Identifier.pp ppf identifier
    | Term.Pattern.Constant { identifier; quoted = true; _ } ->
        Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
    | Term.Pattern.Constant { identifier; quoted = false; _ } ->
        Qualified_identifier.pp ppf identifier
    | Term.Pattern.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Term.Pattern.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Term.Pattern.Application
                { applicand =
                    Term.Pattern.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_clf_term_pattern
          ~precedence_of_argument:precedence_of_clf_term_pattern
          ~pp_applicand:pp_clf_term_pattern ~pp_argument:pp_clf_term_pattern
          ~parent_precedence ppf (applicand, arguments)
    | Term.Pattern.Abstraction
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
    | Term.Pattern.Wildcard _ -> Format.fprintf ppf "_"
    | Term.Pattern.Substitution { term; substitution; _ } ->
        Format.fprintf ppf "@[<2>%a[%a]@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             pp_clf_term_pattern)
          term pp_clf_substitution substitution
    | Term.Pattern.Tuple { terms; _ } ->
        Format.fprintf ppf "@[<2><%a>@]"
          (List1.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
             pp_clf_term_pattern)
          terms
    | Term.Pattern.Projection { term; projection = `By_position i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<2>%a.%d@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             pp_clf_term_pattern)
          term i
    | Term.Pattern.Projection { term; projection = `By_identifier i; _ } ->
        (* Projections are left-associative *)
        Format.fprintf ppf "@[<2>%a.%a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             pp_clf_term_pattern)
          term Identifier.pp i
    | Term.Pattern.TypeAnnotated { term; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_clf_term_pattern ~parent_precedence
             pp_clf_term_pattern)
          term pp_clf_typ typ

  and pp_clf_substitution_pattern ppf substitution_pattern =
    match substitution_pattern with
    | { Substitution.Pattern.head = Substitution.Pattern.Head.None _
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "^"
    | { Substitution.Pattern.head = Substitution.Pattern.Head.Identity _
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf ".."
    | { Substitution.Pattern.head = Substitution.Pattern.Head.None _
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a@]"
          (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
          terms
    | { Substitution.Pattern.head = Substitution.Pattern.Head.Identity _
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<2>..,@ %a@]"
          (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
          terms
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a@]" Identifier.pp identifier
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a[%a]@]" Identifier.pp identifier
          pp_clf_substitution closure
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
          (List.pp ~pp_sep:Format.comma pp_clf_term_pattern)
          terms
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
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
    | { Context.Pattern.head = Context.Pattern.Head.None _
      ; bindings = []
      ; _
      } ->
        Format.fprintf ppf "^"
    | { Context.Pattern.head = Context.Pattern.Head.Hole _
      ; bindings = []
      ; _
      } ->
        Format.fprintf ppf "_"
    | { Context.Pattern.head =
          Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } ->
        Identifier.pp ppf identifier
    | { Context.Pattern.head = Context.Pattern.Head.None _; bindings; _ } ->
        Format.fprintf ppf "@[<2>%a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { Context.Pattern.head = Context.Pattern.Head.Hole _; bindings; _ } ->
        Format.fprintf ppf "@[<2>_,@ %a@]"
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
    | { Context.Pattern.head =
          Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
          (List.pp ~pp_sep:Format.comma pp_typing)
          bindings
end

(** {1 Pretty-Printing Meta-Level Syntax} *)
module Meta = struct
  open Meta

  open Make_parenthesizer (Meta_precedence)

  let rec pp_meta_typ ppf typ =
    match typ with
    | Typ.Context_schema { schema; _ } -> pp_schema ppf schema
    | Typ.Contextual_typ { context; typ; _ } ->
        Format.fprintf ppf "@[<2>(%a@ ⊢@ %a)@]" CLF.pp_clf_context context
          CLF.pp_clf_typ typ
    | Typ.Parameter_typ { context; typ; _ } ->
        Format.fprintf ppf "@[<2>#(%a@ ⊢@ %a)@]" CLF.pp_clf_context context
          CLF.pp_clf_typ typ
    | Typ.Plain_substitution_typ { domain; range; _ } ->
        Format.fprintf ppf "@[<2>$(%a@ ⊢@ %a)@]" CLF.pp_clf_context domain
          CLF.pp_clf_context range
    | Typ.Renaming_substitution_typ { domain; range; _ } ->
        Format.fprintf ppf "@[<2>$(%a@ ⊢#@ %a)@]" CLF.pp_clf_context domain
          CLF.pp_clf_context range

  and pp_meta_object ppf object_ =
    match object_ with
    | Object.Context { context; _ } ->
        Format.fprintf ppf "@[[%a]@]" CLF.pp_clf_context context
    | Object.Contextual_term { context; term; _ } ->
        Format.fprintf ppf "@[<2>[%a@ ⊢@ %a]@]" CLF.pp_clf_context context
          CLF.pp_clf_term term
    | Object.Plain_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<2>$[%a@ ⊢@ %a]@]" CLF.pp_clf_context domain
          CLF.pp_clf_substitution range
    | Object.Renaming_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<2>$[%a@ ⊢#@ %a]@]" CLF.pp_clf_context domain
          CLF.pp_clf_substitution range

  and pp_meta_pattern ppf pattern =
    match pattern with
    | Pattern.Context { context; _ } ->
        Format.fprintf ppf "@[[%a]@]" CLF.pp_clf_context_pattern context
    | Pattern.Contextual_term { context; term; _ } ->
        Format.fprintf ppf "@[<2>[%a@ ⊢@ %a]@]" CLF.pp_clf_context_pattern
          context CLF.pp_clf_term_pattern term
    | Pattern.Plain_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<2>$[%a@ ⊢@ %a]@]" CLF.pp_clf_context_pattern
          domain CLF.pp_clf_substitution_pattern range
    | Pattern.Renaming_substitution { domain; range; _ } ->
        Format.fprintf ppf "@[<2>$[%a@ ⊢#@ %a]@]" CLF.pp_clf_context_pattern
          domain CLF.pp_clf_substitution_pattern range

  and pp_meta_context ppf context =
    let { Context.bindings; _ } = context in
    List.pp ~pp_sep:Format.comma
      (fun ppf (i, t) ->
        Format.fprintf ppf "@[%a :@ %a@]" Identifier.pp i pp_meta_typ t)
      ppf bindings

  and pp_schema ppf schema =
    let parent_precedence = precedence_of_schema schema in
    let pp_bindings =
      List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
          Format.fprintf ppf "@[%a :@ %a@]" Identifier.pp i CLF.pp_clf_typ t)
    in
    match schema with
    | Schema.Constant { identifier; _ } ->
        Qualified_identifier.pp ppf identifier
    | Schema.Alternation { schemas; _ } ->
        List2.pp
          ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ +@ ")
          (parenthesize_term_of_lesser_than_or_equal_precedence
             precedence_of_schema ~parent_precedence pp_schema)
          ppf schemas
    | Schema.Element { some = Option.None; block = `Unnamed t; _ } ->
        Format.fprintf ppf "@[<2>block@ %a@]" CLF.pp_clf_typ t
    | Schema.Element { some = Option.None; block = `Record bindings; _ } ->
        Format.fprintf ppf "@[<2>block@ (%a)@]" pp_bindings bindings
    | Schema.Element
        { some = Option.Some some_bindings; block = `Unnamed t; _ } ->
        Format.fprintf ppf "@[<2>some@ [%a]@ block@ %a@]" pp_bindings
          some_bindings CLF.pp_clf_typ t
    | Schema.Element
        { some = Option.Some some_bindings
        ; block = `Record block_bindings
        ; _
        } ->
        Format.fprintf ppf "@[<2>some@ [%a]@ block@ (%a)@]" pp_bindings
          some_bindings pp_bindings block_bindings
end

(** {1 Pretty-Printing Computation-Level Syntax} *)

module Comp = struct
  open Comp

  open Make_parenthesizer (Comp_precedence)

  (** [is_atomic_pattern pattern] is [true] if and only if [pattern] is an
      atomic pattern as defined in {!Parser}, meaning that it never requires
      additional enclosing parentheses during printing to avoid ambiguities. *)
  let is_atomic_pattern pattern =
    match pattern with
    | Pattern.Variable _
    | Pattern.Constant _
    | Pattern.MetaObject _
    | Pattern.Tuple _
    | Pattern.Wildcard _ ->
        true
    | _ -> false

  let is_atomic_copattern copattern =
    match copattern with
    | Copattern.Observation _ -> true
    | Copattern.Pattern pattern -> is_atomic_pattern pattern

  let rec pp_kind ppf kind =
    let parent_precedence = precedence_of_comp_kind kind in
    match kind with
    | Kind.Ctype _ -> Format.pp_print_string ppf "ctype"
    | Kind.Arrow { domain; range; _ } ->
        (* Right arrows are right-associative *)
        Format.fprintf ppf "@[<2>%a@ →@ %a@]"
          (parenthesize_left_argument_right_associative_operator
             precedence_of_comp_typ ~parent_precedence pp_typ)
          domain pp_kind range
    | Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
        (* Pi-operators are weak prefix operators *)
        match parameter_identifier with
        | Option.None ->
            Format.fprintf ppf "@[<2>{@ _ :@ %a@ }@ %a@]" Meta.pp_meta_typ
              parameter_type pp_kind body
        | Option.Some parameter_identifier ->
            Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
              parameter_identifier Meta.pp_meta_typ parameter_type pp_kind
              body)

  and pp_typ ppf typ =
    let parent_precedence = precedence_of_comp_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
        else Qualified_identifier.pp ppf identifier
    | Typ.Pi { parameter_identifier; plicity; parameter_type; body; _ } -> (
        (* Pi-operators are weak prefix operators *)
        let pp_parameter_identifier parameter_type ppf parameter_identifier =
          match (parameter_identifier, parameter_type) with
          | Option.Some parameter_identifier, _ ->
              Identifier.pp ppf parameter_identifier
          | ( Option.None
            , ( Synext_definition.Meta.Typ.Context_schema _
              | Synext_definition.Meta.Typ.Contextual_typ _ ) ) ->
              Format.pp_print_string ppf "_"
          | Option.None, Synext_definition.Meta.Typ.Parameter_typ _ ->
              Format.pp_print_string ppf "#_"
          | ( Option.None
            , ( Synext_definition.Meta.Typ.Plain_substitution_typ _
              | Synext_definition.Meta.Typ.Renaming_substitution_typ _ ) ) ->
              Format.pp_print_string ppf "$_"
        in
        match plicity with
        | Plicity.Implicit ->
            Format.fprintf ppf "@[<2>(@ %a :@ %a@ )@ %a@]"
              (pp_parameter_identifier parameter_type)
              parameter_identifier Meta.pp_meta_typ parameter_type pp_typ
              body
        | Plicity.Explicit ->
            Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
              (pp_parameter_identifier parameter_type)
              parameter_identifier Meta.pp_meta_typ parameter_type pp_typ
              body)
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
        (* Forward arrows are right-associative and of equal precedence with
           backward arrows *)
        Format.fprintf ppf "@[<2>%a →@ %a@]"
          (match domain with
          | Typ.Arrow { orientation = `Backward; _ } -> parenthesize pp_typ
          | _ ->
              parenthesize_left_argument_right_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_typ)
          domain
          (match range with
          | Typ.Arrow { orientation = `Backward; _ } -> parenthesize pp_typ
          | _ ->
              parenthesize_right_argument_right_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_typ)
          range
    | Typ.Arrow { range; domain; orientation = `Backward; _ } ->
        (* Backward arrows are left-associative and of equal precedence with
           forward arrows *)
        Format.fprintf ppf "@[<2>%a@ ← %a@]"
          (match range with
          | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_typ
          | _ ->
              parenthesize_left_argument_left_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_typ)
          range
          (match domain with
          | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_typ
          | _ ->
              parenthesize_right_argument_left_associative_operator
                precedence_of_comp_typ ~parent_precedence pp_typ)
          domain
    | Typ.Cross { types; _ } ->
        List2.pp
          ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ * ")
          (parenthesize_term_of_lesser_than_or_equal_precedence
             precedence_of_comp_typ ~parent_precedence pp_typ)
          ppf types
    | Typ.Box { meta_type; _ } -> Meta.pp_meta_typ ppf meta_type
    | Typ.Application { applicand; arguments; _ } -> (
        match applicand with
        | Typ.Application
            { applicand =
                Typ.Constant { identifier; operator; quoted = false; _ }
            ; _
            } -> (
            match Operator.fixity operator with
            | Fixity.Prefix ->
                Format.fprintf ppf "@[<2>%a@ %a@]" Qualified_identifier.pp
                  identifier
                  (List1.pp ~pp_sep:Format.pp_print_space Meta.pp_meta_object)
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
                Format.fprintf ppf "@[<2>%a@ %a@ %a@]" Meta.pp_meta_object
                  left_argument Qualified_identifier.pp identifier
                  Meta.pp_meta_object right_argument
            | Fixity.Postfix ->
                assert (
                  List1.compare_length_with arguments 1
                  = 0
                    (* Postfix operators must be applied with exactly one
                       argument. *));
                let[@warning "-8"] (List1.T (argument, [])) = arguments in
                Format.fprintf ppf "@[<2>%a@ %a@]" Meta.pp_meta_object
                  argument Qualified_identifier.pp identifier)
        | _ ->
            Format.fprintf ppf "@[<2>%a@ %a@]"
              (parenthesize_term_of_lesser_than_or_equal_precedence
                 precedence_of_comp_typ ~parent_precedence pp_typ)
              applicand
              (List1.pp ~pp_sep:Format.pp_print_space Meta.pp_meta_object)
              arguments)

  and pp_expression ppf expression =
    let parent_precedence = precedence_of_comp_expression expression in
    match expression with
    | Expression.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Expression.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
        else Qualified_identifier.pp ppf identifier
    | Expression.Fn { parameters; body; _ } ->
        let pp_parameter ppf parameter =
          match parameter with
          | Option.None -> Format.pp_print_string ppf "_"
          | Option.Some parameter -> Identifier.pp ppf parameter
        in
        Format.fprintf ppf "@[<2>fn@ %a =>@ %a@]"
          (List1.pp ~pp_sep:Format.pp_print_space pp_parameter)
          parameters pp_expression body
    | Expression.Mlam { parameters; body; _ } ->
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
          pp_expression body
    | Expression.Fun { branches; _ } ->
        let pp_branch_pattern ppf copattern =
          if is_atomic_copattern copattern then pp_copattern ppf copattern
          else parenthesize pp_copattern ppf copattern
        in
        let pp_branch_patterns =
          List1.pp ~pp_sep:Format.pp_print_space pp_branch_pattern
        in
        let pp_branch ppf (patterns, expression) =
          Format.fprintf ppf "@[<hov 2>|@ %a =>@ %a@]" pp_branch_patterns
            patterns pp_expression expression
        in
        let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
        Format.fprintf ppf "@[<2>fun@;%a@]" pp_branches branches
    | Expression.Let { pattern; scrutinee; body; _ } ->
        Format.fprintf ppf "@[<hov 2>let@ %a =@ %a@ in@ %a@]" pp_pattern
          pattern pp_expression scrutinee pp_expression body
    | Expression.Box { meta_object; _ } ->
        Meta.pp_meta_object ppf meta_object
    | Expression.Impossible { scrutinee; _ } ->
        (* [impossible (impossible (...))] is right-associative *)
        Format.fprintf ppf "@[<2>impossible@ %a@]"
          (parenthesize_right_argument_right_associative_operator
             precedence_of_comp_expression ~parent_precedence pp_expression)
          scrutinee
    | Expression.Case { scrutinee; check_coverage; branches; _ } ->
        let pp_branch ppf (pattern, expression) =
          Format.fprintf ppf "@[<hov 2>|@ %a =>@ %a@]" pp_pattern pattern
            pp_expression expression
        in
        let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
        if check_coverage then
          Format.fprintf ppf "@[case@ %a@ --not@ of@;%a@]" pp_expression
            scrutinee pp_branches branches
        else
          Format.fprintf ppf "@[case@ %a@ of@;%a@]" pp_expression scrutinee
            pp_branches branches
    | Expression.Tuple { elements; _ } ->
        Format.fprintf ppf "@[<2>(%a)@]"
          (List2.pp ~pp_sep:Format.comma pp_expression)
          elements
    | Expression.Hole { label; _ } -> (
        match label with
        | Option.None -> Format.pp_print_string ppf "?"
        | Option.Some label -> Format.fprintf ppf "?%a" Identifier.pp label)
    | Expression.BoxHole _ -> Format.pp_print_string ppf "_"
    | Expression.Observation { observation; arguments; _ } -> (
        match List1.of_list arguments with
        | Option.None ->
            Format.fprintf ppf ".%a" Qualified_identifier.pp observation
        | Option.Some arguments ->
            Format.fprintf ppf ".%a@ %a" Qualified_identifier.pp observation
              (List1.pp ~pp_sep:Format.pp_print_space
                 (parenthesize_argument_prefix_operator
                    precedence_of_comp_expression ~parent_precedence
                    pp_expression))
              arguments)
    | Expression.TypeAnnotated { expression; typ; _ } ->
        (* Type ascriptions are left-associative *)
        Format.fprintf ppf "@[<2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_comp_expression ~parent_precedence pp_expression)
          expression
          (parenthesize_right_argument_left_associative_operator
             precedence_of_comp_typ ~parent_precedence pp_typ)
          typ
    | Expression.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Expression.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Expression.Application
                { applicand =
                    Expression.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_comp_expression
          ~precedence_of_argument:precedence_of_comp_expression
          ~pp_applicand:pp_expression ~pp_argument:pp_expression
          ~parent_precedence ppf (applicand, arguments)

  and pp_pattern ppf pattern =
    let parent_precedence = precedence_of_comp_pattern pattern in
    match pattern with
    | Pattern.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Pattern.Constant { identifier; quoted; operator; _ } ->
        if quoted && Bool.not (Operator.is_nullary operator) then
          Format.fprintf ppf "(%a)" Qualified_identifier.pp identifier
        else Qualified_identifier.pp ppf identifier
    | Pattern.MetaObject { meta_pattern; _ } ->
        Meta.pp_meta_pattern ppf meta_pattern
    | Pattern.Tuple { elements; _ } ->
        Format.fprintf ppf "@[<2>(%a)@]"
          (List2.pp ~pp_sep:Format.comma pp_pattern)
          elements
    | Pattern.TypeAnnotated { pattern; typ; _ } ->
        (* The type annotation operator is left-associative *)
        Format.fprintf ppf "@[<2>%a :@ %a@]"
          (parenthesize_left_argument_left_associative_operator
             precedence_of_comp_pattern ~parent_precedence pp_pattern)
          pattern
          (parenthesize_right_argument_left_associative_operator
             precedence_of_comp_typ ~parent_precedence pp_typ)
          typ
    | Pattern.MetaTypeAnnotated
        { annotation_identifier; annotation_type; body; _ } ->
        Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
          annotation_identifier Meta.pp_meta_typ annotation_type pp_pattern
          body
    | Pattern.Wildcard _ -> Format.pp_print_string ppf "_"
    | Pattern.Application { applicand; arguments; _ } ->
        pp_application
          ~guard_operator:(function
            | Pattern.Constant { operator; quoted = false; _ } ->
                `Operator operator
            | _ -> `Term)
          ~guard_operator_application:(function
            | Pattern.Application
                { applicand =
                    Pattern.Constant { operator; quoted = false; _ }
                ; _
                } ->
                `Operator_application operator
            | _ -> `Term)
          ~precedence_of_applicand:precedence_of_comp_pattern
          ~precedence_of_argument:precedence_of_comp_pattern
          ~pp_applicand:pp_pattern ~pp_argument:pp_pattern ~parent_precedence
          ppf (applicand, arguments)

  and pp_copattern ppf copattern =
    let[@warning "-26"] parent_precedence = precedence_of_comp_copattern in
    match copattern with
    | Copattern.Observation { observation; arguments; _ } -> (
        match List1.of_list arguments with
        | Option.None ->
            Format.fprintf ppf "@[<2>.%a@]" Qualified_identifier.pp
              observation
        | Option.Some arguments ->
            Format.fprintf ppf "@[<2>.%a@ %a@]" Qualified_identifier.pp
              observation
              (List1.pp ~pp_sep:Format.pp_print_space pp_pattern)
              arguments)
    | Copattern.Pattern pattern -> pp_pattern ppf pattern

  and pp_context ppf context =
    let pp_binding ppf (identifier, typ) =
      Format.fprintf ppf "%a :@ %a" Identifier.pp identifier pp_typ typ
    in
    let { Context.bindings; _ } = context in
    List.pp ~pp_sep:Format.comma pp_binding ppf bindings
end

(** {1 Pretty-Printing Harpoon Syntax} *)

module Harpoon = struct
  open Harpoon

  let rec pp_proof ppf proof =
    match proof with
    | Proof.Incomplete { label; _ } -> (
        match label with
        | Option.None -> Format.pp_print_string ppf "?"
        | Option.Some label -> Identifier.pp ppf label)
    | Proof.Command { command; body; _ } ->
        Format.fprintf ppf "@[%a@];@,%a" pp_command command pp_proof body
    | Proof.Directive { directive; _ } -> pp_directive ppf directive

  and pp_command ppf command =
    match command with
    | Command.By { expression; assignee; _ } ->
        Format.fprintf ppf "@[<2>by@ %a@ as@ %a@]" Comp.pp_expression
          expression Identifier.pp assignee
    | Command.Unbox { expression; assignee; modifier = Option.None; _ } ->
        Format.fprintf ppf "@[<2>unbox@ %a@ as@ %a@]" Comp.pp_expression
          expression Identifier.pp assignee
    | Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
        Format.fprintf ppf "@[<2>strengthen@ %a@ as@ %a@]" Comp.pp_expression
          expression Identifier.pp assignee

  and pp_directive ppf directive =
    match directive with
    | Directive.Intros { hypothetical; _ } ->
        Format.fprintf ppf "@[<v>intros@,%a@]" pp_hypothetical hypothetical
    | Directive.Solve { solution; _ } ->
        Format.fprintf ppf "@[<hov 2>solve@ %a@]" Comp.pp_expression solution
    | Directive.Split { scrutinee; branches; _ } ->
        Format.fprintf ppf "@[split@ %a as@]@,@[<v>%a@]" Comp.pp_expression
          scrutinee
          (List1.pp ~pp_sep:Format.pp_print_cut pp_split_branch)
          branches
    | Directive.Impossible { scrutinee; _ } ->
        Format.fprintf ppf "@[impossible@ @[%a@]@]" Comp.pp_expression
          scrutinee
    | Directive.Suffices { scrutinee; branches; _ } ->
        Format.fprintf ppf "@[<v>@[<2>suffices by@ %a@] toshow@,@[<v>%a@]@]"
          Comp.pp_expression scrutinee
          (List.pp ~pp_sep:Format.pp_print_cut pp_suffices_branch)
          branches

  and pp_split_branch ppf branch =
    let { Split_branch.label; body; _ } = branch in
    Format.fprintf ppf "@[<v>case %a:@,%a@]" pp_split_branch_label label
      pp_hypothetical body

  and pp_split_branch_label ppf label =
    match label with
    | Split_branch.Label.Constant { identifier; _ } ->
        Qualified_identifier.pp ppf identifier
    | Split_branch.Label.Bound_variable _ ->
        Format.pp_print_string ppf "head variable"
    | Split_branch.Label.Empty_context _ ->
        Format.pp_print_string ppf "empty context"
    | Split_branch.Label.Extended_context { schema_element; _ } ->
        Format.fprintf ppf "extended by %d" schema_element
    | Split_branch.Label.Parameter_variable { schema_element; projection; _ }
      -> (
        match projection with
        | Option.None -> Format.fprintf ppf "%d" schema_element
        | Option.Some projection ->
            Format.fprintf ppf "%d.%d" schema_element projection)

  and pp_suffices_branch ppf branch =
    let { Suffices_branch.goal; proof; _ } = branch in
    Format.fprintf ppf "@[<v 2>@[%a@] {@,@[<v>%a@]@]@,}" Comp.pp_typ goal
      pp_proof proof

  and pp_hypothetical ppf hypothetical =
    let { Hypothetical.meta_context =
            { Synext_definition.Meta.Context.bindings = meta_context_bindings
            ; _
            }
        ; comp_context =
            { Synext_definition.Comp.Context.bindings = comp_context_bindings
            ; _
            }
        ; proof
        ; _
        } =
      hypothetical
    in
    Format.fprintf ppf "@[<v>{ @[<hv>%a@]@,| @[<hv>%a@]@,; @[<v>%a@]@,}@]"
      (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
           Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp i
             Meta.pp_meta_typ t))
      meta_context_bindings
      (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
           Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp i Comp.pp_typ t))
      comp_context_bindings pp_proof proof

  and pp_repl_command ppf repl_command =
    match repl_command with
    | Repl.Command.Rename { rename_from; rename_to; level = `comp; _ } ->
        Format.fprintf ppf "@[<2>rename@ comp@ %a@ %a@]" Identifier.pp
          rename_from Identifier.pp rename_to
    | Repl.Command.Rename { rename_from; rename_to; level = `meta; _ } ->
        Format.fprintf ppf "@[<2>rename@ meta@ %a@ %a@]" Identifier.pp
          rename_from Identifier.pp rename_to
    | Repl.Command.Toggle_automation { kind; change; _ } ->
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
    | Repl.Command.Type { scrutinee; _ } ->
        Format.fprintf ppf "@[<2>type@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.Info { kind; object_identifier; _ } ->
        let pp_info_kind ppf = function
          | `prog -> Format.pp_print_string ppf "theorem"
        in
        Format.fprintf ppf "@[<2>info@ %a@ %a@]" pp_info_kind kind
          Qualified_identifier.pp object_identifier
    | Repl.Command.Select_theorem { theorem; _ } ->
        Format.fprintf ppf "@[<2>select@ %a@]" Qualified_identifier.pp
          theorem
    | Repl.Command.Theorem { subcommand; _ } ->
        let pp_theorem_subcommand ppf = function
          | `list -> Format.pp_print_string ppf "list"
          | `defer -> Format.fprintf ppf "defer"
          | `show_ihs -> Format.pp_print_string ppf "show-ihs"
          | `show_proof -> Format.pp_print_string ppf "show-proof"
          | `dump_proof path -> Format.fprintf ppf "dump-proof@ \"%s\"" path
        in
        Format.fprintf ppf "@[<2>theorem@ %a@]" pp_theorem_subcommand
          subcommand
    | Repl.Command.Session { subcommand; _ } ->
        let pp_session_subcommand ppf = function
          | `list -> Format.pp_print_string ppf "list"
          | `defer -> Format.pp_print_string ppf "defer"
          | `create -> Format.pp_print_string ppf "create"
          | `serialize -> Format.pp_print_string ppf "serialize"
        in
        Format.fprintf ppf "@[<2>session@ %a@]" pp_session_subcommand
          subcommand
    | Repl.Command.Subgoal { subcommand; _ } ->
        let pp_subgoal_subcommand ppf = function
          | `list -> Format.pp_print_string ppf "list"
          | `defer -> Format.pp_print_string ppf "defer"
        in
        Format.fprintf ppf "@[<2>subgoal@ %a@]" pp_subgoal_subcommand
          subcommand
    | Repl.Command.Undo _ -> Format.pp_print_string ppf "undo"
    | Repl.Command.Redo _ -> Format.pp_print_string ppf "redo"
    | Repl.Command.History _ -> Format.pp_print_string ppf "history"
    | Repl.Command.Translate { theorem; _ } ->
        Format.fprintf ppf "@[<2>translate@ %a@]" Qualified_identifier.pp
          theorem
    | Repl.Command.Intros { introduced_variables = Option.None; _ } ->
        Format.pp_print_string ppf "intros"
    | Repl.Command.Intros { introduced_variables = Option.Some variables; _ }
      ->
        Format.fprintf ppf "@[intros@ %a@]"
          (List1.pp ~pp_sep:Format.pp_print_space Identifier.pp)
          variables
    | Repl.Command.Split { scrutinee; _ } ->
        Format.fprintf ppf "@[<2>split@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.Invert { scrutinee; _ } ->
        Format.fprintf ppf "@[<2>invert@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.Impossible { scrutinee; _ } ->
        Format.fprintf ppf "@[<2>impossible@ %a@]" Comp.pp_expression
          scrutinee
    | Repl.Command.Msplit { identifier; _ } ->
        Format.fprintf ppf "@[<2>msplit@ %a@]" Identifier.pp identifier
    | Repl.Command.Solve { solution; _ } ->
        Format.fprintf ppf "@[<2>solve@ %a@]" Comp.pp_expression solution
    | Repl.Command.Unbox { expression; assignee; modifier = None; _ } ->
        Format.fprintf ppf "@[<2>unbox@ %a@ as@ %a@]" Comp.pp_expression
          expression Identifier.pp assignee
    | Repl.Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
        Format.fprintf ppf "@[<2>strengthen@ %a@ as@ %a@]" Comp.pp_expression
          expression Identifier.pp assignee
    | Repl.Command.By { expression; assignee; _ } ->
        Format.fprintf ppf "@[<2>by@ %a@ as@ %a@]" Comp.pp_expression
          expression Identifier.pp assignee
    | Repl.Command.Suffices { implication; goal_premises; _ } ->
        Format.fprintf ppf "@[suffices@ by@ %a@ toshow@ %a@]"
          Comp.pp_expression implication
          (List.pp ~pp_sep:Format.comma (fun ppf -> function
             | `exact typ -> Comp.pp_typ ppf typ
             | `infer _ -> Format.pp_print_string ppf "_"))
          goal_premises
    | Repl.Command.Help _ -> Format.pp_print_string ppf "help"
end

(** {1 Pretty-Printing Signature Syntax} *)

module Signature = struct
  open Signature

  exception Unsupported_non_recursive_declaration

  exception Unsupported_recursive_declaration

  let pp_associativity ppf = function
    | Associativity.Left_associative -> Format.pp_print_string ppf "left"
    | Associativity.Right_associative -> Format.pp_print_string ppf "right"
    | Associativity.Non_associative -> Format.pp_print_string ppf "none"

  let rec pp_pragma ppf pragma =
    match pragma with
    | Pragma.Name
        { constant; meta_variable_base; computation_variable_base; _ } -> (
        match computation_variable_base with
        | Option.None ->
            Format.fprintf ppf "@[<2>--name@ %a@ %a.@]"
              Qualified_identifier.pp constant Identifier.pp
              meta_variable_base
        | Option.Some computation_variable_base ->
            Format.fprintf ppf "@[<2>--name@ %a@ %a@ %a.@]"
              Qualified_identifier.pp constant Identifier.pp
              meta_variable_base Identifier.pp computation_variable_base)
    | Pragma.Default_associativity { associativity; _ } ->
        Format.fprintf ppf "@[<2>--assoc@ %a.@]" pp_associativity
          associativity
    | Pragma.Prefix_fixity { constant; precedence; _ } -> (
        match precedence with
        | Option.None ->
            Format.fprintf ppf "@[<2>--prefix@ %a.@]" Qualified_identifier.pp
              constant
        | Option.Some precedence ->
            Format.fprintf ppf "@[<2>--prefix@ %a@ %i.@]"
              Qualified_identifier.pp constant precedence)
    | Pragma.Infix_fixity { constant; precedence; associativity; _ } -> (
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
    | Pragma.Postfix_fixity { constant; precedence; _ } -> (
        match precedence with
        | Option.None ->
            Format.fprintf ppf "@[<2>--postfix@ %a.@]"
              Qualified_identifier.pp constant
        | Option.Some precedence ->
            Format.fprintf ppf "@[<2>--postfix@ %a@ %i.@]"
              Qualified_identifier.pp constant precedence)
    | Pragma.Not _ -> Format.pp_print_string ppf "--not"
    | Pragma.Open_module { module_identifier; _ } ->
        Format.fprintf ppf "@[<2>--open@ %a.@]" Qualified_identifier.pp
          module_identifier
    | Pragma.Abbreviation { module_identifier; abbreviation; _ } ->
        Format.fprintf ppf "@[<2>--abbrev@ %a@ %a.@]" Qualified_identifier.pp
          module_identifier Identifier.pp abbreviation

  and pp_global_pragma ppf global_pragma =
    match global_pragma with
    | Pragma.Global.No_strengthening _ ->
        Format.pp_print_string ppf "--nostrengthen"
    | Pragma.Global.Coverage { variant = `Error; _ } ->
        Format.pp_print_string ppf "--coverage"
    | Pragma.Global.Coverage { variant = `Warn; _ } ->
        Format.pp_print_string ppf "--warncoverage"

  and pp_totality_declaration ppf totality_declaration =
    match totality_declaration with
    | Totality.Declaration.Trust _ -> Format.pp_print_string ppf "trust"
    | Totality.Declaration.Named { order; program; argument_labels; _ } -> (
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
              (pp_totality_order Identifier.pp)
              order
              (List.pp ~pp_sep:Format.pp_print_space pp_identifier_option)
              (Option.some program :: argument_labels))
    | Totality.Declaration.Numeric { order; _ } -> (
        match order with
        | Option.None -> Format.pp_print_string ppf "total"
        | Option.Some order ->
            Format.fprintf ppf "@[total@ %a@]"
              (pp_totality_order Int.pp)
              order)

  and pp_totality_order :
      type a.
         (Format.formatter -> a -> Unit.t)
      -> Format.formatter
      -> a Totality.Order.t
      -> Unit.t =
   fun ppv ppf totality_order ->
    match totality_order with
    | Totality.Order.Argument { argument; _ } -> ppv ppf argument
    | Totality.Order.Lexical_ordering { arguments; _ } ->
        Format.fprintf ppf "@[<2>{@ %a@ }@]"
          (List1.pp ~pp_sep:Format.pp_print_space (pp_totality_order ppv))
          arguments
    | Totality.Order.Simultaneous_ordering { arguments; _ } ->
        Format.fprintf ppf "@[<2>[@ %a@ ]@]"
          (List1.pp ~pp_sep:Format.pp_print_space (pp_totality_order ppv))
          arguments

  and pp_declaration ppf declaration =
    match declaration with
    | Declaration.CompTyp _
    | Declaration.CompCotyp _
    | Declaration.CompConst _
    | Declaration.CompDest _
    | Declaration.Theorem _
    | Declaration.Proof _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration declaration)
          Unsupported_non_recursive_declaration
    | Declaration.Typ { identifier; kind; _ } ->
        Format.fprintf ppf "@[<2>%a :@ %a.@]" Identifier.pp identifier
          LF.pp_lf_kind kind
    | Declaration.Const { identifier; typ; _ } ->
        Format.fprintf ppf "@[<2>%a :@ %a.@]" Identifier.pp identifier
          LF.pp_lf_typ typ
    | Declaration.Schema { identifier; schema; _ } ->
        Format.fprintf ppf "@[<2>schema %a =@ %a;@]" Identifier.pp identifier
          Meta.pp_schema schema
    | Declaration.Pragma { pragma; _ } -> pp_pragma ppf pragma
    | Declaration.GlobalPragma { pragma; _ } -> pp_global_pragma ppf pragma
    | Declaration.Recursive_declarations { declarations; _ } ->
        pp_recursive_declarations ppf declarations
    | Declaration.CompTypAbbrev { identifier; kind; typ; _ } ->
        Format.fprintf ppf "@[<2>typedef %a :@ %a =@ %a;@]" Identifier.pp
          identifier Comp.pp_kind kind Comp.pp_typ typ
    | Declaration.Val { identifier; typ; expression; _ } -> (
        match typ with
        | Option.None ->
            Format.fprintf ppf "@[<2>let@ %a@ =@ %a@]" Identifier.pp
              identifier Comp.pp_expression expression
        | Option.Some typ ->
            Format.fprintf ppf "@[<2>let@ %a :@ %a@ =@ %a@]" Identifier.pp
              identifier Comp.pp_typ typ Comp.pp_expression expression)
    | Declaration.Query
        { identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        ; _
        } -> (
        let pp_meta_context ppf meta_context =
          let { Synext_definition.Meta.Context.bindings; _ } =
            meta_context
          in
          List.pp ~pp_sep:Format.pp_print_space
            (fun ppf (i, t) ->
              Format.fprintf ppf "@[{@ %a :@ %a@ }@]" Identifier.pp i
                Meta.pp_meta_typ t)
            ppf bindings
        in
        let pp_query_argument ppf = function
          | Option.None -> Format.pp_print_string ppf "*"
          | Option.Some argument -> Format.pp_print_int ppf argument
        in
        match identifier with
        | Option.None ->
            Format.fprintf ppf "@[<2>query@ %a@ %a@ %a@ %a@]"
              pp_query_argument expected_solutions pp_query_argument
              maximum_tries pp_meta_context meta_context LF.pp_lf_typ typ
        | Option.Some identifier ->
            Format.fprintf ppf "@[<2>query@ %a@ %a@ %a@ %a :@ %a@]"
              pp_query_argument expected_solutions pp_query_argument
              maximum_tries pp_meta_context meta_context Identifier.pp
              identifier LF.pp_lf_typ typ)
    | Declaration.MQuery
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
            Format.fprintf ppf "@[<2>mquery@ %a@ %a@ %a@ %a@]"
              pp_mquery_argument expected_solutions pp_mquery_argument
              search_tries pp_mquery_argument search_depth Comp.pp_typ typ
        | Option.Some identifier ->
            Format.fprintf ppf "@[<2>mquery@ %a@ %a@ %a@ %a :@ %a@]"
              pp_mquery_argument expected_solutions pp_mquery_argument
              search_tries pp_mquery_argument search_depth Identifier.pp
              identifier Comp.pp_typ typ)
    | Declaration.Module { identifier; declarations; _ } ->
        Format.fprintf ppf "module %a = struct@;<1 2>@[<v 0>%a@]@.end"
          Identifier.pp identifier pp_signature declarations
    | Declaration.Comment { content; _ } ->
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
            LF.pp_lf_typ typ
        in
        Format.fprintf ppf "@[<v 0>LF %a :@ %a =@,%a@]" Identifier.pp
          identifier LF.pp_lf_kind kind
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.")
             pp_constant)
          constants
    | `Inductive_comp_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, typ) =
          Format.fprintf ppf "@[<h>| %a :@ %a@]@" Identifier.pp identifier
            Comp.pp_typ typ
        in
        Format.fprintf ppf "@[<v 0>inductive %a :@ %a =@,%a@]" Identifier.pp
          identifier Comp.pp_kind kind
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.")
             pp_constant)
          constants
    | `Stratified_comp_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, typ) =
          Format.fprintf ppf "@[<h>| %a :@ %a@]@" Identifier.pp identifier
            Comp.pp_typ typ
        in
        Format.fprintf ppf "@[<v 0>stratified %a :@ %a =@,%a@]" Identifier.pp
          identifier Comp.pp_kind kind
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.")
             pp_constant)
          constants
    | `Coinductive_comp_typ (identifier, kind, constants) ->
        let pp_constant ppf (identifier, observation_typ, return_typ) =
          Format.fprintf ppf "@[<h>| %a :@ %a ::@ %a@]@" Identifier.pp
            identifier Comp.pp_typ observation_typ Comp.pp_typ return_typ
        in
        Format.fprintf ppf "@[<v 0>coinductive %a :@ %a =@,%a@]"
          Identifier.pp identifier Comp.pp_kind kind
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.")
             pp_constant)
          constants
    | `Theorem (identifier, typ, order, body) -> (
        match order with
        | Option.None ->
            Format.fprintf ppf "@[<v 0>rec %a :@ %a =@ @[<v 2>%a@]@]"
              Identifier.pp identifier Comp.pp_typ typ Comp.pp_expression
              body
        | Option.Some order ->
            Format.fprintf ppf "@[<v 0>rec %a :@ %a =@.%a@.@[<v 2>%a@]@]"
              Identifier.pp identifier Comp.pp_typ typ
              pp_totality_declaration order Comp.pp_expression body)
    | `Proof (identifier, typ, order, body) -> (
        match order with
        | Option.None ->
            Format.fprintf ppf "@[<v 0>proof %a :@ %a =@ @[<v 2>%a@]@]"
              Identifier.pp identifier Comp.pp_typ typ Harpoon.pp_proof body
        | Option.Some order ->
            Format.fprintf ppf "@[<v 0>proof %a :@ %a =@.%a@.@[<v 2>%a@]@]"
              Identifier.pp identifier Comp.pp_typ typ
              pp_totality_declaration order Harpoon.pp_proof body)

  and group_recursive_declarations declarations =
    let (List1.T (first_declaration, declarations')) = declarations in
    match first_declaration with
    | Declaration.Typ _ ->
        group_recursive_lf_typ_declarations first_declaration declarations'
    | Declaration.Theorem _
    | Declaration.Proof _ ->
        group_recursive_theorem_declarations first_declaration declarations'
    | Declaration.CompTyp _
    | Declaration.CompCotyp _ ->
        group_recursive_comp_typ_declarations first_declaration declarations'
    | _ ->
        Error.raise_at1
          (Synext_location.location_of_signature_declaration
             first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_lf_typ_declarations first_declaration declarations =
    match first_declaration with
    | Declaration.Typ { identifier; kind; _ } -> (
        let lf_term_constant_declarations, declarations' =
          List.take_while_map
            (function
              | Declaration.Const { identifier; typ; _ } ->
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
    | Declaration.Theorem { identifier; typ; order; body; _ } -> (
        let theorem_declaration = `Theorem (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton theorem_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons theorem_declaration theorem_declarations)
    | Declaration.Proof { identifier; typ; order; body; _ } -> (
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
    | Declaration.CompTyp { identifier; kind; datatype_flavour; _ } -> (
        let comp_constructor_declarations, declarations' =
          List.take_while_map
            (function
              | Declaration.CompConst { identifier; typ; _ } ->
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
    | Declaration.CompCotyp { identifier; kind; _ } -> (
        let comp_destructor_declarations, declarations' =
          List.take_while_map
            (function
              | Declaration.CompDest
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

  and pp_signature ppf signature =
    Format.fprintf ppf "@[<v 0>%a@]@."
      (List.pp
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@.@.")
         pp_declaration)
      signature

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
end

(** {1 Aliases} *)

(** {2 LF} *)

let pp_lf_kind = LF.pp_lf_kind

let pp_lf_typ = LF.pp_lf_typ

let pp_lf_term = LF.pp_lf_term

(** {2 Contextual LF} *)

let pp_clf_typ = CLF.pp_clf_typ

let pp_clf_term = CLF.pp_clf_term

let pp_clf_term_pattern = CLF.pp_clf_term_pattern

let pp_clf_substitution = CLF.pp_clf_substitution

let pp_clf_substitution_pattern = CLF.pp_clf_substitution_pattern

let pp_clf_context = CLF.pp_clf_context

let pp_clf_context_pattern = CLF.pp_clf_context_pattern

(** {2 Meta-Level} *)

let pp_meta_typ = Meta.pp_meta_typ

let pp_meta_object = Meta.pp_meta_object

let pp_meta_context = Meta.pp_meta_context

let pp_meta_pattern = Meta.pp_meta_pattern

let pp_schema = Meta.pp_schema

(** {2 Computation-Level} *)

let pp_comp_kind = Comp.pp_kind

let pp_comp_typ = Comp.pp_typ

let pp_comp_expression = Comp.pp_expression

let pp_comp_pattern = Comp.pp_pattern

let pp_comp_copattern = Comp.pp_copattern

let pp_comp_context = Comp.pp_context

(** {2 Harpoon} *)

let pp_harpoon_proof = Harpoon.pp_proof

let pp_harpoon_command = Harpoon.pp_command

let pp_harpoon_directive = Harpoon.pp_directive

let pp_harpoon_hypothetical = Harpoon.pp_hypothetical

let pp_harpoon_repl_command = Harpoon.pp_repl_command

(** {2 Signature} *)

let pp_signature_pragma = Signature.pp_pragma

let pp_signature_global_pragma = Signature.pp_global_pragma

let pp_signature_totality_declaration = Signature.pp_totality_declaration

let pp_signature_declaration = Signature.pp_declaration

let pp_signature_signature = Signature.pp_signature
