open Support
open Synext'

module LF = struct
  open LF

  (** [remove_parentheses_kind kind] is [kind] without parentheses, except
      for quoted type-level and term-level constants. Printing this kind may
      not result in a syntactically valid LF kind. *)
  let rec remove_parentheses_kind kind =
    match kind with
    | Kind.Typ _ -> kind
    | Kind.Arrow { location; domain; range } ->
      let domain' = remove_parentheses_typ domain
      and range' = remove_parentheses_kind range in
      Kind.Arrow { location; domain = domain'; range = range' }
    | Kind.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = remove_parentheses_typ parameter_type
      and body' = remove_parentheses_kind body in
      Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Kind.Parenthesized { kind; _ } -> remove_parentheses_kind kind

  (** [remove_parentheses_typ typ] is [typ] without parentheses, except for
      quoted type-level and term-level constants. Printing this type may not
      result in a syntactically valid LF type. *)
  and remove_parentheses_typ typ =
    match typ with
    | Typ.Constant _ -> typ
    | Typ.Application { location; applicand; arguments } ->
      let applicand' = remove_parentheses_typ applicand
      and arguments' = List.map remove_parentheses_term arguments in
      Typ.Application
        { location; applicand = applicand'; arguments = arguments' }
    | Typ.ForwardArrow { location; domain; range } ->
      let domain' = remove_parentheses_typ domain
      and range' = remove_parentheses_typ range in
      Typ.ForwardArrow { location; domain = domain'; range = range' }
    | Typ.BackwardArrow { location; domain; range } ->
      let domain' = remove_parentheses_typ domain
      and range' = remove_parentheses_typ range in
      Typ.BackwardArrow { location; domain = domain'; range = range' }
    | Typ.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = remove_parentheses_typ parameter_type
      and body' = remove_parentheses_typ body in
      Typ.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Typ.Parenthesized { typ = Typ.Constant _; _ } -> typ
    | Typ.Parenthesized { typ; _ } -> remove_parentheses_typ typ

  (** [remove_parentheses_term term] is [term] without parentheses, except
      for quoted type-level and term-level constants. Printing this term may
      not result in a syntactically valid LF term. *)
  and remove_parentheses_term term =
    match term with
    | Term.Variable _ -> term
    | Term.Constant _ -> term
    | Term.Application { location; applicand; arguments } ->
      let applicand' = remove_parentheses_term applicand
      and arguments' = List.map remove_parentheses_term arguments in
      Term.Application
        { location; applicand = applicand'; arguments = arguments' }
    | Term.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = Option.map remove_parentheses_typ parameter_type
      and body' = remove_parentheses_term body in
      Term.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Wildcard _ -> term
    | Term.TypeAnnotated { location; term; typ } ->
      let term' = remove_parentheses_term term
      and typ' = remove_parentheses_typ typ in
      Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Term.Parenthesized { term; _ } -> remove_parentheses_term term

  let add_parentheses_kind kind =
    let location = location_of_kind kind in
    Kind.Parenthesized { location; kind }

  let add_parentheses_typ typ =
    let location = location_of_typ typ in
    Typ.Parenthesized { location; typ }

  let add_parentheses_term term =
    let location = location_of_term term in
    Term.Parenthesized { location; term }

  (** [parenthesize_kind kind] is [kind] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_kind},
      then the resultant LF kind can be parsed to the same AST modulo
      {!remove_parentheses_kind}. *)
  let rec parenthesize_kind kind =
    match kind with
    | Kind.Typ _ -> kind
    | Kind.Arrow { location; domain; range } ->
      let domain' =
        match domain with
        | Typ.Pi _ | Typ.ForwardArrow _ | Typ.BackwardArrow _ ->
          add_parentheses_typ (parenthesize_typ domain)
        | _ -> parenthesize_typ domain
      and range' = parenthesize_kind range in
      Kind.Arrow { location; domain = domain'; range = range' }
    | Kind.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = parenthesize_typ parameter_type
      and body' = parenthesize_kind body in
      Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Kind.Parenthesized _ -> kind

  (** [parenthesize_typ typ] is [typ] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_typ},
      then the resultant LF type can be parsed to the same AST modulo
      {!remove_parentheses_typ}. *)
  and parenthesize_typ typ =
    match typ with
    | Typ.Constant _ -> typ
    | Typ.Application
        { location
        ; applicand =
            Typ.Constant { operator = applicand_operator; _ } as applicand
        ; arguments
        } ->
      let applicand_precedence = Operator.precedence applicand_operator in
      let arguments' =
        parenthesize_arguments ~applicand_precedence arguments
      in
      Typ.Application { location; applicand; arguments = arguments' }
    | Typ.Application { location; applicand; arguments } ->
      let applicand' =
        match applicand with
        | (Typ.Constant _ | Typ.Parenthesized _) as argument ->
          parenthesize_typ argument
        | ( Typ.Application _
          | Typ.Pi _
          | Typ.ForwardArrow _
          | Typ.BackwardArrow _ ) as argument ->
          add_parentheses_typ (parenthesize_typ argument)
      in
      let arguments' = parenthesize_arguments arguments in
      Typ.Application
        { location; applicand = applicand'; arguments = arguments' }
    | Typ.ForwardArrow { location; domain; range } ->
      let domain' =
        match domain with
        | Typ.Pi _ | Typ.ForwardArrow _ | Typ.BackwardArrow _ ->
          add_parentheses_typ (parenthesize_typ domain)
        | _ -> parenthesize_typ domain
      and range' = parenthesize_typ range in
      Typ.ForwardArrow { location; domain = domain'; range = range' }
    | Typ.BackwardArrow { location; range; domain } ->
      let range' =
        match range with
        | Typ.Pi _ | Typ.ForwardArrow _ ->
          add_parentheses_typ (parenthesize_typ range)
        | _ -> parenthesize_typ range
      and domain' =
        match domain with
        | Typ.BackwardArrow _ ->
          add_parentheses_typ (parenthesize_typ domain)
        | _ -> parenthesize_typ domain
      in
      Typ.BackwardArrow { location; range = range'; domain = domain' }
    | Typ.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = parenthesize_typ parameter_type
      and body' = parenthesize_typ body in
      Typ.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Typ.Parenthesized _ -> typ

  (** [parenthesize_term term] is [term] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_term},
      then the resultant LF term can be parsed to the same AST modulo
      {!remove_parentheses_term}. *)
  and parenthesize_term term =
    match term with
    | Term.Variable _ -> term
    | Term.Constant _ -> term
    | Term.Application
        { location
        ; applicand =
            Term.Constant { operator = applicand_operator; _ } as applicand
        ; arguments
        } ->
      let applicand_precedence = Operator.precedence applicand_operator in
      let arguments' =
        parenthesize_arguments ~applicand_precedence arguments
      in
      Term.Application { location; applicand; arguments = arguments' }
    | Term.Application { location; applicand; arguments } ->
      let applicand' =
        match applicand with
        | ( Term.Variable _
          | Term.Constant _
          | Term.Wildcard _
          | Term.Parenthesized _ ) as argument -> parenthesize_term argument
        | (Term.Application _ | Term.Abstraction _ | Term.TypeAnnotated _) as
          argument -> add_parentheses_term (parenthesize_term argument)
      in
      let arguments' = parenthesize_arguments arguments in
      Term.Application
        { location; applicand = applicand'; arguments = arguments' }
    | Term.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = Option.map parenthesize_typ parameter_type
      and body' = parenthesize_term body in
      Term.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Wildcard _ -> term
    | Term.TypeAnnotated { location; term; typ } ->
      let term' =
        match term with
        | Term.Abstraction _ | Term.TypeAnnotated _ ->
          add_parentheses_term (parenthesize_term term)
        | _ -> parenthesize_term term
      and typ' = parenthesize_typ typ in
      Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Term.Parenthesized _ -> term

  and parenthesize_arguments ?(applicand_precedence = -1) arguments =
    List.map
      (function
        | Term.Application
            { applicand = Term.Constant { operator = argument_operator; _ }
            ; _
            } as argument ->
          let argument_precedence = Operator.precedence argument_operator in
          if argument_precedence > applicand_precedence then
            add_parentheses_term (parenthesize_term argument)
          else parenthesize_term argument
        | ( Term.Variable _
          | Term.Constant _
          | Term.Wildcard _
          | Term.Parenthesized _ ) as argument -> parenthesize_term argument
        | (Term.Application _ | Term.Abstraction _ | Term.TypeAnnotated _) as
          argument -> add_parentheses_term (parenthesize_term argument))
      arguments

  let rec pp_kind ppf kind =
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_kind range
    | Kind.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_typ parameter_type
        pp_kind body
    | Kind.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_kind body
    | Kind.Parenthesized { kind; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_kind kind

  and pp_typ ppf typ =
    match typ with
    | Typ.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ applicand
    | Typ.Application
        { applicand = Typ.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term left_argument
          QualifiedIdentifier.pp identifier pp_term right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term argument
          QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_typ applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_typ range
    | Typ.BackwardArrow { range; domain; _ } ->
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]" pp_typ range pp_typ domain
    | Typ.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_typ parameter_type
        pp_typ body
    | Typ.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Parenthesized { typ; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_typ typ

  and pp_term ppf term =
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term applicand
    | Term.Application
        { applicand = Term.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term left_argument
          QualifiedIdentifier.pp identifier pp_term right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term argument
          QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_term applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term body
    | Term.Wildcard _ -> Format.fprintf ppf "_"
    | Term.TypeAnnotated { term; typ; _ } ->
      Format.fprintf ppf "@[<2>%a@ :@ %a@]" pp_term term pp_typ typ
    | Term.Parenthesized { term; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_term term

  module Debug = struct
    let rec pp_kind ppf kind =
      match kind with
      | Kind.Typ _ -> Format.fprintf ppf "type"
      | Kind.Arrow { domain; range; _ } ->
        Format.fprintf ppf "@[<2>KindArrow(%a@ ->@ %a)@]" pp_typ domain
          pp_kind range
      | Kind.Pi
          { parameter_identifier = Option.None; parameter_type; body; _ } ->
        Format.fprintf ppf "@[<2>KindPi({@ _@ :@ %a@ }@ %a)@]" pp_typ
          parameter_type pp_kind body
      | Kind.Pi
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>KindPi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_kind body
      | Kind.Parenthesized { kind; _ } ->
        Format.fprintf ppf "@[<2>KindParenthesized(%a)@]" pp_kind kind

    and pp_typ ppf typ =
      match typ with
      | Typ.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Typ.Application { applicand; arguments = []; _ } ->
        Format.fprintf ppf "@[<2>TypeApplication(%a)@]" pp_typ applicand
      | Typ.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TypeApplication(%a@ %a)@]" pp_typ applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Typ.ForwardArrow { domain; range; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(%a@ ->@ %a)@]" pp_typ domain
          pp_typ range
      | Typ.BackwardArrow { range; domain; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(%a@ <-@ %a)@]" pp_typ range pp_typ
          domain
      | Typ.Pi
          { parameter_identifier = Option.None; parameter_type; body; _ } ->
        Format.fprintf ppf "@[<2>TypePi({@ _@ :@ %a@ }@ %a)@]" pp_typ
          parameter_type pp_typ body
      | Typ.Pi
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TypePi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_typ body
      | Typ.Parenthesized { typ; _ } ->
        Format.fprintf ppf "@[<2>TypeParenthesized(%a)@]" pp_typ typ

    and pp_term ppf term =
      match term with
      | Term.Variable { identifier; _ } ->
        Format.fprintf ppf "%a" Identifier.pp identifier
      | Term.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Term.Application { applicand; arguments = []; _ } ->
        Format.fprintf ppf "@[<2>TermApplication(%a)@]" pp_term applicand
      | Term.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TermApplication(%a@ %a)@]" pp_term applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\_.@ %a)@]" pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\_:%a.@ %a)@]" pp_typ
          parameter_type pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\%a.@ %a)@]" Identifier.pp
          parameter_identifier pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\%a:%a.@ %a)@]"
          Identifier.pp parameter_identifier pp_typ parameter_type pp_term
          body
      | Term.Wildcard _ -> Format.fprintf ppf "_"
      | Term.TypeAnnotated { term; typ; _ } ->
        Format.fprintf ppf "@[<2>TermAnnotated(%a@ :@ %a)@]" pp_term term
          pp_typ typ
      | Term.Parenthesized { term; _ } ->
        Format.fprintf ppf "@[<2>TermParenthesized(%a)@]" pp_term term
  end
end

module CLF = struct
  open CLF

  let rec pp_typ ppf typ =
    match typ with
    | Typ.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ applicand
    | Typ.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_typ applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_typ range
    | Typ.BackwardArrow { range; domain; _ } ->
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]" pp_typ range pp_typ domain
    | Typ.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_typ parameter_type
        pp_typ body
    | Typ.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Block { elements = (Option.None, typ), []; _ } ->
      Format.fprintf ppf "@[<2>block %a]" pp_typ typ
    | Typ.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ } ->
      raise
      @@ Invalid_argument
           "[pp_typ] missing identifier for first type in block"
    | Typ.Block { elements = (Option.Some i1, t1), nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,")
           (fun ppf (i, t) ->
             Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t))
        ((i1, t1) :: nts)
    | Typ.Parenthesized { typ; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_typ typ

  and pp_term ppf term =
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term applicand
    | Term.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_term applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term body
    | Term.Hole _ -> Format.fprintf ppf "_"
    | Term.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a%a@]" pp_term term pp_substitution
        substitution
    | Term.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,") pp_term)
        terms
    | Term.Projection { term; projection = `By_position i; _ } ->
      Format.fprintf ppf "@[<2>%a.%d@]" pp_term term i
    | Term.Projection { term; projection = `By_identifier i; _ } ->
      Format.fprintf ppf "@[<2>%a.%a@]" pp_term term Identifier.pp i
    | Term.TypeAnnotated { term; typ; _ } ->
      Format.fprintf ppf "@[<2>%a@ :@ %a@]" pp_term term pp_typ typ
    | Term.Parenthesized { term; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_term term

  and pp_substitution ppf substitution =
    match substitution with
    | Substitution.{ extends_identity = false; terms = []; _ } ->
      Format.fprintf ppf "[]"
    | Substitution.{ extends_identity = true; terms = []; _ } ->
      Format.fprintf ppf "[..]"
    | Substitution.{ extends_identity = false; terms; _ } ->
      Format.fprintf ppf "@[<2>[%a]@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
        terms
    | Substitution.{ extends_identity = true; terms; _ } ->
      Format.fprintf ppf "@[<2>[..,@,%a]@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
        terms

  module Debug = struct
    let rec pp_typ ppf typ =
      match typ with
      | Typ.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Typ.Application { applicand; arguments = []; _ } ->
        Format.fprintf ppf "@[<2>TypeApplication(%a)@]" pp_typ applicand
      | Typ.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TypeApplication(%a@ %a)@]" pp_typ applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Typ.ForwardArrow { domain; range; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(%a@ ->@ %a)@]" pp_typ domain
          pp_typ range
      | Typ.BackwardArrow { range; domain; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(%a@ <-@ %a)@]" pp_typ range pp_typ
          domain
      | Typ.Pi
          { parameter_identifier = Option.None; parameter_type; body; _ } ->
        Format.fprintf ppf "@[<2>TypePi({@ _@ :@ %a@ }@ %a)@]" pp_typ
          parameter_type pp_typ body
      | Typ.Pi
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TypePi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_typ body
      | Typ.Block { elements = (Option.None, typ), []; _ } ->
        Format.fprintf ppf "@[<2>TypeBlock(block %a)]" pp_typ typ
      | Typ.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ } ->
        raise
        @@ Invalid_argument
             "[pp_typ] missing identifier for first type in block"
      | Typ.Block { elements = (Option.Some i1, t1), nts; _ } ->
        Format.fprintf ppf "@[<2>TypeBlock(block (%a))]"
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,")
             (fun ppf (i, t) ->
               Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t))
          ((i1, t1) :: nts)
      | Typ.Parenthesized { typ; _ } ->
        Format.fprintf ppf "@[<2>TypeParenthesized(%a)@]" pp_typ typ

    and pp_term ppf term =
      match term with
      | Term.Variable { identifier; _ } ->
        Format.fprintf ppf "%a" Identifier.pp identifier
      | Term.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Term.Application { applicand; arguments = []; _ } ->
        Format.fprintf ppf "@[<2>TermApplication(%a)@]" pp_term applicand
      | Term.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TermApplication(%a@ %a)@]" pp_term applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\_.@ %a)@]" pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\_:%a.@ %a)@]" pp_typ
          parameter_type pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\%a.@ %a)@]" Identifier.pp
          parameter_identifier pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\%a:%a.@ %a)@]"
          Identifier.pp parameter_identifier pp_typ parameter_type pp_term
          body
      | Term.Hole _ -> Format.fprintf ppf "_"
      | Term.Substitution { term; substitution; _ } ->
        Format.fprintf ppf "@[<2>TermSubstitution(%a%a)@]" pp_term term
          pp_substitution substitution
      | Term.Tuple { terms; _ } ->
        Format.fprintf ppf "@[<2>TermTuple(<%a>)@]"
          (List1.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,") pp_term)
          terms
      | Term.Projection { term; projection = `By_position i; _ } ->
        Format.fprintf ppf "@[<2>TermProjection(%a.%d)@]" pp_term term i
      | Term.Projection { term; projection = `By_identifier i; _ } ->
        Format.fprintf ppf "@[<2>TermProjection(%a.%a)@]" pp_term term
          Identifier.pp i
      | Term.TypeAnnotated { term; typ; _ } ->
        Format.fprintf ppf "@[<2>TermAnnotated(%a@ :@ %a)@]" pp_term term
          pp_typ typ
      | Term.Parenthesized { term; _ } ->
        Format.fprintf ppf "@[<2>TermParenthesized(%a)@]" pp_term term

    and pp_substitution ppf substitution =
      match substitution with
      | Substitution.{ extends_identity = false; terms = []; _ } ->
        Format.fprintf ppf "Substitution([])"
      | Substitution.{ extends_identity = true; terms = []; _ } ->
        Format.fprintf ppf "Substitution([..])"
      | Substitution.{ extends_identity = false; terms; _ } ->
        Format.fprintf ppf "@[<2>Substitution([%a])@]"
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
          terms
      | Substitution.{ extends_identity = true; terms; _ } ->
        Format.fprintf ppf "@[<2>Substitution([..,@,%a])@]"
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
          terms
  end
end
