open Support
open Synext'

module LF = struct
  open LF

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
