open Support

(** {1 External LF Syntax}

    The representation of LF kinds, types, and terms after parsing and
    data-dependent disambiguation. ASTs constructed with the constructors
    therein are not necessarily normalized.

    These types are only intended to be used in the definition of LF
    type-level or term-level constants. This is a weak, representational
    function space without case analysis or recursion.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation. *)
module LF = struct
  (** External LF kinds. *)
  module rec Kind : sig
    type t =
      | Typ of { location : Location.t }
          (** [Typ { _ }] is the kind of simple types `type'. *)
      | Arrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Kind.t
          }
          (** [Arrow { domain; range; _ }] is the kind `domain -> range'. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; body : Kind.t
          }
          (** [Pi { parameter_identifier = x; parameter_type = t; body; _ }] is the
              dependent product kind `{ x : t } body'. *)
      | Parenthesized of
          { location : Location.t
          ; kind : Kind.t
          }  (** [Parenthesized { kind; _ }] is the kind `( kind )`. *)
  end =
    Kind

  (** External LF types. *)
  and Typ : sig
    type t =
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          }
          (** [Constant { identifier; _ }] is the type-level constant with
              qualified identifier `identifier', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments }] is the type-level
              application of `applicand' with arguments `arguments'. *)
      | ForwardArrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Typ.t
          }
          (** [ForwardArrow { domain; range; _ }] is the type `domain ->
              range'. *)
      | BackwardArrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Typ.t
          }
          (** [BackwardArrow { domain; range; _ }] is the type `domain <-
              range'. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; body : Typ.t
          }
          (** [Pi { parameter_identifier = x; parameter_type = t; body; _ }] is the
              dependent product type `{ x : t } body'. *)
      | Parenthesized of
          { location : Location.t
          ; typ : Typ.t
          }  (** [Parenthesized { typ; _ }] is the type `( typ )`. *)
  end =
    Typ

  (** External LF terms. *)
  and Term : sig
    type t =
      | Variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
          (** [Variable { identifier; _ }] is the term-level variable with
              name `identifier', which is either a bound variable having a
              lambda binder, or a free variable having no such corresponding
              binder. *)
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          }
          (** [Constant { identifier; _ }] is the term-level constant with
              qualified identifier `identifier', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Term.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments }] is the term-level
              application of `applicand' with arguments `arguments'. *)
      | Abstraction of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t Option.t
          ; body : Term.t
          }
          (** [Abstraction { parameter_identifier = x; body; _ }] is the term
              `\x. body'. *)
      | Wildcard of { location : Location.t }
          (** [Wildcard { _ }] is the omission of a fresh term-level
              variable. *)
      | TypeAnnotated of
          { location : Location.t
          ; term : Term.t
          ; typ : Typ.t
          }
          (** [TypeAnnotated { term = u; typ = t; _ }] is the term `u : t`. *)
      | Parenthesized of
          { location : Location.t
          ; term : Term.t
          }  (** [Parenthesized { term; _ }] is the term `( term )`. *)
  end =
    Term

  let location_of_kind kind =
    match kind with
    | Kind.Typ { location; _ }
    | Kind.Arrow { location; _ }
    | Kind.Pi { location; _ }
    | Kind.Parenthesized { location; _ } -> location

  let location_of_typ typ =
    match typ with
    | Typ.Constant { location; _ }
    | Typ.Application { location; _ }
    | Typ.ForwardArrow { location; _ }
    | Typ.BackwardArrow { location; _ }
    | Typ.Pi { location; _ }
    | Typ.Parenthesized { location; _ } -> location

  let location_of_term term =
    match term with
    | Term.Variable { location; _ }
    | Term.Constant { location; _ }
    | Term.Application { location; _ }
    | Term.Abstraction { location; _ }
    | Term.Wildcard { location; _ }
    | Term.TypeAnnotated { location; _ }
    | Term.Parenthesized { location; _ } -> location

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
    | Typ.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_typ applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_typ range
    | Typ.BackwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]" pp_typ domain pp_typ range
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

  let rec pp_kind_debug ppf kind =
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>KindArrow(%a@ ->@ %a)@]" pp_typ domain pp_kind_debug range
    | Kind.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>KindPi({@ _@ :@ %a@ }@ %a)@]" pp_typ parameter_type
        pp_kind_debug body
    | Kind.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>KindPi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_kind_debug body
    | Kind.Parenthesized { kind; _ } ->
      Format.fprintf ppf "@[<2>KindParenthesized(%a)@]" pp_kind_debug kind

  and pp_typ_debug ppf typ =
    match typ with
    | Typ.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>TypeApplication(%a)@]" pp_typ_debug applicand
    | Typ.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>TypeApplication(%a@ %a)@]" pp_typ_debug applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term_debug)
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>TypeArrow(%a@ ->@ %a)@]" pp_typ_debug domain pp_typ_debug range
    | Typ.BackwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>TypeArrow(%a@ <-@ %a)@]" pp_typ_debug domain pp_typ_debug range
    | Typ.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>TypePi({@ _@ :@ %a@ }@ %a)@]" pp_typ_debug parameter_type
        pp_typ_debug body
    | Typ.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>TypePi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
        parameter_identifier pp_typ_debug parameter_type pp_typ_debug body
    | Typ.Parenthesized { typ; _ } ->
      Format.fprintf ppf "@[<2>TypeParenthesized(%a)@]" pp_typ_debug typ

  and pp_term_debug ppf term =
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>TermApplication(%a)@]" pp_term_debug applicand
    | Term.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>TermApplication(%a@ %a)@]" pp_term_debug applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term_debug)
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>TermAbstraction(\\_.@ %a)@]" pp_term_debug body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>TermAbstraction(\\_:%a.@ %a)@]" pp_typ parameter_type pp_term_debug
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>TermAbstraction(\\%a.@ %a)@]" Identifier.pp
        parameter_identifier pp_term_debug body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>TermAbstraction(\\%a:%a.@ %a)@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term_debug body
    | Term.Wildcard _ -> Format.fprintf ppf "_"
    | Term.TypeAnnotated { term; typ; _ } ->
      Format.fprintf ppf "@[<2>TermAnnotated(%a@ :@ %a)@]" pp_term_debug term pp_typ typ
    | Term.Parenthesized { term; _ } ->
      Format.fprintf ppf "@[<2>TermParenthesized(%a)@]" pp_term_debug term
end
