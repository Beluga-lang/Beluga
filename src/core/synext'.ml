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
          ; parameter_name : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; range : Kind.t
          }
          (** [Pi { parameter_name = x; parameter_type = t; range; _ }] is the
              dependent product kind `{ x : t } range'. *)
      | Parenthesized of
          { location : Location.t
          ; kind : Kind.t
          }  (** [Parenthesized { kind; _ }] is the kind `( kind )`. *)
  end =
    Kind

  (** External LF types. *)
  and Typ : sig
    type t =
      | Variable of
          { location : Location.t
          ; name : Identifier.t
          }
          (** [Variable { name }] is the type-level variable with name
              `name', which is either a bound variable having a Pi-type
              binder, or a free variable having no such corresponding binder. *)
      | Constant of
          { location : Location.t
          ; name : QualifiedIdentifier.t
          }
          (** [Constant { name }] is the type-level constant with qualified
              name `name', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Term.t List1.t
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
          ; parameter_name : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; range : Typ.t
          }
          (** [Pi { parameter_name = x; parameter_type = t; range; _ }] is the
              dependent product type `{ x : t } range'. *)
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
          ; name : Identifier.t
          }
          (** [Variable { name }] is the term-level variable with name
              `name', which is either a bound variable having a lambda
              binder, or a free variable having no such corresponding binder. *)
      | Constant of
          { location : Location.t
          ; name : QualifiedIdentifier.t
          }
          (** [Constant { name }] is the term-level constant with qualified
              name `name', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Term.t
          ; arguments : Term.t List1.t
          }
          (** [Application { applicand; arguments }] is the term-level
              application of `applicand' with arguments `arguments'. *)
      | Abstraction of
          { location : Location.t
          ; parameter_name : Identifier.t Option.t
          ; parameter_type : Typ.t Option.t
          ; body : Term.t
          }
          (** [Abstraction { parameter_name = x; body; _ }] is the term `\x.
              body'. *)
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
    | Typ.Variable { location; _ }
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
end
