open Support

(** {1 External LF Syntax}

    The representation of LF kinds, types, and terms after parsing and
    data-dependent disambiguation. ASTs constructed with the constructors in
    this module are not necessarily normalized.

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
          ; operator : Operator.t
          }
          (** [Constant { identifier; _ }] is the type-level constant with
              qualified identifier `identifier', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the type-level
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
          ; operator : Operator.t
          }
          (** [Constant { identifier; _ }] is the term-level constant with
              qualified identifier `identifier', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Term.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the term-level
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
end

(** {1 External Contextual LF Syntax}

    The representation of contextual LF types, terms, and patterns after
    parsing and data-dependent disambiguation. ASTs constructed with the
    constructors in this module are not necessarily normalized.

    The distinction between contextual LF objects and plain LF objects is
    that contextual LF objects may have substitutions, and may appear in
    patterns.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation. *)
module CLF = struct
  (** External contextual LF types. *)
  module rec Typ : sig
    type t =
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          }
          (** [Constant { identifier; _ }] is the type-level constant with
              qualified identifier `identifier', which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the type-level
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
          (** [Pi { parameter_identifier = x; parameter_type = t; body; _ }]
              is the dependent product type `[{ x : t } body]'. *)
      | Block of
          { location : Location.t
          ; elements :
              (Identifier.t Option.t * Typ.t) * (Identifier.t * Typ.t) List.t
          }
          (** [Block { elements; _ }] is the block type `block (elements)'.

              - If [elements = ((Option.None, _typ), rest)], then
                [rest = \[\]].
              - If [elements = ((label, _typ), rest)] with [rest <> \[\]],
                then [label = Option.Some identifier]. *)
      | Parenthesized of
          { location : Location.t
          ; typ : Typ.t
          }  (** [Parenthesized { typ; _ }] is the type `( typ )`. *)
  end =
    Typ

  (** External contextual LF terms. *)
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
          ; operator : Operator.t
          }
          (** [Constant { identifier; _ }] is the term-level constant with
              qualified identifier `identifier', which is necessarily bound. *)
      | Substitution of
          { location : Location.t
          ; term : Term.t
          ; substitution : Substitution.t
          }
          (** [Substitution { term; substitution; _ }] is the term
              `term[substitution]'. *)
      | Application of
          { location : Location.t
          ; applicand : Term.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the term-level
              application of `applicand' with arguments `arguments'. *)
      | Abstraction of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t Option.t
          ; body : Term.t
          }
          (** [Abstraction { parameter_identifier = x; body; _ }] is the term
              `\x. body'. *)
      | Hole of
          { location : Location.t
          ; variant : [ `Underscore | `Unlabelled | `Labelled of String.t ]
          }
          (** [Hole { variant; _ }] is the omission of a term for
              reconstruction.

              - If [variant = `Underscore], then it is the hole `_'.
              - If [variant = `Unlabelled], then it is the hole `?'.
              - If [variant = `Labelled label], then it is the hole `?label'. *)
      | Tuple of
          { location : Location.t
          ; terms : Term.t List1.t
          }
          (** [Tuple { terms; _ }] is the tuple term `<t1; t2; t3>' if
              [List1.to_list terms = \[t1; t2; t3\]].

              This should not be confused with computational-level tuples.
              The type of a contextual LF term-level tuple is a block. *)
      | Projection of
          { location : Location.t
          ; term : Term.t
          ; projection :
              [ `By_identifier of Identifier.t | `By_position of Int.t ]
          }
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

  and Substitution : sig
    (** [{ extends_identity; terms; _ }] is either:

        - The empty substitution `[]' if [extends_identity = false] and
          [terms = \[\]]
        - The identity substitution `[..]' if [extends_identity = true] and
          [terms = \[\]]
        - A plain substitution `[t1, t2, t3]' if [extends_identity = false]
          and [terms = \[t1; t2; t3\]]
        - A substitution that extends the identity substitution
          `[.., t1, t2, t3]' if [extends_identity = true] and
          [terms = \[t1; t2; t3\]] *)
    type t =
      { location : Location.t
      ; extends_identity : Bool.t
      ; terms : Term.t List.t
      }
  end =
    Substitution

  let location_of_typ typ =
    match typ with
    | Typ.Constant { location; _ }
    | Typ.Application { location; _ }
    | Typ.ForwardArrow { location; _ }
    | Typ.BackwardArrow { location; _ }
    | Typ.Pi { location; _ }
    | Typ.Block { location; _ }
    | Typ.Parenthesized { location; _ } -> location

  let location_of_term term =
    match term with
    | Term.Variable { location; _ }
    | Term.Constant { location; _ }
    | Term.Application { location; _ }
    | Term.Abstraction { location; _ }
    | Term.Hole { location; _ }
    | Term.Substitution { location; _ }
    | Term.Tuple { location; _ }
    | Term.Projection { location; _ }
    | Term.TypeAnnotated { location; _ }
    | Term.Parenthesized { location; _ } -> location

  let location_of_substitution substitution =
    match substitution with
    | Substitution.{ location; _ } -> location
end
