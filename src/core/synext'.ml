(** The external syntax of Beluga. *)

open Support

(** {1 External LF Syntax} *)

(** The representation of LF kinds, types, and terms after parsing and
    data-dependent disambiguation.

    ASTs constructed with the constructors in this module are not necessarily
    normalized.

    These types are only intended to be used in the definition of LF
    type-level or term-level constants. This is a weak, representational
    function space without case analysis or recursion.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation.

    The metavariable:

    - [x] ranges over variables
    - [c] ranges over term-level constants
    - [a] ranges over type-level constants

    {[
      Kinds   K    ::= type | Πx:A.K | A → K
      Types   A, B ::= a | Πx:A.B | A → B | A M1 M2 ... Mn
      Terms   M, N ::= c | x | λx:A.M | M N1 N2 ... Nn | M:A | _
    ]} *)
module LF = struct
  (** External LF kinds. *)
  module rec Kind : sig
    type t =
      | Typ of { location : Location.t }
          (** [Typ { _ }] is the kind of simple types [type]. *)
      | Arrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Kind.t
          }
          (** [Arrow { domain; range; _ }] is the kind [domain -> range]. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; body : Kind.t
          }
          (** - [Pi { parameter_identifier = Option.Some "x"; parameter_type = t; body; _ }]
                is the dependent product kind [{ x : t } body]. The variable
                ["x"] ranges over LF terms.

              - [Pi { parameter_identifier = Option.None; parameter_type = t; body; _ }]
                is the dependent product kind [{ _ : t } body]. *)
  end =
    Kind

  (** External LF types. *)
  and Typ : sig
    type t =
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
          (** [Constant { identifier = "c"; _ }] is the type-level constant
              with qualified identifier ["c"], which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the type-level
              application of [applicand] with [arguments].

              - If [applicand = Typ.Constant { operator; _ }] and
                [Operator.is_infix operator], then
                [List.length arguments = 2].
              - If [applicand = Typ.Constant { operator; _ }] and
                [Operator.is_postfix operator], then
                [List.length arguments = 1]. *)
      | Arrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Typ.t
          ; orientation : [ `Forward | `Backward ]
          }
          (** - [Arrow { domain; range; orientation = `Forward; _ }] is the
                type [domain -> range].
              - [Arrow { range; domain; orientation = `Backward; _ }] is the
                type [range <- domain]. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; body : Typ.t
          }
          (** - [Pi { parameter_identifier = Option.Some "x"; parameter_type = t; body; _ }]
                is the dependent product type [{ x : t } body]. The variable
                ["x"] ranges over LF terms.

              - [Pi { parameter_identifier = Option.None; parameter_type = t; body; _ }]
                is the dependent product type [{ _ : t } body]. *)
  end =
    Typ

  (** External LF terms. *)
  and Term : sig
    type t =
      | Variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
          (** [Variable { identifier = "x"; _ }] is the term-level variable
              with name ["x"], which is either a bound variable having a
              lambda binder, or a free variable having no such corresponding
              binder. *)
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
          (** [Constant { identifier = "c"; _ }] is the term-level constant
              with qualified identifier ["c"], which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Term.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the term-level
              application of [applicand] with [arguments].

              - If [applicand = Term.Constant { operator; _ }] and
                [Operator.is_infix operator], then
                [List.length arguments = 2].
              - If [applicand = Term.Constant { operator; _ }] and
                [Operator.is_postfix operator], then
                [List.length arguments = 1]. *)
      | Abstraction of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t Option.t
          ; body : Term.t
          }
          (** - [Abstraction { parameter_identifier = Option.Some "x"; body; _ }]
                is the term [\x. body]. The variable ["x"] ranges over LF
                terms.

              - [Abstraction { parameter_identifier = Option.None; body; _ }]
                is the term [\_. body]. *)
      | Wildcard of { location : Location.t }
          (** [Wildcard { _ }] is the omission [_] of a fresh term-level
              variable. *)
      | TypeAnnotated of
          { location : Location.t
          ; term : Term.t
          ; typ : Typ.t
          }
          (** [TypeAnnotated { term = u; typ = t; _ }] is the term [u : t]. *)
  end =
    Term

  (** {2 Locations} *)

  let location_of_kind kind =
    match kind with
    | Kind.Typ { location; _ }
    | Kind.Arrow { location; _ }
    | Kind.Pi { location; _ } -> location

  let location_of_typ typ =
    match typ with
    | Typ.Constant { location; _ }
    | Typ.Application { location; _ }
    | Typ.Arrow { location; _ }
    | Typ.Pi { location; _ } -> location

  let location_of_term term =
    match term with
    | Term.Variable { location; _ }
    | Term.Constant { location; _ }
    | Term.Application { location; _ }
    | Term.Abstraction { location; _ }
    | Term.Wildcard { location; _ }
    | Term.TypeAnnotated { location; _ } -> location
end

(** {1 External Contextual LF Syntax} *)

(** The representation of contextual LF types, terms, and patterns after
    parsing and data-dependent disambiguation.

    ASTs constructed with the constructors in this module are not necessarily
    normalized.

    The distinction between contextual LF objects and plain LF objects is
    that contextual LF objects may have substitutions, and may appear in
    patterns.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation.

    The metavariable:

    - [x] ranges over variables
    - [c] ranges over term-level constants
    - [a] ranges over type-level constants
    - [s] ranges over substitutions
    - [g] ranges over context schemas
    - [id] ranges over identifiers
    - [#] ranges over integers

    {[
      Types           A, B ::= a | Πx:A.B | A → B | A M1 M2 ... Mn
                                 | block (x1:A1, x2:A2, ..., xn:An)
      Terms           M, N ::= c | x | #x | $x | λx:A.M | M N1 N2 ... Nn
                                 | M:A | M[σ]
                                 | _ | ? | ?id | <M1; M2; ...; Mn> | M.# | M.id
      Substitutions   σ    ::= ^ | … | σ, M | s[σ]
      Contexts        Ψ    ::= ^ | g | Ψ, x:A

      Term patterns           Mp, Np ::= c | x | #x | $x | λx:A.Mp
                                           | Mp Np1 Np2 ... Npn
                                           | Mp:A | Mp[σ] | _
                                           | <Mp1; Mp2; ...; Mpn>
                                           | Mp.# | Mp.id
      Substitution patterns   σp     ::= ^ | … | σp, Mp | s[σ]
      Context patterns        Ψp     ::= ^ | g | Ψp, x:A
    ]} *)
module CLF = struct
  (** External contextual LF types. *)
  module rec Typ : sig
    type t =
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
          (** [Constant { identifier = "c"; _ }] is the type-level constant
              with qualified identifier ["c"], which is necessarily bound. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the type-level
              application of [applicand] with [arguments].

              - If [applicand = Typ.Constant { operator; _ }] and
                [Operator.is_infix operator], then
                [List.length arguments = 2].
              - If [applicand = Typ.Constant { operator; _ }] and
                [Operator.is_postfix operator], then
                [List.length arguments = 1]. *)
      | Arrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Typ.t
          ; orientation : [ `Forward | `Backward ]
          }
          (** - [Arrow { domain; range; orientation = `Forward; _ }] is the
                type [domain -> range].
              - [Arrow { range; domain; orientation = `Backward; _ }] is the
                type [range <- domain]. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t
          ; body : Typ.t
          }
          (** - [Pi { parameter_identifier = Option.Some "x"; parameter_type = t; body; _ }]
                is the dependent product type [{ x : t } body]. The variable
                ["x"] ranges over LF terms.

              - [Pi { parameter_identifier = Option.None; parameter_type = t; body; _ }]
                is the dependent product type [{ _ : t } body]. *)
      | Block of
          { location : Location.t
          ; elements :
              [ `Unnamed of Typ.t
              | `Record of (Identifier.t * Typ.t) List1.t
              ]
          }
          (** - [Block { elements = `Unnamed t; _ }] is the block type
                [block t].

              - [Block { elements = `Record \[("x1", t1); ("x2", t2); ...; ("xn", tn)\]; _ }]
                is the block type [block (x1 : t1, x2 : t2, ..., xn : tn)].
                This is a dependent sum type, with [tj] being able to refer
                to ["xi"] when [i < j]. *)
  end =
    Typ

  (** External contextual LF terms. *)
  and Term : sig
    type t =
      | Variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
          (** [Variable { identifier = "x"; _ }] is the term-level variable
              with name ["x"], which is either a bound variable having a
              lambda binder, or a free variable having no such corresponding
              binder. *)
      | Parameter_variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
          (** [Parameter_variable { identifier = "#x"; _ }] is the term-level
              parameter variable with name ["#x"]. *)
      | Substitution_variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
          (** [Substitution_variable { identifier = "$x"; _ }] is the
              term-level substitution variable with name ["$x"]. *)
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
          (** [Constant { identifier = "c"; _ }] is the term-level constant
              with qualified identifier ["c"], which is necessarily bound. *)
      | Substitution of
          { location : Location.t
          ; term : Term.t
          ; substitution : Substitution.t
          }
          (** [Substitution { term; substitution; _ }] is the term
              [term\[substitution\]]. *)
      | Application of
          { location : Location.t
          ; applicand : Term.t
          ; arguments : Term.t List.t
          }
          (** [Application { applicand; arguments; _ }] is the term-level
              application of [applicand] with [arguments].

              - If [applicand = Term.Constant { operator; _ }] and
                [Operator.is_infix operator], then
                [List.length arguments = 2].
              - If [applicand = Term.Constant { operator; _ }] and
                [Operator.is_postfix operator], then
                [List.length arguments = 1]. *)
      | Abstraction of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_type : Typ.t Option.t
          ; body : Term.t
          }
          (** - [Abstraction { parameter_identifier = Option.Some "x"; body; _ }]
                is the term [\x. body].
              - [Abstraction { parameter_identifier = Option.None; body; _ }]
                is the term [\_. body]. *)
      | Hole of
          { location : Location.t
          ; variant :
              [ `Underscore | `Unlabelled | `Labelled of Identifier.t ]
          }
          (** [Hole { variant; _ }] is the omission of a term for
              reconstruction.

              - If [variant = `Underscore], then it is the hole [_].
              - If [variant = `Unlabelled], then it is the hole [?].
              - If [variant = `Labelled label], then it is the hole [?label]. *)
      | Tuple of
          { location : Location.t
          ; terms : Term.t List1.t
          }
          (** [Tuple { terms; _ }] is the tuple term [<t1; t2; ...; tn>] if
              [List1.to_list terms = \[t1; t2; ...; tn\]].

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
          (** [TypeAnnotated { term = u; typ = t; _ }] is the term [u : t]. *)

    (** External contextual LF term patterns. *)
    module rec Pattern : sig
      type t =
        | Variable of
            { location : Location.t
            ; identifier : Identifier.t
            }
            (** [Variable { identifier = "x"; _ }] is the term-level variable
                pattern ["x"]. *)
        | Parameter_variable of
            { location : Location.t
            ; identifier : Identifier.t
            }
            (** [Parameter_variable { identifier = "#x"; _ }] is the
                term-level parameter variable pattern with name ["#x"]. *)
        | Substitution_variable of
            { location : Location.t
            ; identifier : Identifier.t
            }
            (** [Substitution_variable { identifier = "$x"; _ }] is the
                term-level substitution variable pattern with name ["$x"]. *)
        | Constant of
            { location : Location.t
            ; identifier : QualifiedIdentifier.t
            ; operator : Operator.t
            ; quoted : Bool.t
            }
            (** [Constant { identifier = "c"; _ }] is the term-level constant
                pattern ["c"]. *)
        | Wildcard of { location : Location.t }
            (** [Wildcard _] is the term-level catch-all pattern [_]. *)
        | Tuple of
            { location : Location.t
            ; terms : Term.Pattern.t List1.t
            }
            (** [Tuple { terms; _ }] is the tuple pattern [<p1; p2; ...; pn>]
                if [terms = \[p1; p2; ...; pn\]]. *)
        | Projection of
            { location : Location.t
            ; term : Term.Pattern.t
            ; projection :
                [ `By_identifier of Identifier.t | `By_position of Int.t ]
            }
            (** [Projection { term; _ }] is the pattern for the projection of
                a tuple [term]. This projection is used to indicate which
                element of a tuple the scrutinee is matched against in a
                [case]-expression. *)
        | Abstraction of
            { location : Location.t
            ; parameter_identifier : Identifier.t Option.t
            ; parameter_type : Typ.t Option.t
            ; body : Term.Pattern.t
            }
            (** [Abstraction { parameter_identifier = Option.Some "x"; parameter_type = Option.Some t; body; _ }]
                is the pattern [\x:t. body]. *)
        | Substitution of
            { location : Location.t
            ; term : Term.Pattern.t
            ; substitution : Substitution.t
            }
            (** [Substitution { term; substitution; _ }] is the pattern
                [term\[substitution\]]. *)
        | Application of
            { location : Location.t
            ; applicand : Term.Pattern.t
            ; arguments : Term.Pattern.t List.t
            }
            (** [Application { applicand; arguments; _ }] is the term-level
                application pattern of [applicand] with [arguments].

                - If [applicand = Term.Constant { operator; _ }] and
                  [Operator.is_infix operator], then
                  [List.length arguments = 2].
                - If [applicand = Term.Constant { operator; _ }] and
                  [Operator.is_postfix operator], then
                  [List.length arguments = 1]. *)
        | TypeAnnotated of
            { location : Location.t
            ; term : Term.Pattern.t
            ; typ : Typ.t
            }
            (** [TypeAnnotated { term = x; typ = t; _ }] is the pattern
                [x : t]. *)
    end
  end =
    Term

  (** External contextual LF substitutions. *)
  and Substitution : sig
    (** [{ Substitution.head; terms; _ }] is the substitution

        - [^] if [head = Head.None] and [terms = \[\]]
        - [m1, m2, ..., mn] if [head = Head.None] and
          [terms = \[m1; m2; ...; mn\]]
        - [..] if [head = Head.Identity _] and [terms = \[\]]
        - [.., m1, m2, ..., mn] if [head = Head.Identitiy _] and
          [terms = \[m1; m2; ...; mn\]]
        - [$S] if
          [head = Head.Substitution_variable { identifier = "$S"; closure = Option.None; _ }]
          and [terms = \[\]]
        - [$S\[o\]] if
          [head = Head.Substitution_variable { identifier = "$S"; closure = Option.Some o; _ }]
          and [terms = \[\]]
        - [$S, m1, m2, ..., mn] if
          [head = Head.Substitution_variable { identifier = "$S"; closure = Option.None; _ }]
          and [terms = \[m1; m2; ...; mn\]]
        - [$S\[o\], m1, m2, ..., mn] if
          [head = Head.Substitution_variable { identifier = "$S"; closure = Option.Some o; _ }]
          and [terms = \[m1; m2; ...; mn\]] *)
    type t =
      { location : Location.t
      ; head : Substitution.Head.t
      ; terms : Term.t List.t
      }

    module Head : sig
      type t =
        | None
        | Identity of { location : Location.t }
        | Substitution_variable of
            { location : Location.t
            ; identifier : Identifier.t
            ; closure : Substitution.t Option.t
            }
    end

    (** External contextual LF substitution patterns. *)
    module Pattern : sig
      type t =
        { location : Location.t
        ; head : Substitution.Pattern.Head.t
        ; terms : Term.Pattern.t List.t
        }

      module Head : sig
        type t =
          | None
          | Identity of { location : Location.t }
          | Substitution_variable of
              { location : Location.t
              ; identifier : Identifier.t
              ; closure : Substitution.t Option.t
              }
      end
    end
  end =
    Substitution

  (** External contextual LF contexts. *)
  and Context : sig
    (** [{ Context.head; typings; _ }] is the context

        - [^] if [head = Head.None] and [typings = \[\]].
        - [x1 : t1, x2 : t2, ..., xn : tn] if [head = Head.None] and
          [typings = \[("x1", t1); ("x2", t2); ..., ("xn", tn)\]].
        - [_] if [head = Head.Hole] and [typings = \[\]].
        - [_, x1 : t1, x2 : t2, ..., xn : tn] if [head = Head.Hole] and
          [typings = \[("x1", t1); ("x2", t2); ..., ("xn", tn)\]].
        - [g] if [head = Head.Context_variable { identifier = "g"; _ }] and
          [typings = \[\]].
        - [g, x1 : t1, x2 : t2, ..., xn : tn] if
          [head = Head.Context_variable { identifier = "g"; _ }] and
          [typings = \[("x1", t1); ("x2", t2); ..., ("xn", tn)\]]. *)
    type t =
      { location : Location.t
      ; head : Context.Head.t
      ; typings : (Identifier.t * Typ.t) List.t
      }

    module Head : sig
      type t =
        | None
        | Hole of { location : Location.t }
        | Context_variable of { identifier : Identifier.t }
    end

    (** External contextual LF context patterns. *)
    module Pattern : sig
      type t =
        { location : Location.t
        ; head : Context.Pattern.Head.t
        ; typings : (Identifier.t * Typ.t) List.t
        }

      module Head : sig
        type t =
          | None
          | Hole of { location : Location.t }
          | Context_variable of { identifier : Identifier.t }
      end
    end
  end =
    Context

  (** {2 Locations} *)

  let location_of_typ typ =
    match typ with
    | Typ.Constant { location; _ }
    | Typ.Application { location; _ }
    | Typ.Arrow { location; _ }
    | Typ.Pi { location; _ }
    | Typ.Block { location; _ } -> location

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
    | Term.TypeAnnotated { location; _ } -> location

  let location_of_substitution substitution =
    match substitution with
    | Substitution.{ location; _ } -> location

  let location_of_substitution_pattern substitution_pattern =
    match substitution_pattern with
    | Substitution.Pattern.{ location; _ } -> location

  let location_of_context context =
    match context with
    | Context.{ location; _ } -> location

  let location_of_context_pattern context_pattern =
    match context_pattern with
    | Context.Pattern.{ location; _ } -> location

  let location_of_term_pattern term_pattern =
    match term_pattern with
    | Term.Pattern.Variable { location; _ }
    | Term.Pattern.Constant { location; _ }
    | Term.Pattern.Wildcard { location; _ }
    | Term.Pattern.Tuple { location; _ }
    | Term.Pattern.Projection { location; _ }
    | Term.Pattern.Abstraction { location; _ }
    | Term.Pattern.Substitution { location; _ }
    | Term.Pattern.Application { location; _ }
    | Term.Pattern.TypeAnnotated { location; _ } -> location
end

(** {1 External Meta-Syntax} *)

(** The representation of meta-types, meta-objects, meta-object patterns,
    meta-substitutions and meta-contexts after parsing and data-dependent
    disambiguation.

    ASTs constructed with the constructors in this module are not necessarily
    normalized.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation.

    The metavariable:

    - [X] ranges over meta-variables
    - [g] ranges over context schemas

    {[
      Meta-types           U ::= g | Ψ ⊢ A | Ψ ⊢ Ψ | Ψ #⊢ Ψ
      Meta-objects         C ::= Ψ | Ψ ⊢ M | Ψ ⊢ σ | Ψ #⊢ σ
      Meta-substitutions   θ ::= ^ | θ, C/X
      Meta-contexts        Δ ::= ^ | Δ, X:U
      Schemas              G ::= g | G + G | some [x1:A1, x2:A2, ..., xn:An] block (y1:B1, y2:B2, ..., ym:Bm)

      Meta-object patterns   Cp ::= Ψp | Ψp ⊢ Mp | Ψp ⊢ σp | Ψp #⊢ σp
    ]} *)
module Meta = struct
  (** External meta-types. *)
  module rec Typ : sig
    type t =
      | Context_schema of
          { location : Location.t
          ; schema : Schema.t
          }
          (** [Context_schema_constant { schema; _ }] is the context schema
              [schema]. *)
      | Contextual_typ of
          { location : Location.t
          ; context : CLF.Context.t
          ; typ : CLF.Typ.t
          }
          (** [Contextual_typ { context; typ; _ }] is the contextual type
              [context |- typ]. *)
      | Plain_substitution_typ of
          { location : Location.t
          ; domain : CLF.Context.t
          ; range : CLF.Context.t
          }
          (** [Plain_substitution_typ { domain; range; _ }] is the type for
              the plain substitution [domain |- range]. *)
      | Renaming_substitution_typ of
          { location : Location.t
          ; domain : CLF.Context.t
          ; range : CLF.Context.t
          }
          (** [Renaming_substitution_typ { domain; range; _ }] is the type
              for the renaming substitution [domain #|- range]. *)
  end =
    Typ

  (** External meta-objects. *)
  and Object : sig
    type t =
      | Context of
          { location : Location.t
          ; context : CLF.Context.t
          }
          (** [Context { context; _ }] is the context meta-object [context]. *)
      | Contextual_term of
          { location : Location.t
          ; context : CLF.Context.t
          ; term : CLF.Term.t
          }
          (** [Contextual_term { context; term; _ }] is the contextual term
              [context |- term]. *)
      | Plain_substitution of
          { location : Location.t
          ; domain : CLF.Context.t
          ; range : CLF.Substitution.t
          }
          (** [Plain_substitution { domain; range; _ }] is the plain
              substitution [domain |- range]. *)
      | Renaming_substitution of
          { location : Location.t
          ; domain : CLF.Context.t
          ; range : CLF.Substitution.t
          }
          (** [Renaming_substitution { domain; range; _ }] is the renaming
              substitution [domain #|- range]. *)

    (** External meta-object patterns. *)
    module Pattern : sig
      type t =
        | Context of
            { location : Location.t
            ; context : CLF.Context.Pattern.t
            }
            (** [Context { context; _ }] is the context meta-object pattern
                `context'. *)
        | Contextual_term of
            { location : Location.t
            ; context : CLF.Context.Pattern.t
            ; term : CLF.Term.Pattern.t
            }
            (** [Contextual_term { context; term; _ }] is the contextual term
                pattern [context |- term]. *)
        | Plain_substitution of
            { location : Location.t
            ; domain : CLF.Context.Pattern.t
            ; range : CLF.Substitution.Pattern.t
            }
            (** [Plain_substitution { domain; range; _ }] is the plain
                substitution pattern [domain |- range]. *)
        | Renaming_substitution of
            { location : Location.t
            ; domain : CLF.Context.Pattern.t
            ; range : CLF.Substitution.Pattern.t
            }
            (** [Renaming_substitution { domain; range; _ }] is the renaming
                substitution pattern [domain #|- range]. *)
    end
  end =
    Object

  (** External meta-substitutions. *)
  and Substitution : sig
    (** [{ Substitution.objects; _ }] is the meta-context

        - [^] if [objects = \[\]]
        - [m1, m2, ..., mn] if [objects = \[m1; m2; ...; mn\]] *)
    type t =
      { location : Location.t
      ; objects : Object.t List.t
      }
  end =
    Substitution

  (** External meta-contexts. *)
  and Context : sig
    (** [{ Context.typings; _ }] is the meta-context

        - [^] if [typings = \[\]]
        - [x1 : a1, x2 : a2, ..., xn : an] if
          [typings = \[("x1", a1); ("x2", a2); ...; ("xn", an)\]] *)
    type t =
      { location : Location.t
      ; typings : (Identifier.t * Typ.t) List.t
      }
  end =
    Context

  (** External context schemas. *)
  and Schema : sig
    type t =
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          }
          (** [Constant { identifier = "ctx"; _ }] is the schema having
              identifier ["ctx"] declared elsewhere in the signature.

              A tuple term has a block type [t] matching against this schema
              if [t] matches against the schema referred to as `identifier'. *)
      | Alternation of
          { location : Location.t
          ; schemas : Schema.t List2.t
          }
          (** [Alternation { schemas = \[g1; g2; ...; gn\]; _ }] is the
              schema [g1 + g2 + ... + gn].

              A tuple term has a block type [t] matching against this schema
              if [t] matches against at least one of [g1], [g2], ..., [gn]. *)
      | Element of
          { location : Location.t
          ; some : (Identifier.t * CLF.Typ.t) List1.t Option.t
          ; block :
              [ `Unnamed of CLF.Typ.t
              | `Record of (Identifier.t * CLF.Typ.t) List1.t
              ]
          }
          (** - [Element { some = \[("x1", p1); ("x2", p2); ...; ("xn", pn)\]; block = `Unnamed t; _ }]
                is the schema
                [some \[x1 : p1, x2 : p2, ..., xn : pn\] block t].

              - [Element { some = \[("x1", p1); ("x2", p2); ...; ("xn", pn)\]; block = `Record \[("y1", q1); ("y2", q2); ...; ("yn", qn)\]; _ }]
                is the schema
                [some \[x1 : p1, x2 : p2, ..., xn : pn\] block (y1 : q1, y2 : q2, ..., yn : qn)].

              A tuple term has a block type [t] matching against this schema
              if there exist terms having types in [p] in the context, and if
              the elements in [t] match against those in [q]. *)
  end =
    Schema

  (** {2 Locations} *)

  let location_of_meta_type meta_type =
    match meta_type with
    | Typ.Context_schema { location; _ }
    | Typ.Contextual_typ { location; _ }
    | Typ.Plain_substitution_typ { location; _ }
    | Typ.Renaming_substitution_typ { location; _ } -> location

  let location_of_meta_object meta_object =
    match meta_object with
    | Object.Context { location; _ }
    | Object.Contextual_term { location; _ }
    | Object.Plain_substitution { location; _ }
    | Object.Renaming_substitution { location; _ } -> location

  let location_of_meta_object_pattern meta_object_pattern =
    match meta_object_pattern with
    | Object.Pattern.Context { location; _ }
    | Object.Pattern.Contextual_term { location; _ }
    | Object.Pattern.Plain_substitution { location; _ }
    | Object.Pattern.Renaming_substitution { location; _ } -> location

  let location_of_substitution substitution =
    match substitution with
    | Substitution.{ location; _ } -> location

  let location_of_context context =
    match context with
    | Context.{ location; _ } -> location

  let location_of_schema schema =
    match schema with
    | Schema.Constant { location; _ }
    | Schema.Alternation { location; _ }
    | Schema.Element { location; _ } -> location
end
