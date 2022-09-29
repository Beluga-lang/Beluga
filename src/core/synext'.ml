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
      LF kinds   K    ::= type | Πx:A.K | A → K
      LF types   A, B ::= a | Πx:A.B | A → B | A M1 M2 ... Mn
      LF terms   M, N ::= c | x | λx:A.M | M N1 N2 ... Nn | M:A | _
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
    patterns. Plain LF objects are only used in the definition of type-level
    or term-level LF constants.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation.

    The metavariable:

    - [x] ranges over variables
    - [c] ranges over term-level constants
    - [a] ranges over type-level constants
    - [s] ranges over substitutions
    - [g] ranges over contexts
    - [id] ranges over identifiers
    - [n] ranges over integers

    {[
      Contextual LF types           A, B ::= a | Πx:A.B | A → B | A M1 M2 ... Mn
                                               | block (x1:A1, x2:A2, ..., xn:An)
      Contextual LF terms           M, N ::= c | x | #x | $x | λx:A.M | M N1 N2 ... Nn
                                               | M:A | M[σ]
                                               | _ | ? | ?id | <M1; M2; ...; Mn> | M.n | M.id
      Contextual LF substitutions   σ    ::= ^ | … | σ, M | s[σ]
      Contextual LF contexts        Ψ    ::= ^ | g | Ψ, x:A

      Contextual LF patterns                Mp, Np ::= c | x | #x | $x | λx:A.Mp
                                                    | Mp Np1 Np2 ... Npn
                                                    | Mp:A | Mp[σ] | _
                                                    | <Mp1; Mp2; ...; Mpn>
                                                    | Mp.n | Mp.id
      Contextual LF substitution patterns   σp     ::= ^ | … | σp, Mp | s[σ]
      Contextual LF context patterns        Ψp     ::= ^ | g | Ψp, x:A
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
        | None of { location : Location.t }
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
          | None of { location : Location.t }
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
    (** [{ Context.head; bindings; _ }] is the context

        - [^] if [head = Head.None] and [bindings = \[\]].
        - [x1 : t1, x2 : t2, ..., xn : tn] if [head = Head.None] and
          [bindings = \[("x1", t1); ("x2", t2); ..., ("xn", tn)\]].
        - [_] if [head = Head.Hole] and [bindings = \[\]].
        - [_, x1 : t1, x2 : t2, ..., xn : tn] if [head = Head.Hole] and
          [bindings = \[("x1", t1); ("x2", t2); ..., ("xn", tn)\]].
        - [g] if [head = Head.Context_variable { identifier = "g"; _ }] and
          [bindings = \[\]].
        - [g, x1 : t1, x2 : t2, ..., xn : tn] if
          [head = Head.Context_variable { identifier = "g"; _ }] and
          [bindings = \[("x1", t1); ("x2", t2); ..., ("xn", tn)\]]. *)
    type t =
      { location : Location.t
      ; head : Context.Head.t
      ; bindings : (Identifier.t * Typ.t Option.t) List.t
      }

    module Head : sig
      type t =
        | None of { location : Location.t }
        | Hole of { location : Location.t }
        | Context_variable of
            { location : Location.t
            ; identifier : Identifier.t
            }
    end

    (** External contextual LF context patterns. *)
    module Pattern : sig
      type t =
        { location : Location.t
        ; head : Context.Pattern.Head.t
        ; bindings : (Identifier.t * Typ.t) List.t
        }

      module Head : sig
        type t =
          | None of { location : Location.t }
          | Hole of { location : Location.t }
          | Context_variable of
              { location : Location.t
              ; identifier : Identifier.t
              }
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
    | { Substitution.location; _ } -> location

  let location_of_substitution_pattern substitution_pattern =
    match substitution_pattern with
    | { Substitution.Pattern.location; _ } -> location

  let location_of_context context =
    match context with
    | { Context.location; _ } -> location

  let location_of_context_pattern context_pattern =
    match context_pattern with
    | { Context.Pattern.location; _ } -> location

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

    - [X] ranges over meta-level variables
    - [g] ranges over context schemas

    {[
      Meta-types           U ::= g | Ψ ⊢ A | Ψ ⊢ Ψ | Ψ ⊢# Ψ
      Meta-objects         C ::= Ψ | Ψ ⊢ M | Ψ ⊢ σ | Ψ ⊢# σ
      Meta-substitutions   θ ::= ^ | θ, C/X
      Meta-contexts        Δ ::= ^ | Δ, X:U
      Schemas              G ::= g | G + G | some [x1:A1, x2:A2, ..., xn:An] block (y1:B1, y2:B2, ..., ym:Bm)

      Meta-object patterns   Cp ::= Ψp | Ψp ⊢ Mp | Ψp ⊢ σp | Ψp ⊢# σp
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
              for the renaming substitution [domain |-# range]. *)
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
              substitution [domain |-# range]. *)
  end =
    Object

  (** External meta-object patterns. *)
  and Pattern : sig
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
  end =
    Pattern

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
    (** [{ Context.bindings; _ }] is the meta-context

        - [^] if [bindings = \[\]]
        - [x1 : a1, x2 : a2, ..., xn : an] if
          [bindings = \[("x1", a1, _); ("x2", a2, _); ...; ("xn", an, _)\]] *)
    type t =
      { location : Location.t
      ; bindings : (Identifier.t * Typ.t) List.t
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
    | Object.Context { location; _ }
    | Object.Contextual_term { location; _ }
    | Object.Plain_substitution { location; _ }
    | Object.Renaming_substitution { location; _ } -> location

  let location_of_substitution substitution =
    match substitution with
    | { Substitution.location; _ } -> location

  let location_of_context context =
    match context with
    | { Context.location; _ } -> location

  let location_of_schema schema =
    match schema with
    | Schema.Constant { location; _ }
    | Schema.Alternation { location; _ }
    | Schema.Element { location; _ } -> location
end

(** {1 External Computational Syntax} *)

(** The representation of computation-level kinds, types, expressions and
    patterns after parsing and data-dependent disambiguation.

    ASTs constructed with the constructors in this module are not necessarily
    normalized.

    These types are suited for pretty-printing and elaboration to the
    internal syntax. Note that this is a named representation.

    The metavariable:

    - [x] ranges over computation-level variables
    - [c] ranges over computation-level constants
    - [X] ranges over meta-level variables

    {[
      Computational kinds         K    ::= ctype | ΠX:T.K | T → K |
      Computational types         T, S ::= ΠX:T.S | T → S | T × S
                                                  | [U] | T [C1] [C2] ... [CN]
      Computational expressions   E    ::= x | c | let x = P in E | impossible E
                                             | (E1, E2, ..., En) | ? | ?id | _
                                             | E1 E2 ... En
                                             | (case E of P1 => E1 | P2 => E2 | ... | Pn => En)
                                             | fn x1, x2, ..., xn => E
                                             | mlam X1, X2, ..., Xn => E
                                             | (fun P1 => E1 | P2 => E2 | ... | Pn => En)
      Computational patterns      P    ::= x | c | [Cp] | (P1, P2, ..., Pn) | P1 P2 ... Pn
                                             | P : T | { X : U } P | _
      Computational context       Γ    ::= ^ | Γ, x : T
    ]} *)
module Comp = struct
  (** External computation-level kinds. *)
  module rec Kind : sig
    type t =
      | Ctype of { location : Location.t }
          (** [Ctype { _ }] is the kind of computational types [ctype]. *)
      | Arrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Kind.t
          }
          (** [Arrow { domain; range; _ }] is the computational kind
              [domain -> range]. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; plicity : Plicity.t
          ; parameter_type : Meta.Typ.t
          ; body : Kind.t
          }
          (** [Pi { parameter_identifier = Option.Some "x"; parameter_type = t; explicit; body; _ }]
              is the explicit dependent product kind [{ x : t } body] if
              [plicity = Plicity.Explicit], and the implicit dependent
              product kind [(x : t) body] if [plicity = Plicity.Implicit].
              The variable ["x"] ranges over computational terms. *)
  end =
    Kind

  (** External computation-level types. *)
  and Typ : sig
    type t =
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
          (** [Constant { identifier = "c"; _ }] is the computation0level
              type constant ["c"]. *)
      | Pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; plicity : Plicity.t
          ; parameter_type : Meta.Typ.t
          ; body : Typ.t
          }
          (** [Pi { parameter_identifier = Option.Some "x"; parameter_type = t; explicit; body; _ }]
              is the explicit dependent product type [{ x : t } body] if
              [plicity = Plicity.Explicit], and the implicit dependent
              product type [(x : t) body] if [plicity = Plicity.Implicit].
              The variable ["x"] ranges over computational terms. *)
      | Arrow of
          { location : Location.t
          ; domain : Typ.t
          ; range : Typ.t
          ; orientation : [ `Forward | `Backward ]
          }
          (** [Arrow { domain; range; _ }] is the computational type
              [domain -> range]. *)
      | Cross of
          { location : Location.t
          ; types : Typ.t List2.t
          }
          (** [Cross { typs = \[t1; t2; ...; tn\]; _ }] is the type of tuple
              [t1 * t2 * ... * tn]. *)
      | Box of
          { location : Location.t
          ; meta_type : Meta.Typ.t
          }  (** [Box { typ = u; _ }] is a boxed meta-type [\[u\]]. *)
      | Application of
          { location : Location.t
          ; applicand : Typ.t
          ; arguments : Typ.t List1.t
          }
          (** [Application { applicand; arguments; _ }] is the application of
              [applicand] with [arguments]. *)
      | Base of
          { location : Location.t
          ; applicand : QualifiedIdentifier.t
          ; operator : Operator.t
          ; arguments : Meta.Object.t List.t
          }
          (** [Base { applicand = "c"; arguments; _ }] is the application of
              the inductive or stratified type constructor ["c"] with
              [arguments]. *)
      | Cobase of
          { location : Location.t
          ; applicand : QualifiedIdentifier.t
          ; operator : Operator.t
          ; arguments : Meta.Object.t List.t
          }
          (** [Cobase { applicand = "c"; arguments; _ }] is the application
              of the coinductive type constructor ["c"] with [arguments]. *)
  end =
    Typ

  (** External computation-level expressions. *)
  and Expression : sig
    type t =
      | Variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
          (** [Variable { identifier = "x"; _ }] is the computation-level
              variable ["x"]. *)
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
          (** [Constant { identifier = "c"; _ }] is the computation-level
              constant ["c"] referring to a value. *)
      | Fn of
          { location : Location.t
          ; parameters : Identifier.t Option.t List1.t
          ; body : Expression.t
          }
          (** [Fn { parameters = \["x1"; "x2"; ...; "xn"\]; body; _ }] is the
              computation-level abstraction [fn x1, x2, ..., xn => body]. *)
      | Mlam of
          { location : Location.t
          ; parameters :
              (Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]) List1.t
          ; body : Expression.t
          }
          (** [Mlam { parameters = \["X1"; "X2"; ...; "Xn"\]; body; _ }] is
              the computation-level abstraction over meta-objects
              [mlam X1, X2, ..., Xn => body]. *)
      | Fun of
          { location : Location.t
          ; branches : (Pattern.t List1.t * Expression.t) List1.t
          }
          (** [Fun { branches = \[(p1s, e1); (p2, e2); ...; (pn, en)\]; _ }]
              is the pattern-matching computation-level abstraction
              [fun p1 => e1 | p2 => e2 | ... | pn => en]. Each of [p1], [p2],
              ..., [pn] is a non-empty list of comma-separated patterns. *)
      | Let of
          { location : Location.t
          ; pattern : Pattern.t
          ; scrutinee : Expression.t
          ; body : Expression.t
          }
          (** [Let { pattern = p; scrutinee = e1; body = e2; _ }] is the
              pattern-matching let-binding expression [let p = e1 in e2]. *)
      | Box of
          { location : Location.t
          ; meta_object : Meta.Object.t
          }
          (** [Box { meta_object = C; _ }] is the meta-object expression
              [\[C\]]. *)
      | Impossible of
          { location : Location.t
          ; scrutinee : Expression.t
          }
          (** [Impossible { expression = e; _ }] is the pattern-matching with
              no branches [impossible e]. *)
      | Case of
          { location : Location.t
          ; scrutinee : Expression.t
          ; check_coverage : Bool.t
          ; branches : (Pattern.t * Expression.t) List1.t
          }
          (** [Case { scrutinee = e; branches = \[(p1, e1); (p2, e2); ...; (pn, en)\]; check_coverage; _ }]
              is the pattern-matching expression
              [case e of p1 => e1 | p2 => e2 | ... | pn => en].

              If [check_coverage = false], then coverage-checking is disable
              for this case-expression. *)
      | Tuple of
          { location : Location.t
          ; elements : Expression.t List2.t
          }
          (** [Tuple { elements = \[e1; e2; ...; en\]; _ }] is the tuple
              expression [(e1, e2, ..., en)]. *)
      | Hole of
          { location : Location.t
          ; label : Identifier.t Option.t
          }
          (** [Hole { label = Option.Some "x"; _ }] is the hole [?x] ranging
              over expressions. *)
      | BoxHole of { location : Location.t }
          (** [BoxHole _] is the hole [_] ranging over meta-objects. *)
      | Application of
          { location : Location.t
          ; applicand : Expression.t
          ; arguments : Expression.t List1.t
          }
          (** [Application { applicand; arguments; _ }] the application of
              [applicand] with [arguments]. *)
      | Observation of
          { location : Location.t
          ; observation : QualifiedIdentifier.t
          ; arguments : Expression.t List.t
          }
          (** [Observation { observation = "c"; arguments = \[e1; e2; ...; en\];  }]
              is the observation [.c e1 e2 ... en]. *)
      | TypeAnnotated of
          { location : Location.t
          ; expression : Expression.t
          ; typ : Typ.t
          }
          (** [TypeAnnotated { expression = e; typ = t; _ }] is the
              type-annotated computation-level expression [e : t]. *)
  end =
    Expression

  (** External computation-level patterns. *)
  and Pattern : sig
    type t =
      | Variable of
          { location : Location.t
          ; identifier : Identifier.t
          }
      | Constant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; quoted : Bool.t
          }
      | MetaObject of
          { location : Location.t
          ; meta_pattern : Meta.Pattern.t
          }
      | Tuple of
          { location : Location.t
          ; elements : Pattern.t List2.t
          }
      | Application of
          { location : Location.t
          ; applicand : Pattern.t
          ; arguments : Pattern.t List1.t
          }
      | Observation of
          { location : Location.t
          ; observation : QualifiedIdentifier.t
          ; arguments : Pattern.t List.t
          }
      | TypeAnnotated of
          { location : Location.t
          ; pattern : Pattern.t
          ; typ : Typ.t
          }
      | MetaTypeAnnotated of
          { location : Location.t
          ; annotation_identifier : Identifier.t Option.t
          ; annotation_type : Meta.Typ.t
          ; body : Pattern.t
          }
      | Wildcard of { location : Location.t }
  end =
    Pattern

  (** External computation-level contexts. *)
  and Context : sig
    (** [{ Context.bindings; _ }] is the computation-level context

          - [^] if [bindings = \[\]]
          - [x1 : a1, x2 : a2, ..., xn : an] if [bindings = \[("x1", a1); ("x2", a2); ...; ("xn", an)]]
      *)
    type t =
      { location : Location.t
      ; bindings : (Identifier.t * Typ.t) List.t
      }
  end =
    Context

  (** {2 Locations} *)

  let location_of_kind kind =
    match kind with
    | Kind.Pi { location; _ }
    | Kind.Arrow { location; _ }
    | Kind.Ctype { location; _ } -> location

  let location_of_typ typ =
    match typ with
    | Typ.Pi { location; _ }
    | Typ.Arrow { location; _ }
    | Typ.Cross { location; _ }
    | Typ.Box { location; _ }
    | Typ.Base { location; _ }
    | Typ.Cobase { location; _ } -> location

  let location_of_expression expression =
    match expression with
    | Expression.Fn { location; _ }
    | Expression.Fun { location; _ }
    | Expression.Mlam { location; _ }
    | Expression.Let { location; _ }
    | Expression.Box { location; _ }
    | Expression.Impossible { location; _ }
    | Expression.Case { location; _ }
    | Expression.Tuple { location; _ }
    | Expression.Hole { location; _ }
    | Expression.BoxHole { location; _ }
    | Expression.Variable { location; _ }
    | Expression.Constant { location; _ }
    | Expression.Application { location; _ }
    | Expression.Observation { location; _ }
    | Expression.TypeAnnotated { location; _ } -> location

  let location_of_pattern pattern =
    match pattern with
    | Pattern.Variable { location; _ }
    | Pattern.Constant { location; _ }
    | Pattern.MetaObject { location; _ }
    | Pattern.Tuple { location; _ }
    | Pattern.Application { location; _ }
    | Pattern.Observation { location; _ }
    | Pattern.TypeAnnotated { location; _ }
    | Pattern.MetaTypeAnnotated { location; _ }
    | Pattern.Wildcard { location; _ } -> location
end

(** {1 External Harpoon Syntax} *)

module Harpoon = struct
  module rec Proof : sig
    type t =
      | Incomplete of
          { location : Location.t
          ; label : Identifier.t Option.t
          }
      | Command of
          { location : Location.t
          ; command : Command.t
          ; body : Proof.t
          }
      | Directive of
          { location : Location.t
          ; directive : Directive.t
          }
  end =
    Proof

  and Command : sig
    type t =
      | By of
          { location : Location.t
          ; expression : Comp.Expression.t
          ; assignee : Identifier.t
          }
      | Unbox of
          { location : Location.t
          ; expression : Comp.Expression.t
          ; assignee : Identifier.t
          ; modifier : [ `Strengthened ] Option.t
          }
  end =
    Command

  and Directive : sig
    type t =
      | Intros of
          { location : Location.t
          ; hypothetical : Hypothetical.t
          }
      | Solve of
          { location : Location.t
          ; solution : Comp.Expression.t
          }
      | Split of
          { location : Location.t
          ; scrutinee : Comp.Expression.t
          ; branches : Split_branch.t List.t
          }
      | Suffices of
          { location : Location.t
          ; scrutinee : Comp.Expression.t
          ; branches : Suffices_branch.t List.t
          }
  end =
    Directive

  and Split_branch : sig
    type t =
      { location : Location.t
      ; label : Split_branch.Label.t
      ; body : Hypothetical.t
      }

    module Label : sig
      type t =
        | Constant of
            { location : Location.t
            ; identifier : QualifiedIdentifier.t
            }
        | Bound_variable of { location : Location.t }
        | Empty_context of { location : Location.t }
        | Extended_context of
            { location : Location.t
            ; schema_element : Int.t  (** 1-based *)
            }
        | Parameter_variable of
            { location : Location.t
            ; schema_element : Int.t  (** 1-based *)
            ; projection : Int.t Option.t  (** 1-based *)
            }
    end
  end =
    Split_branch

  and Suffices_branch : sig
    type t =
      { location : Location.t
      ; goal : Comp.Typ.t
      ; proof : Proof.t
      }
  end =
    Suffices_branch

  and Hypothetical : sig
    type t =
      { location : Location.t
      ; meta_context : Meta.Context.t
      ; comp_context : Comp.Context.t
      ; proof : Proof.t
      }
  end =
    Hypothetical

  module rec Repl : sig
    module Command : sig
      type t =
        (* Administrative commands *)
        | Rename of
            { location : Location.t
            ; rename_from : Identifier.t
            ; rename_to : Identifier.t
            ; level : [ `meta | `comp ]
            }
        | ToggleAutomation of
            { location : Location.t
            ; kind : [ `auto_intros | `auto_solve_trivial ]
            ; change : [ `on | `off | `toggle ]
            }
        | Type of
            { location : Location.t
            ; scrutinee : Comp.Expression.t
            }
        | Info of
            { location : Location.t
            ; kind : [ `prog ]
            ; object_identifier : QualifiedIdentifier.t
            }
        | SelectTheorem of
            { location : Location.t
            ; theorem : QualifiedIdentifier.t
            }
        | Theorem of
            { location : Location.t
            ; subcommand :
                [ `list
                | `defer
                | `show_ihs
                | `show_proof
                | `dump_proof of String.t  (** File path *)
                ]
            }
        | Session of
            { location : Location.t
            ; subcommand : [ `list | `defer | `create | `serialize ]
            }
        | Subgoal of
            { location : Location.t
            ; subcommand : [ `list | `defer ]
            }
        | Undo of { location : Location.t }
        | Redo of { location : Location.t }
        | History of { location : Location.t }
        | Translate of
            { location : Location.t
            ; theorem : QualifiedIdentifier.t
            }
        (* Actual tactics *)
        | Intros of
            { location : Location.t
            ; introduced_variables : Identifier.t List1.t Option.t
            }
        | Split of
            { location : Location.t
            ; scrutinee : Comp.Expression.t
            }
        | Invert of
            { location : Location.t
            ; scrutinee : Comp.Expression.t
            }
        | Impossible of
            { location : Location.t
            ; scrutinee : Comp.Expression.t
            }
        | MSplit of
            { location : Location.t
            ; identifier : Identifier.t
            }
        | Solve of
            { location : Location.t
            ; solution : Comp.Expression.t
            }
        | Unbox of
            { location : Location.t
            ; expression : Comp.Expression.t
            ; assignee : Identifier.t
            ; modifier : [ `Strengthened ] Option.t
            }
        | By of
            { location : Location.t
            ; expression : Comp.Expression.t
            ; assignee : Identifier.t
            }
        | Suffices of
            { location : Location.t
            ; implication : Comp.Expression.t
            ; goal_premises :
                [ `exact of Comp.Typ.t | `infer of Location.t ] List.t
            }
        | Help of { location : Location.t }
    end
  end =
    Repl

  let location_of_proof proof =
    match proof with
    | Proof.Incomplete { location; _ }
    | Proof.Command { location; _ }
    | Proof.Directive { location; _ } -> location

  let location_of_command command =
    match command with
    | Command.By { location; _ } | Command.Unbox { location; _ } -> location

  let location_of_directive directive =
    match directive with
    | Directive.Intros { location; _ }
    | Directive.Solve { location; _ }
    | Directive.Split { location; _ }
    | Directive.Suffices { location; _ } -> location

  let location_of_split_branch split_branch =
    match split_branch with
    | { Split_branch.location; _ } -> location

  let location_of_split_branch_label split_branch_label =
    match split_branch_label with
    | Split_branch.Label.Constant { location; _ }
    | Split_branch.Label.Bound_variable { location; _ }
    | Split_branch.Label.Empty_context { location; _ }
    | Split_branch.Label.Extended_context { location; _ }
    | Split_branch.Label.Parameter_variable { location; _ } -> location

  let location_of_suffices_branch suffices_branch =
    match suffices_branch with
    | { Suffices_branch.location; _ } -> location

  let location_of_hypothetical hypothetical =
    match hypothetical with
    | { Hypothetical.location; _ } -> location

  let location_of_repl_command repl_command =
    match repl_command with
    | Repl.Command.Rename { location; _ }
    | Repl.Command.ToggleAutomation { location; _ }
    | Repl.Command.Type { location; _ }
    | Repl.Command.Info { location; _ }
    | Repl.Command.SelectTheorem { location; _ }
    | Repl.Command.Theorem { location; _ }
    | Repl.Command.Session { location; _ }
    | Repl.Command.Subgoal { location; _ }
    | Repl.Command.Undo { location; _ }
    | Repl.Command.Redo { location; _ }
    | Repl.Command.History { location; _ }
    | Repl.Command.Translate { location; _ }
    | Repl.Command.Intros { location; _ }
    | Repl.Command.Split { location; _ }
    | Repl.Command.Invert { location; _ }
    | Repl.Command.Impossible { location; _ }
    | Repl.Command.MSplit { location; _ }
    | Repl.Command.Solve { location; _ }
    | Repl.Command.Unbox { location; _ }
    | Repl.Command.By { location; _ }
    | Repl.Command.Suffices { location; _ }
    | Repl.Command.Help { location; _ } -> location
end

(** {1 External Signature Syntax} *)

module Signature = struct
  module Pragma = struct
    type t =
      | Name of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; meta_variable_base : Identifier.t
          ; computation_variable_base : Identifier.t Option.t
          }
      | Default_associativity of
          { location : Location.t
          ; associativity : Associativity.t
          }
      | Prefix_fixity of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; precedence : Int.t
          }
      | Infix_fixity of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; precedence : Int.t
          ; associativity : Associativity.t Option.t
          }
      | Postfix_fixity of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; precedence : Int.t
          }
      | Not of { location : Location.t }
      | Open_module of
          { location : Location.t
          ; module_identifier : QualifiedIdentifier.t
          }
      | Abbreviation of
          { location : Location.t
          ; module_identifier : QualifiedIdentifier.t
          ; abbreviation : Identifier.t
          }

    module Global = struct
      type t =
        | No_strengthening of { location : Location.t }
        | Coverage of
            { location : Location.t
            ; variant : [ `Error | `Warn ]
            }
    end
  end

  module rec Theorem : sig
    type t =
      { location : Location.t
      ; name : Identifier.t
      ; typ : Comp.Typ.t
      ; order : Totality.Declaration.t Option.t
      ; body : [ `Program of Comp.Expression.t | `Proof of Harpoon.Proof.t ]
      }
  end =
    Theorem

  and Totality : sig
    module rec Declaration : sig
      type t =
        | Trust of { location : Location.t }
        | Numeric of
            { location : Location.t
            ; order : Int.t Order.t Option.t
            }
        | Named of
            { location : Location.t
            ; order : Identifier.t Order.t Option.t
            ; program : Identifier.t
            ; argument_labels : Identifier.t Option.t List.t
            }
    end

    and Order : sig
      type 'a t =
        | Argument of
            { location : Location.t
            ; argument : 'a
            }
        | Lexical_ordering of
            { location : Location.t
            ; arguments : 'a Order.t List1.t
            }
        | Simultaneous_ordering of
            { location : Location.t
            ; arguments : 'a Order.t List1.t
            }
    end
  end =
    Totality

  module rec Declaration : sig
    (** Parsed signature element *)
    type t =
      | Typ of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : LF.Kind.t
          }  (** LF type-level constant declaration *)
      | Const of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : LF.Typ.t
          }  (** LF term-level constant declaration *)
      | CompTyp of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Kind.t
          ; datatype_flavour : [ `Inductive | `Stratified ]
          }  (** Computation-level data type constant declaration *)
      | CompCotyp of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Kind.t
          }  (** Computation-level codata type constant declaration *)
      | CompConst of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Typ.t
          }  (** Computation-level type constructor declaration *)
      | CompDest of
          { location : Location.t
          ; identifier : Identifier.t
          ; observation_type : Comp.Typ.t
          ; return_type : Comp.Typ.t
          }  (** Computation-level type destructor declaration *)
      | CompTypAbbrev of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Kind.t
          ; typ : Comp.Typ.t
          }
          (** Synonym declaration for computation-level type constructor *)
      | Schema of
          { location : Location.t
          ; identifier : Identifier.t
          ; schema : Meta.Schema.t
          }  (** Declaration of a specification for a set of contexts *)
      | Pragma of
          { location : Location.t
          ; pragma : Pragma.t
          }  (** Compiler directive *)
      | GlobalPragma of
          { location : Location.t
          ; pragma : Pragma.Global.t
          }  (** Global directive *)
      | Mutually_recursive_datatypes of
          { location : Location.t
          ; declarations : (Declaration.t * Declaration.t List.t) List1.t
          }  (** Mutually-recursive datatypes declaration(s) *)
      | Theorems of
          { location : Location.t
          ; theorems : Theorem.t List1.t
          }  (** Mutually recursive theorem declaration(s) *)
      | Val of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Typ.t Option.t
          ; expression : Comp.Expression.t
          }  (** Computation-level value declaration *)
      | Query of
          { location : Location.t
          ; name : Identifier.t Option.t
          ; meta_context : Meta.Context.t
          ; typ : LF.Typ.t
          ; expected_solutions : Int.t Option.t
          ; maximum_tries : Int.t Option.t
          }  (** Logic programming query on an LF type *)
      | MQuery of
          { location : Location.t
          ; typ : Comp.Typ.t
          ; expected_solutions : Int.t Option.t
          ; search_tries : Int.t Option.t
          ; search_depth : Int.t Option.t
          }  (** Logic programming mquery on a computational type *)
      | Module of
          { location : Location.t
          ; identifier : Identifier.t
          ; declarations : Declaration.t List.t
          }  (** Namespace declaration for other declarations *)
      | Comment of
          { location : Location.t
          ; content : String.t
          }  (** Documentation comment *)
  end =
    Declaration

  type t = Declaration.t List.t

  (** {2 Locations} *)

  let location_of_pragma pragma =
    match pragma with
    | Pragma.Name { location; _ }
    | Pragma.Default_associativity { location; _ }
    | Pragma.Prefix_fixity { location; _ }
    | Pragma.Infix_fixity { location; _ }
    | Pragma.Postfix_fixity { location; _ }
    | Pragma.Not { location; _ }
    | Pragma.Open_module { location; _ }
    | Pragma.Abbreviation { location; _ } -> location

  let location_of_global_pragma global_pragma =
    match global_pragma with
    | Pragma.Global.No_strengthening { location; _ }
    | Pragma.Global.Coverage { location; _ } -> location

  let location_of_theorem theorem =
    match theorem with
    | { Theorem.location; _ } -> location

  let location_of_totality_declaration totality_declaration =
    match totality_declaration with
    | Totality.Declaration.Trust { location; _ }
    | Totality.Declaration.Numeric { location; _ }
    | Totality.Declaration.Named { location; _ } -> location

  let location_of_totality_order totality_order =
    match totality_order with
    | Totality.Order.Argument { location; _ }
    | Totality.Order.Lexical_ordering { location; _ }
    | Totality.Order.Simultaneous_ordering { location; _ } -> location

  let location_of_declaration declaration =
    match declaration with
    | Declaration.Typ { location; _ }
    | Declaration.Const { location; _ }
    | Declaration.CompTyp { location; _ }
    | Declaration.CompCotyp { location; _ }
    | Declaration.CompConst { location; _ }
    | Declaration.CompDest { location; _ }
    | Declaration.CompTypAbbrev { location; _ }
    | Declaration.Schema { location; _ }
    | Declaration.Pragma { location; _ }
    | Declaration.GlobalPragma { location; _ }
    | Declaration.Mutually_recursive_datatypes { location; _ }
    | Declaration.Theorems { location; _ }
    | Declaration.Val { location; _ }
    | Declaration.Query { location; _ }
    | Declaration.MQuery { location; _ }
    | Declaration.Module { location; _ }
    | Declaration.Comment { location; _ } -> location
end
