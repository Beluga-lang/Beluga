(** Precedences of AST nodes for pretty-printing.

    The values used as precedence levels are defined based on the recursive
    descent parsers in the parser. Specifically, the precedence values
    correspond to the number suffixes to the productions in the documented
    grammar, like in the following grammar for LF objects where type
    ascriptions have precedence [2] and arrows have precedence [3].

    {[
      <lf-weak-prefix> ::=
        | `{' <omittable-identifier> [`:' <lf-object>] `}' <lf-object>
        | `\' <omittable-identifier> [`:' <lf-object>] `.' <lf-object>

      <lf-object> ::=
        | <lf-object1>

      <lf-object1> ::=
        | <lf-weak-prefix>
        | <lf-object2>

      <lf-object2> ::=
        | <lf-object3> (`:' (<lf-object3> | <lf-weak-prefix>))+
        | <lf-object3>

      <lf-object3> ::=
        | <lf-object4> (<forward-arrow> (<lf-object4> | <lf-weak-prefix>))+
        | <lf-object4> (<backward-arrow> (<lf-object4> | <lf-weak-prefix>))+
        | <lf-object4>

      <lf-object4> ::=
        | <lf-object5> (<lf-object5> | <lf-weak-prefix>)+
        | <lf-object5>

      <lf-object5> ::=
        | <identifier>
        | <qualified-identifier>
        | `type'
        | `_'
        | `(' <lf-object> `)'
    ]} *)

open Support
open Common
open Synext_definition

module Lf_precedence = struct
  type t =
    | Static of Int.t
    | User_defined of Int.t

  let lf_application_precedence = 4

  let precedence_of_lf_kind kind =
    match kind with
    | LF.Kind.Pi _ -> Static 1
    | LF.Kind.Arrow _ -> Static 3
    | LF.Kind.Typ _ -> Static 5

  let precedence_of_lf_typ typ =
    match typ with
    | LF.Typ.Pi _ -> Static 1
    | LF.Typ.Arrow _ -> Static 3
    | LF.Typ.Application
        { applicand = LF.Typ.Constant { operator; prefixed; _ }; _ }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static lf_application_precedence
    | LF.Typ.Application
        { applicand = LF.Typ.Constant { operator; prefixed = false; _ }; _ }
    (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
    | LF.Typ.Application _ -> Static lf_application_precedence
    | LF.Typ.Constant _ -> Static 5

  let precedence_of_lf_term term =
    match term with
    | LF.Term.Abstraction _ -> Static 1
    | LF.Term.Type_annotated _ -> Static 2
    | LF.Term.Application
        { applicand = LF.Term.Constant { operator; prefixed; _ }; _ }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static lf_application_precedence
    | LF.Term.Application
        { applicand = LF.Term.Constant { operator; prefixed = false; _ }; _ }
    (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
    | LF.Term.Application _ -> Static lf_application_precedence
    | LF.Term.Wildcard _
    | LF.Term.Variable _
    | LF.Term.Constant _ ->
        Static 6

  include (
    Ord.Make (struct
      type nonrec t = t

      let compare x y =
        match (x, y) with
        | Static x, Static y -> Int.compare x y
        | User_defined x, User_defined y -> Int.compare x y
        | User_defined _, Static y ->
            if lf_application_precedence <= y then -1 else 1
        | Static x, User_defined _ ->
            if x < lf_application_precedence then -1 else 1
    end) :
      Ord.ORD with type t := t)
end

module Clf_precedence = struct
  type t =
    | Static of Int.t
    | User_defined of Int.t

  let clf_application_precedence = 5

  let precedence_of_clf_typ typ =
    match typ with
    | CLF.Typ.Pi _ -> Static 1
    | CLF.Typ.Arrow _ -> Static 3
    | CLF.Typ.Block _ -> Static 4
    | CLF.Typ.Application
        { applicand = CLF.Typ.Constant { operator; prefixed; _ }; _ }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static clf_application_precedence
    | CLF.Typ.Application
        { applicand = CLF.Typ.Constant { operator; prefixed = false; _ }; _ }
    (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
    | CLF.Typ.Application _ -> Static clf_application_precedence
    | CLF.Typ.Constant _ -> Static 8

  let precedence_of_clf_term term =
    match term with
    | CLF.Term.Abstraction _ -> Static 1
    | CLF.Term.Type_annotated _ -> Static 2
    | CLF.Term.Application
        { applicand = CLF.Term.Constant { operator; prefixed; _ }; _ }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static clf_application_precedence
    | CLF.Term.Application
        { applicand = CLF.Term.Constant { operator; prefixed = false; _ }
        ; _
        }
    (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
    | CLF.Term.Application _ -> Static clf_application_precedence
    | CLF.Term.Substitution _ -> Static 6
    | CLF.Term.Projection _ -> Static 7
    | CLF.Term.Variable _
    | CLF.Term.Parameter_variable _
    | CLF.Term.Substitution_variable _
    | CLF.Term.Constant _
    | CLF.Term.Hole _
    | CLF.Term.Tuple _ ->
        Static 8

  let precedence_of_clf_term_pattern term =
    match term with
    | CLF.Term.Pattern.Abstraction _ -> Static 1
    | CLF.Term.Pattern.Type_annotated _ -> Static 2
    | CLF.Term.Pattern.Application
        { applicand = CLF.Term.Pattern.Constant { operator; prefixed; _ }
        ; _
        }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static clf_application_precedence
    | CLF.Term.Pattern.Application
        { applicand =
            CLF.Term.Pattern.Constant { operator; prefixed = false; _ }
        ; _
        }
    (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
    | CLF.Term.Pattern.Application _ -> Static clf_application_precedence
    | CLF.Term.Pattern.Substitution _ -> Static 6
    | CLF.Term.Pattern.Projection _ -> Static 7
    | CLF.Term.Pattern.Wildcard _
    | CLF.Term.Pattern.Variable _
    | CLF.Term.Pattern.Parameter_variable _
    | CLF.Term.Pattern.Substitution_variable _
    | CLF.Term.Pattern.Constant _
    | CLF.Term.Pattern.Tuple _ ->
        Static 8

  include (
    Ord.Make (struct
      type nonrec t = t

      let compare x y =
        match (x, y) with
        | Static x, Static y -> Int.compare x y
        | User_defined x, User_defined y -> Int.compare x y
        | User_defined _, Static y ->
            if clf_application_precedence <= y then -1 else 1
        | Static x, User_defined _ ->
            if x < clf_application_precedence then -1 else 1
    end) :
      Ord.ORD with type t := t)
end

module Meta_precedence = struct
  type t = Static of Int.t [@unboxed]

  let precedence_of_schema schema =
    match schema with
    | Meta.Schema.Alternation _ -> Static 1
    | Meta.Schema.Constant _
    | Meta.Schema.Element _ ->
        Static 2

  include (
    Ord.Make (struct
      type nonrec t = t

      let compare (Static x) (Static y) = Int.compare x y
    end) :
      Ord.ORD with type t := t)
end

module Comp_precedence = struct
  type t =
    | Static of Int.t
    | User_defined_type of Int.t
    | User_defined_expression of Int.t
    | User_defined_pattern of Int.t

  let type_application_precedence = 4

  let expression_application_precedence = 2

  let pattern_application_precedence = 3

  let precedence_of_comp_kind kind =
    match kind with
    | Comp.Kind.Pi _ -> Static 1
    | Comp.Kind.Arrow _ -> Static 2
    | Comp.Kind.Ctype _ -> Static 5

  let precedence_of_comp_typ typ =
    match typ with
    | Comp.Typ.Pi _ -> Static 1
    | Comp.Typ.Arrow _ -> Static 2
    | Comp.Typ.Cross _ -> Static 3
    | Comp.Typ.Application
        { applicand =
            ( Comp.Typ.Inductive_typ_constant { operator; prefixed; _ }
            | Comp.Typ.Stratified_typ_constant { operator; prefixed; _ }
            | Comp.Typ.Coinductive_typ_constant { operator; prefixed; _ }
            | Comp.Typ.Abbreviation_typ_constant { operator; prefixed; _ } )
        ; _
        }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static type_application_precedence
    | Comp.Typ.Application
        { applicand =
            ( Comp.Typ.Inductive_typ_constant
                { operator; prefixed = false; _ }
            | Comp.Typ.Stratified_typ_constant
                { operator; prefixed = false; _ }
            | Comp.Typ.Coinductive_typ_constant
                { operator; prefixed = false; _ }
            | Comp.Typ.Abbreviation_typ_constant
                { operator; prefixed = false; _ } )
        ; _
        }
    (* User-defined operator application *) ->
        User_defined_type (Operator.precedence operator)
    | Comp.Typ.Application _ -> Static type_application_precedence
    | Comp.Typ.Inductive_typ_constant _
    | Comp.Typ.Stratified_typ_constant _
    | Comp.Typ.Coinductive_typ_constant _
    | Comp.Typ.Abbreviation_typ_constant _
    | Comp.Typ.Box _ ->
        Static 5

  let precedence_of_comp_expression expression =
    match expression with
    | Comp.Expression.Type_annotated _ -> Static 1
    | Comp.Expression.Application
        { applicand =
            ( Comp.Expression.Constructor { operator; prefixed; _ }
            | Comp.Expression.Program
                { operator = Option.Some operator; prefixed; _ } )
        ; _
        }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static expression_application_precedence
    | Comp.Expression.Application
        { applicand =
            ( Comp.Expression.Constructor { operator; prefixed = false; _ }
            | Comp.Expression.Program
                { operator = Option.Some operator; prefixed = false; _ } )
        ; _
        }
    (* User-defined operator application *) ->
        User_defined_expression (Operator.precedence operator)
    | Comp.Expression.Application _ ->
        Static expression_application_precedence
    | Comp.Expression.Let _
    | Comp.Expression.Impossible _
    | Comp.Expression.Case _
    | Comp.Expression.Fn _
    | Comp.Expression.Mlam _
    | Comp.Expression.Fun _ ->
        Static 3
    | Comp.Expression.Observation _ -> Static 4
    | Comp.Expression.Hole _
    | Comp.Expression.Box _
    | Comp.Expression.Box_hole _
    | Comp.Expression.Tuple _
    | Comp.Expression.Variable _
    | Comp.Expression.Constructor _
    | Comp.Expression.Program _ ->
        Static 5

  let precedence_of_comp_pattern pattern =
    match pattern with
    | Comp.Pattern.Meta_type_annotated _ -> Static 1
    | Comp.Pattern.Type_annotated _ -> Static 2
    | Comp.Pattern.Application
        { applicand = Comp.Pattern.Constant { operator; prefixed; _ }; _ }
      when prefixed || Operator.is_prefix operator
           (* Juxtapositions are of higher precedence than user-defined
              operators *) ->
        Static pattern_application_precedence
    | Comp.Pattern.Application
        { applicand = Comp.Pattern.Constant { operator; prefixed = false; _ }
        ; _
        }
    (* User-defined operator application *) ->
        User_defined_pattern (Operator.precedence operator)
    | Comp.Pattern.Application _ -> Static pattern_application_precedence
    | Comp.Pattern.Variable _
    | Comp.Pattern.Constant _
    | Comp.Pattern.Meta_object _
    | Comp.Pattern.Tuple _
    | Comp.Pattern.Wildcard _ ->
        Static 4

  let precedence_of_comp_copattern copattern =
    match copattern with
    | Comp.Copattern.Observation _ -> Static 3
    | Comp.Copattern.Pattern pattern -> precedence_of_comp_pattern pattern

  include (
    Ord.Make (struct
      type nonrec t = t

      let compare x y =
        match (x, y) with
        | Static x, Static y -> Int.compare x y
        | User_defined_type x, User_defined_type y -> Int.compare x y
        | User_defined_type _, Static y ->
            if type_application_precedence <= y then -1 else 1
        | Static x, User_defined_type _ ->
            if x < type_application_precedence then -1 else 1
        | User_defined_expression x, User_defined_expression y ->
            Int.compare x y
        | User_defined_expression _, Static y ->
            if expression_application_precedence <= y then -1 else 1
        | Static x, User_defined_expression _ ->
            if x < expression_application_precedence then -1 else 1
        | User_defined_pattern _, Static y ->
            if pattern_application_precedence <= y then -1 else 1
        | Static x, User_defined_pattern _ ->
            if x < pattern_application_precedence then -1 else 1
        | _ ->
            Error.raise_violation
              "[Precedence.compare] cannot compare precedences for \
               user-defined type, expression and pattern constants"
    end) :
      Ord.ORD with type t := t)
end

(** {1 Aliases} *)

(** {2 LF} *)

let precedence_of_lf_kind = Lf_precedence.precedence_of_lf_kind

let precedence_of_lf_typ = Lf_precedence.precedence_of_lf_typ

let precedence_of_lf_term = Lf_precedence.precedence_of_lf_term

(** {2 Contextual LF} *)

let precedence_of_clf_typ = Clf_precedence.precedence_of_clf_typ

let precedence_of_clf_term = Clf_precedence.precedence_of_clf_term

let precedence_of_clf_term_pattern =
  Clf_precedence.precedence_of_clf_term_pattern

(** {2 Meta-Level} *)

let precedence_of_schema = Meta_precedence.precedence_of_schema

(** {2 Computation-Level} *)

let precedence_of_comp_kind = Comp_precedence.precedence_of_comp_kind

let precedence_of_comp_typ = Comp_precedence.precedence_of_comp_typ

let precedence_of_comp_expression =
  Comp_precedence.precedence_of_comp_expression

let precedence_of_comp_pattern = Comp_precedence.precedence_of_comp_pattern

let precedence_of_comp_copattern =
  Comp_precedence.precedence_of_comp_copattern
