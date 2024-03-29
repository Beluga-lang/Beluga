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
open Syncom
open Synext_definition

module type BASE_PRECEDENCE = sig
  type precedence

  module Ord : Ord.ORD with type t = precedence
end

module type LF_PRECEDENCE = sig
  include Imperative_state.IMPERATIVE_STATE

  include BASE_PRECEDENCE

  val precedence_of_lf_kind : state -> lf_kind -> precedence

  val precedence_of_lf_typ : state -> lf_typ -> precedence

  val precedence_of_lf_term : state -> lf_term -> precedence
end

module type CLF_PRECEDENCE = sig
  include Imperative_state.IMPERATIVE_STATE

  include BASE_PRECEDENCE

  val precedence_of_clf_typ : state -> clf_typ -> precedence

  val precedence_of_clf_term : state -> clf_term -> precedence

  val precedence_of_clf_term_pattern :
    state -> clf_term_pattern -> precedence
end

module type SCHEMA_PRECEDENCE = sig
  include Imperative_state.IMPERATIVE_STATE

  include BASE_PRECEDENCE

  val precedence_of_schema : state -> schema -> precedence
end

module type COMP_SORT_PRECEDENCE = sig
  include Imperative_state.IMPERATIVE_STATE

  include BASE_PRECEDENCE

  val precedence_of_comp_kind : state -> comp_kind -> precedence

  val precedence_of_comp_typ : state -> comp_typ -> precedence
end

module type COMP_EXPRESSION_PRECEDENCE = sig
  include Imperative_state.IMPERATIVE_STATE

  include BASE_PRECEDENCE

  val precedence_of_comp_expression : state -> comp_expression -> precedence
end

module type COMP_PATTERN_PRECEDENCE = sig
  include Imperative_state.IMPERATIVE_STATE

  include BASE_PRECEDENCE

  val precedence_of_comp_pattern : state -> comp_pattern -> precedence
end

module type PRECEDENCE_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  val lookup_operator_precedence :
    state -> Qualified_identifier.t -> Int.t Option.t
end

module Base : sig
  type precedence

  val make_static : int -> precedence

  val make_user_defined : int -> precedence

  val compare : application_precedence:int -> precedence -> precedence -> int
end = struct
  type precedence =
    | Static of Int.t
    | User_defined of Int.t

  let[@inline] make_static p = Static p

  let[@inline] make_user_defined p = User_defined p

  let compare ~application_precedence x y =
    match (x, y) with
    | Static x, Static y -> Int.compare x y
    | User_defined x, User_defined y -> Int.compare x y
    | User_defined _, Static y ->
        if application_precedence <= y then -1 else 1
    | Static x, User_defined _ ->
        if x < application_precedence then -1 else 1
end

module Make_lf_precedence (S : PRECEDENCE_STATE) :
  LF_PRECEDENCE with type state = S.state = struct
  include Base

  let application_precedence = 4

  module Ord : Ord.ORD with type t = precedence =
    (val Ord.make (compare ~application_precedence))

  include S

  let precedence_of_lf_kind _state = function
    | LF.Kind.Pi _ -> make_static 1
    | LF.Kind.Arrow _ -> make_static 3
    | LF.Kind.Typ _ -> make_static 5

  let precedence_of_lf_typ state = function
    | LF.Typ.Pi _ -> make_static 1
    | LF.Typ.Arrow _ -> make_static 3
    | LF.Typ.Application { applicand = LF.Typ.Constant { identifier; _ }; _ }
      -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | LF.Typ.Application _ -> make_static application_precedence
    | LF.Typ.Constant _ -> make_static 5

  let precedence_of_lf_term state = function
    | LF.Term.Abstraction _ -> make_static 1
    | LF.Term.Type_annotated _ -> make_static 2
    | LF.Term.Application
        { applicand = LF.Term.Constant { identifier; _ }; _ } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | LF.Term.Application _ -> make_static application_precedence
    | LF.Term.Wildcard _
    | LF.Term.Variable _
    | LF.Term.Constant _ ->
        make_static 6
end

module Make_clf_precedence (S : PRECEDENCE_STATE) :
  CLF_PRECEDENCE with type state = S.state = struct
  include Base

  let application_precedence = 5

  module Ord : Ord.ORD with type t = precedence =
    (val Ord.make (compare ~application_precedence))

  include S

  let precedence_of_clf_typ state = function
    | CLF.Typ.Pi _ -> make_static 1
    | CLF.Typ.Arrow _ -> make_static 3
    | CLF.Typ.Block _ -> make_static 4
    | CLF.Typ.Application
        { applicand = CLF.Typ.Constant { identifier; _ }; _ } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | CLF.Typ.Application _ -> make_static application_precedence
    | CLF.Typ.Constant _ -> make_static 8

  let precedence_of_clf_term state = function
    | CLF.Term.Abstraction _ -> make_static 1
    | CLF.Term.Type_annotated _ -> make_static 2
    | CLF.Term.Application
        { applicand = CLF.Term.Constant { identifier; _ }; _ } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | CLF.Term.Application _ -> make_static application_precedence
    | CLF.Term.Substitution _ -> make_static 6
    | CLF.Term.Projection _ -> make_static 7
    | CLF.Term.Variable _
    | CLF.Term.Meta_variable _
    | CLF.Term.Parameter_variable _
    | CLF.Term.Constant _
    | CLF.Term.Hole _
    | CLF.Term.Tuple _ ->
        make_static 8

  let precedence_of_clf_term_pattern state = function
    | CLF.Term.Pattern.Abstraction _ -> make_static 1
    | CLF.Term.Pattern.Type_annotated _ -> make_static 2
    | CLF.Term.Pattern.Application
        { applicand = CLF.Term.Pattern.Constant { identifier; _ }; _ } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | CLF.Term.Pattern.Application _ -> make_static application_precedence
    | CLF.Term.Pattern.Substitution _ -> make_static 6
    | CLF.Term.Pattern.Projection _ -> make_static 7
    | CLF.Term.Pattern.Wildcard _
    | CLF.Term.Pattern.Variable _
    | CLF.Term.Pattern.Meta_variable _
    | CLF.Term.Pattern.Parameter_variable _
    | CLF.Term.Pattern.Constant _
    | CLF.Term.Pattern.Tuple _ ->
        make_static 8
end

module Make_schema_precedence (S : PRECEDENCE_STATE) :
  SCHEMA_PRECEDENCE with type state = S.state = struct
  include S

  type precedence = Static of Int.t [@unboxed]

  let precedence_of_schema _state = function
    | Meta.Schema.Alternation _ -> Static 1
    | Meta.Schema.Constant _
    | Meta.Schema.Element _ ->
        Static 2

  module Ord : Ord.ORD with type t = precedence = Ord.Make (struct
    type nonrec t = precedence

    let compare (Static x) (Static y) = Int.compare x y
  end)
end

module Make_comp_sort_precedence (S : PRECEDENCE_STATE) :
  COMP_SORT_PRECEDENCE with type state = S.state = struct
  include Base

  let application_precedence = 4

  module Ord : Ord.ORD with type t = precedence =
    (val Ord.make (compare ~application_precedence))

  include S

  let precedence_of_comp_kind _state kind =
    match kind with
    | Comp.Kind.Pi _ -> make_static 1
    | Comp.Kind.Arrow _ -> make_static 2
    | Comp.Kind.Ctype _ -> make_static 5

  let precedence_of_comp_typ state typ =
    match typ with
    | Comp.Typ.Pi _ -> make_static 1
    | Comp.Typ.Arrow _ -> make_static 2
    | Comp.Typ.Cross _ -> make_static 3
    | Comp.Typ.Application
        { applicand =
            ( Comp.Typ.Inductive_typ_constant { identifier; _ }
            | Comp.Typ.Stratified_typ_constant { identifier; _ }
            | Comp.Typ.Coinductive_typ_constant { identifier; _ }
            | Comp.Typ.Abbreviation_typ_constant { identifier; _ } )
        ; _
        } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | Comp.Typ.Application _ -> make_static application_precedence
    | Comp.Typ.Inductive_typ_constant _
    | Comp.Typ.Stratified_typ_constant _
    | Comp.Typ.Coinductive_typ_constant _
    | Comp.Typ.Abbreviation_typ_constant _
    | Comp.Typ.Box _ ->
        make_static 5
end

module Make_comp_expression_precedence (S : PRECEDENCE_STATE) :
  COMP_EXPRESSION_PRECEDENCE with type state = S.state = struct
  include Base

  let application_precedence = 3

  module Ord : Ord.ORD with type t = precedence =
    (val Ord.make (compare ~application_precedence))

  include S

  let precedence_of_comp_expression state expression =
    match expression with
    | Comp.Expression.Type_annotated _ -> make_static 1
    | Comp.Expression.Let _
    | Comp.Expression.Impossible _
    | Comp.Expression.Case _
    | Comp.Expression.Fn _
    | Comp.Expression.Mlam _
    | Comp.Expression.Fun _ ->
        make_static 2
    | Comp.Expression.Application
        { applicand =
            ( Comp.Expression.Program { identifier; _ }
            | Comp.Expression.Constructor { identifier; _ } )
        ; _
        } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | Comp.Expression.Application _ -> make_static application_precedence
    | Comp.Expression.Observation _ -> make_static 4
    | Comp.Expression.Hole _
    | Comp.Expression.Box _
    | Comp.Expression.Box_hole _
    | Comp.Expression.Tuple _
    | Comp.Expression.Variable _
    | Comp.Expression.Constructor _
    | Comp.Expression.Program _ ->
        make_static 5
end

module Make_comp_pattern_precedence (S : PRECEDENCE_STATE) :
  COMP_PATTERN_PRECEDENCE with type state = S.state = struct
  include Base

  let application_precedence = 3

  module Ord : Ord.ORD with type t = precedence =
    (val Ord.make (compare ~application_precedence))

  include S

  let precedence_of_comp_pattern state pattern =
    match pattern with
    | Comp.Pattern.Type_annotated _ -> make_static 2
    | Comp.Pattern.Application
        { applicand = Comp.Pattern.Constructor { identifier; _ }; _ } -> (
        match lookup_operator_precedence state identifier with
        | Option.Some precedence -> make_user_defined precedence
        | Option.None -> make_static application_precedence)
    | Comp.Pattern.Application _ -> make_static application_precedence
    | Comp.Pattern.Variable _
    | Comp.Pattern.Constructor _
    | Comp.Pattern.Meta_object _
    | Comp.Pattern.Tuple _
    | Comp.Pattern.Wildcard _ ->
        make_static 4
end

module Make_precedences (S : PRECEDENCE_STATE) = struct
  include S
  module Lf_precedence = Make_lf_precedence (S)
  module Clf_precedence = Make_clf_precedence (S)
  module Schema_precedence = Make_schema_precedence (S)
  module Comp_sort_precedence = Make_comp_sort_precedence (S)
  module Comp_expression_precedence = Make_comp_expression_precedence (S)
  module Comp_pattern_precedence = Make_comp_pattern_precedence (S)
  include Lf_precedence
  include Clf_precedence
  include Schema_precedence
  include Comp_sort_precedence
  include Comp_expression_precedence
  include Comp_pattern_precedence
end
