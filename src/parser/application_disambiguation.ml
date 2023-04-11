open Support
open Beluga_syntax

module type EXPRESSION = sig
  type t

  type location

  val location : t -> location
end

module type APPLICATION_DISAMBIGUATION = sig
  type expression

  type source

  val make_expression : expression -> source

  val make_operator :
    expression -> Operator.t -> Qualified_identifier.t -> source

  type target = private
    | Atom of
        { expression : expression
        ; location : Location.t
        }
    | Application of
        { applicand : expression
        ; arguments : target List1.t
        ; location : Location.t
        }

  val disambiguate_application :
    source List2.t -> expression * target List1.t
end

module Make_application_parser = Application_parser.Make_application_parser
module Make_application_rewriter = Shunting_yard.Make_application_rewriter

module Make_fallback_application_disambiguation
    (Disambiguation : APPLICATION_DISAMBIGUATION)
    (Error_disambiguation : APPLICATION_DISAMBIGUATION
                              with type expression =
                                Disambiguation.expression) :
  APPLICATION_DISAMBIGUATION
    with type expression = Disambiguation.expression
     and type target = Disambiguation.target = struct
  exception Inconsistent_application_disambiguation

  type expression = Disambiguation.expression

  type source =
    | Expression of expression
    | Operator of
        { expression : expression
        ; operator : Operator.t
        ; identifier : Qualified_identifier.t
        }

  let[@inline] make_expression expression = Expression expression

  let[@inline] make_operator expression operator identifier =
    Operator { expression; operator; identifier }

  type target = Disambiguation.target = private
    | Atom of
        { expression : expression
        ; location : Location.t
        }
    | Application of
        { applicand : expression
        ; arguments : target List1.t
        ; location : Location.t
        }

  let prepare_disambiguation_expression = function
    | Expression expression -> Disambiguation.make_expression expression
    | Operator { expression; operator; identifier } ->
        Disambiguation.make_operator expression operator identifier

  let prepare_error_expression = function
    | Expression expression ->
        Error_disambiguation.make_expression expression
    | Operator { expression; operator; identifier } ->
        Error_disambiguation.make_operator expression operator identifier

  let disambiguate_application expressions =
    let disambiguation_expressions =
      List2.map prepare_disambiguation_expression expressions
    in
    try
      Disambiguation.disambiguate_application disambiguation_expressions
    with
    | _ ->
        (* Disambiguation using [Disambiguation] failed. Disambiguation with
           [Error_disambiguation] must fail, and provide a better error to
           report. *)
        let error_expressions =
          List2.map prepare_error_expression expressions
        in
        ignore
          (Error_disambiguation.disambiguate_application
             error_expressions (* Should raise *));
        (* Did not raise, the two algorithms are not equivalent *)
        Error.raise Inconsistent_application_disambiguation
end

module Make_rewrite_parse_application_disambiguation
    (Expression : EXPRESSION with type location = Location.t) :
  APPLICATION_DISAMBIGUATION with type expression = Expression.t = struct
  module Disambiguation = Make_application_parser (Expression)
  module Error_disambiguation = Make_application_rewriter (Expression)
  include
    Make_fallback_application_disambiguation
      (Disambiguation)
      (Error_disambiguation)
end

(* Choose one of [Make_application_parser], [Make_application_rewriter] or
   [Make_rewrite_parse_application_disambiguation]. *)
module Make_application_disambiguation = Make_application_parser
