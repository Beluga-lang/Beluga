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

(* Choose one of [Make_application_parser] or [Make_application_rewriter]. *)
module Make_application_disambiguation = Make_application_parser
