(** Disambiguation of expression applications with user-defined operators and
    juxtapositions.

    @author Marc-Antoine Ouimet *)

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

module Make_application_disambiguation
    (Expression : EXPRESSION with type location = Location.t) :
  APPLICATION_DISAMBIGUATION with type expression = Expression.t
