(** Disambiguation of expression applications with user-defined operators and
    juxtapositions using Dijkstra's shunting yard algorithm.

    @author Marc-Antoine Ouimet *)

open Support
open Beluga_syntax

module type EXPRESSION = sig
  type t

  type location

  val location : t -> location
end

module Make_application_rewriter
    (Expression : EXPRESSION with type location = Location.t) : sig
  type expression = Expression.t

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
