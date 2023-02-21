(** Disambiguation of term applications.

    @author Marc-Antoine Ouimet *)

open Support
open Beluga_syntax

module type EXPRESSION = sig
  type t

  type location

  val location : t -> location
end

module Make_application_parser
    (Expression : EXPRESSION with type location = Location.t) : sig
  type source

  val make_expression : Expression.t -> source

  val make_operator :
    Expression.t -> Operator.t -> Qualified_identifier.t -> source

  type target = private
    | Atom of
        { expression : Expression.t
        ; location : Location.t
        }
    | Application of
        { applicand : Expression.t
        ; arguments : target List1.t
        ; location : Location.t
        }

  val parse_application : source List2.t -> Expression.t * target List1.t
end
