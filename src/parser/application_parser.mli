(** Disambiguation of expression applications with user-defined operators and
    juxtapositions by dynamic recursive descent parsing.

    This implementation is inspired by Parsec's [buildExpressionParser] found
    {{:https://github.com/haskell/parsec/blob/1f542120d9adc5e22f8791a6d595210e93c6c389/src/Text/Parsec/Expr.hs#L95-L177}
      here}, and figure 2 of Nils Anders Danielsson and Ulf Norell's "Parsing
    Mixfix Operators".

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
