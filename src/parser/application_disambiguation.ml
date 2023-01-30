open Support
open Beluga_syntax

module type APPLICATION_DISAMBIGUATION_STATE = sig
  include State.STATE

  type operator

  type expression

  val guard_operator : expression -> operator Option.t t
end

module type OPERAND = sig
  type expression

  type t =
    | Atom of expression
    | Application of
        { applicand : expression
        ; arguments : t List1.t
        }
end

module type APPLICATION_DISAMBIGUATOR = sig
  (** @closed *)
  include APPLICATION_DISAMBIGUATION_STATE

  type operand

  exception
    Misplaced_operator of
      { operator : operator
      ; operands : operand list
      }

  exception
    Ambiguous_operator_placement of
      { left_operator : operator
      ; right_operator : operator
      }

  exception
    Consecutive_non_associative_operators of
      { left_operator : operator
      ; right_operator : operator
      }

  exception
    Arity_mismatch of
      { operator : operator
      ; operator_arity : int
      ; operands : operand list
      }

  val disambiguate_application :
    expression List2.t -> (expression * operand List1.t, exn) result t
end

module Make
    (Associativity : Shunting_yard.ASSOCIATIVITY)
    (Fixity : Shunting_yard.FIXITY)
    (Operand : OPERAND) (Operator : sig
      include
        Shunting_yard.OPERATOR
          with type associativity = Associativity.t
           and type fixity = Fixity.t
           and type operand = Operand.t

      val applicand : t -> Operand.expression
    end)
    (Disambiguation_state : APPLICATION_DISAMBIGUATION_STATE
                              with type operator = Operator.t
                               and type expression = Operand.expression) :
  APPLICATION_DISAMBIGUATOR
    with type state = Disambiguation_state.state
     and type operator = Operator.t
     and type expression = Operand.expression
     and type operand = Operand.t = struct
  include Disambiguation_state

  type operand = Operand.t

  module Shunting_yard =
    Shunting_yard.Make (Associativity) (Fixity) (Operand) (Operator)

  exception Misplaced_operator = Shunting_yard.Misplaced_operator

  exception
    Ambiguous_operator_placement = Shunting_yard.Ambiguous_operator_placement

  exception
    Consecutive_non_associative_operators = Shunting_yard
                                            .Consecutive_non_associative_operators

  exception Arity_mismatch = Shunting_yard.Arity_mismatch

  let make_atom expression = Operand.Atom expression

  let make_application applicand arguments =
    Operand.Application { applicand; arguments }

  (** [identify expression] determines whether [expression] should be
      considered as an operand or an operator, based on {!guard_operator}. *)
  let identify expression =
    guard_operator expression >>= function
    | Option.None -> return (`Operand expression)
    | Option.Some operator -> return (`Operator operator)

  let rec take_while_operand expressions =
    match expressions with
    | `Operand x :: xs ->
        let operands, rest = take_while_operand xs in
        (x :: operands, rest)
    | expressions -> ([], expressions)

  let rec reduce_juxtapositions expressions =
    match expressions with
    | `Operand expression :: rest -> (
        match take_while_operand rest with
        | [], rest ->
            (* [expression] is not in juxtaposition, so leave [expression] as
               an atom. *)
            let expression' = make_atom expression in
            let rest' = reduce_juxtapositions rest in
            Shunting_yard.operand expression' :: rest'
        | x :: xs, rest ->
            (* The expressions [expression], [x] and those in [xs] are in
               juxtaposition, so they are reduced to an application with
               applicand [expression]. *)
            let arguments' = List1.map make_atom (List1.from x xs) in
            let expression' = make_application expression arguments' in
            let rest' = reduce_juxtapositions rest in
            Shunting_yard.operand expression' :: rest')
    | `Operator op :: rest -> (
        match Operator.fixity op with
        | Fixity.Prefix -> (
            match take_while_operand rest with
            | [], rest' ->
                (* [op] is a prefix operator not followed by operands, so
                   leave [op] as an operator. *)
                let rest'' = reduce_juxtapositions rest' in
                Shunting_yard.operator op :: rest''
            | x :: xs, rest' ->
                (* [op] is a prefix operator followed by operands, so [op],
                   [x] and [xs] are reduced to an application. This
                   effectively disregards [op]'s precedence, but
                   juxtapositions have to be of higher precedence than
                   user-defined operators. *)
                let expression = Operator.applicand op in
                let arguments' = List1.map make_atom (List1.from x xs) in
                let expression' = make_application expression arguments' in
                let rest'' = reduce_juxtapositions rest' in
                Shunting_yard.operand expression' :: rest'')
        | Fixity.Infix
        | Fixity.Postfix ->
            let rest' = reduce_juxtapositions rest in
            Shunting_yard.operator op :: rest')
    | [] -> []

  let disambiguate_application expressions =
    let expressions_list = List2.to_list expressions in
    let* identified_expressions = traverse_list identify expressions_list in
    let translated_expressions =
      reduce_juxtapositions identified_expressions
    in
    match Shunting_yard.shunting_yard translated_expressions with
    | Operand.Atom _
    (* [expressions] is a list of expressions. This was necessarily
       elaborated to an [Application]. *) ->
        assert false
    | Operand.Application { applicand; arguments } ->
        return (Result.ok (applicand, arguments))
    | exception Shunting_yard.Misplaced_operator { operator; operands } ->
        return (Result.error (Misplaced_operator { operator; operands }))
    | exception
        Shunting_yard.Ambiguous_operator_placement
          { left_operator; right_operator } ->
        return
          (Result.error
             (Ambiguous_operator_placement { left_operator; right_operator }))
    | exception
        Shunting_yard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        return
          (Result.error
             (Consecutive_non_associative_operators
                { left_operator; right_operator }))
    | exception
        Shunting_yard.Arity_mismatch { operator; operator_arity; operands }
      ->
        return
          (Result.error
             (Arity_mismatch { operator; operator_arity; operands }))
    | exception cause -> Error.raise cause
end
