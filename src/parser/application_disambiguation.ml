open Support

module type APPLICATION_DISAMBIGUATION_STATE = sig
  type t

  type operator

  type expression

  val guard_operator : expression -> t -> operator Option.t
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

module Make
    (Associativity : Centiparsec.Shunting_yard.ASSOCIATIVITY)
    (Fixity : Centiparsec.Shunting_yard.FIXITY)
    (Operand : OPERAND) (Operator : sig
      include
        Centiparsec.Shunting_yard.OPERATOR
          with type associativity = Associativity.t
           and type fixity = Fixity.t
           and type operand = Operand.t

      val applicand : t -> Operand.expression
    end)
    (Disambiguation_state : APPLICATION_DISAMBIGUATION_STATE
                              with type operator = Operator.t
                               and type expression = Operand.expression) =
struct
  module Shunting_yard =
    Centiparsec.Shunting_yard.Make (Associativity) (Fixity) (Operand)
      (Operator)

  exception Misplaced_operator = Shunting_yard.Misplaced_operator

  exception
    Ambiguous_operator_placement = Shunting_yard.Ambiguous_operator_placement

  exception
    Consecutive_non_associative_operators = Shunting_yard
                                            .Consecutive_non_associative_operators

  exception Arity_mismatch = Shunting_yard.Arity_mismatch

  include State.Make (Disambiguation_state)

  let make_atom expression = Operand.Atom expression

  let make_application applicand arguments =
    Operand.Application { applicand; arguments }

  let identify expression =
    get >>= fun state ->
    match Disambiguation_state.guard_operator expression state with
    | Option.None -> return (`Operand expression)
    | Option.Some operator -> return (`Operator operator)

  let rec identify_list expressions =
    match expressions with
    | [] -> return []
    | x :: xs ->
        let* y = identify x in
        let* ys = identify_list xs in
        return (y :: ys)

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
            let expression' = make_atom expression in
            let rest' = reduce_juxtapositions rest in
            Shunting_yard.operand expression' :: rest'
        | x :: xs, rest ->
            let arguments' = List1.map make_atom (List1.from x xs) in
            let expression' = make_application expression arguments' in
            let rest' = reduce_juxtapositions rest in
            Shunting_yard.operand expression' :: rest')
    | `Operator operator :: rest -> (
        match Operator.fixity operator with
        | Fixity.Prefix -> (
            match take_while_operand rest with
            | [], rest' ->
                let rest'' = reduce_juxtapositions rest' in
                Shunting_yard.operator operator :: rest''
            | x :: xs, rest' ->
                let expression = Operator.applicand operator in
                let arguments' = List1.map make_atom (List1.from x xs) in
                let expression' = make_application expression arguments' in
                let rest'' = reduce_juxtapositions rest' in
                Shunting_yard.operand expression' :: rest'')
        | Fixity.Infix
        | Fixity.Postfix ->
            let rest' = reduce_juxtapositions rest in
            Shunting_yard.operator operator :: rest')
    | [] -> []

  let disambiguate_application expressions =
    let expressions_list = List2.to_list expressions in
    let* identified_expressions = identify_list expressions_list in
    let translated_expressions =
      reduce_juxtapositions identified_expressions
    in
    match Shunting_yard.shunting_yard translated_expressions with
    | Operand.Atom _ -> assert false
    | Operand.Application { applicand; arguments } ->
        return (Result.ok (applicand, arguments))
    | exception cause -> return (Result.error cause)
end
