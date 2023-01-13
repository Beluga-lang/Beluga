(** Disambiguation of term applications.

    This makes use of Dijkstra's shunting yard algorithm, but first makes
    sure that the juxtaposition of non-operator terms and nullary operators
    has higher precedence than the application of user-defined operators. *)

open Support

module type APPLICATION_DISAMBIGUATION_STATE = sig
  include State.STATE

  type operator

  type expression

  (** [guard_operator expression state] is [(state', Option.some operator)]
      if [expression] corresponds to a non-nullary [operator] in the
      disambiguation [state], and [(state', Option.None)] otherwise.

      A concrete implementation of this function typically pattern-matches on
      [expression] to see if it is a constant, then performs a lookup in
      [state] for that constant to get its user-defined operator description,
      then checks whether the operator is nullary. *)
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
                               and type expression = Operand.expression) : sig
  (** @closed *)
  include
    APPLICATION_DISAMBIGUATION_STATE
      with type state = Disambiguation_state.state
       and type operator = Operator.t
       and type expression = Operand.expression

  type operand = Operand.t

  (** [Misplaced_operator { operator; operands }] is raised from
      [shunting_yard primitives] if [operator] appears in an illegal position
      in [primitives] such that it would be rewritten with arguments
      [arguments]. *)
  exception
    Misplaced_operator of
      { operator : operator
      ; operands : operand list
      }

  (** [Ambiguous_operator_placement { left_operator; right_operator }] is
      raised from [shunting_yard primitives] if [right_operator] appears in
      an illegal position in [primitives] with respect to [left_operator],
      such that [left_operator] and [right_operator] have the same
      precedence, and would be rewritten as being consecutive while one of
      [left_operator] and [right_operator] is left-associative with the other
      being right-associative.

      For instance:

      - [a -> b <- c] is ambiguous if [->] is right-associative and [<-] is
        left-associative, with [->] and [<-] having the same precedence.
      - [a <- b -> c] is ambiguous if [<-] is left-associative and [->] is
        right-associative, with [<-] and [->] having the same precedence.
      - [++ a + b] is ambiguous if [++] is right-associative and [+] is
        left-associative, with [++] and [+] having the same precedence.
      - [++ a !] is ambiguous if [++] is right-associative and [!] is
        left-associative, with [++] and [!] having the same precedence.
      - [a ^ b !] is ambiguous if [^] is right-associative and [!] is
        left-associative, with [^] and [!] having the same precedence. *)
  exception
    Ambiguous_operator_placement of
      { left_operator : operator
      ; right_operator : operator
      }

  (** [Consecutive_non_associative_operators { left_operator; right_operator }]
      is raised from [shunting_yard primitives] if non-associative operator
      [right_operator] appears in an illegal position in [primitives] with
      respect to [left_operator], such that [left_operator = right_operator],
      and [left_operator] and [right_operator] would be rewritten as being
      consecutive, as in [a left_operator b right_operator c]. *)
  exception
    Consecutive_non_associative_operators of
      { left_operator : operator
      ; right_operator : operator
      }

  (** [Arity_mismatch { operator; operator_arity; operands }] is raised from
      [shunting_yard primitives] if [operator] appears in an illegal position
      in [primitives] such that it is applied to too few arguments, meaning
      that [List.length arguments < operator_arity]. *)
  exception
    Arity_mismatch of
      { operator : operator
      ; operator_arity : int
      ; operands : operand list
      }

  val disambiguate_application :
    expression List2.t -> (expression * operand List1.t, exn) result t
end = struct
  include Disambiguation_state
  include
    Centiparsec.Shunting_yard.Make (Associativity) (Fixity) (Operand)
      (Operator)

  let make_atom expression = Operand.Atom expression

  let make_application applicand arguments =
    Operand.Application { applicand; arguments }

  let identify expression =
    Disambiguation_state.guard_operator expression >>= function
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
            let expression' = make_atom expression in
            let rest' = reduce_juxtapositions rest in
            operand expression' :: rest'
        | x :: xs, rest ->
            let arguments' = List1.map make_atom (List1.from x xs) in
            let expression' = make_application expression arguments' in
            let rest' = reduce_juxtapositions rest in
            operand expression' :: rest')
    | `Operator op :: rest -> (
        match Operator.fixity op with
        | Fixity.Prefix -> (
            match take_while_operand rest with
            | [], rest' ->
                let rest'' = reduce_juxtapositions rest' in
                operator op :: rest''
            | x :: xs, rest' ->
                let expression = Operator.applicand op in
                let arguments' = List1.map make_atom (List1.from x xs) in
                let expression' = make_application expression arguments' in
                let rest'' = reduce_juxtapositions rest' in
                operand expression' :: rest'')
        | Fixity.Infix
        | Fixity.Postfix ->
            let rest' = reduce_juxtapositions rest in
            operator op :: rest')
    | [] -> []

  let disambiguate_application expressions =
    let expressions_list = List2.to_list expressions in
    let* identified_expressions = traverse_list identify expressions_list in
    let translated_expressions =
      reduce_juxtapositions identified_expressions
    in
    match shunting_yard translated_expressions with
    | Operand.Atom _
    (* [expressions] is a list of expressions. This was necessarily
       elaborated to an [Application]. *) ->
        assert false
    | Operand.Application { applicand; arguments } ->
        return (Result.ok (applicand, arguments))
    | exception cause -> return (Result.error cause)
end
