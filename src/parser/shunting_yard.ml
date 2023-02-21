open Support
open Beluga_syntax

(* Extension to the {!module:Stdlib.List} module. *)
module List : sig
  include module type of List

  (** [take_rev_opt k \[x1; x2; ...; xn\]] is
      [Option.Some (\[xk; x(k-1); ...; x1\], \[x(k+1); x(k+2); ...; xn\])] if
      [0 <= k <= n], and [Option.None] otherwise.

      This implementation avoids an extraneous list reversal in the shunting
      yard algorithm.

      @raise Invalid_argument if [k < 0]. *)
  val take_rev_opt : int -> 'a list -> ('a list * 'a list) option
end = struct
  include List

  let take_rev_opt =
    let rec take_rev_opt k l acc =
      if k = 0 then Option.some (acc, l)
      else
        match l with
        | x :: xs -> take_rev_opt (k - 1) xs (x :: acc)
        | [] -> Option.none
    in
    fun k l ->
      if k < 0 then
        raise (Invalid_argument "Shunting_yard.List.take_rev_opt")
      else take_rev_opt k l []
end

module type EXPRESSION = sig
  type t

  type location

  val location : t -> location
end

module Make_application_rewriter
    (Expression : EXPRESSION with type location = Location.t) =
struct
  type expression = Expression.t

  type operator =
    { applicand : Expression.t
    ; operator : Operator.t
    }

  type source =
    | Expression of expression
    | Operator of operator
    | Juxtaposition of
        { applicand : expression
        ; arguments : expression List1.t
        }

  let make_expression expression = Expression expression

  let make_operator applicand operator _identifier =
    Operator { applicand; operator }

  let make_juxtaposition applicand arguments =
    Juxtaposition { applicand; arguments }

  type target =
    | Atom of
        { expression : Expression.t
        ; location : Location.t
        }
    | Application of
        { applicand : Expression.t
        ; arguments : target List1.t
        ; location : Location.t
        }

  let parse_tree_location = function
    | Atom { location; _ }
    | Application { location; _ } ->
        location

  let atom expression =
    Atom { expression; location = Expression.location expression }

  let application applicand arguments =
    let location =
      Location.join
        (Expression.location applicand)
        (Location.join
           (parse_tree_location (List1.head arguments))
           (parse_tree_location (List1.last arguments)))
    in
    Application { applicand; arguments; location }

  exception Misplaced_operator

  exception Ambiguous_operator_placement

  exception Consecutive_non_associative_operators

  exception
    Arity_mismatch of
      { expected_arity : Int.t
      ; available_arguments : Int.t
      }

  exception Leftover_expressions

  (** [validate_argument_indices operator arguments] ensures that writing of
      operator [operator] with arguments [arguments] is valid based on their
      relative positioning in the initial list of primitives to rewrite.

      - If [operator] is prefix, then its argument should appear right of it
      - If [operator] is infix, then its left argument should appear left of
        it, and its right argument should appear right of it
      - If [operator] is postfix, then its argument should appear left of it

      @raise Misplaced_operator *)
  let[@inline] validate_argument_indices (i, o)
      (arguments : (int * target) list) =
    let raise_misplaced_operator_exception () =
      Error.raise_at1 (Expression.location o.applicand) Misplaced_operator
    in
    match Operator.fixity o.operator with
    | Fixity.Prefix ->
        (* Argument to a prefix operator appear right of the operator *)
        let[@warning "-8"] [ (j, _argument) ] = arguments in
        if i < j then () else raise_misplaced_operator_exception ()
    | Fixity.Infix ->
        let[@warning "-8"] [ (left, _left_argument)
                           ; (right, _right_argument)
                           ] =
          arguments
        in
        (* The left and right arguments appear left and right of the operator
           respectively *)
        if left < i && i < right then ()
        else raise_misplaced_operator_exception ()
    | Fixity.Postfix ->
        (* Argument to a postfix operator appear left of the operator *)
        let[@warning "-8"] [ (j, _argument) ] = arguments in
        if j < i then () else raise_misplaced_operator_exception ()

  (** [write operator output] writes [operator] onto [output] by taking
      arguments from [output]. Operands in [output] are in reverse order of
      their initial appearance in the list of primitives since it is a stack.

      @raise Arity_mismatch *)
  let write (i, o) output =
    let operator_arity = Operator.arity o.operator in
    match List.take_rev_opt operator_arity output with
    | Option.Some (arguments, output) ->
        validate_argument_indices (i, o) arguments;
        let arguments = List.map Pair.snd arguments in
        let result =
          application o.applicand (List1.unsafe_of_list arguments)
        in
        (i, result) :: output
    | Option.None ->
        Error.raise_at1
          (Expression.location o.applicand)
          (Arity_mismatch
             { expected_arity = operator_arity
             ; available_arguments = List.length output
             })

  (** [validate_left_associative_operator_placement ~x ~px ~y ~py] ensures
      that [x] and [y] are not operators of the same precedence [px] and [py]
      respectively, with [x] being left-associative and [y] being
      right-associative. Otherwise, [x] and [y] are ambiguous in the operator
      stack. *)
  let[@inline] validate_left_associative_operator_placement ~x ~px ~y ~py =
    if Int.(px = py) && Operator.is_right_associative x.operator then
      Error.raise_at2
        (Expression.location x.applicand)
        (Expression.location y.applicand)
        Ambiguous_operator_placement

  (** [validate_right_associative_operator_placement ~x ~px ~y ~py] ensures
      that [x] and [y] are not operators of the same precedence [px] and [py]
      respectively, with [x] being right-associative and [y] being
      left-associative. Otherwise, [x] and [y] are ambiguous in the operator
      stack. *)
  let[@inline] validate_right_associative_operator_placement ~x ~px ~y ~py =
    if Int.(px = py) && Operator.is_left_associative x.operator then
      Error.raise_at2
        (Expression.location x.applicand)
        (Expression.location y.applicand)
        Ambiguous_operator_placement

  (** [validate_non_associative_operator_placement ~x ~y] ensures that [x]
      and [y] are not equal non-associative operators. Otherwise, [x] and [y]
      are invalid in the operator stack. *)
  let[@inline] validate_non_associative_operator_placement ~x ~y =
    if Operator.(x.operator = y.operator) then
      Error.raise_at2
        (Expression.location x.applicand)
        (Expression.location y.applicand)
        Consecutive_non_associative_operators

  (** [pop x output stack] pops the operator stack [stack] as needed with
      respect to [x] and [output] to ensure that writing [x] respects the
      precedence and associativity of operators in [stack].

      @raise Consecutive_non_associative_operators
      @raise Ambiguous_operator_placement *)
  let[@inline] rec pop y output stack =
    match stack with
    | (index, x) :: xs -> (
        (* In the original input list to {!shunting_yard}, [x] is an operator
           on the left, and [y] is an operator on the right. *)
        let[@inline] write_x_if cond =
          if cond then
            let output' = write (index, x) output in
            pop y output' xs
          else (output, stack)
        in
        let px = Operator.precedence x.operator in
        let py = Operator.precedence y.operator in
        match Operator.associativity y.operator with
        | Associativity.Left_associative ->
            validate_left_associative_operator_placement ~x ~px ~y ~py;
            write_x_if Int.(px >= py)
        | Associativity.Right_associative ->
            validate_right_associative_operator_placement ~x ~px ~y ~py;
            write_x_if Int.(px > py)
        | Associativity.Non_associative ->
            validate_non_associative_operator_placement ~x ~y;
            write_x_if Int.(px >= py))
    | [] -> (output, stack)

  let[@inline] rec pop_all output operators =
    match operators with
    | op :: ops ->
        let output' = write op output in
        pop_all output' ops
    | [] -> output

  (** [shunting_yard operands operators primitives] reduces [primitives] to a
      single operand by successively adding operands to [operands] and
      writing operators from [operators] using arguments in [operands]. The
      list of primitives [primitives] is rewritten using reverse Polish
      notation based on the precedence, fixity, arity and associativity of
      the operators in [operators]. [operands] and [operators] are both
      stacks. Elements of [operands], [operators] and [primitives] are
      indexed by their initial position in the list of expressions to rewrite
      for early error detection and error reporting.

      @raise Arity_mismatch
      @raise Leftover_expressions
      @raise Consecutive_non_associative_operators
      @raise Ambiguous_operator_placement
      @raise Misplaced_operator *)
  let rec shunting_yard operands operators primitives =
    match primitives with
    | (index, Expression expression) :: ps ->
        let operands' = (index, atom expression) :: operands in
        shunting_yard operands' operators ps
    | (index, Juxtaposition { applicand; arguments }) :: ps ->
        let operands' =
          (index, application applicand (List1.map atom arguments))
          :: operands
        in
        shunting_yard operands' operators ps
    | (index, Operator o) :: ps -> (
        match Operator.fixity o.operator with
        | Fixity.Prefix ->
            (* Writing of [operator] is delayed since its arguments have yet
               to be encountered in [primitives]. *)
            let operators' = (index, o) :: operators in
            shunting_yard operands operators' ps
        | Fixity.Infix ->
            (* Prepare [operator]'s left argument. *)
            let output, operators' = pop o operands operators in
            (* Writing of [operator] is delayed since its right argument has
               yet to be encountered in [primitives]. *)
            let operators'' = (index, o) :: operators' in
            shunting_yard output operators'' ps
        | Fixity.Postfix ->
            (* Prepare [operator]'s left arguments. *)
            let output, operators' = pop o operands operators in
            (* Immediately write the postfix operator. *)
            let output' = write (index, o) output in
            shunting_yard output' operators' ps)
    | [] -> (
        let output = pop_all operands operators in
        match List.rev output with
        | [ (_, e) ] -> e
        | e1 :: e2 :: es ->
            Error.raise_at
              (List2.to_list1
                 (List2.map
                    (fun (_index, expression) ->
                      parse_tree_location expression)
                    (List2.from e1 e2 es)))
              Leftover_expressions
        | [] -> assert false)

  let shunting_yard terms = shunting_yard [] [] (List.index terms)

  let rec rewrite_juxtapositions expressions =
    match expressions with
    | (Expression applicand as e) :: expressions -> (
        match
          List.take_while_map
            (function
              | Expression expression -> Option.some expression
              | Operator _ -> Option.none
              | Juxtaposition _ -> assert false)
            expressions
        with
        | [], expressions -> e :: rewrite_juxtapositions expressions
        | x :: xs, expressions ->
            make_juxtaposition applicand (List1.from x xs)
            :: rewrite_juxtapositions expressions)
    | (Operator _ as e) :: expressions ->
        e :: rewrite_juxtapositions expressions
    | [] -> []
    | Juxtaposition _ :: _ -> assert false

  let disambiguate_application expressions =
    let expressions_list = List2.to_list expressions in
    match shunting_yard (rewrite_juxtapositions expressions_list) with
    | Atom _expression -> assert false
    | Application { applicand; arguments; _ } -> (applicand, arguments)

  let () =
    Error.register_exception_printer (function
      | Misplaced_operator -> Format.dprintf "This operator is misplaced."
      | Ambiguous_operator_placement ->
          Format.dprintf "This operator's placement is ambiguous."
      | Consecutive_non_associative_operators ->
          Format.dprintf
            "These non-associative operators may not appear consecutively \
             at the same precedence level."
      | Arity_mismatch { expected_arity; available_arguments } ->
          Format.dprintf
            "This operator expected %d argument(s), but only %d argument(s) \
             are given."
            expected_arity available_arguments
      | Leftover_expressions ->
          Format.dprintf
            "These expressions are are leftover after application rewriting."
      | cause -> Error.raise_unsupported_exception_printing cause)
end
