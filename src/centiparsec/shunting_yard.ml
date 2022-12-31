open Support

module type ASSOCIATIVITY = sig
  type t = private
    | Left_associative
    | Right_associative
    | Non_associative
end

module type FIXITY = sig
  type t = private
    | Prefix
    | Infix
    | Postfix
end

module type OPERAND = sig
  type t
end

module type OPERATOR = sig
  type associativity

  type fixity

  type operand

  type t

  val arity : t -> int

  val precedence : t -> int

  val fixity : t -> fixity

  val associativity : t -> associativity

  val write : t -> operand list -> operand

  include Eq.EQ with type t := t
end

module type S = sig
  type operand

  type operator

  type primitive

  val operand : operand -> primitive

  val operator : operator -> primitive

  exception Empty_expression

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

  exception Leftover_expressions of operand List2.t

  val shunting_yard : primitive list -> operand
end

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
      if k < 0 then raise (Invalid_argument "ShuntingYard.List.take_rev_opt")
      else take_rev_opt k l []
end

module Make
    (Associativity : ASSOCIATIVITY)
    (Fixity : FIXITY)
    (Operand : OPERAND)
    (Operator : OPERATOR
                  with type associativity = Associativity.t
                   and type fixity = Fixity.t
                   and type operand = Operand.t) :
  S with type operand = Operand.t and type operator = Operator.t = struct
  type operand = Operand.t

  type operator = Operator.t

  exception Empty_expression

  exception
    Misplaced_operator of
      { operator : Operator.t
      ; operands : Operand.t List.t
      }

  exception
    Ambiguous_operator_placement of
      { left_operator : Operator.t
      ; right_operator : Operator.t
      }

  exception
    Consecutive_non_associative_operators of
      { left_operator : Operator.t
      ; right_operator : Operator.t
      }

  exception
    Arity_mismatch of
      { operator : Operator.t
      ; operator_arity : Int.t
      ; operands : Operand.t List.t
      }

  exception Leftover_expressions of Operand.t List2.t

  type primitive =
    | Operand of Operand.t
    | Operator of Operator.t

  let[@inline] operand a = Operand a

  let[@inline] operator op = Operator op

  let[@inline] is_operator_right_associative operator =
    match Operator.associativity operator with
    | Associativity.Right_associative -> true
    | Associativity.Left_associative
    | Associativity.Non_associative ->
        false

  let[@inline] is_operator_left_associative operator =
    match Operator.associativity operator with
    | Associativity.Left_associative -> true
    | Associativity.Right_associative
    | Associativity.Non_associative ->
        false

  (** [validate_argument_indices operator arguments] ensures that writing of
      operator [operator] with arguments [arguments] is valid based on their
      relative positioning in the initial list of primitives to rewrite.

      If [operator] is infix, then [List.length arguments = 2].

      - If [operator] is prefix, then all of its arguments should appear
        right of it
      - If [operator] is infix, then its left argument should appear left of
        it, and its right argument should appear right of it
      - If [operator] is postfix, then all of its arguments should appear
        left of it

      @raise Misplaced_operator *)
  let[@inline] validate_argument_indices (i, operator) arguments =
    let raise_misplaced_operator_exception () =
      let operands = List.map Pair.snd arguments in
      raise (Misplaced_operator { operator; operands })
    in
    match Operator.fixity operator with
    | Fixity.Prefix ->
        (* Arguments to a prefix operator appear right of the operator *)
        if List.for_all (fun (j, _) -> i < j) arguments then ()
        else raise_misplaced_operator_exception ()
    | Fixity.Infix ->
        let[@warning "-8"] [ (left, _); (right, _) ] = arguments in
        (* The left and right arguments appear left and right of the operator
           respectively *)
        if left < i && i < right then ()
        else raise_misplaced_operator_exception ()
    | Fixity.Postfix ->
        (* Arguments to a postfix operator appear left of the operator *)
        if List.for_all (fun (j, _) -> j < i) arguments then ()
        else raise_misplaced_operator_exception ()

  (** [write operator output] writes [operator] onto [output] by taking
      arguments from [output]. Operands in [output] are in reverse order of
      their initial appearance in the list of primitives since it is a stack.

      @raise Arity_mismatch *)
  let write (index, operator) output =
    let operator_arity = Operator.arity operator in
    match List.take_rev_opt operator_arity output with
    | Option.Some (arguments, output) ->
        validate_argument_indices (index, operator) arguments;
        let arguments = List.map Pair.snd arguments in
        let result = Operator.write operator arguments in
        (index, result) :: output
    | Option.None ->
        let operands = List.map Pair.snd output in
        raise (Arity_mismatch { operator; operator_arity; operands })

  (** [validate_left_associative_operator_placement ~x ~px ~y ~py] ensures
      that [x] and [y] are not operators of the same precedence [px] and [py]
      respectively, with [x] being left-associative and [y] being
      right-associative. Otherwise, [x] and [y] are ambiguous in the operator
      stack. *)
  let[@inline] validate_left_associative_operator_placement ~x ~px ~y ~py =
    if Int.(px = py) && is_operator_right_associative x then
      raise
        (Ambiguous_operator_placement
           { left_operator = x; right_operator = y })

  (** [validate_right_associative_operator_placement ~x ~px ~y ~py] ensures
      that [x] and [y] are not operators of the same precedence [px] and [py]
      respectively, with [x] being right-associative and [y] being
      left-associative. Otherwise, [x] and [y] are ambiguous in the operator
      stack. *)
  let[@inline] validate_right_associative_operator_placement ~x ~px ~y ~py =
    if Int.(px = py) && is_operator_left_associative x then
      raise
        (Ambiguous_operator_placement
           { left_operator = x; right_operator = y })

  (** [validate_non_associative_operator_placement ~x ~y] ensures that [x]
      and [y] are not equal non-associative operators. Otherwise, [x] and [y]
      are invalid in the operator stack. *)
  let[@inline] validate_non_associative_operator_placement ~x ~y =
    if Operator.(x = y) then
      raise
        (Consecutive_non_associative_operators
           { left_operator = x; right_operator = y })

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
        let px = Operator.precedence x in
        let py = Operator.precedence y in
        match Operator.associativity y with
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

      @raise Empty_expression
      @raise Arity_mismatch
      @raise Leftover_expressions
      @raise Consecutive_non_associative_operators
      @raise Ambiguous_operator_placement
      @raise Misplaced_operator *)
  let rec shunting_yard operands operators primitives =
    match primitives with
    | (index, Operand operand) :: ps ->
        let operands' = (index, operand) :: operands in
        shunting_yard operands' operators ps
    | (index, Operator operator) :: ps -> (
        match Operator.fixity operator with
        | Fixity.Prefix ->
            (* Writing of [operator] is delayed since its arguments have yet
               to be encountered in [primitives]. *)
            let operators' = (index, operator) :: operators in
            shunting_yard operands operators' ps
        | Fixity.Infix ->
            (* Prepare [operator]'s left argument. *)
            let output, operators' = pop operator operands operators in
            (* Writing of [operator] is delayed since its right argument has
               yet to be encountered in [primitives]. *)
            let operators'' = (index, operator) :: operators' in
            shunting_yard output operators'' ps
        | Fixity.Postfix ->
            (* Prepare [operator]'s left arguments. *)
            let output, operators' = pop operator operands operators in
            (* Immediately write the postfix operator. *)
            let output' = write (index, operator) output in
            shunting_yard output' operators' ps)
    | [] -> (
        let output = pop_all operands operators in
        match List.rev output with
        | [ (_, e) ] -> e
        | e1 :: e2 :: es ->
            let leftover_expressions =
              List2.map Pair.snd (List2.from e1 e2 es)
            in
            raise (Leftover_expressions leftover_expressions)
        | [] -> raise Empty_expression)

  let shunting_yard terms = shunting_yard [] [] (List.index terms)
end
