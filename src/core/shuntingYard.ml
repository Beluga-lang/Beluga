open Support

module List : sig
  include module type of List

  (** [take_opt k \[x1; x2; ...; xn\]] is
      [Option.Some (\[xk; x(k-1); ...; x1\], \[x(k+1); x(k+2); ...; xn\])] if
      [0 <= k <= n], and [Option.None] otherwise.

      This implementation avoids an extraneous list reversal in the shunting
      yard algorithm.

      @raise Invalid_argument if [k < 0]. *)
  val take_opt : int -> 'a list -> ('a list * 'a list) option
end = struct
  include List

  let take_opt =
    let rec take_opt k l acc =
      if k = 0 then Option.some (acc, l)
      else
        match l with
        | x :: xs -> take_opt (k - 1) xs (x :: acc)
        | [] -> Option.none
    in
    fun k l ->
      if k < 0 then raise @@ Invalid_argument "ShuntingYard.List.take_opt"
      else take_opt k l []
end

module Make (Operand : sig
  type t
end) (Operator : sig
  type t

  (** {1 Destructors} *)

  val arity : t -> Int.t

  val precedence : t -> Int.t

  val fixity : t -> Fixity.t

  val associativity : t -> Associativity.t

  (** {1 Instances} *)

  include Eq.EQ with type t := t
end) (Writer : sig
  val write : Operator.t -> Operand.t List.t -> Operand.t
end) =
struct
  exception Empty_expression

  exception
    Misplaced_operator of
      { operator : Operator.t
      ; operands : Operand.t List.t
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

  let operand a = Operand a

  let operator op = Operator op

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
  let validate_argument_indices (i, operator) arguments =
    let raise_misplaced_operator_exception () =
      let operands = List.map Pair.snd arguments in
      raise @@ Misplaced_operator { operator; operands }
    in
    match Operator.fixity operator with
    | Fixity.Prefix ->
      if Bool.not @@ List.for_all (fun (j, _) -> i < j) arguments then
        raise_misplaced_operator_exception ()
    | Fixity.Infix ->
      let[@warning "-8"] [ (left, _); (right, _) ] = arguments in
      if Bool.not (left < i) then raise_misplaced_operator_exception ();
      if Bool.not (i < right) then raise_misplaced_operator_exception ()
    | Fixity.Postfix ->
      if Bool.not @@ List.for_all (fun (j, _) -> j < i) arguments then
        raise_misplaced_operator_exception ()

  (** [write operator output] writes [operator] onto [output] by taking
      arguments from [output]. Operands in [output] are in reverse order of
      their initial appearance in the list of primitives since it is a stack.

      @raise Arity_mismatch *)
  let write (index, operator) output =
    let operator_arity = Operator.arity operator in
    match List.take_opt operator_arity output with
    | Option.Some (arguments, output) ->
      validate_argument_indices (index, operator) arguments;
      let arguments = List.map Pair.snd arguments in
      let result = Writer.write operator arguments in
      (index, result) :: output
    | Option.None ->
      let operands = List.map Pair.snd output in
      raise @@ Arity_mismatch { operator; operator_arity; operands }

  (** [pop x output stack] pops the operator stack [stack] as needed with
      respect to [x] and [output] to ensure that writing [x] respects the
      precedence and associativity of operators in [stack].

      @raise Consecutive_non_associative_operators *)
  let rec pop x output stack =
    match stack with
    | (index, y) :: ys -> (
      match Operator.associativity x with
      | Associativity.Left_associative ->
        if Int.(Operator.precedence x <= Operator.precedence y) then
          pop x (write (index, y) output) ys
        else (output, stack)
      | Associativity.Right_associative ->
        if Int.(Operator.precedence x < Operator.precedence y) then
          pop x (write (index, y) output) ys
        else (output, stack)
      | Associativity.Non_associative ->
        if Operator.(x = y) then
          raise
          @@ Consecutive_non_associative_operators
               { left_operator = y; right_operator = x }
        else if Int.(Operator.precedence x <= Operator.precedence y) then
          pop x (write (index, y) output) ys
        else (output, stack))
    | [] -> (output, stack)

  let rec pop_all output operators =
    match operators with
    | op :: ops -> pop_all (write op output) ops
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
      @raise Misplaced_operator *)
  let rec shunting_yard operands operators primitives =
    match primitives with
    | (index, Operand operand) :: ps ->
      let operands' = (index, operand) :: operands in
      shunting_yard operands' operators ps
    | (index, Operator operator) :: ps -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        (* Writing of [operator] is delayed since its arguments have yet to
           be encountered in [primitives]. *)
        let operators' = (index, operator) :: operators in
        shunting_yard operands operators' ps
      | Fixity.Infix ->
        (* Prepare [operator]'s left argument. *)
        let output, operators' = pop operator operands operators in
        (* Writing of [operator] is delayed since its right argument has yet
           to be encountered in [primitives]. *)
        let operators'' = (index, operator) :: operators' in
        shunting_yard output operators'' ps
      | Fixity.Postfix ->
        (* Prepare [operator]'s left arguments. *)
        let output, operators' = pop operator operands operators in
        (* Immediatly write the postfix operator. *)
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
        raise @@ Leftover_expressions leftover_expressions
      | [] -> raise Empty_expression)

  let shunting_yard terms = shunting_yard [] [] (List.index terms)
end
