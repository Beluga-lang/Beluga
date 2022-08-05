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

  exception Misplaced_operator of Operator.t * Operand.t List.t

  exception Consecutive_non_associative_operators of Operator.t * Operator.t

  exception Arity_mismatch of Operator.t * Operand.t List.t

  exception Leftover_expressions of Operand.t List2.t

  type primitive =
    | Operand of Operand.t
    | Operator of Operator.t

  let operand a = Operand a

  let operator op = Operator op

  let validate_argument_indices (i, op) arguments =
    let raise_misplaced_operator_exception () =
      raise @@ Misplaced_operator (op, List.map Pair.snd arguments)
    in
    match Operator.fixity op with
    | Fixity.Prefix ->
      if Bool.not @@ List.for_all (fun (j, _) -> i < j) arguments then
        raise_misplaced_operator_exception ()
    | Fixity.Infix ->
      let [ (left, _); (right, _) ] = arguments in
      if Bool.not (left < i) then raise_misplaced_operator_exception ();
      if Bool.not (i < right) then raise_misplaced_operator_exception ()
    | Fixity.Postfix ->
      if Bool.not @@ List.for_all (fun (j, _) -> j < i) arguments then
        raise_misplaced_operator_exception ()

  let write (index, op) output =
    match List.take_opt (Operator.arity op) output with
    | Option.Some (arguments, output) ->
      validate_argument_indices (index, op) arguments;
      let arguments = List.map Pair.snd arguments in
      let result = Writer.write op arguments in
      (index, result) :: output
    | Option.None ->
      let operands = List.map Pair.snd output in
      raise @@ Arity_mismatch (op, operands)

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
          raise @@ Consecutive_non_associative_operators (y, x)
        else if Int.(Operator.precedence x <= Operator.precedence y) then
          pop x (write (index, y) output) ys
        else (output, stack))
    | [] -> (output, stack)

  let rec pop_all output operators =
    match operators with
    | op :: ops -> pop_all (write op output) ops
    | [] -> output

  let shunting_yard =
    let rec shunting_yard operands operators primitives =
      match primitives with
      | (index, Operand a) :: ps ->
        shunting_yard ((index, a) :: operands) operators ps
      | (index, Operator op) :: ps -> (
        match Operator.fixity op with
        | Fixity.Prefix ->
          shunting_yard operands ((index, op) :: operators) ps
        | Fixity.Infix ->
          let output, operators' = pop op operands operators in
          shunting_yard output ((index, op) :: operators') ps
        | Fixity.Postfix ->
          let output, operators' = pop op operands operators in
          shunting_yard (write (index, op) output) operators' ps)
      | [] -> (
        let output = pop_all operands operators in
        match output with
        | [ (_, e) ] -> e
        | e1 :: e2 :: es ->
          let leftover_expressions =
            List2.map Pair.snd (List2.from e1 e2 es)
          in
          raise @@ Leftover_expressions leftover_expressions
        | [] -> raise Empty_expression)
    in
    fun terms -> shunting_yard [] [] (List.index terms)
end
