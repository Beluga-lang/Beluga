open Support
open Beluga

module Operand = struct
  type t =
    | Number of Int.t
    | Addition of
        { left_operand : t
        ; right_operand : t
        }
    | Subtraction of
        { left_operand : t
        ; right_operand : t
        }
    | Multiplication of
        { left_operand : t
        ; right_operand : t
        }
    | Division of
        { left_operand : t
        ; right_operand : t
        }
    | Minus of { operand : t }
    | Factorial of { operand : t }
    | Exponentiation of
        { base : t
        ; power : t
        }
    | Less_than of
        { left_operand : t
        ; right_operand : t
        }
    | Postfix2 of
        { left_operand : t
        ; right_operand : t
        }
end

module Operator = struct
  type t =
    | Addition
    | Subtraction
    | Multiplication
    | Division
    | Minus
    | Exponent
    | Factorial
    | Less_than
    | Postfix2

  let arity operator =
    match operator with
    | Addition
    | Subtraction
    | Multiplication
    | Division
    | Exponent
    | Less_than
    | Postfix2 -> 2
    | Minus | Factorial -> 1

  let precedence operator =
    match operator with
    | Factorial | Exponent -> 5
    | Minus -> 4
    | Multiplication | Division -> 3
    | Postfix2 -> 2
    | Addition | Subtraction -> 1
    | Less_than -> 0

  let fixity operator =
    match operator with
    | Minus -> Fixity.prefix
    | Addition
    | Subtraction
    | Multiplication
    | Division
    | Exponent
    | Less_than -> Fixity.infix
    | Factorial | Postfix2 -> Fixity.postfix

  let associativity operator =
    match operator with
    | Addition
    | Subtraction
    | Factorial
    | Postfix2
    | Multiplication
    | Division -> Associativity.left_associative
    | Minus | Exponent -> Associativity.right_associative
    | Less_than -> Associativity.non_associative

  include (
    Eq.Make (struct
      type nonrec t = t

      let equal = Stdlib.( = )
    end) :
      Eq.EQ with type t := t)
end

module Writer = struct
  let write operator operands =
    match (operator, operands) with
    | Operator.Addition, [ left_operand; right_operand ] ->
      Operand.Addition { left_operand; right_operand }
    | Operator.Subtraction, [ left_operand; right_operand ] ->
      Operand.Subtraction { left_operand; right_operand }
    | Operator.Multiplication, [ left_operand; right_operand ] ->
      Operand.Multiplication { left_operand; right_operand }
    | Operator.Division, [ left_operand; right_operand ] ->
      Operand.Division { left_operand; right_operand }
    | Operator.Factorial, [ operand ] -> Operand.Factorial { operand }
    | Operator.Minus, [ operand ] -> Operand.Minus { operand }
    | Operator.Exponent, [ base; power ] ->
      Operand.Exponentiation { base; power }
    | Operator.Less_than, [ left_operand; right_operand ] ->
      Operand.Less_than { left_operand; right_operand }
    | Operator.Postfix2, [ left_operand; right_operand ] ->
      Operand.Postfix2 { left_operand; right_operand }
    | _ -> raise @@ Invalid_argument "Unexpected write failure"
end

module ShuntingYard = ShuntingYard.Make (Operand) (Operator) (Writer)

module Primitive_constructors = struct
  let n' i = ShuntingYard.operand @@ Operand.Number i

  let ( + ) = ShuntingYard.operator @@ Operator.Addition

  let ( - ) = ShuntingYard.operator @@ Operator.Subtraction

  let ( * ) = ShuntingYard.operator @@ Operator.Multiplication

  let ( / ) = ShuntingYard.operator @@ Operator.Division

  let ( ~- ) = ShuntingYard.operator @@ Operator.Minus

  let ( ** ) = ShuntingYard.operator @@ Operator.Exponent

  let ( ! ) = ShuntingYard.operator @@ Operator.Factorial

  let ( < ) = ShuntingYard.operator @@ Operator.Less_than

  let p2 = ShuntingYard.operator @@ Operator.Postfix2
end

module Operand_constructors = struct
  let n i = Operand.Number i

  let add left_operand right_operand =
    Operand.Addition { left_operand; right_operand }

  let sub left_operand right_operand =
    Operand.Subtraction { left_operand; right_operand }

  let mul left_operand right_operand =
    Operand.Multiplication { left_operand; right_operand }

  let div left_operand right_operand =
    Operand.Division { left_operand; right_operand }

  let minus operand = Operand.Minus { operand }

  let exp base power = Operand.Exponentiation { base; power }

  let fact operand = Operand.Factorial { operand }

  let lt left_operand right_operand =
    Operand.Less_than { left_operand; right_operand }

  let p2' left_operand right_operand =
    Operand.Postfix2 { left_operand; right_operand }
end

let assert_raises_empty_expression f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [ShuntingYard.Empty_expression] to be raised"
  with ShuntingYard.Empty_expression -> ()

let assert_raises_misplaced_operator f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [ShuntingYard.Misplaced_operator] to be raised"
  with ShuntingYard.Misplaced_operator _ -> ()

let assert_raises_consecutive_non_associative_operators f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception \
       [ShuntingYard.Consecutive_non_associative_operators] to be raised"
  with ShuntingYard.Consecutive_non_associative_operators _ -> ()

let assert_raises_arity_mismatch f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [ShuntingYard.Arity_mismatch] to be raised"
  with ShuntingYard.Arity_mismatch _ -> ()

let assert_raises_leftover_expressions f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [ShuntingYard.Leftover_expressions] to be raised"
  with ShuntingYard.Leftover_expressions _ -> ()

let test_shunting_yard =
  let test_success input expected _test_ctxt =
    OUnit2.assert_equal expected (ShuntingYard.shunting_yard input)
  in
  let success_test_cases =
    let open Primitive_constructors in
    let open Operand_constructors in
    [ ([ n' 1 ], n 1)
    ; ([ n' 1; ( + ); n' 2 ], add (n 1) (n 2))
    ; ([ n' 1; ( * ); n' 2 ], mul (n 1) (n 2))
    ; ([ n' 1; ( * ); ( ~- ); n' 2 ], mul (n 1) (minus (n 2)))
    ; ([ n' 1; ( * ); ( ~- ); ( ~- ); n' 2 ], mul (n 1) (minus (minus (n 2))))
    ; ([ ( ~- ); n' 1; ( * ); n' 2 ], mul (minus (n 1)) (n 2))
    ; ([ n' 1; ( * ); n' 2; ( * ); n' 3 ], mul (mul (n 1) (n 2)) (n 3))
    ; ([ n' 1; ( ! ) ], fact (n 1))
    ; ([ n' 1; ( + ); n' 2; ( * ); n' 3 ], add (n 1) (mul (n 2) (n 3)))
    ; ([ n' 1; ( + ); n' 2; ( < ); n' 3 ], lt (add (n 1) (n 2)) (n 3))
    ; ([ n' 1; ( / ); n' 2; ( - ); n' 3 ], sub (div (n 1) (n 2)) (n 3))
    ; ( [ n' 1; ( + ); n' 2; ( ! ); ( * ); n' 3 ]
      , add (n 1) (mul (fact (n 2)) (n 3)) )
    ; ([ ( ~- ); n' 2; ( ** ); n' 3 ], minus (exp (n 2) (n 3)))
    ; ([ n' 1; ( * ); n' 2; ( ** ); n' 3 ], mul (n 1) (exp (n 2) (n 3)))
    ; ([ n' 1; n' 2; p2 ], p2' (n 1) (n 2))
    ; ([ n' 1; n' 2; ( * ); n' 3; p2 ], p2' (n 1) (mul (n 2) (n 3)))
    ; ( [ n' 0; ( + ); n' 1; n' 2; ( * ); n' 3; p2 ]
      , add (n 0) (p2' (n 1) (mul (n 2) (n 3))) )
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (input, expected) ->
           OUnit2.test_case @@ test_success input expected)
  in
  let failure_empty_expression_test =
    OUnit2.test_case (fun _test_ctxt ->
        assert_raises_empty_expression (fun () ->
            ShuntingYard.shunting_yard []))
  in
  let test_failure_misplaced_operator input _test_ctxt =
    assert_raises_misplaced_operator (fun () ->
        ShuntingYard.shunting_yard input)
  in
  let failure_misplaced_operator_test_cases =
    let open Primitive_constructors in
    [ [ n' 1; n' 2; ( + ); ( + ); n' 3 ]
    ; [ n' 1; ( + ); n' 2; ( / ); ( - ); n' 3 ]
    ]
  in
  let failure_misplaced_operator_tests =
    failure_misplaced_operator_test_cases
    |> List.map (fun input ->
           OUnit2.test_case @@ test_failure_misplaced_operator input)
  in
  let test_failure_consecutive_non_associative_operators input _test_ctxt =
    assert_raises_consecutive_non_associative_operators (fun () ->
        ShuntingYard.shunting_yard input)
  in
  let failure_consecutive_non_associative_operators_test_cases =
    let open Primitive_constructors in
    [ [ n' 1; ( < ); n' 2; ( < ); n' 3 ]
    ; [ n' 1; ( < ); n' 2; ( + ); n' 3; ( < ); n' 4 ]
    ; [ n' 1; ( < ); n' 2; ( + ); n' 3; ( * ); n' 4; ( < ); n' 5 ]
    ]
  in
  let failure_consecutive_non_associative_operators_tests =
    failure_consecutive_non_associative_operators_test_cases
    |> List.map (fun input ->
           OUnit2.test_case
           @@ test_failure_consecutive_non_associative_operators input)
  in
  let test_failure_arity_mismatch input _test_ctxt =
    assert_raises_arity_mismatch (fun () -> ShuntingYard.shunting_yard input)
  in
  let failure_arity_mismatch_test_cases =
    let open Primitive_constructors in
    [ [ n' 1; ( + ) ]
    ; [ ( + ); n' 1 ]
    ; [ ( ! ) ]
    ; [ n' 1; ( / ); n' 2; ( + ) ]
    ]
  in
  let failure_arity_mismatch_tests =
    failure_arity_mismatch_test_cases
    |> List.map (fun input ->
           OUnit2.test_case @@ test_failure_arity_mismatch input)
  in
  let failure_leftover_expressions_test =
    OUnit2.test_case (fun _test_ctxt ->
        assert_raises_leftover_expressions (fun () ->
            let open Primitive_constructors in
            ShuntingYard.shunting_yard [ n' 1; n' 2 ]))
  in
  let open OUnit2 in
  [ "success" >::: success_tests
  ; "failure_empty_expression" >::: [ failure_empty_expression_test ]
  ; "failure_arity_mismatch" >::: failure_arity_mismatch_tests
  ; "failure_consecutive_non_associative_operators"
    >::: failure_consecutive_non_associative_operators_tests
  ; "failure_misplaced_operator" >::: failure_misplaced_operator_tests
  ; "failure_leftover_expressions" >::: [ failure_leftover_expressions_test ]
  ]

let tests =
  let open OUnit2 in
  "ShuntingYard" >::: [ "shunting_yard" >::: test_shunting_yard ]
