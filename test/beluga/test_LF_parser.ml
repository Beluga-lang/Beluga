open Support
open Beluga

module Synprs_to_synext' = struct
  module Disambiguation_state = Synprs_to_synext'.Disambiguation_state
  module LF = Synprs_to_synext'.LF (Disambiguation_state)
end

let parse_lf_object input =
  Runparser.parse_string Location.ghost input (Parser.only Parser.lf_object)
  |> Parser.extract

let assert_raises_illegal_identifier_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_identifier_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_identifier_kind _ -> ()

let assert_raises_illegal_qualified_identifier_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_qualified_identifier_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_qualified_identifier_kind _ -> ()

let assert_raises_illegal_backward_arrow_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_backward_arrow_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_backward_arrow_kind _ -> ()

let assert_raises_illegal_hole_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_hole_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_hole_kind _ -> ()

let assert_raises_illegal_lambda_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_lambda_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_lambda_kind _ -> ()

let assert_raises_illegal_annotated_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_annotated_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_annotated_kind _ -> ()

let assert_raises_illegal_application_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_application_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_application_kind _ -> ()

let assert_raises_illegal_untyped_pi_kind f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_untyped_pi_kind _] to be raised"
  with Synprs_to_synext'.LF.Illegal_untyped_pi_kind _ -> ()

let assert_raises_illegal_type_kind_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_type_kind_type _] to be raised"
  with Synprs_to_synext'.LF.Illegal_type_kind_type _ -> ()

let assert_raises_illegal_hole_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_hole_type _] to be raised"
  with Synprs_to_synext'.LF.Illegal_hole_type _ -> ()

let assert_raises_illegal_lambda_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_lambda_type _] to be raised"
  with Synprs_to_synext'.LF.Illegal_lambda_type _ -> ()

let assert_raises_illegal_annotated_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_annotated_type _] to be raised"
  with Synprs_to_synext'.LF.Illegal_annotated_type _ -> ()

let assert_raises_illegal_untyped_pi_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_untyped_pi_type _] to be raised"
  with Synprs_to_synext'.LF.Illegal_untyped_pi_type _ -> ()

let assert_raises_unbound_type_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Unbound_type_constant _] to be raised"
  with Synprs_to_synext'.LF.Unbound_type_constant _ -> ()

let assert_raises_illegal_type_kind_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_type_kind_term _] to be raised"
  with Synprs_to_synext'.LF.Illegal_type_kind_term _ -> ()

let assert_raises_illegal_pi_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_pi_term _] to be raised"
  with Synprs_to_synext'.LF.Illegal_pi_term _ -> ()

let assert_raises_illegal_forward_arrow_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_forward_arrow_term _] to be raised"
  with Synprs_to_synext'.LF.Illegal_forward_arrow_term _ -> ()

let assert_raises_illegal_backward_arrow_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_backward_arrow_term _] to be raised"
  with Synprs_to_synext'.LF.Illegal_backward_arrow_term _ -> ()

let assert_raises_unbound_term_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Unbound_term_constant _] to be raised"
  with Synprs_to_synext'.LF.Unbound_term_constant _ -> ()

let assert_raises_expected_term_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Expected_term_constant _] to be raised"
  with Synprs_to_synext'.LF.Expected_term_constant _ -> ()

let assert_raises_expected_type_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Expected_type_constant _] to be raised"
  with Synprs_to_synext'.LF.Expected_type_constant _ -> ()

let assert_raises_expected_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure "Expected exception [Expected_term _] to be raised"
  with Synprs_to_synext'.LF.Expected_term _ -> ()

let assert_raises_expected_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure "Expected exception [Expected_type _] to be raised"
  with Synprs_to_synext'.LF.Expected_type _ -> ()

let assert_raises_misplaced_operator f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Misplaced_operator _] to be raised"
  with Synprs_to_synext'.LF.Misplaced_operator _ -> ()

let assert_raises_consecutive_non_associative_operators f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Consecutive_non_associative_operators _] to be \
       raised"
  with Synprs_to_synext'.LF.Consecutive_non_associative_operators _ -> ()

let assert_raises_arity_mismatch f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Arity_mismatch _] to be raised"
  with Synprs_to_synext'.LF.Arity_mismatch _ -> ()

let mock_state_1 = Synprs_to_synext'.Disambiguation_state.empty

let mock_state_2 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (id "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "sum/s")

let mock_state_3 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_module
       (empty
       |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "nat")
       |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "z")
       |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "s")
       |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (id "sum")
       |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "sum/z")
       |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "sum/s")
       |> get_bindings)
       (id "Nat")

let mock_state_4 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_module
       (empty
       |> add_module
            (empty
            |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "nat")
            |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "z")
            |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "s")
            |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (id "sum")
            |> add_prefix_lf_term_constant ~arity:0 ~precedence:1
                 (id "sum/z")
            |> add_prefix_lf_term_constant ~arity:1 ~precedence:1
                 (id "sum/s")
            |> get_bindings)
            (id "Nat")
       |> get_bindings)
       (id "Util")

let mock_state_5 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "tp")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "bool")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "nat")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:2 (id "arrow")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (id "term")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:3 (id "has_type")

let mock_state_6 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "exp")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:3
       (id "app")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "lam")
  |> add_infix_lf_type_constant ~associativity:Associativity.left_associative
       ~precedence:1 (id "eq")

let mock_state_7 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_module
       (empty
       |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "tp")
       |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (id "bool")
       |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "nat")
       |> add_infix_lf_term_constant
            ~associativity:Associativity.left_associative ~precedence:2
            (id "arrow")
       |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (id "term")
       |> get_bindings)
       (id "Statics")

let mock_state_8 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_infix_lf_type_constant
       ~associativity:Associativity.right_associative ~precedence:1
       (id "msteps")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "lam")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (id "term")

let mock_state_9 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "tp")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (id "target")

let mock_state_10 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "a")
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "b")
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "c")

let test_kind =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.LF.of_kind >> Synext'_json.without_locations
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:Synext'_eq.LF.kind_equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.disambiguate_as_kind elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_lf_object input
    |> Synprs_to_synext'.LF.disambiguate_as_kind elaboration_context
  in
  let success_test_cases =
    let open Synext'_constructors.LF in
    [ (mock_state_1, "type", typ)
    ; (mock_state_2, "nat -> nat -> type", t_c "nat" ==> (t_c "nat" ==> typ))
    ; ( mock_state_2
      , "nat -> (nat -> type)"
      , t_c "nat" ==> (t_c "nat" ==> typ) )
    ; ( mock_state_2
      , "nat -> nat -> nat -> type"
      , t_c "nat" ==> (t_c "nat" ==> (t_c "nat" ==> typ)) )
    ; (mock_state_2, "(nat -> nat) -> type", t_c "nat" => t_c "nat" ==> typ)
    ; ( mock_state_3
      , "Nat.nat -> Nat.nat -> type"
      , t_c ~m:[ "Nat" ] "nat" ==> (t_c ~m:[ "Nat" ] "nat" ==> typ) )
    ; ( mock_state_4
      , "Util.Nat.nat -> Util.Nat.nat -> type"
      , t_c ~m:[ "Util"; "Nat" ] "nat"
        ==> (t_c ~m:[ "Util"; "Nat" ] "nat" ==> typ) )
    ; ( mock_state_8
      , "({ x : term } (M x) msteps (M' x)) -> (lam M) msteps (lam M') -> \
         type"
      , t_pi ~x:"x" ~t:(t_c "term")
          (t_app (t_c "msteps")
             [ app (v "M") [ v "x" ]; app (v "M'") [ v "x" ] ])
        ==> (t_app (t_c "msteps")
               [ app (c "lam") [ v "M" ]; app (c "lam") [ v "M'" ] ]
            ==> typ) )
    ; ( mock_state_9
      , "{ Lf : tp } target Lf -> type"
      , k_pi ~x:"Lf" ~t:(t_c "tp") (t_app (t_c "target") [ v "Lf" ] ==> typ)
      )
    ; ( mock_state_9
      , "{ Lf : tp } { _ : tp } target Lf -> type"
      , k_pi ~x:"Lf" ~t:(t_c "tp")
          (k_pi ~t:(t_c "tp") (t_app (t_c "target") [ v "Lf" ] ==> typ)) )
    ]
  and failure_test_cases =
    [ (mock_state_1, "M", assert_raises_illegal_identifier_kind)
    ; (mock_state_1, "Q.M", assert_raises_illegal_qualified_identifier_kind)
    ; (mock_state_2, "type <- nat", assert_raises_illegal_backward_arrow_kind)
    ; (mock_state_1, "_", assert_raises_illegal_hole_kind)
    ; (mock_state_1, "(\\x. _)", assert_raises_illegal_lambda_kind)
    ; (mock_state_2, "type : _", assert_raises_illegal_annotated_kind)
    ; (mock_state_2, "nat _", assert_raises_illegal_application_kind)
    ; ( mock_state_9
      , "{ Lf } target Lf -> type"
      , assert_raises_illegal_untyped_pi_kind )
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           let open OUnit2 in
           input >:: test_success elaboration_context input expected)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (elaboration_context, input, assert_exn) ->
           let open OUnit2 in
           input >:: test_failure elaboration_context input assert_exn)
  in
  let open OUnit2 in
  [ "success" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let test_type =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.LF.of_typ >> Synext'_json.without_locations
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:Synext'_eq.LF.typ_equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.disambiguate_as_typ elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_lf_object input
    |> Synprs_to_synext'.LF.disambiguate_as_typ elaboration_context
  in
  let success_test_cases =
    let open Synext'_constructors.LF in
    [ (mock_state_2, "nat -> nat", t_c "nat" => t_c "nat")
    ; ( mock_state_2
      , "nat -> nat -> nat"
      , t_c "nat" => (t_c "nat" => t_c "nat") )
    ; ( mock_state_2
      , "(nat -> nat) -> nat"
      , t_c "nat" => t_c "nat" => t_c "nat" )
    ; (mock_state_2, "nat <- nat <- nat", t_c "nat" <= t_c "nat" <= t_c "nat")
    ; ( mock_state_2
      , "nat <- nat <- nat <- nat"
      , t_c "nat" <= t_c "nat" <= t_c "nat" <= t_c "nat" )
    ; ( mock_state_2
      , "sum (s z) (s (s z)) (s (s (s z)))"
      , t_app (t_c "sum")
          [ app (c "s") [ c "z" ]
          ; app (c "s") [ app (c "s") [ c "z" ] ]
          ; app (c "s") [ app (c "s") [ app (c "s") [ c "z" ] ] ]
          ] )
    ; (mock_state_10, "a -> b -> c", t_c "a" => (t_c "b" => t_c "c"))
    ; (mock_state_10, "(a -> b) -> c", t_c "a" => t_c "b" => t_c "c")
    ; (mock_state_10, "a <- b <- c", t_c "a" <= t_c "b" <= t_c "c")
    ; (mock_state_10, "a <- (b <- c)", t_c "a" <= (t_c "b" <= t_c "c"))
    ; (mock_state_10, "(a <- b) -> c", t_c "a" <= t_c "b" => t_c "c")
    ; (mock_state_10, "a <- (b -> c)", t_c "a" <= (t_c "b" => t_c "c"))
    ; (mock_state_10, "a -> (b <- c)", t_c "a" => (t_c "b" <= t_c "c"))
    ; (mock_state_10, "a <- (b -> c)", t_c "a" <= (t_c "b" => t_c "c"))
    ; ( mock_state_2
      , "nat <- (nat -> nat)"
      , t_c "nat" <= (t_c "nat" => t_c "nat") )
    ; ( mock_state_2
      , "nat <- (nat <- nat)"
      , t_c "nat" <= (t_c "nat" <= t_c "nat") )
    ; ( mock_state_2
      , "nat -> (nat <- nat) -> nat"
      , t_c "nat" => (t_c "nat" <= t_c "nat" => t_c "nat") )
    ; ( mock_state_2
      , "{ x : nat } sum x x x"
      , t_pi ~x:"x" ~t:(t_c "nat")
          (t_app (t_c "sum") [ v "x"; v "x"; v "x" ]) )
    ; ( mock_state_2
      , "{ x : nat } { y : nat } sum x y y"
      , t_pi ~x:"x" ~t:(t_c "nat")
          (t_pi ~x:"y" ~t:(t_c "nat")
             (t_app (t_c "sum") [ v "x"; v "y"; v "y" ])) )
    ; ( mock_state_2
      , "{ x : nat } { y : nat } { z : nat } sum x y z"
      , t_pi ~x:"x" ~t:(t_c "nat")
          (t_pi ~x:"y" ~t:(t_c "nat")
             (t_pi ~x:"z" ~t:(t_c "nat")
                (t_app (t_c "sum") [ v "x"; v "y"; v "z" ]))) )
    ; ( mock_state_5
      , "(term T -> term T') -> term (T arrow T')"
      , t_app (t_c "term") [ v "T" ]
        => t_app (t_c "term") [ v "T'" ]
        => t_app (t_c "term") [ app (c "arrow") [ v "T"; v "T'" ] ] )
    ; ( mock_state_5
      , "term (T arrow T') -> term T -> term T'"
      , t_app (t_c "term") [ app (c "arrow") [ v "T"; v "T'" ] ]
        => (t_app (t_c "term") [ v "T" ] => t_app (t_c "term") [ v "T'" ]) )
    ; ( mock_state_5
      , "(term T -> term T') -> term ((arrow) T T')"
      , t_app (t_c "term") [ v "T" ]
        => t_app (t_c "term") [ v "T'" ]
        => t_app (t_c "term")
             [ app (c ~quoted:true "arrow") [ v "T"; v "T'" ] ] )
    ; ( mock_state_5
      , "(term T -> term T') -> term (((arrow)) T T')"
      , t_app (t_c "term") [ v "T" ]
        => t_app (t_c "term") [ v "T'" ]
        => t_app (t_c "term")
             [ app (c ~quoted:true "arrow") [ v "T"; v "T'" ] ] )
    ; ( mock_state_5
      , "(term T -> term T') -> term ((((arrow))) T T')"
      , t_app (t_c "term") [ v "T" ]
        => t_app (t_c "term") [ v "T'" ]
        => t_app (t_c "term")
             [ app (c ~quoted:true "arrow") [ v "T"; v "T'" ] ] )
    ; ( mock_state_5
      , "term \\x. T x"
      , t_app (t_c "term") [ lam ~x:"x" (app (v "T") [ v "x" ]) ] )
    ; ( mock_state_5
      , "term ((arrow) T T') -> term T -> term T'"
      , t_app (t_c "term") [ app (c ~quoted:true "arrow") [ v "T"; v "T'" ] ]
        => (t_app (t_c "term") [ v "T" ] => t_app (t_c "term") [ v "T'" ]) )
    ; ( mock_state_6
      , "E1 eq F1 -> E2 eq F2 -> (E1 app E2) eq (F1 app F2)"
      , t_app (t_c "eq") [ v "E1"; v "F1" ]
        => (t_app (t_c "eq") [ v "E2"; v "F2" ]
           => t_app (t_c "eq")
                [ app (c "app") [ v "E1"; v "E2" ]
                ; app (c "app") [ v "F1"; v "F2" ]
                ]) )
    ; ( mock_state_6
      , "(eq) E1 F1 -> (eq) E2 F2 -> (eq) ((app) E1 E2) ((app) F1 F2)"
      , t_app (t_c ~quoted:true "eq") [ v "E1"; v "F1" ]
        => (t_app (t_c ~quoted:true "eq") [ v "E2"; v "F2" ]
           => t_app (t_c ~quoted:true "eq")
                [ app (c ~quoted:true "app") [ v "E1"; v "E2" ]
                ; app (c ~quoted:true "app") [ v "F1"; v "F2" ]
                ]) )
    ; ( mock_state_6
      , "{ _ : exp } _ eq _"
      , t_pi ~t:(t_c "exp") (t_app (t_c "eq") [ hole; hole ]) )
    ; ( mock_state_6
      , "({x : exp} x eq x -> (E x) eq (F x)) -> (lam (\\x. E x)) eq (lam \
         (\\x. F x))"
      , t_pi ~x:"x" ~t:(t_c "exp")
          (t_app (t_c "eq") [ v "x"; v "x" ]
          => t_app (t_c "eq")
               [ app (v "E") [ v "x" ]; app (v "F") [ v "x" ] ])
        => t_app (t_c "eq")
             [ app (c "lam") [ lam ~x:"x" (app (v "E") [ v "x" ]) ]
             ; app (c "lam") [ lam ~x:"x" (app (v "F") [ v "x" ]) ]
             ] )
    ; ( mock_state_6
      , "({x : exp} (eq) x x -> (eq) (E x) (F x)) -> (eq) (lam (\\x. E x)) \
         (lam (\\x. F x))"
      , t_pi ~x:"x" ~t:(t_c "exp")
          (t_app (t_c ~quoted:true "eq") [ v "x"; v "x" ]
          => t_app (t_c ~quoted:true "eq")
               [ app (v "E") [ v "x" ]; app (v "F") [ v "x" ] ])
        => t_app (t_c ~quoted:true "eq")
             [ app (c "lam") [ lam ~x:"x" (app (v "E") [ v "x" ]) ]
             ; app (c "lam") [ lam ~x:"x" (app (v "F") [ v "x" ]) ]
             ] )
    ; ( mock_state_6
      , "({x : exp} (eq) x x -> (eq) (E x) (F x)) -> (eq) (lam (\\x. (E) \
         x)) (lam (\\x. (F) x))"
      , t_pi ~x:"x" ~t:(t_c "exp")
          (t_app (t_c ~quoted:true "eq") [ v "x"; v "x" ]
          => t_app (t_c ~quoted:true "eq")
               [ app (v "E") [ v "x" ]; app (v "F") [ v "x" ] ])
        => t_app (t_c ~quoted:true "eq")
             [ app (c "lam") [ lam ~x:"x" (app (v "E") [ v "x" ]) ]
             ; app (c "lam") [ lam ~x:"x" (app (v "F") [ v "x" ]) ]
             ] )
    ; ( mock_state_7
      , "(Statics.term T -> Statics.term T') -> Statics.term (T \
         Statics.arrow T')"
      , t_app (t_c ~m:[ "Statics" ] "term") [ v "T" ]
        => t_app (t_c ~m:[ "Statics" ] "term") [ v "T'" ]
        => t_app
             (t_c ~m:[ "Statics" ] "term")
             [ app (c ~m:[ "Statics" ] "arrow") [ v "T"; v "T'" ] ] )
    ; ( mock_state_7
      , "(Statics.term T -> Statics.term T') -> Statics.term \
         ((Statics.arrow) T T')"
      , t_app (t_c ~m:[ "Statics" ] "term") [ v "T" ]
        => t_app (t_c ~m:[ "Statics" ] "term") [ v "T'" ]
        => t_app
             (t_c ~m:[ "Statics" ] "term")
             [ app
                 (c ~quoted:true ~m:[ "Statics" ] "arrow")
                 [ v "T"; v "T'" ]
             ] )
    ]
  and failure_test_cases =
    [ (mock_state_1, "type", assert_raises_illegal_type_kind_type)
    ; (mock_state_1, "_", assert_raises_illegal_hole_type)
    ; (mock_state_1, "\\x. _", assert_raises_illegal_lambda_type)
    ; (mock_state_2, "nat : type", assert_raises_illegal_annotated_type)
    ; (mock_state_6, "{ x } x eq x", assert_raises_illegal_untyped_pi_type)
    ; (mock_state_1, "z", assert_raises_unbound_type_constant)
    ; (mock_state_3, "Nat.add", assert_raises_unbound_type_constant)
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           let open OUnit2 in
           input >:: test_success elaboration_context input expected)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (elaboration_context, input, assert_exn) ->
           let open OUnit2 in
           input >:: test_failure elaboration_context input assert_exn)
  in
  let open OUnit2 in
  [ "success" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let test_term =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.LF.of_term >> Synext'_json.without_locations
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:Synext'_eq.LF.term_equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.disambiguate_as_term elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_lf_object input
    |> Synprs_to_synext'.LF.disambiguate_as_term elaboration_context
  in
  let success_test_cases =
    let open Synext'_constructors.LF in
    [ (mock_state_1, "M x y z", app (v "M") [ v "x"; v "y"; v "z" ])
    ; (mock_state_1, "_ x y z", app hole [ v "x"; v "y"; v "z" ])
    ; (mock_state_1, "M _ y z", app (v "M") [ hole; v "y"; v "z" ])
    ; (mock_state_1, "M x _ z", app (v "M") [ v "x"; hole; v "z" ])
    ; (mock_state_1, "M x y _", app (v "M") [ v "x"; v "y"; hole ])
    ; (mock_state_1, "M _ y _", app (v "M") [ hole; v "y"; hole ])
    ; (mock_state_1, "M _ _ _", app (v "M") [ hole; hole; hole ])
    ; (mock_state_1, "\\x. x", lam ~x:"x" (v "x"))
    ; (mock_state_1, "\\x. M x", lam ~x:"x" (app (v "M") [ v "x" ]))
    ; ( mock_state_1
      , "\\x. \\y. \\z. M x y z"
      , lam ~x:"x"
          (lam ~x:"y" (lam ~x:"z" (app (v "M") [ v "x"; v "y"; v "z" ]))) )
    ; (mock_state_2, "z", c "z")
    ; (mock_state_2, "z : nat", c "z" &: t_c "nat")
    ; (mock_state_2, "\\x. s x", lam ~x:"x" (app (c "s") [ v "x" ]))
    ; ( mock_state_2
      , "\\x. \\_. s x"
      , lam ~x:"x" (lam (app (c "s") [ v "x" ])) )
    ; ( mock_state_2
      , "\\x:nat. s x"
      , lam ~x:"x" ~t:(t_c "nat") (app (c "s") [ v "x" ]) )
    ; ( mock_state_2
      , "\\x. s (x : nat)"
      , lam ~x:"x" (app (c "s") [ v "x" &: t_c "nat" ]) )
    ; ( mock_state_2
      , "\\x. s x : nat"
      , lam ~x:"x" (app (c "s") [ v "x" ] &: t_c "nat") )
    ; (mock_state_2, "(x : nat) : nat", v "x" &: t_c "nat" &: t_c "nat")
    ; (mock_state_2, "x : nat : nat", v "x" &: t_c "nat" &: t_c "nat")
    ; ( mock_state_2
      , "(\\x. s x) : nat -> nat"
      , lam ~x:"x" (app (c "s") [ v "x" ]) &: (t_c "nat" => t_c "nat") )
    ; (mock_state_2, "s z", app (c "s") [ c "z" ])
    ; ( mock_state_5
      , "M (arrow) x arrow M' (arrow) y"
      , app (c "arrow")
          [ app (v "M") [ c ~quoted:true "arrow"; v "x" ]
          ; app (v "M'") [ c ~quoted:true "arrow"; v "y" ]
          ] )
    ; ( mock_state_5
      , "(arrow) (arrow)"
      , app (c ~quoted:true "arrow") [ c ~quoted:true "arrow" ] )
    ; (mock_state_10, "x : a : b : c", v "x" &: t_c "a" &: t_c "b" &: t_c "c")
    ]
  and failure_test_cases =
    [ (mock_state_1, "type", assert_raises_illegal_type_kind_term)
    ; (mock_state_2, "{ x : nat } x", assert_raises_illegal_pi_term)
    ; (mock_state_1, "\\x. x -> x", assert_raises_illegal_forward_arrow_term)
    ; (mock_state_1, "x <- \\x. x", assert_raises_illegal_backward_arrow_term)
    ; (mock_state_3, "Nat.one", assert_raises_unbound_term_constant)
    ; ( mock_state_5
      , "has_type has_type"
      , assert_raises_consecutive_non_associative_operators )
    ; ( mock_state_5
      , "x has_type y has_type z"
      , assert_raises_consecutive_non_associative_operators )
    ; (mock_state_5, "x arrow", assert_raises_arity_mismatch)
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           let open OUnit2 in
           input >:: test_success elaboration_context input expected)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (elaboration_context, input, assert_exn) ->
           let open OUnit2 in
           input >:: test_failure elaboration_context input assert_exn)
  in
  let open OUnit2 in
  [ "success" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let tests =
  let open OUnit2 in
  "LF_parser"
  >::: [ "kind" >::: test_kind
       ; "type" >::: test_type
       ; "term" >::: test_term
       ]
