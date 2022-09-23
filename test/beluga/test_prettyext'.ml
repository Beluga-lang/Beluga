open Support
open Beluga

let mock_state_1 = Synprs_to_synext'.Disambiguation_state.empty

let mock_state_2 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (qid "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "sum/s")

let mock_state_3 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Nat" ] "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Nat" ] "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1
       (qid ~m:[ "Nat" ] "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1
       (qid ~m:[ "Nat" ] "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Nat" ] "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1
       (qid ~m:[ "Nat" ] "sum/s")

let mock_state_4 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Util"; "Nat" ] "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Util"; "Nat" ] "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1
       (qid ~m:[ "Util"; "Nat" ] "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1
       (qid ~m:[ "Util"; "Nat" ] "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Util"; "Nat" ] "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1
       (qid ~m:[ "Util"; "Nat" ] "sum/s")

let mock_state_5 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "tp")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "bool")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "nat")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:2 (qid "arrow")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "term")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:3 (qid "has_type")

let mock_state_6 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "exp")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:3
       (qid "app")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_infix_lf_type_constant ~associativity:Associativity.left_associative
       ~precedence:1 (qid "eq")

let mock_state_7 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Statics" ] "tp")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1
       (qid ~m:[ "Statics" ] "bool")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1
       (qid ~m:[ "Statics" ] "nat")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:2
       (qid ~m:[ "Statics" ] "arrow")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1
       (qid ~m:[ "Statics" ] "term")

let mock_state_8 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_infix_lf_type_constant
       ~associativity:Associativity.right_associative ~precedence:1
       (qid "msteps")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "term")

let mock_state_9 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "tp")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "target")

let mock_state_10 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "a")
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "b")
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "c")

let mock_state_11 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "T")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:1 (qid "L1")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:1
       (qid "R1")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:2 (qid "L2")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:2
       (qid "R2")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:1 (qid "N1")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:2 (qid "N2")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:3 (qid "N3")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "P11")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:2 (qid "P12")
  |> add_prefix_lf_term_constant ~arity:2 ~precedence:1 (qid "P21")
  |> add_prefix_lf_term_constant ~arity:2 ~precedence:2 (qid "P22")
  |> add_postfix_lf_term_constant ~precedence:1 (qid "Q1")
  |> add_postfix_lf_term_constant ~precedence:2 (qid "Q2")
  |> add_postfix_lf_term_constant ~precedence:3 (qid "Q3")

let parse_lf_object input =
  Runparser.parse_string Location.ghost input
    (Parser.only Parser.lf_object)
  |> Parser.extract

let parse_lf_kind elaboration_context input =
  parse_lf_object input
  |> Synprs_to_synext'.LF.disambiguate_as_kind elaboration_context

let parse_lf_type elaboration_context input =
  parse_lf_object input
  |> Synprs_to_synext'.LF.disambiguate_as_typ elaboration_context

let parse_lf_term elaboration_context input =
  parse_lf_object input
  |> Synprs_to_synext'.LF.disambiguate_as_term elaboration_context

let test_pp_kind =
  let test elaboration_context input _test_ctxt =
    let kind = parse_lf_kind elaboration_context input in
    let kind' =
      parse_lf_kind elaboration_context
        (Format.stringify Prettyext'.LF.pp_kind kind)
    in
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.LF.of_kind
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:Synext'_eq.LF.Kind.equal kind kind'
  in
  let test_cases =
    [ (mock_state_1, "type")
    ; (mock_state_1, "(type)")
    ; (mock_state_1, "((type))")
    ; (mock_state_2, "nat -> type")
    ; (mock_state_2, "nat -> (nat -> type)")
    ; (mock_state_2, "nat -> nat -> type")
    ; (mock_state_2, "(nat -> nat) -> type")
    ; (mock_state_2, "((nat -> nat)) -> type")
    ; (mock_state_2, "{ x : nat } nat -> nat -> type")
    ; (mock_state_2, "{ _ : nat } nat -> nat -> type")
    ; (mock_state_2, "({ x : nat } nat -> nat) -> type")
    ; (mock_state_3, "({ x : Nat::nat } Nat::nat -> Nat::nat) -> type")
    ]
  in
  let tests =
    List.map
      (fun (elaboration_context, input) ->
        let open OUnit2 in
        input >:: test elaboration_context input)
      test_cases
  in
  tests

let test_pp_type =
  let test elaboration_context input _test_ctxt =
    let typ = parse_lf_type elaboration_context input in
    let typ' =
      parse_lf_type elaboration_context
        (Format.stringify Prettyext'.LF.pp_typ typ)
    in
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.LF.of_typ
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:Synext'_eq.LF.Typ.equal typ typ'
  in
  let test_cases =
    [ (mock_state_2, "nat")
    ; (mock_state_2, "nat -> nat")
    ; (mock_state_2, "nat -> nat -> nat")
    ; (mock_state_2, "(nat -> nat) -> nat")
    ; (mock_state_2, "(nat <- nat) -> nat")
    ; (mock_state_2, "nat <- (nat -> nat)")
    ; (mock_state_2, "{ x : nat } nat")
    ; (mock_state_2, "{ _ : nat } nat")
    ; (mock_state_2, "{ x : nat } { y : nat } nat")
    ; (mock_state_2, "{ x : nat } { y : nat } { z : nat } sum x y z")
    ; (mock_state_2, "({ x : nat } nat) <- sum x x x")
    ; (mock_state_2, "{ x : nat } nat <- sum x x x")
    ; ( mock_state_6
      , "({x : exp} (eq) x x -> (eq) (E x) (F x)) -> (eq) (lam (\\x. (E) \
         x)) (lam (\\x. (F) x))" )
    ; ( mock_state_6
      , "({x : exp} x eq x -> (E x) eq (F x)) -> (lam (\\x. (E) x)) eq (lam \
         (\\x. (F) x))" )
    ; (mock_state_6, "E (x : exp) eq F x")
    ; ( mock_state_6
      , "({x : exp} (x eq (x)) -> ((E (x : exp)) eq (F x))) -> ((lam) (\\x. \
         (E) x)) eq (lam (\\x. (F) x))" )
    ; (mock_state_6, "{x : exp} x eq x")
    ; (mock_state_6, "{x : exp} _ eq _")
    ; (mock_state_6, "{x : exp} (x : exp) eq _")
    ; (mock_state_10, "a -> b -> c")
    ; (mock_state_10, "(a -> b) -> c")
    ; (mock_state_10, "a <- b <- c")
    ; (mock_state_10, "a <- (b <- c)")
    ; (mock_state_10, "(a <- b) -> c")
    ; (mock_state_10, "a <- (b -> c)")
    ; (mock_state_10, "(a -> b) <- c")
    ; (mock_state_10, "a <- (b -> c)")
    ; (mock_state_10, "a -> (b -> c)")
    ; (mock_state_10, "(a <- b) <- c")
    ; (mock_state_10, "(a -> b) <- c")
    ; (mock_state_10, "a <- (b -> c)")
    ]
  in
  let tests =
    List.map
      (fun (elaboration_context, input) ->
        let open OUnit2 in
        input >:: test elaboration_context input)
      test_cases
  in
  tests

let test_pp_term =
  let test elaboration_context input _test_ctxt =
    let term = parse_lf_term elaboration_context input in
    let term' =
      parse_lf_term elaboration_context
        (Format.stringify Prettyext'.LF.pp_term term)
    in
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.LF.of_term
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:Synext'_eq.LF.Term.equal term term'
  in
  let test_cases =
    [ (mock_state_1, "M x y z")
    ; (mock_state_1, "M _ y z")
    ; (mock_state_1, "M x _ z")
    ; (mock_state_1, "M (x) y ((z))")
    ; (mock_state_1, "((M)) _ y z")
    ; (mock_state_1, "M x (((_))) z")
    ; (mock_state_1, "\\x. M x")
    ; (mock_state_1, "\\x. ((M x))")
    ; (mock_state_1, "\\x. \\y. \\z. M x y z")
    ; (mock_state_1, "\\x. (\\y. \\z. M x y z)")
    ; (mock_state_1, "\\x. (\\y. (\\z. M x y z))")
    ; (mock_state_1, "\\x. \\y. \\z. (M x y z)")
    ; (mock_state_1, "\\x. \\y. \\z. M x (y) z")
    ; (mock_state_1, "\\x. (\\y. \\z. M x (y) z)")
    ; (mock_state_1, "\\x. (\\y. (\\z. M x (y) z))")
    ; (mock_state_2, "(\\x. s x) : nat -> nat")
    ; (mock_state_11, "a R1 b R1 c")
    ; (mock_state_11, "(a R1 b) R1 c")
    ; (mock_state_11, "a L1 b L1 c")
    ; (mock_state_11, "a L1 (b L1 c)")
    ; (mock_state_11, "(a L1 b) R1 c")
    ; (mock_state_11, "a L1 (b R1 c)")
    ; (mock_state_11, "a R1 (b R1 c)")
    ; (mock_state_11, "(a L1 b) L1 c")
    ; (mock_state_11, "(a R1 b) L1 c")
    ; (mock_state_11, "a L1 (b R1 c)")
    ; (mock_state_11, "a1 L1 a2 R2 a3 Q3")
    ; (mock_state_11, "x N1 y N2 z N3 w")
    ; (mock_state_11, "x N1 y N3 z N2 w")
    ; (mock_state_11, "x N3 y N2 z N1 w")
    ; (mock_state_11, "x N2 y N3 z N1 w")
    ; (mock_state_11, "_ N3 _ N2 _ N1 _")
    ; (mock_state_11, "x N1 y N2 z N3 w")
    ; (mock_state_11, "(x N1 y) N3 z N2 w")
    ; (mock_state_11, "x N3 (y N2 z) N1 w")
    ; (mock_state_11, "x N2 (y N3 (z N1 w))")
    ; (mock_state_11, "x N1 y R2 z N3 w")
    ; (mock_state_11, "x R1 y N3 z N2 w")
    ; (mock_state_11, "x R3 y N2 z L1 w")
    ; (mock_state_11, "x N2 y L3 z N1 w")
    ; (mock_state_11, "(_ N3 _) N2 _ N1 _")
    ; (mock_state_11, "a1 Q3 L1 a2 Q2 Q1 R2 a3 Q3")
    ; (mock_state_11, "a1 Q3 L1 P11 a2 Q2 Q1 R2 P22 a3 a4 Q3")
    ; (mock_state_11, "_ Q3 L1 P11 _ Q2 Q1 R2 P22 _ _ Q3")
    ; (mock_state_11, "_ Q3 L1 P11 _ Q2 Q1 N1 P22 _ _ Q3")
    ; (mock_state_11, "_ Q3 L1 P11 _ Q2 Q1 N2 P22 _ _ Q3")
    ; (mock_state_11, "_ Q3 L1 P11 _ Q2 Q1 N3 _ Q3")
    ; (mock_state_11, "_ Q3 L1 (P11 _ Q2) Q1 N1 P22 _ _ Q3")
    ; (mock_state_11, "(((_ Q3) L1 ((P11 _) Q2)) Q1) N1 ((P22 _ _) Q3)")
    ; (mock_state_11, "(((_ Q3) L1 (P11 _) Q2) Q1) R2 (P22 _ _ Q3)")
    ; (mock_state_11, "_ Q1 Q1 Q1")
    ; (mock_state_11, "((_ Q1) Q1) Q1")
    ; (mock_state_11, "_ Q2 Q3 Q1")
    ; ( mock_state_11
      , "((a1 : T) Q3) L1 (((P11 (a2 : T)) Q2) Q1) R2 (P22 a3 (a4 Q3))" )
    ; ( mock_state_11
      , "((a1 : T) Q3) L1 (((P11 (P21 _ a : T)) Q2) Q1) R2 (P22 a3 (a4 Q3))"
      )
    ; ( mock_state_11
      , "((a1 : T) Q3) L1 ((((P11 (P21 _ a : T)) Q2) Q1) R2 (P22 a3 (a4 \
         Q3)))" )
    ; (mock_state_11, "a1 L1 ((a Q1) R2 (P22 a3 (a4 Q3)))")
    ; (mock_state_11, "(a1 L1 (a Q1)) R2 (P22 a3 (a4 Q3))")
    ; (mock_state_11, "(_ L1 _) Q1 R2 _")
    ; (mock_state_11, "_ L1 (_ Q1) R2 _")
    ; (mock_state_11, "a Q1 R2 b")
    ]
  in
  let tests =
    List.map
      (fun (elaboration_context, input) ->
        let open OUnit2 in
        input >:: test elaboration_context input)
      test_cases
  in
  tests

let test_lf =
  let open OUnit2 in
  [ "pp_kind" >::: test_pp_kind
  ; "pp_type" >::: test_pp_type
  ; "pp_term" >::: test_pp_term
  ]

let tests =
  let open OUnit2 in
  "Prettyext'" >::: [ "LF" >::: test_lf ]
