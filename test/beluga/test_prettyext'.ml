open Support
open Beluga

module Synprs_to_synext' = struct
  module Disambiguation_state = Synprs_to_synext'.Disambiguation_state
  module LF = Synprs_to_synext'.LF (Disambiguation_state)
  module CLF = Synprs_to_synext'.CLF (Disambiguation_state)
end

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

let mock_state_11 =
  let open Synext'_constructors.LF in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (id "T")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:1 (id "L1")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:1 (id "R1")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:2 (id "L2")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:2 (id "R2")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:1 (id "N1")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:2 (id "N2")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:3 (id "N3")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (id "P11")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:2 (id "P12")
  |> add_prefix_lf_term_constant ~arity:2 ~precedence:1 (id "P21")
  |> add_prefix_lf_term_constant ~arity:2 ~precedence:2 (id "P22")
  |> add_postfix_lf_term_constant ~precedence:1 (id "Q1")
  |> add_postfix_lf_term_constant ~precedence:2 (id "Q2")
  |> add_postfix_lf_term_constant ~precedence:3 (id "Q3")

let parse_lf_object input =
  Runparser.parse_string Location.ghost input (Parser.only Parser.lf_object)
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
      ~cmp:Synext'_eq.LF.kind_equal kind kind'
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
      ~cmp:Synext'_eq.LF.typ_equal typ typ'
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
      ~cmp:Synext'_eq.LF.term_equal term term'
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
