open Support
open Beluga

module LF = struct
  module rec Kind : sig
    include module type of Synext'.LF.Kind

    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.LF.Kind

    let equal x y =
      match (x, y) with
      | Typ _, Typ _ -> true
      | ( Arrow { domain = d1; range = r1; _ }
        , Arrow { domain = d2; range = r2; _ } ) ->
        Typ.equal d1 d2 && Kind.equal r1 r2
      | ( Pi { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Pi { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Typ.equal t1 t2 && Kind.equal b1 b2
      | Parenthesized { kind = k1; _ }, Parenthesized { kind = k2; _ } ->
        Kind.equal k1 k2
      | _ -> false
  end

  and Typ : sig
    include module type of Synext'.LF.Typ

    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.LF.Typ

    let equal x y =
      match (x, y) with
      | Constant { identifier = i1; _ }, Constant { identifier = i2; _ } ->
        QualifiedIdentifier.equal i1 i2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Typ.equal f1 f2 && List.equal Term.equal as1 as2
      | ( ForwardArrow { domain = d1; range = r1; _ }
        , ForwardArrow { domain = d2; range = r2; _ } ) ->
        Typ.equal d1 d2 && Typ.equal r1 r2
      | ( BackwardArrow { domain = d1; range = r1; _ }
        , BackwardArrow { domain = d2; range = r2; _ } ) ->
        Typ.equal d1 d2 && Typ.equal r1 r2
      | ( Pi { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Pi { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Typ.equal t1 t2 && Typ.equal b1 b2
      | Parenthesized { typ = t1; _ }, Parenthesized { typ = t2; _ } ->
        Typ.equal t1 t2
      | _ -> false
  end

  and Term : sig
    include module type of Synext'.LF.Term

    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.LF.Term

    let equal x y =
      match (x, y) with
      | Variable { identifier = i1; _ }, Variable { identifier = i2; _ } ->
        Identifier.equal i1 i2
      | Constant { identifier = i1; _ }, Constant { identifier = i2; _ } ->
        QualifiedIdentifier.equal i1 i2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Term.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Abstraction
            { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Abstraction
            { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Option.equal Typ.equal t1 t2
        && Term.equal b1 b2
      | Wildcard _, Wildcard _ -> true
      | ( TypeAnnotated { term = u1; typ = t1; _ }
        , TypeAnnotated { term = u2; typ = t2; _ } ) ->
        Term.equal u1 u2 && Typ.equal t1 t2
      | Parenthesized { term = t1; _ }, Parenthesized { term = t2; _ } ->
        Term.equal t1 t2
      | _ -> false
  end
end

module LF_constructors = struct
  open Synext'.LF

  let location = Location.ghost

  let id n = Identifier.make ~location n

  let qid ?m n =
    QualifiedIdentifier.make ~location
      ?modules:(Option.map (List.map id) m)
      (id n)

  (* LF kind constructors *)

  let typ = Kind.Typ { location }

  let ( ==> ) domain range = Kind.Arrow { location; domain; range }

  let pik ?x ~t body =
    Kind.Pi
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let park kind = Kind.Parenthesized { location; kind }

  (* LF type constructors *)

  let ct ?m identifier =
    Typ.Constant { location; identifier = qid ?m identifier }

  let appt applicand arguments =
    Typ.Application { location; applicand; arguments }

  let ( => ) domain range = Typ.ForwardArrow { location; domain; range }

  let ( <= ) domain range = Typ.BackwardArrow { location; domain; range }

  let pit ?x ~t body =
    Typ.Pi
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let part typ = Typ.Parenthesized { location; typ }

  (* LF term constructors *)

  let v identifier = Term.Variable { location; identifier = id identifier }

  let c ?m identifier =
    Term.Constant { location; identifier = qid ?m identifier }

  let app applicand arguments =
    Term.Application { location; applicand; arguments }

  let lam ?x ?t body =
    Term.Abstraction
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let hole = Term.Wildcard { location }

  let ( &: ) term typ = Term.TypeAnnotated { location; term; typ }

  let par term = Term.Parenthesized { location; term }
end

let parse_lf_object input =
  Runparser.parse_string Location.ghost input
    (Parser.only Parser.LF_parsers.lf_object)
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

let mock_dictionary_1 = Synprs_to_synext'.Dictionary.empty

let mock_dictionary_2 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (qid "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "sum/s")

let mock_dictionary_3 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
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

let mock_dictionary_4 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
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

let mock_dictionary_5 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "tp")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "bool")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "nat")
  |> add_infix_lf_term_constant ~associativity:Associativity.left_associative
       ~precedence:2 (qid "arrow")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "term")
  |> add_infix_lf_term_constant ~associativity:Associativity.non_associative
       ~precedence:3 (qid "has_type")

let mock_dictionary_6 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "exp")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:3
       (qid "app")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_infix_lf_type_constant ~associativity:Associativity.left_associative
       ~precedence:1 (qid "eq")

let mock_dictionary_7 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
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

let mock_dictionary_8 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
  empty
  |> add_infix_lf_type_constant
       ~associativity:Associativity.right_associative ~precedence:1
       (qid "msteps")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "term")

let mock_dictionary_9 =
  let open LF_constructors in
  let open Synprs_to_synext'.Dictionary in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "tp")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "target")

let test_kind =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Synext'.LF.pp_kind)
      ~cmp:LF.Kind.equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.elaborate_kind elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_lf_object input
    |> Synprs_to_synext'.LF.elaborate_kind elaboration_context
  in
  let success_test_cases =
    let open LF_constructors in
    [ (mock_dictionary_1, "type", typ)
    ; ( mock_dictionary_2
      , "nat -> nat -> type"
      , ct "nat" ==> (ct "nat" ==> typ) )
    ; ( mock_dictionary_2
      , "nat -> (nat -> type)"
      , ct "nat" ==> park (ct "nat" ==> typ) )
    ; ( mock_dictionary_2
      , "nat -> nat -> nat -> type"
      , ct "nat" ==> (ct "nat" ==> (ct "nat" ==> typ)) )
    ; ( mock_dictionary_2
      , "(nat -> nat) -> type"
      , part (ct "nat" => ct "nat") ==> typ )
    ; ( mock_dictionary_3
      , "Nat::nat -> Nat::nat -> type"
      , ct ~m:[ "Nat" ] "nat" ==> (ct ~m:[ "Nat" ] "nat" ==> typ) )
    ; ( mock_dictionary_4
      , "Util::Nat::nat -> Util::Nat::nat -> type"
      , ct ~m:[ "Util"; "Nat" ] "nat"
        ==> (ct ~m:[ "Util"; "Nat" ] "nat" ==> typ) )
    ; ( mock_dictionary_8
      , "({ x : term } (M x) msteps (M' x)) -> (lam M) msteps (lam M') -> \
         type"
      , part
          (pit ~x:"x" ~t:(ct "term")
             (appt (ct "msteps")
                [ par (app (v "M") [ v "x" ]); par (app (v "M'") [ v "x" ]) ]))
        ==> (appt (ct "msteps")
               [ par (app (c "lam") [ v "M" ])
               ; par (app (c "lam") [ v "M'" ])
               ]
            ==> typ) )
    ; ( mock_dictionary_9
      , "{ Lf : tp } target Lf -> type"
      , pik ~x:"Lf" ~t:(ct "tp") (appt (ct "target") [ v "Lf" ] ==> typ) )
    ; ( mock_dictionary_9
      , "{ Lf : tp } { _ : tp } target Lf -> type"
      , pik ~x:"Lf" ~t:(ct "tp")
          (pik ~t:(ct "tp") (appt (ct "target") [ v "Lf" ] ==> typ)) )
    ]
  and failure_test_cases =
    [ (mock_dictionary_1, "M", assert_raises_illegal_identifier_kind)
    ; ( mock_dictionary_1
      , "Q::M"
      , assert_raises_illegal_qualified_identifier_kind )
    ; ( mock_dictionary_2
      , "type <- nat"
      , assert_raises_illegal_backward_arrow_kind )
    ; (mock_dictionary_1, "_", assert_raises_illegal_hole_kind)
    ; (mock_dictionary_1, "(\\x. _)", assert_raises_illegal_lambda_kind)
    ; (mock_dictionary_2, "type : _", assert_raises_illegal_annotated_kind)
    ; (mock_dictionary_2, "nat _", assert_raises_illegal_application_kind)
    ; ( mock_dictionary_9
      , "{ Lf } target Lf -> type"
      , assert_raises_illegal_untyped_pi_kind )
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           OUnit2.test_case
           @@ test_success elaboration_context input expected)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (elaboration_context, input, assert_exn) ->
           OUnit2.test_case
           @@ test_failure elaboration_context input assert_exn)
  in
  let open OUnit2 in
  [ "sucess" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let test_type =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Synext'.LF.pp_typ)
      ~cmp:LF.Typ.equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.elaborate_typ elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_lf_object input
    |> Synprs_to_synext'.LF.elaborate_typ elaboration_context
  in
  let success_test_cases =
    let open LF_constructors in
    [ (mock_dictionary_2, "nat -> nat", ct "nat" => ct "nat")
    ; ( mock_dictionary_2
      , "nat -> nat -> nat"
      , ct "nat" => (ct "nat" => ct "nat") )
    ; ( mock_dictionary_2
      , "(nat -> nat) -> nat"
      , part (ct "nat" => ct "nat") => ct "nat" )
    ; ( mock_dictionary_2
      , "nat <- (nat -> nat)"
      , ct "nat" <= part (ct "nat" => ct "nat") )
    ; ( mock_dictionary_2
      , "nat <- nat -> nat"
      , ct "nat" <= (ct "nat" => ct "nat") )
    ; ( mock_dictionary_2
      , "nat -> nat <- nat -> nat"
      , ct "nat" => (ct "nat" <= (ct "nat" => ct "nat")) )
    ; ( mock_dictionary_5
      , "(term T -> term T') -> term (T arrow T')"
      , part (appt (ct "term") [ v "T" ] => appt (ct "term") [ v "T'" ])
        => appt (ct "term") [ par (app (c "arrow") [ v "T"; v "T'" ]) ] )
    ; ( mock_dictionary_5
      , "term (T arrow T') -> term T -> term T'"
      , appt (ct "term") [ par (app (c "arrow") [ v "T"; v "T'" ]) ]
        => (appt (ct "term") [ v "T" ] => appt (ct "term") [ v "T'" ]) )
    ; ( mock_dictionary_5
      , "(term T -> term T') -> term ((arrow) T T')"
      , part (appt (ct "term") [ v "T" ] => appt (ct "term") [ v "T'" ])
        => appt (ct "term") [ par (app (par (c "arrow")) [ v "T"; v "T'" ]) ]
      )
    ; ( mock_dictionary_5
      , "(term T -> term T') -> term (((arrow)) T T')"
      , part (appt (ct "term") [ v "T" ] => appt (ct "term") [ v "T'" ])
        => appt (ct "term")
             [ par (app (par (par (c "arrow"))) [ v "T"; v "T'" ]) ] )
    ; ( mock_dictionary_5
      , "(term T -> term T') -> term ((((arrow))) T T')"
      , part (appt (ct "term") [ v "T" ] => appt (ct "term") [ v "T'" ])
        => appt (ct "term")
             [ par (app (par (par (par (c "arrow")))) [ v "T"; v "T'" ]) ] )
    ; ( mock_dictionary_5
      , "term ((arrow) T T') -> term T -> term T'"
      , appt (ct "term") [ par (app (par (c "arrow")) [ v "T"; v "T'" ]) ]
        => (appt (ct "term") [ v "T" ] => appt (ct "term") [ v "T'" ]) )
    ; ( mock_dictionary_6
      , "E1 eq F1 -> E2 eq F2 -> (E1 app E2) eq (F1 app F2)"
      , appt (ct "eq") [ v "E1"; v "F1" ]
        => (appt (ct "eq") [ v "E2"; v "F2" ]
           => appt (ct "eq")
                [ par (app (c "app") [ v "E1"; v "E2" ])
                ; par (app (c "app") [ v "F1"; v "F2" ])
                ]) )
    ; ( mock_dictionary_6
      , "(eq) E1 F1 -> (eq) E2 F2 -> (eq) ((app) E1 E2) ((app) F1 F2)"
      , appt (part (ct "eq")) [ v "E1"; v "F1" ]
        => (appt (part (ct "eq")) [ v "E2"; v "F2" ]
           => appt
                (part (ct "eq"))
                [ par (app (par (c "app")) [ v "E1"; v "E2" ])
                ; par (app (par (c "app")) [ v "F1"; v "F2" ])
                ]) )
    ; ( mock_dictionary_6
      , "{ _ : exp } _ eq _"
      , pit ~t:(ct "exp") (appt (ct "eq") [ hole; hole ]) )
    ; ( mock_dictionary_6
      , "({x : exp} x eq x -> (E x) eq (F x)) -> (lam (\\x. E x)) eq (lam \
         (\\x. F x))"
      , part
          (pit ~x:"x" ~t:(ct "exp")
             (appt (ct "eq") [ v "x"; v "x" ]
             => appt (ct "eq")
                  [ par (app (v "E") [ v "x" ])
                  ; par (app (v "F") [ v "x" ])
                  ]))
        => appt (ct "eq")
             [ par
                 (app (c "lam") [ par (lam ~x:"x" (app (v "E") [ v "x" ])) ])
             ; par
                 (app (c "lam") [ par (lam ~x:"x" (app (v "F") [ v "x" ])) ])
             ] )
    ; ( mock_dictionary_6
      , "({x : exp} (eq) x x -> (eq) (E x) (F x)) -> (eq) (lam (\\x. E x)) \
         (lam (\\x. F x))"
      , part
          (pit ~x:"x" ~t:(ct "exp")
             (appt (part (ct "eq")) [ v "x"; v "x" ]
             => appt
                  (part (ct "eq"))
                  [ par (app (v "E") [ v "x" ])
                  ; par (app (v "F") [ v "x" ])
                  ]))
        => appt
             (part (ct "eq"))
             [ par
                 (app (c "lam") [ par (lam ~x:"x" (app (v "E") [ v "x" ])) ])
             ; par
                 (app (c "lam") [ par (lam ~x:"x" (app (v "F") [ v "x" ])) ])
             ] )
    ; ( mock_dictionary_6
      , "({x : exp} (eq) x x -> (eq) (E x) (F x)) -> (eq) (lam (\\x. (E) \
         x)) (lam (\\x. (F) x))"
      , part
          (pit ~x:"x" ~t:(ct "exp")
             (appt (part (ct "eq")) [ v "x"; v "x" ]
             => appt
                  (part (ct "eq"))
                  [ par (app (v "E") [ v "x" ])
                  ; par (app (v "F") [ v "x" ])
                  ]))
        => appt
             (part (ct "eq"))
             [ par
                 (app (c "lam")
                    [ par (lam ~x:"x" (app (par (v "E")) [ v "x" ])) ])
             ; par
                 (app (c "lam")
                    [ par (lam ~x:"x" (app (par (v "F")) [ v "x" ])) ])
             ] )
    ; ( mock_dictionary_7
      , "(Statics::term T -> Statics::term T') -> Statics::term (T \
         Statics::arrow T')"
      , part
          (appt (ct ~m:[ "Statics" ] "term") [ v "T" ]
          => appt (ct ~m:[ "Statics" ] "term") [ v "T'" ])
        => appt
             (ct ~m:[ "Statics" ] "term")
             [ par (app (c ~m:[ "Statics" ] "arrow") [ v "T"; v "T'" ]) ] )
    ; ( mock_dictionary_7
      , "(Statics::term T -> Statics::term T') -> Statics::term \
         ((Statics::arrow) T T')"
      , part
          (appt (ct ~m:[ "Statics" ] "term") [ v "T" ]
          => appt (ct ~m:[ "Statics" ] "term") [ v "T'" ])
        => appt
             (ct ~m:[ "Statics" ] "term")
             [ par (app (par (c ~m:[ "Statics" ] "arrow")) [ v "T"; v "T'" ])
             ] )
    ]
  and failure_test_cases =
    [ (mock_dictionary_1, "type", assert_raises_illegal_type_kind_type)
    ; (mock_dictionary_1, "_", assert_raises_illegal_hole_type)
    ; (mock_dictionary_1, "\\x. _", assert_raises_illegal_lambda_type)
    ; (mock_dictionary_2, "nat : type", assert_raises_illegal_annotated_type)
    ; ( mock_dictionary_6
      , "{ x } x eq x"
      , assert_raises_illegal_untyped_pi_type )
    ; (mock_dictionary_1, "z", assert_raises_unbound_type_constant)
    ; (mock_dictionary_3, "Nat::add", assert_raises_unbound_type_constant)
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           OUnit2.test_case
           @@ test_success elaboration_context input expected)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (elaboration_context, input, assert_exn) ->
           OUnit2.test_case
           @@ test_failure elaboration_context input assert_exn)
  in
  let open OUnit2 in
  [ "sucess" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let test_term =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Synext'.LF.pp_term_debug)
      ~cmp:LF.Term.equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.elaborate_term elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_lf_object input
    |> Synprs_to_synext'.LF.elaborate_term elaboration_context
  in
  let success_test_cases =
    let open LF_constructors in
    [ (mock_dictionary_1, "M x y z", app (v "M") [ v "x"; v "y"; v "z" ])
    ; (mock_dictionary_1, "_ x y z", app hole [ v "x"; v "y"; v "z" ])
    ; (mock_dictionary_1, "M _ y z", app (v "M") [ hole; v "y"; v "z" ])
    ; (mock_dictionary_1, "M x _ z", app (v "M") [ v "x"; hole; v "z" ])
    ; (mock_dictionary_1, "M x y _", app (v "M") [ v "x"; v "y"; hole ])
    ; (mock_dictionary_1, "M _ y _", app (v "M") [ hole; v "y"; hole ])
    ; (mock_dictionary_1, "M _ _ _", app (v "M") [ hole; hole; hole ])
    ; (mock_dictionary_1, "\\x. x", lam ~x:"x" (v "x"))
    ; (mock_dictionary_1, "\\x. M x", lam ~x:"x" (app (v "M") [ v "x" ]))
    ; ( mock_dictionary_1
      , "\\x. \\y. \\z. M x y z"
      , lam ~x:"x"
          (lam ~x:"y" (lam ~x:"z" (app (v "M") [ v "x"; v "y"; v "z" ]))) )
    ; (mock_dictionary_2, "z", c "z")
    ; (mock_dictionary_2, "z : nat", c "z" &: ct "nat")
    ; (mock_dictionary_2, "\\x. s x", lam ~x:"x" (app (c "s") [ v "x" ]))
    ; ( mock_dictionary_2
      , "\\x. \\_. s x"
      , lam ~x:"x" (lam (app (c "s") [ v "x" ])) )
    ; ( mock_dictionary_2
      , "\\x:nat. s x"
      , lam ~x:"x" ~t:(ct "nat") (app (c "s") [ v "x" ]) )
    ; ( mock_dictionary_2
      , "\\x. s (x : nat)"
      , lam ~x:"x" (app (c "s") [ par (v "x" &: ct "nat") ]) )
    ; ( mock_dictionary_2
      , "\\x. s x : nat"
      , lam ~x:"x" (app (c "s") [ v "x" ] &: ct "nat") )
    ; ( mock_dictionary_2
      , "(\\x. s x) : nat -> nat"
      , par (lam ~x:"x" (app (c "s") [ v "x" ])) &: (ct "nat" => ct "nat") )
    ; (mock_dictionary_2, "s z", app (c "s") [ app (c "z") [] ])
    ; ( mock_dictionary_5
      , "M (arrow) x arrow M' (arrow) y"
      , app (c "arrow")
          [ app (v "M") [ par (c "arrow"); v "x" ]
          ; app (v "M'") [ par (c "arrow"); v "y" ]
          ] )
    ; ( mock_dictionary_5
      , "(arrow) (arrow)"
      , app (par (c "arrow")) [ par (c "arrow") ] )
    ]
  and failure_test_cases =
    [ (mock_dictionary_1, "type", assert_raises_illegal_type_kind_term)
    ; (mock_dictionary_2, "{ x : nat } x", assert_raises_illegal_pi_term)
    ; ( mock_dictionary_1
      , "\\x. x -> x"
      , assert_raises_illegal_forward_arrow_term )
    ; ( mock_dictionary_1
      , "x <- \\x. x"
      , assert_raises_illegal_backward_arrow_term )
    ; (mock_dictionary_3, "Nat::one", assert_raises_unbound_term_constant)
    ; ( mock_dictionary_5
      , "has_type has_type"
      , assert_raises_consecutive_non_associative_operators )
    ; ( mock_dictionary_5
      , "x has_type y has_type z"
      , assert_raises_consecutive_non_associative_operators )
    ; ( mock_dictionary_5
      , "x arrow"
      , assert_raises_arity_mismatch )
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           OUnit2.test_case
           @@ test_success elaboration_context input expected)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (elaboration_context, input, assert_exn) ->
           OUnit2.test_case
           @@ test_failure elaboration_context input assert_exn)
  in
  let open OUnit2 in
  [ "sucess" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let tests =
  let open OUnit2 in
  "LF_parser"
  >::: [ "kind" >::: test_kind
       ; "type" >::: test_type
       ; "term" >::: test_term
       ]
