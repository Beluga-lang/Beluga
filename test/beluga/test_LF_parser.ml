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

let test_kind =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Synext'.LF.pp_kind)
      ~cmp:LF.Kind.equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.elaborate_kind elaboration_context)
  in
  let success_test_cases =
    let open LF_constructors in
    [ (mock_dictionary_1, "type", typ)
    ; ( mock_dictionary_2
      , "nat -> nat -> type"
      , ct "nat" ==> (ct "nat" ==> typ) )
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
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           OUnit2.test_case
           @@ test_success elaboration_context input expected)
  in
  let open OUnit2 in
  [ "sucess" >::: success_tests ]

let test_type =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Synext'.LF.pp_typ)
      ~cmp:LF.Typ.equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.elaborate_typ elaboration_context)
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
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           OUnit2.test_case
           @@ test_success elaboration_context input expected)
  in
  let open OUnit2 in
  [ "sucess" >::: success_tests ]

let test_term =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Synext'.LF.pp_term)
      ~cmp:LF.Term.equal expected
      (parse_lf_object input
      |> Synprs_to_synext'.LF.elaborate_term elaboration_context)
  in
  let success_test_cases =
    let open LF_constructors in
    [ (mock_dictionary_1, "\\x. x", lam ~x:"x" (v "x"))
    ; (mock_dictionary_2, "z", c "z")
    ; (mock_dictionary_2, "\\x. s x", lam ~x:"x" (app (c "s") [ v "x" ]))
    ; (mock_dictionary_2, "s z", app (c "s") [ app (c "z") [] ])
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (elaboration_context, input, expected) ->
           OUnit2.test_case
           @@ test_success elaboration_context input expected)
  in
  let open OUnit2 in
  [ "sucess" >::: success_tests ]

let tests =
  let open OUnit2 in
  "LF_parser"
  >::: [ "kind" >::: test_kind
       ; "type" >::: test_type
       ; "term" >::: test_term
       ]
