open Support
open Beluga

module CLF = struct
  module rec Typ : sig
    include module type of Synext'.CLF.Typ

    (** [equal x y] is [true] if and only if types [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.CLF.Typ

    let equal x y =
      match (x, y) with
      | ( Constant { identifier = i1; quoted = q1; _ }
        , Constant { identifier = i2; quoted = q2; _ } ) ->
        QualifiedIdentifier.equal i1 i2 && Bool.equal q1 q2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Typ.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Arrow { domain = d1; range = r1; orientation = o1; _ }
        , Arrow { domain = d2; range = r2; orientation = o2; _ } ) ->
        o1 = o2 && Typ.equal d1 d2 && Typ.equal r1 r2
      | ( Pi { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Pi { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Typ.equal t1 t2 && Typ.equal b1 b2
      | Block { elements = e1; _ }, Block { elements = e2; _ } -> (
        match (e1, e2) with
        | `Unnamed t1, `Unnamed t2 -> Typ.equal t1 t2
        | `Record ts1, `Record ts2 ->
          List1.equal (Pair.equal Identifier.equal Typ.equal) ts1 ts2
        | _ -> false)
      | _ -> false
  end

  and Term : sig
    include module type of Synext'.CLF.Term

    (** [equal x y] is [true] if and only if terms [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.CLF.Term

    let equal x y =
      match (x, y) with
      | Variable { identifier = i1; _ }, Variable { identifier = i2; _ } ->
        Identifier.equal i1 i2
      | ( Constant { identifier = i1; quoted = q1; _ }
        , Constant { identifier = i2; quoted = q2; _ } ) ->
        QualifiedIdentifier.equal i1 i2 && Bool.equal q1 q2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Term.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Substitution { term = t1; substitution = s1; _ }
        , Substitution { term = t2; substitution = s2; _ } ) ->
        Term.equal t1 t2 && Substitution.equal s1 s2
      | ( Abstraction
            { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Abstraction
            { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Option.equal Typ.equal t1 t2
        && Term.equal b1 b2
      | Hole { variant = v1; _ }, Hole { variant = v2; _ } -> (
        match (v1, v2) with
        | `Underscore, `Underscore | `Unlabelled, `Unlabelled -> true
        | `Labelled l1, `Labelled l2 -> Identifier.equal l1 l2
        | _ -> false)
      | Tuple { terms = ts1; _ }, Tuple { terms = ts2; _ } ->
        List1.equal Term.equal ts1 ts2
      | ( Projection { term = t1; projection = p1; _ }
        , Projection { term = t2; projection = p2; _ } ) -> (
        Term.equal t1 t2
        &&
        match (p1, p2) with
        | `By_identifier i1, `By_identifier i2 -> Identifier.equal i1 i2
        | `By_position i1, `By_position i2 -> Int.equal i1 i2
        | _ -> false)
      | ( TypeAnnotated { term = u1; typ = t1; _ }
        , TypeAnnotated { term = u2; typ = t2; _ } ) ->
        Term.equal u1 u2 && Typ.equal t1 t2
      | _ -> false
  end

  and Substitution : sig
    include module type of Synext'.CLF.Substitution

    (** [equal x y] is [true] if and only if terms [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.CLF.Substitution

    let rec head_equal x y =
      match (x, y) with
      | Substitution.Head.None, Substitution.Head.None
      | Substitution.Head.Identity _, Substitution.Head.Identity _ -> true
      | ( Substitution.Head.Substitution_variable
            { identifier = i1; closure = o1; _ }
        , Substitution.Head.Substitution_variable
            { identifier = i2; closure = o2; _ } ) ->
        Identifier.equal i1 i2 && Option.equal equal o1 o2
      | _ -> false

    and equal x y =
      match (x, y) with
      | ( { Substitution.head = h1; terms = ts1; _ }
        , { Substitution.head = h2; terms = ts2; _ } ) ->
        head_equal h1 h2 && List.equal Term.equal ts1 ts2
  end
end

(** Abbreviated constructors for contextual LF types, terms, substitutions,
    contexts and patterns. These are strictly used for testing. *)
module CLF_constructors = struct
  open Synext'.CLF

  let location = Obj.magic ()

  let id n = Identifier.make ~location n

  let qid ?m n =
    QualifiedIdentifier.make ~location
      ?modules:(Option.map (List.map id) m)
      (id n)

  (* LF type constructors *)

  let t_c ?(quoted = false) ?m identifier =
    Typ.Constant
      { location
      ; identifier = qid ?m identifier
      ; operator = Obj.magic ()
      ; quoted
      }

  let t_app applicand arguments =
    Typ.Application { location; applicand; arguments }

  let ( => ) domain range =
    Typ.Arrow { location; domain; range; orientation = `Forward }

  let ( <= ) range domain =
    Typ.Arrow { location; domain; range; orientation = `Backward }

  let t_pi ?x ~t body =
    Typ.Pi
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let t_block_s t = Typ.Block { location; elements = `Unnamed t }

  let t_block ts =
    Typ.Block
      { location; elements = `Record (List1.map (Pair.map_left id) ts) }

  (* LF term constructors *)

  let v identifier = Term.Variable { location; identifier = id identifier }

  let c ?(quoted = false) ?m identifier =
    Term.Constant
      { location
      ; identifier = qid ?m identifier
      ; operator = Obj.magic ()
      ; quoted
      }

  let app applicand arguments =
    Term.Application { location; applicand; arguments }

  let lam ?x ?t body =
    Term.Abstraction
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let hole = Term.Hole { location; variant = `Underscore }

  let u_hole = Term.Hole { location; variant = `Unlabelled }

  let l_hole l = Term.Hole { location; variant = `Labelled (id l) }

  let ( &: ) term typ = Term.TypeAnnotated { location; term; typ }

  let rec substitution sub =
    let head, terms = sub in
    let head' =
      match head with
      | `None -> Substitution.Head.None
      | `Id -> Substitution.Head.Identity { location }
      | `SVar i ->
        Substitution.Head.Substitution_variable
          { location; identifier = id i; closure = Option.none }
      | `SClo (i, closure) ->
        let closure' = substitution closure in
        Substitution.Head.Substitution_variable
          { location; identifier = id i; closure = Option.some closure' }
    in
    { Substitution.head = head'; terms; location }

  let sub term sub =
    Term.Substitution { location; term; substitution = substitution sub }

  let tuple terms = Term.Tuple { location; terms }

  let proj_i term i =
    Term.Projection { location; term; projection = `By_position i }

  let proj_x term x =
    Term.Projection { location; term; projection = `By_identifier (id x) }
end

let parse_clf_object input =
  Runparser.parse_string Location.ghost input
    (Parser.only Parser.CLF_parsers.clf_object)
  |> Parser.extract

let assert_raises_illegal_hole_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_hole_type _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_hole_type _ -> ()

let assert_raises_illegal_lambda_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_lambda_type _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_lambda_type _ -> ()

let assert_raises_illegal_annotated_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_annotated_type _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_annotated_type _ -> ()

let assert_raises_illegal_untyped_pi_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_untyped_pi_type _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_untyped_pi_type _ -> ()

let assert_raises_unbound_type_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Unbound_type_constant _] to be raised"
  with Synprs_to_synext'.CLF.Unbound_type_constant _ -> ()

let assert_raises_illegal_pi_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_pi_term _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_pi_term _ -> ()

let assert_raises_illegal_forward_arrow_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_forward_arrow_term _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_forward_arrow_term _ -> ()

let assert_raises_illegal_backward_arrow_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Illegal_backward_arrow_term _] to be raised"
  with Synprs_to_synext'.CLF.Illegal_backward_arrow_term _ -> ()

let assert_raises_unbound_term_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Unbound_term_constant _] to be raised"
  with Synprs_to_synext'.CLF.Unbound_term_constant _ -> ()

let assert_raises_expected_term_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Expected_term_constant _] to be raised"
  with Synprs_to_synext'.CLF.Expected_term_constant _ -> ()

let assert_raises_expected_type_constant f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Expected_type_constant _] to be raised"
  with Synprs_to_synext'.CLF.Expected_type_constant _ -> ()

let assert_raises_expected_term f =
  try
    ignore @@ f ();
    OUnit2.assert_failure "Expected exception [Expected_term _] to be raised"
  with Synprs_to_synext'.CLF.Expected_term _ -> ()

let assert_raises_expected_type f =
  try
    ignore @@ f ();
    OUnit2.assert_failure "Expected exception [Expected_type _] to be raised"
  with Synprs_to_synext'.CLF.Expected_type _ -> ()

let assert_raises_misplaced_operator f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Misplaced_operator _] to be raised"
  with Synprs_to_synext'.CLF.Misplaced_operator _ -> ()

let assert_raises_consecutive_non_associative_operators f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Consecutive_non_associative_operators _] to be \
       raised"
  with Synprs_to_synext'.CLF.Consecutive_non_associative_operators _ -> ()

let assert_raises_arity_mismatch f =
  try
    ignore @@ f ();
    OUnit2.assert_failure
      "Expected exception [Arity_mismatch _] to be raised"
  with Synprs_to_synext'.CLF.Arity_mismatch _ -> ()

let mock_state_1 = Synprs_to_synext'.Disambiguation_state.empty

let mock_state_2 =
  let open CLF_constructors in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (qid "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "sum/s")

let mock_state_3 =
  let open CLF_constructors in
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
  let open CLF_constructors in
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
  let open CLF_constructors in
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
  let open CLF_constructors in
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
  let open CLF_constructors in
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
  let open CLF_constructors in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_infix_lf_type_constant
       ~associativity:Associativity.right_associative ~precedence:1
       (qid "msteps")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "term")

let mock_state_9 =
  let open CLF_constructors in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "tp")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "target")

let mock_state_10 =
  let open CLF_constructors in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "a")
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "b")
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "c")

let mock_state_11 =
  let open CLF_constructors in
  let open Synprs_to_synext'.Disambiguation_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (qid "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "sum/s")
  |> add_substitution_variable (id "$S")

let test_type =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.CLF.of_typ
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:CLF.Typ.equal expected
      (parse_clf_object input
      |> Synprs_to_synext'.CLF.disambiguate_as_typ elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_clf_object input
    |> Synprs_to_synext'.CLF.disambiguate_as_typ elaboration_context
  in
  let success_test_cases =
    let open CLF_constructors in
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
      , "(Statics::term T -> Statics::term T') -> Statics::term (T \
         Statics::arrow T')"
      , t_app (t_c ~m:[ "Statics" ] "term") [ v "T" ]
        => t_app (t_c ~m:[ "Statics" ] "term") [ v "T'" ]
        => t_app
             (t_c ~m:[ "Statics" ] "term")
             [ app (c ~m:[ "Statics" ] "arrow") [ v "T"; v "T'" ] ] )
    ; ( mock_state_7
      , "(Statics::term T -> Statics::term T') -> Statics::term \
         ((Statics::arrow) T T')"
      , t_app (t_c ~m:[ "Statics" ] "term") [ v "T" ]
        => t_app (t_c ~m:[ "Statics" ] "term") [ v "T'" ]
        => t_app
             (t_c ~m:[ "Statics" ] "term")
             [ app
                 (c ~quoted:true ~m:[ "Statics" ] "arrow")
                 [ v "T"; v "T'" ]
             ] )
    ; (mock_state_2, "block nat", t_block_s (t_c "nat"))
    ; ( mock_state_2
      , "block x : nat"
      , t_block (List1.singleton ("x", t_c "nat")) )
    ; ( mock_state_2
      , "block (x : nat, y : sum x z x)"
      , t_block
          (List1.from
             ("x", t_c "nat")
             [ ("y", t_app (t_c "sum") [ v "x"; c "z"; v "x" ]) ]) )
    ; ( mock_state_2
      , "block (z : nat, y : sum z z z)"
      , t_block
          (List1.from
             ("z", t_c "nat")
             [ ("y", t_app (t_c "sum") [ v "z"; v "z"; v "z" ]) ]) )
    ]
  and failure_test_cases =
    [ (mock_state_1, "_", assert_raises_illegal_hole_type)
    ; (mock_state_1, "\\x. _", assert_raises_illegal_lambda_type)
    ; (mock_state_2, "nat : nat", assert_raises_illegal_annotated_type)
    ; (mock_state_6, "{ x } x eq x", assert_raises_illegal_untyped_pi_type)
    ; (mock_state_1, "z", assert_raises_unbound_type_constant)
    ; (mock_state_3, "Nat::add", assert_raises_unbound_type_constant)
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
  [ "sucess" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let test_term =
  let test_success elaboration_context input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:
        Fun.(
          Synext'_json.CLF.of_term
          >> Format.stringify (Yojson.Safe.pretty_print ~std:true))
      ~cmp:CLF.Term.equal expected
      (parse_clf_object input
      |> Synprs_to_synext'.CLF.disambiguate_as_term elaboration_context)
  and test_failure elaboration_context input assert_exn _test_ctxt =
    assert_exn @@ fun () ->
    parse_clf_object input
    |> Synprs_to_synext'.CLF.disambiguate_as_term elaboration_context
  in
  let success_test_cases =
    let open CLF_constructors in
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
    ; (mock_state_1, "_", hole)
    ; (mock_state_1, "?", u_hole)
    ; (mock_state_1, "?x", l_hole "x")
    ; (mock_state_2, "s _", app (c "s") [ hole ])
    ; (mock_state_2, "s ?", app (c "s") [ u_hole ])
    ; (mock_state_2, "s ?x", app (c "s") [ l_hole "x" ])
    ; ( mock_state_2
      , "<x1; x2; x3>"
      , tuple (List1.from (v "x1") [ v "x2"; v "x3" ]) )
    ; ( mock_state_2
      , "<?; ?; ?>"
      , tuple (List1.from u_hole [ u_hole; u_hole ]) )
    ; ( mock_state_2
      , "<?x1; ?x2; ?x3>"
      , tuple (List1.from (l_hole "x1") [ l_hole "x2"; l_hole "x3" ]) )
    ; (mock_state_2, "<x>.1", proj_i (tuple (List1.from (v "x") [])) 1)
    ; ( mock_state_2
      , "<x>.1.2.3"
      , proj_i (proj_i (proj_i (tuple (List1.from (v "x") [])) 1) 2) 3 )
    ; ( mock_state_2
      , "<x>.x.1.y"
      , proj_x (proj_i (proj_x (tuple (List1.from (v "x") [])) "x") 1) "y" )
    ; (mock_state_2, "x[]", sub (v "x") (`None, []))
    ; (mock_state_2, "x[z]", sub (v "x") (`None, [ c "z" ]))
    ; (mock_state_2, "x[\\z. z]", sub (v "x") (`None, [ lam ~x:"z" (v "z") ]))
    ; ( mock_state_2
      , "\\y1. \\y2. \\y3. x[y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3" (sub (v "x") (`None, [ v "y1"; v "y2"; v "y3" ]))))
      )
    ; (mock_state_2, "x[.., z]", sub (v "x") (`Id, [ c "z" ]))
    ; ( mock_state_2
      , "\\y1. \\y2. \\y3. x[.., y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3" (sub (v "x") (`Id, [ v "y1"; v "y2"; v "y3" ]))))
      )
    ; ( mock_state_2
      , "\\y1. \\y2. \\y3. x[y1[], y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3"
                (sub (v "x")
                   (`None, [ sub (v "y1") (`None, []); v "y2"; v "y3" ]))))
      )
    ; ( mock_state_11
      , "\\y1. \\y2. \\y3. x[$S, y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3"
                (sub (v "x") (`SVar "$S", [ v "y1"; v "y2"; v "y3" ])))) )
    ; ( mock_state_11
      , "\\y1. \\y2. \\y3. x[$S[], y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3"
                (sub (v "x")
                   (`SClo ("$S", (`None, [])), [ v "y1"; v "y2"; v "y3" ]))))
      )
    ; ( mock_state_11
      , "\\y1. \\y2. \\y3. x[$S[..], y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3"
                (sub (v "x")
                   (`SClo ("$S", (`Id, [])), [ v "y1"; v "y2"; v "y3" ]))))
      )
    ; ( mock_state_11
      , "\\y1. \\y2. \\y3. x[$S[y1, y2, y3], y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3"
                (sub (v "x")
                   ( `SClo ("$S", (`None, [ v "y1"; v "y2"; v "y3" ]))
                   , [ v "y1"; v "y2"; v "y3" ] )))) )
    ; ( mock_state_11
      , "\\y1. \\y2. \\y3. x[$S[.., y1, y2, y3], y1, y2, y3]"
      , lam ~x:"y1"
          (lam ~x:"y2"
             (lam ~x:"y3"
                (sub (v "x")
                   ( `SClo ("$S", (`Id, [ v "y1"; v "y2"; v "y3" ]))
                   , [ v "y1"; v "y2"; v "y3" ] )))) )
    ]
  and failure_test_cases =
    [ (mock_state_2, "{ x : nat } x", assert_raises_illegal_pi_term)
    ; (mock_state_1, "\\x. x -> x", assert_raises_illegal_forward_arrow_term)
    ; (mock_state_1, "x <- \\x. x", assert_raises_illegal_backward_arrow_term)
    ; (mock_state_3, "Nat::one", assert_raises_unbound_term_constant)
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
  [ "sucess" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let tests =
  let open OUnit2 in
  "CLF_parser" >::: [ "type" >::: test_type; "term" >::: test_term ]
