open Support
open Beluga

module LF = struct
  module rec Kind : sig
    include module type of Synext'.LF.Kind

    (** [equal x y] is [true] if and only if kinds [x] and [y] are
        structurally equal, without regards for locations. *)
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

    (** [equal x y] is [true] if and only if types [x] and [y] are
        structurally equal, without regards for locations. *)
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

    (** [equal x y] is [true] if and only if terms [x] and [y] are
        structurally equal, without regards for locations. *)
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

(** Abbreviated constructors for LF kinds, types and terms. These are
    strictly used for testing. *)
module LF_constructors = struct
  let location = Obj.magic ()

  let id n = Identifier.make ~location n

  let qid ?m n =
    QualifiedIdentifier.make ~location
      ?modules:(Option.map (List.map id) m)
      (id n)
end

let mock_state_1 = Synprs_to_synext'.Elaboration_state.empty

let mock_state_2 =
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "nat")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "s")
  |> add_prefix_lf_type_constant ~arity:3 ~precedence:1 (qid "sum")
  |> add_prefix_lf_term_constant ~arity:0 ~precedence:1 (qid "sum/z")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "sum/s")

let mock_state_3 =
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
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
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
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
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
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
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "exp")
  |> add_infix_lf_term_constant
       ~associativity:Associativity.right_associative ~precedence:3
       (qid "app")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_infix_lf_type_constant ~associativity:Associativity.left_associative
       ~precedence:1 (qid "eq")

let mock_state_7 =
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
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
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
  empty
  |> add_infix_lf_type_constant
       ~associativity:Associativity.right_associative ~precedence:1
       (qid "msteps")
  |> add_prefix_lf_term_constant ~arity:1 ~precedence:1 (qid "lam")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "term")

let mock_state_9 =
  let open LF_constructors in
  let open Synprs_to_synext'.Elaboration_state in
  empty
  |> add_prefix_lf_type_constant ~arity:0 ~precedence:1 (qid "tp")
  |> add_prefix_lf_type_constant ~arity:1 ~precedence:1 (qid "target")

let parse_lf_object input =
  Runparser.parse_string Location.ghost input
    (Parser.only Parser.LF_parsers.lf_object)
  |> Parser.extract

let parse_lf_kind elaboration_context input =
  parse_lf_object input
  |> Synprs_to_synext'.LF.elaborate_kind elaboration_context

let parse_lf_type elaboration_context input =
  parse_lf_object input
  |> Synprs_to_synext'.LF.elaborate_typ elaboration_context

let parse_lf_term elaboration_context input =
  parse_lf_object input
  |> Synprs_to_synext'.LF.elaborate_term elaboration_context

let test_pp_kind =
  let test elaboration_context input _test_ctxt =
    let kind = parse_lf_kind elaboration_context input in
    let kind' =
      kind |> Prettyext'.LF.remove_parentheses_kind
      |> Prettyext'.LF.parenthesize_kind
    in
    let kind'' =
      parse_lf_kind elaboration_context
        (Format.asprintf "%a" Prettyext'.LF.pp_kind kind')
    in
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Prettyext'.LF.Debug.pp_kind)
      ~cmp:LF.Kind.equal kind' kind''
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
    ; (mock_state_2, "({ x : nat } nat -> nat) -> type")
    ; (mock_state_3, "({ x : Nat::nat } Nat::nat -> Nat::nat) -> type")
    ]
  in
  let tests =
    List.map
      (fun (elaboration_context, input) ->
        OUnit2.test_case @@ test elaboration_context input)
      test_cases
  in
  tests

let test_pp_type =
  let test elaboration_context input _test_ctxt =
    let typ = parse_lf_type elaboration_context input in
    let typ' =
      typ |> Prettyext'.LF.remove_parentheses_typ
      |> Prettyext'.LF.parenthesize_typ
    in
    let typ'' =
      parse_lf_type elaboration_context
        (Format.asprintf "%a" Prettyext'.LF.pp_typ typ')
    in
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Prettyext'.LF.Debug.pp_typ)
      ~cmp:LF.Typ.equal typ' typ''
  in
  let test_cases =
    [ (mock_state_2, "nat")
    ; (mock_state_2, "(nat)")
    ; (mock_state_2, "((nat))")
    ; (mock_state_2, "nat -> nat")
    ; (mock_state_2, "nat -> nat -> nat")
    ; (mock_state_2, "(nat -> nat) -> nat")
    ; (mock_state_2, "nat <- nat -> nat")
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
    ; ( mock_state_6
      , "({x : exp} (x eq (x)) -> ((E (x : exp)) eq (F x))) -> ((lam) (\\x. \
         (E) x)) eq (lam (\\x. (F) x))" )
    ; (mock_state_6, "{x : exp} x eq x")
    ; (mock_state_6, "{x : exp} _ eq _")
    ; (mock_state_6, "{x : exp} (x : exp) eq _")
    ]
  in
  let tests =
    List.map
      (fun (elaboration_context, input) ->
        OUnit2.test_case @@ test elaboration_context input)
      test_cases
  in
  tests

let test_pp_term =
  let test elaboration_context input _test_ctxt =
    let term = parse_lf_term elaboration_context input in
    let term' =
      term |> Prettyext'.LF.remove_parentheses_term
      |> Prettyext'.LF.parenthesize_term
    in
    let term'' =
      parse_lf_term elaboration_context
        (Format.asprintf "%a" Prettyext'.LF.pp_term term')
    in
    OUnit2.assert_equal
      ~printer:(Format.asprintf "%a" Prettyext'.LF.Debug.pp_term)
      ~cmp:LF.Term.equal term' term''
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
    ]
  in
  let tests =
    List.map
      (fun (elaboration_context, input) ->
        OUnit2.test_case @@ test elaboration_context input)
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
