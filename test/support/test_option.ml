open Support

let int_option_printer = Format.asprintf "%a" (Option.pp Int.pp)

let assert_int_option_equal =
  OUnit2.assert_equal ~cmp:(Option.equal Int.equal)
    ~printer:int_option_printer

let unit_option_printer =
  Format.asprintf "%a" (Option.pp (fun ppf () -> Format.fprintf ppf "()"))

let assert_unit_option_equal =
  OUnit2.assert_equal
    ~cmp:(Option.equal Stdlib.( = ))
    ~printer:unit_option_printer

let test_from_predicate =
  let test predicate value expected _test_ctxt =
    assert_int_option_equal expected (Option.from_predicate predicate value)
  in
  let test_cases =
    [ ((fun x -> Int.(x >= 0)), 0, Option.some 0)
    ; ((fun x -> Int.(x >= 0)), -1, Option.none)
    ]
  in
  test_cases
  |> List.map (fun (predicate, value, expected) ->
         OUnit2.test_case @@ test predicate value expected)

let test_of_bool =
  let test_is_some_when_true _test_ctxt =
    assert_unit_option_equal (Option.some ()) (Option.of_bool true)
  and test_is_none_when_false _test_ctxt =
    assert_unit_option_equal Option.none (Option.of_bool false)
  in
  [ test_is_some_when_true; test_is_none_when_false ]
  |> List.map OUnit2.test_case

let test_lazy_alt =
  let test_does_not_initialy_force_arguments _test_ctxt =
    let o1 = lazy (Option.some 1)
    and o2 = lazy (Option.some 2) in
    let o = Option.lazy_alt o1 o2 in
    OUnit2.assert_bool "result is forced" (Bool.not @@ Lazy.is_val o);
    OUnit2.assert_bool "first argument is forced" (Bool.not @@ Lazy.is_val o1);
    OUnit2.assert_bool "second argument is forced"
      (Bool.not @@ Lazy.is_val o2)
  and test_does_not_unnecessarily_force_second_argument _test_ctxt =
    let o1 = lazy (Option.some 1)
    and o2 = lazy (Option.some 2) in
    ignore (Lazy.force @@ Option.lazy_alt o1 o2 : Int.t Option.t);
    OUnit2.assert_bool "first argument is not forced" (Lazy.is_val o1);
    OUnit2.assert_bool "second argument is forced"
      (Bool.not @@ Lazy.is_val o2)
  and test o1 o2 expected _test_ctxt =
    assert_int_option_equal (Lazy.force expected)
      (Lazy.force @@ Option.lazy_alt o1 o2)
  in
  let test_cases =
    [ (lazy (Option.some 1), lazy (Option.some 2), lazy (Option.some 1))
    ; (lazy (Option.some 1), lazy Option.none, lazy (Option.some 1))
    ; (lazy Option.none, lazy (Option.some 2), lazy (Option.some 2))
    ; (lazy Option.none, lazy Option.none, lazy Option.none)
    ]
  in
  ([ test_does_not_initialy_force_arguments
   ; test_does_not_unnecessarily_force_second_argument
   ]
  |> List.map OUnit2.test_case)
  @ (test_cases
    |> List.map (fun (o1, o2, expected) ->
           OUnit2.test_case @@ test o1 o2 expected))

let tests =
  let open OUnit2 in
  "Option"
  >::: [ "from_predicate" >::: test_from_predicate
       ; "of_bool" >::: test_of_bool
       ; "lazy_alt" >::: test_lazy_alt
       ]
