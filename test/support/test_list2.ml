open Support

let assert_raises_invalid_argument f =
  try
    ignore (f ());
    OUnit2.assert_failure
      "Expected exception [Invalid_argument _] to be raised"
  with Invalid_argument _ -> ()

let pp_list ppv ppf =
  Format.fprintf ppf "[@[%a@]]"
    (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ") ppv)

let int_list_printer = Format.asprintf "%a" (pp_list Int.pp)

let assert_int_list_equal =
  OUnit2.assert_equal ~cmp:(List.equal Int.equal) ~printer:int_list_printer

let int_pair_list_printer =
  Format.asprintf "%a" (pp_list (Pair.pp Int.pp Int.pp))

let assert_int_pair_list_equal =
  OUnit2.assert_equal
    ~cmp:(List.equal (Pair.equal Int.equal Int.equal))
    ~printer:int_pair_list_printer

let pp_int_list2 ppf =
  Format.fprintf ppf "[@[%a@]]"
    (List2.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ") Int.pp)

let int_list2_printer = Format.asprintf "%a" pp_int_list2

let assert_int_list2_equal =
  OUnit2.assert_equal ~cmp:(List2.equal Int.equal) ~printer:int_list2_printer

let int_pair_list2_printer =
  Format.asprintf "[%a]"
    (List2.pp
       ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ";@ ")
       (Pair.pp Int.pp Int.pp))

let assert_int_pair_list2_equal =
  OUnit2.assert_equal
    ~cmp:(List2.equal (Pair.equal Int.equal Int.equal))
    ~printer:int_pair_list2_printer

let test_last =
  let test input expected _test_ctxt =
    OUnit2.assert_equal expected (List2.last input)
  in
  let test_cases =
    [ (List2.pair 1 2, 2)
    ; (List2.from 1 2 [ 3 ], 3)
    ; (List2.from 1 2 [ 3; 4 ], 4)
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case @@ test input expected)

let test_length =
  let test input expected _test_ctxt =
    OUnit2.assert_equal expected (List2.length input)
  in
  let test_cases =
    [ (List2.pair 1 2, 2)
    ; (List2.from 1 2 [ 3 ], 3)
    ; (List2.from 1 2 [ 3; 4 ], 4)
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case @@ test input expected)

let test_iter =
  let test input _test_ctxt =
    let call_reverse_order = ref [] in
    List2.iter
      (fun x -> call_reverse_order := x :: !call_reverse_order)
      input;
    assert_int_list_equal (List2.to_list input)
      (List.rev !call_reverse_order)
  in
  let test_cases =
    [ List2.pair 1 2
    ; List2.from 1 2 [ 3 ]
    ; List2.from 1 2 [ 3; 4 ]
    ; List2.from 1 2 [ 3; 4; 5 ]
    ]
  in
  test_cases |> List.map (fun input -> OUnit2.test_case @@ test input)

let test_iter2 =
  let test_success l1 l2 _test_ctxt =
    let call_reverse_order = ref [] in
    List2.iter2
      (fun x y -> call_reverse_order := (x, y) :: !call_reverse_order)
      l1 l2;
    assert_int_pair_list_equal
      (List2.to_list @@ List2.combine l1 l2)
      (List.rev !call_reverse_order)
  and test_failure l1 l2 _test_ctxt =
    assert_raises_invalid_argument (fun () ->
        List2.iter2 (fun _ _ -> ()) l1 l2)
  in
  let success_test_cases =
    [ (List2.pair 1 2, List2.pair 1 2)
    ; (List2.from 1 2 [ 3; 4 ], List2.from 4 3 [ 2; 1 ])
    ]
  and failure_test_cases =
    [ (List2.pair 1 2, List2.from 1 2 [ 3 ])
    ; (List2.from 1 2 [ 3 ], List2.pair 1 2)
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (l1, l2) ->
           let open OUnit2 in
           Format.asprintf "[List2.iter2 %a %a] succeeds" pp_int_list2 l1
             pp_int_list2 l2
           >:: test_success l1 l2)
  and failure_tests =
    failure_test_cases
    |> List.map (fun (l1, l2) ->
           let open OUnit2 in
           Format.asprintf "[List2.iter2 %a %a] fails" pp_int_list2 l1
             pp_int_list2 l2
           >:: test_failure l1 l2)
  in
  success_tests @ failure_tests

let test_rev =
  let test input expected _test_ctxt =
    assert_int_list2_equal expected (List2.rev input)
  in
  let tests_cases =
    [ (List2.pair 1 2, List2.pair 2 1)
    ; (List2.from 1 2 [ 3 ], List2.from 3 2 [ 1 ])
    ; (List2.from 1 2 [ 3; 4 ], List2.from 4 3 [ 2; 1 ])
    ]
  in
  tests_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case @@ test input expected)

let test_map =
  let test f input expected _test_ctxt =
    assert_int_list2_equal expected (List2.map f input)
  in
  let test_cases =
    [ ((fun x -> x + 1), List2.pair 1 2, List2.pair 2 3)
    ; ((fun x -> x - 1), List2.from 1 2 [ 3 ], List2.from 0 1 [ 2 ])
    ]
  in
  test_cases
  |> List.map (fun (f, input, expected) ->
         OUnit2.test_case @@ test f input expected)

let tests =
  let open OUnit2 in
  "List2"
  >::: [ "last" >::: test_last
       ; "length" >::: test_length
       ; "iter" >::: test_iter
       ; "iter2" >::: test_iter2
       ; "rev" >::: test_rev
       ; "map" >::: test_map
       ]
