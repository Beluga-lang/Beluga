open Support

let assert_raises_invalid_argument f =
  try
    ignore (f ());
    OUnit2.assert_failure
      "Expected exception [Invalid_argument _] to be raised"
  with
  | Invalid_argument _ -> ()

let pp_print_list ppv ppf =
  Format.fprintf ppf "@[<hov 2>[%a]@]"
    (List.pp ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ";@ ") ppv)

let int_list_printer = Format.stringify (pp_print_list Int.pp)

let assert_int_list_equal =
  OUnit2.assert_equal ~cmp:(List.equal Int.equal) ~printer:int_list_printer

let int_list1_printer =
  Format.asprintf "@[<hov 2>[%a]@]"
    (List1.pp
       ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ";@ ")
       Int.pp)

let assert_int_list1_equal =
  OUnit2.assert_equal ~cmp:(List1.equal Int.equal) ~printer:int_list1_printer

let test_uncons =
  let test input expected _test_ctxt =
    OUnit2.assert_equal
      ~printer:(Pair.show Int.pp (List.pp Int.pp))
      ~cmp:(Pair.equal Int.equal (List.equal Int.equal))
      expected (List1.uncons input)
  in
  let test_cases =
    [ (List1.from 1 [], (1, []))
    ; (List1.from 1 [ 2 ], (1, [ 2 ]))
    ; (List1.from 1 [ 2; 3 ], (1, [ 2; 3 ]))
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case (test input expected))

let test_length =
  let test input expected _test_ctxt =
    OUnit2.assert_equal expected (List1.length input)
  in
  let test_cases =
    [ (List1.from 1 [], 1)
    ; (List1.from 1 [ 2 ], 2)
    ; (List1.from 1 [ 2; 3 ], 3)
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case (test input expected))

let test_rev =
  let test input expected _test_ctxt =
    assert_int_list1_equal expected (List1.rev input)
  in
  let test_cases =
    [ (List1.from 1 [], List1.from 1 [])
    ; (List1.from 1 [ 2 ], List1.from 2 [ 1 ])
    ; (List1.from 1 [ 2; 3 ], List1.from 3 [ 2; 1 ])
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case (test input expected))

let test_iter =
  let test input _test_ctxt =
    let call_reverse_order = ref [] in
    List1.iter
      (fun x -> call_reverse_order := x :: !call_reverse_order)
      input;
    assert_int_list_equal (List1.to_list input)
      (List.rev !call_reverse_order)
  in
  let test_cases =
    [ List1.from 1 []; List1.from 1 [ 2 ]; List1.from 1 [ 2; 3 ] ]
  in
  test_cases |> List.map (fun input -> OUnit2.test_case (test input))

let test_map =
  let test f input expected _test_ctxt =
    assert_int_list1_equal expected (List1.map f input)
  in
  let test_cases =
    [ ((( + ) 1, List1.from 1 [ 2; 3; 4; 5 ]), List1.from 2 [ 3; 4; 5; 6 ]) ]
  in
  test_cases
  |> List.map (fun ((f, input), expected) ->
         OUnit2.test_case (test f input expected))

let test_map2 =
  let test_success f l1 l2 expected _test_ctxt =
    assert_int_list1_equal expected (List1.map2 f l1 l2)
  and test_failure f l1 l2 _test_ctxt =
    assert_raises_invalid_argument (fun () -> List1.map2 f l1 l2)
  in
  let success_test_cases =
    [ ((( + ), List1.from 1 [ 2 ], List1.from 3 [ 4 ]), List1.from 4 [ 6 ]) ]
  and failure_test_cases =
    [ ((fun _ _ -> ()), List1.from 1 [ 2 ], List1.from 1 [])
    ; ((fun _ _ -> ()), List1.from 1 [], List1.from 1 [ 2 ])
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun ((f, l1, l2), expected) ->
           OUnit2.test_case (test_success f l1 l2 expected))
  and failure_tests =
    failure_test_cases
    |> List.map (fun (f, l1, l2) -> OUnit2.test_case (test_failure f l1 l2))
  in
  success_tests @ failure_tests

let test_flatten =
  let test_success l expected _test_ctxt =
    assert_int_list1_equal expected (List1.flatten l)
  in
  let success_test_cases =
    [ (List1.from (List1.singleton 1) [], List1.from 1 [])
    ; ( List1.from (List1.singleton 1) [ List1.from 2 [ 3 ] ]
      , List1.from 1 [ 2; 3 ] )
    ; ( List1.from (List1.from 1 [ 2; 3 ]) [ List1.from 4 [ 5; 6 ] ]
      , List1.from 1 [ 2; 3; 4; 5; 6 ] )
    ; ( List1.from
          (List1.from 1 [ 2; 3 ])
          [ List1.from 4 [ 5; 6 ]; List1.from 7 [ 8; 9 ] ]
      , List1.from 1 [ 2; 3; 4; 5; 6; 7; 8; 9 ] )
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (l, expected) ->
           OUnit2.test_case (test_success l expected))
  in
  success_tests

let tests =
  let open OUnit2 in
  "List1"
  >::: [ "uncons" >::: test_uncons
       ; "length" >::: test_length
       ; "rev" >::: test_rev
       ; "iter" >::: test_iter
       ; "map" >::: test_map
       ; "map2" >::: test_map2
       ; "flatten" >::: test_flatten
       ]
