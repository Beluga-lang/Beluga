open Support

let assert_raises_invalid_argument f =
  try
    ignore (f ());
    OUnit2.assert_failure
      "Expected exception [Invalid_argument _] to be raised"
  with
  | Invalid_argument _ -> ()

let pp_print_list ppv ppf =
  Format.fprintf ppf "[%a]"
    (List.pp ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") ppv)

let int_list_printer = Format.stringify (pp_print_list Int.pp)

let int_pair_list_printer =
  Format.stringify (pp_print_list (Pair.pp Int.pp Int.pp))

let assert_int_list_equal =
  OUnit2.assert_equal ~cmp:(List.equal Int.equal) ~printer:int_list_printer

let assert_int_pair_list_equal =
  OUnit2.assert_equal
    ~cmp:(List.equal (Pair.equal Int.equal Int.equal))
    ~printer:int_pair_list_printer

let test_equal =
  let test eq l1 l2 expected _test_ctxt =
    OUnit2.assert_equal expected (List.equal eq l1 l2)
  in
  let test_cases =
    [ (((fun _ _ -> true), [], []), true)
    ; (((fun _ _ -> true), [], [ 1 ]), false)
    ; (((fun _ _ -> true), [ 1 ], []), false)
    ; (((fun _ _ -> false), [ 1 ], [ 1 ]), false)
    ; ((Int.equal, [ 1; 2; 3 ], [ 1; 2; 3 ]), true)
    ; ((Int.equal, [ 1; 2; 3 ], [ 1; 3; 2 ]), false)
    ; ((Int.equal, [ 1; 3; 2 ], [ 1; 2; 3 ]), false)
    ]
  in
  test_cases
  |> List.map (fun ((eq, l1, l2), expected) ->
         OUnit2.test_case (test eq l1 l2 expected))

let test_last =
  let test_success input expected _test_ctxt =
    OUnit2.assert_equal expected (List.last input)
  in
  let success_test_cases =
    [ ([ 1 ], 1)
    ; ([ 1; 2 ], 2)
    ; ([ 1; 2; 3 ], 3)
    ; ([ 1; 2; 3; 4 ], 4)
    ; ([ 1; 2; 3; 4; 5 ], 5)
    ]
  in
  let success_tests =
    success_test_cases
    |> List.map (fun (input, expected) ->
           OUnit2.test_case (test_success input expected))
  and failure_tests =
    let test_failure_on_empty_list =
      let open OUnit2 in
      "raises [Invalid_argument _] on empty list" >:: fun _test_ctxt ->
      assert_raises_invalid_argument (fun () -> List.last [])
    in
    [ test_failure_on_empty_list ]
  in
  success_tests @ failure_tests

let test_rev =
  let test input expected _test_ctxt =
    assert_int_list_equal expected (List.rev input)
  in
  let test_cases =
    [ ([], [])
    ; ([ 1 ], [ 1 ])
    ; ([ 1; 2 ], [ 2; 1 ])
    ; ([ 1; 2; 3 ], [ 3; 2; 1 ])
    ; ([ 1; 2; 3; 4 ], [ 4; 3; 2; 1 ])
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case (test input expected))

let test_pairs =
  let test input expected _test_ctxt =
    assert_int_pair_list_equal expected (List.pairs input)
  in
  let test_cases =
    [ ([], [])
    ; ([ 1 ], [])
    ; ([ 1; 2 ], [ (1, 2) ])
    ; ([ 1; 2; 3 ], [ (1, 2); (2, 3) ])
    ; ([ 1; 2; 3; 4 ], [ (1, 2); (2, 3); (3, 4) ])
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case (test input expected))

let test_concat_map =
  let test f input expected _test_ctxt =
    assert_int_list_equal expected (List.concat_map f input)
  in
  let test_cases =
    [ (((fun _ -> []), [ 1; 2; 3 ]), [])
    ; (((fun x -> [ x; x + 1 ]), []), [])
    ; (((fun x -> [ x; x + 1 ]), [ 1; 3; 5 ]), [ 1; 2; 3; 4; 5; 6 ])
    ]
  in
  test_cases
  |> List.map (fun ((f, input), expected) ->
         OUnit2.test_case (test f input expected))

let test_concat_mapi =
  let test f input expected _test_ctxt =
    assert_int_list_equal expected (List.concat_mapi f input)
  in
  let test_cases =
    [ (((fun _ _ -> []), [ 1; 2; 3 ]), [])
    ; (((fun _ x -> [ x; x + 1 ]), []), [])
    ; (((fun _ x -> [ x; x + 1 ]), [ 1; 3; 5 ]), [ 1; 2; 3; 4; 5; 6 ])
    ; (((fun i _ -> [ i ]), [ 0; 0; 0; 0 ]), [ 0; 1; 2; 3 ])
    ]
  in
  test_cases
  |> List.map (fun ((f, input), expected) ->
         OUnit2.test_case (test f input expected))

let test_index_of =
  let test p input expected _test_ctxt =
    OUnit2.assert_equal ~cmp:(Option.equal Int.equal) expected
      (List.index_of p input)
  in
  let test_cases =
    [ (((fun x -> x mod 2 = 0), [ 1; 2; 3 ]), Option.some 1)
    ; (((fun x -> x mod 2 = 0), [ 1; 3 ]), Option.none)
    ; (((fun x -> x mod 2 <> 0), [ 1; 3 ]), Option.some 0)
    ; ((Fun.const true, []), Option.none)
    ]
  in
  test_cases
  |> List.map (fun ((p, input), expected) ->
         OUnit2.test_case (test p input expected))

let test_index =
  let test input expected _test_ctxt =
    OUnit2.assert_equal
      ~cmp:(List.equal (Pair.equal Int.equal Int.equal))
      expected (List.index input)
  in
  let test_cases =
    [ ([ 1; 2; 3 ], [ (0, 1); (1, 2); (2, 3) ])
    ; ([ 1 ], [ (0, 1) ])
    ; ([], [])
    ]
  in
  test_cases
  |> List.map (fun (input, expected) ->
         OUnit2.test_case (test input expected))

let test_iter =
  let test input _test_ctxt =
    let call_reverse_order = ref [] in
    List.iter (fun x -> call_reverse_order := x :: !call_reverse_order) input;
    assert_int_list_equal input (List.rev !call_reverse_order)
  in
  let test_cases = [ [ 1; 2; 3 ]; [ 1 ]; [] ] in
  test_cases |> List.map (fun input -> OUnit2.test_case (test input))

let test_mapi2 =
  let test_success f l1 l2 expected _test_ctxt =
    assert_int_list_equal expected (List.mapi2 f l1 l2)
  and test_failure f l1 l2 _test_ctxt =
    assert_raises_invalid_argument (fun () -> List.mapi2 f l1 l2)
  in
  let success_test_cases =
    [ (((fun i _ _ -> i), [ 1; 2 ], [ 1; 2 ]), [ 0; 1 ])
    ; (((fun _ -> ( + )), [ 1; 2 ], [ 3; 4 ]), [ 4; 6 ])
    ]
  and failure_test_cases =
    [ ((fun _ _ _ -> ()), [ 1; 2 ], [ 1 ])
    ; ((fun _ _ _ -> ()), [ 1 ], [ 1; 2 ])
    ; ((fun _ _ _ -> ()), [], [ 1 ])
    ; ((fun _ _ _ -> ()), [ 1 ], [])
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

let test_ap =
  let test xs fs expected _test_ctxt =
    assert_int_list_equal expected (List.ap xs fs)
  in
  let test_cases =
    [ (([ 1; 2; 3 ], [ Fun.id; Fun.id; Fun.id ]), [ 1; 2; 3 ])
    ; (([ 1; 2; 3 ], [ ( + ) 1; ( + ) 2; ( + ) 3 ]), [ 2; 4; 6 ])
    ]
  in
  test_cases
  |> List.map (fun ((xs, fs), expected) ->
         OUnit2.test_case (test xs fs expected))

let tests =
  let open OUnit2 in
  "List"
  >::: [ "equal" >::: test_equal
       ; "last" >::: test_last
       ; "rev" >::: test_rev
       ; "pairs" >::: test_pairs
       ; "concat_map" >::: test_concat_map
       ; "concat_mapi" >::: test_concat_mapi
       ; "index_of" >::: test_index_of
       ; "index" >::: test_index
       ; "iter" >::: test_iter
       ; "mapi2" >::: test_mapi2
       ; "ap" >::: test_ap
       ]
