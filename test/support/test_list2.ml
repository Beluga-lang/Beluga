open OUnit2
open Support

let assert_raises_invalid_argument f =
  try
    ignore (f ());
    assert_failure "Expected exception [Invalid_argument _] to be raised"
  with Invalid_argument _ -> ()

let pp_list ppv ppf =
  Format.fprintf ppf "[@[%a@]]"
    (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ") ppv)

let int_list_printer = Format.asprintf "%a" (pp_list Int.pp)

let assert_int_list_equal =
  assert_equal ~cmp:(List.equal Int.equal) ~printer:int_list_printer

let int_pair_list_printer =
  Format.asprintf "%a" (pp_list (Pair.pp Int.pp Int.pp))

let assert_int_pair_list_equal =
  assert_equal
    ~cmp:(List.equal (Pair.equal Int.equal Int.equal))
    ~printer:int_pair_list_printer

let pp_int_list2 ppf =
  Format.fprintf ppf "[@[%a@]]"
    (List2.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ") Int.pp)

let int_list2_printer = Format.asprintf "%a" pp_int_list2

let assert_int_list2_equal =
  assert_equal ~cmp:(List2.equal Int.equal) ~printer:int_list2_printer

let int_pair_list2_printer =
  Format.asprintf "[%a]"
    (List2.pp
       ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ";@ ")
       (Pair.pp Int.pp Int.pp))

let assert_int_pair_list2_equal =
  assert_equal
    ~cmp:(List2.equal (Pair.equal Int.equal Int.equal))
    ~printer:int_pair_list2_printer

let test_last =
  let test input expected _test_ctxt =
    assert_equal expected (List2.last input)
  in
  let tests =
    [ (List2.pair 1 2, 2)
    ; (List2.from 1 2 [ 3 ], 3)
    ; (List2.from 1 2 [ 3; 4 ], 4)
    ]
    |> List.map (fun (input, expected) ->
           OUnit2.test_case @@ test input expected)
  in
  "last" >::: tests

let test_length =
  let test input expected _test_ctxt =
    assert_equal expected (List2.length input)
  in
  let tests =
    [ (List2.pair 1 2, 2)
    ; (List2.from 1 2 [ 3 ], 3)
    ; (List2.from 1 2 [ 3; 4 ], 4)
    ]
    |> List.map (fun (input, expected) ->
           OUnit2.test_case @@ test input expected)
  in
  "length" >::: tests

let test_iter =
  let test input _test_ctxt =
    let call_reverse_order = ref [] in
    List2.iter
      (fun x -> call_reverse_order := x :: !call_reverse_order)
      input;
    assert_int_list_equal (List2.to_list input)
      (List.rev !call_reverse_order)
  in
  let tests =
    [ List2.pair 1 2; List2.from 1 2 [ 3 ]; List2.from 1 2 [ 3; 4 ] ]
    |> List.map (fun input -> OUnit2.test_case @@ test input)
  in
  "iter" >::: tests

let test_iter2 =
  let test_success l1 l2 _test_ctxt =
    let call_reverse_order = ref [] in
    List2.iter2
      (fun x y -> call_reverse_order := (x, y) :: !call_reverse_order)
      l1 l2;
    assert_int_pair_list_equal
      (List2.to_list @@ List2.combine l1 l2)
      (List.rev !call_reverse_order)
  in
  let test_failure l1 l2 _test_ctxt =
    assert_raises_invalid_argument (fun () ->
        List2.iter2 (fun _ _ -> ()) l1 l2)
  in
  let tests_success =
    [ (List2.pair 1 2, List2.pair 1 2)
    ; (List2.from 1 2 [ 3; 4 ], List2.from 4 3 [ 2; 1 ])
    ]
    |> List.map (fun (l1, l2) ->
           Format.asprintf "List2.iter2 %a %a succeeds" pp_int_list2 l1
             pp_int_list2 l2
           >:: test_success l1 l2)
  in
  let tests_failure =
    [ (List2.pair 1 2, List2.from 1 2 [ 3 ])
    ; (List2.from 1 2 [ 3 ], List2.pair 1 2)
    ]
    |> List.map (fun (l1, l2) ->
           Format.asprintf "List2.iter2 %a %a fails" pp_int_list2 l1
             pp_int_list2 l2
           >:: test_failure l1 l2)
  in
  "iter2" >::: tests_success @ tests_failure

let test_rev =
  let test input expected _test_ctxt =
    assert_int_list2_equal expected (List2.rev input)
  in
  let tests =
    [ (List2.pair 1 2, List2.pair 2 1)
    ; (List2.from 1 2 [ 3 ], List2.from 3 2 [ 1 ])
    ; (List2.from 1 2 [ 3; 4 ], List2.from 4 3 [ 2; 1 ])
    ]
    |> List.map (fun (input, expected) ->
           OUnit2.test_case @@ test input expected)
  in
  "rev" >::: tests

let test_map =
  let test f input expected _test_ctxt =
    assert_int_list2_equal expected (List2.map f input)
  in
  let tests =
    [ ((fun x -> x + 1), List2.pair 1 2, List2.pair 2 3)
    ; ((fun x -> x - 1), List2.from 1 2 [ 3 ], List2.from 0 1 [ 2 ])
    ]
    |> List.map (fun (f, input, expected) ->
           OUnit2.test_case @@ test f input expected)
  in
  "map" >::: tests

let tests =
  "list2"
  >::: [ test_last; test_length; test_iter; test_iter2; test_rev; test_map ]
