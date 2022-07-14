open OUnit2
open Support

let assert_raises_invalid_argument f =
  try
    ignore (f ());
    assert_failure "Expected exception [Invalid_argument _] to be raised"
  with Invalid_argument _ -> ()

let pp_print_list ppv ppf =
  Format.fprintf ppf "[%a]"
    (List.pp ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") ppv)

let int_list_printer = Format.asprintf "%a" (pp_print_list Int.pp)

let assert_int_list_equal =
  assert_equal ~cmp:(List.equal Int.equal) ~printer:int_list_printer

let int_list1_printer =
  Format.asprintf "[%a]"
    (List1.pp ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") Int.pp)

let assert_int_list1_equal =
  assert_equal ~cmp:(List1.equal Int.equal) ~printer:int_list1_printer

let test_uncons (input, expected) _ =
  assert_equal
    ~printer:(Pair.show Int.pp (List.pp Int.pp))
    ~cmp:(Pair.equal Int.equal (List.equal Int.equal))
    expected (List1.uncons input)

let test_length (input, expected) _ =
  assert_equal expected (List1.length input)

let test_rev (input, expected) _ =
  assert_int_list1_equal expected (List1.rev input)

let test_iter input _ =
  let call_reverse_order = ref [] in
  List1.iter (fun x -> call_reverse_order := x :: !call_reverse_order) input;
  assert_int_list_equal (List1.to_list input) (List.rev !call_reverse_order)

let test_map ((f, input), expected) _ =
  assert_int_list1_equal expected (List1.map f input)

let test_map2 ((f, l1, l2), expected) _ =
  assert_int_list1_equal expected (List1.map2 f l1 l2)

let tests =
  "list1"
  >::: [ "uncons"
         >::: ([ (List1.from 1 [], (1, []))
               ; (List1.from 1 [ 2 ], (1, [ 2 ]))
               ; (List1.from 1 [ 2; 3 ], (1, [ 2; 3 ]))
               ]
              |> List.map Fun.(test_uncons >> OUnit2.test_case))
       ; "length"
         >::: ([ (List1.from 1 [], 1)
               ; (List1.from 1 [ 2 ], 2)
               ; (List1.from 1 [ 2; 3 ], 3)
               ]
              |> List.map Fun.(test_length >> OUnit2.test_case))
       ; "rev"
         >::: ([ (List1.from 1 [], List1.from 1 [])
               ; (List1.from 1 [ 2 ], List1.from 2 [ 1 ])
               ; (List1.from 1 [ 2; 3 ], List1.from 3 [ 2; 1 ])
               ]
              |> List.map Fun.(test_rev >> OUnit2.test_case))
       ; "iter"
         >::: ([ List1.from 1 []; List1.from 1 [ 2 ]; List1.from 1 [ 2; 3 ] ]
              |> List.map Fun.(test_iter >> OUnit2.test_case))
       ; "map"
         >::: ([ ( (( + ) 1, List1.from 1 [ 2; 3; 4; 5 ])
                 , List1.from 2 [ 3; 4; 5; 6 ] )
               ]
              |> List.map Fun.(test_map >> OUnit2.test_case))
       ; "map2"
         >::: ("raises [Invalid_argument _] on lists of different lengths"
              >::: ([ ((fun _ _ -> ()), List1.from 1 [ 2 ], List1.from 1 [])
                    ; ((fun _ _ -> ()), List1.from 1 [], List1.from 1 [ 2 ])
                    ]
                   |> List.map (fun (f, l1, l2) ->
                          OUnit2.test_case (fun _ ->
                              assert_raises_invalid_argument (fun () ->
                                  List1.map2 f l1 l2)))))
              :: ([ ( (( + ), List1.from 1 [ 2 ], List1.from 3 [ 4 ])
                    , List1.from 4 [ 6 ] )
                  ]
                 |> List.map Fun.(test_map2 >> OUnit2.test_case))
       ]
