open OUnit2
open Support

let test_equal ((eq, l1, l2), expected) _ =
  assert_equal expected (List.equal eq l1 l2)

let pp_print_list ppv ppf =
  Format.fprintf ppf "[%a]"
    (List.pp ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") ppv)

let int_list_printer = Format.asprintf "%a" (pp_print_list Int.pp)

let int_pair_list_printer =
  Format.asprintf "%a" (pp_print_list (Pair.pp Int.pp Int.pp))

let assert_int_list_equal =
  assert_equal ~cmp:(List.equal Int.equal) ~printer:int_list_printer

let assert_int_pair_list_equal =
  assert_equal
    ~cmp:(List.equal @@ Pair.equal Int.equal Int.equal)
    ~printer:int_pair_list_printer

let test_last (input, expected) _ = assert_equal expected (List.last input)

let test_rev (input, expected) _ =
  assert_int_list_equal expected (List.rev input)

let test_pairs (input, expected) _ =
  assert_int_pair_list_equal expected (List.pairs input)

let test_concat_map ((f, input), expected) _ =
  assert_int_list_equal expected (List.concat_map f input)

let test_concat_mapi ((f, input), expected) _ =
  assert_int_list_equal expected (List.concat_mapi f input)

let test_index_of ((p, input), expected) _ =
  assert_equal ~cmp:(Option.equal Int.equal) expected (List.index_of p input)

let test_index (input, expected) _ =
  assert_equal
    ~cmp:(List.equal @@ Pair.equal Int.equal Int.equal)
    expected (List.index input)

let test_iter input _ =
  let call_reverse_order = ref [] in
  List.iter (fun x -> call_reverse_order := x :: !call_reverse_order) input;
  assert_int_list_equal input (List.rev !call_reverse_order)

let test_mapi2 ((f, l1, l2), expected) _ =
  assert_int_list_equal expected (List.mapi2 f l1 l2)

let test_ap ((xs, fs), expected) _ =
  assert_int_list_equal expected (List.ap xs fs)

let tests =
  "list"
  >::: [ "equal"
         >::: ([ (((fun _ _ -> true), [], []), true)
               ; (((fun _ _ -> true), [], [ 1 ]), false)
               ; (((fun _ _ -> true), [ 1 ], []), false)
               ; (((fun _ _ -> false), [ 1 ], [ 1 ]), false)
               ; ((Int.equal, [ 1; 2; 3 ], [ 1; 2; 3 ]), true)
               ; ((Int.equal, [ 1; 2; 3 ], [ 1; 3; 2 ]), false)
               ; ((Int.equal, [ 1; 3; 2 ], [ 1; 2; 3 ]), false)
               ]
              |> List.map Fun.(test_equal >> OUnit2.test_case))
       ; "last"
         >::: ( "raises `Invalid_argument \"List.last\"` on empty list"
              >:: fun _ ->
                assert_raises (Invalid_argument "List.last") (fun () ->
                    List.last []) )
              :: ([ ([ 1 ], 1); ([ 1; 2 ], 2); ([ 1; 2; 3 ], 3) ]
                 |> List.map Fun.(test_last >> OUnit2.test_case))
       ; "rev"
         >::: ([ ([], [])
               ; ([ 1 ], [ 1 ])
               ; ([ 1; 2 ], [ 2; 1 ])
               ; ([ 1; 2; 3 ], [ 3; 2; 1 ])
               ; ([ 1; 2; 3; 4 ], [ 4; 3; 2; 1 ])
               ]
              |> List.map Fun.(test_rev >> OUnit2.test_case))
       ; "pairs"
         >::: ([ ([], [])
               ; ([ 1 ], [])
               ; ([ 1; 2 ], [ (1, 2) ])
               ; ([ 1; 2; 3 ], [ (1, 2); (2, 3) ])
               ; ([ 1; 2; 3; 4 ], [ (1, 2); (2, 3); (3, 4) ])
               ]
              |> List.map Fun.(test_pairs >> OUnit2.test_case))
       ; "concat_map"
         >::: ([ (((fun _ -> []), [ 1; 2; 3 ]), [])
               ; (((fun x -> [ x; x + 1 ]), []), [])
               ; ( ((fun x -> [ x; x + 1 ]), [ 1; 3; 5 ])
                 , [ 1; 2; 3; 4; 5; 6 ] )
               ]
              |> List.map Fun.(test_concat_map >> OUnit2.test_case))
       ; "concat_mapi"
         >::: ([ (((fun _ _ -> []), [ 1; 2; 3 ]), [])
               ; (((fun _ x -> [ x; x + 1 ]), []), [])
               ; ( ((fun _ x -> [ x; x + 1 ]), [ 1; 3; 5 ])
                 , [ 1; 2; 3; 4; 5; 6 ] )
               ; (((fun i _ -> [ i ]), [ 0; 0; 0; 0 ]), [ 0; 1; 2; 3 ])
               ]
              |> List.map Fun.(test_concat_mapi >> OUnit2.test_case))
       ; "index_of"
         >::: ([ (((fun x -> x mod 2 = 0), [ 1; 2; 3 ]), Option.some 1)
               ; (((fun x -> x mod 2 = 0), [ 1; 3 ]), Option.none)
               ; (((fun x -> x mod 2 <> 0), [ 1; 3 ]), Option.some 0)
               ; ((Fun.const true, []), Option.none)
               ]
              |> List.map Fun.(test_index_of >> OUnit2.test_case))
       ; "index"
         >::: ([ ([ 1; 2; 3 ], [ (0, 1); (1, 2); (2, 3) ])
               ; ([ 1 ], [ (0, 1) ])
               ; ([], [])
               ]
              |> List.map Fun.(test_index >> OUnit2.test_case))
       ; "iter"
         >::: ([ [ 1; 2; 3 ]; [ 1 ]; [] ]
              |> List.map Fun.(test_iter >> OUnit2.test_case))
       ; "mapi2"
         >::: ("raises `Invalid_argument \"List.mapi2\"` on lists of \
                different lengths"
              >::: ([ ((fun _ _ _ -> ()), [ 1; 2 ], [ 1 ])
                    ; ((fun _ _ _ -> ()), [ 1 ], [ 1; 2 ])
                    ; ((fun _ _ _ -> ()), [], [ 1 ])
                    ; ((fun _ _ _ -> ()), [ 1 ], [])
                    ]
                   |> List.map (fun (f, l1, l2) ->
                          OUnit2.test_case (fun _ ->
                              assert_raises (Invalid_argument "List.mapi2")
                                (fun () -> List.mapi2 f l1 l2)))))
              :: ([ (((fun i _ _ -> i), [ 1; 2 ], [ 1; 2 ]), [ 0; 1 ])
                  ; (((fun _ -> ( + )), [ 1; 2 ], [ 3; 4 ]), [ 4; 6 ])
                  ]
                 |> List.map Fun.(test_mapi2 >> OUnit2.test_case))
       ; "ap"
         >::: ([ (([ 1; 2; 3 ], [ Fun.id; Fun.id; Fun.id ]), [ 1; 2; 3 ])
               ; (([ 1; 2; 3 ], [ ( + ) 1; ( + ) 2; ( + ) 3 ]), [ 2; 4; 6 ])
               ]
              |> List.map Fun.(test_ap >> OUnit2.test_case))
       ]
