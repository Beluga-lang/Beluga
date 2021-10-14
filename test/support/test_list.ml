open OUnit2
open Support

let test_equal ((eq, l1, l2), expected) _ =
  assert_equal (List.equal eq l1 l2) expected

let pp_print_list ppv ppf =
  Format.fprintf ppf "[%a]"
  (Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ")
    ppv)

let int_list_printer =
  Format.asprintf "%a" (pp_print_list Format.pp_print_int)

let int_pair_list_printer =
  Format.asprintf "%a"
    (pp_print_list (fun ppf (a, b) -> Format.fprintf ppf "(%d, %d)" a b))

let assert_int_list_equal =
  assert_equal
    ~cmp:(List.equal (=))
    ~printer:int_list_printer

let assert_int_pair_list_equal =
  assert_equal
    ~cmp:(List.equal (=))
    ~printer:int_pair_list_printer

let test_last (input, expected) _ =
  assert_equal (List.last input) expected

let test_pairs (input, expected) _ =
  assert_int_pair_list_equal (List.pairs input) expected

let test_concat_map ((f, input), expected) _ =
  assert_int_list_equal (List.concat_map f input) expected

let test_concat_mapi ((f, input), expected) _ =
  assert_int_list_equal (List.concat_mapi f input) expected

let test_index_of ((p, input), expected) _ =
  assert_equal ~cmp:(Option.equal (=)) (List.index_of p input) expected

let test_index (input, expected) _ =
  assert_equal ~cmp:(List.equal (=)) (List.index input) expected

let test_mapi2 ((f, l1, l2), expected) _ =
  assert_int_list_equal (List.mapi2 f l1 l2) expected

let test_ap ((xs, fs), expected) _ =
  assert_int_list_equal (List.ap xs fs) expected

let tests = "list" >:::
  [ "equal" >::: (
      [ (((fun _ _ -> true), [], []), true)
      ; (((fun _ _ -> true), [], [1]), false)
      ; (((fun _ _ -> true), [1], []), false)
      ; (((fun _ _ -> false), [1], [1]), false)
      ; (((=), [1; 2; 3], [1; 2; 3]), true)
      ; (((=), [1; 2; 3], [1; 3; 2]), false)
      ; (((=), [1; 3; 2], [1; 2; 3]), false)
      ]
      |> List.map Fun.(test_case ++ test_equal)
    )
  ; "last" >:::
    ("raises `Invalid_argument \"List.last\"` on empty list" >::
      fun _ ->
        assert_raises
          (Invalid_argument "List.last")
          (fun () -> List.last [])
    ) :: (
      [ ([1], 1)
      ; ([1; 2], 2)
      ; ([1; 2; 3], 3)
      ]
      |> List.map Fun.(test_case ++ test_last)
    )
  ; "pairs" >::: (
      [ ([], [])
      ; ([1], [])
      ; ([1; 2], [(1, 2)])
      ; ([1; 2; 3], [(1, 2); (2, 3)])
      ; ([1; 2; 3; 4], [(1, 2); (2, 3); (3, 4)])
      ]
      |> List.map Fun.(test_case ++ test_pairs)
    )
  ; "concat_map" >::: (
      [ (((fun _ -> []), [1; 2; 3]), [])
      ; (((fun x -> [x; x + 1]), []), [])
      ; (((fun x -> [x; x + 1]), [1; 3; 5]), [1; 2; 3; 4; 5; 6])
      ]
      |> List.map Fun.(test_case ++ test_concat_map)
    )
  ; "concat_mapi" >::: (
      [ (((fun _ _ -> []), [1; 2; 3]), [])
      ; (((fun _ x -> [x; x + 1]), []), [])
      ; (((fun _ x -> [x; x + 1]), [1; 3; 5]), [1; 2; 3; 4; 5; 6])
      ; (((fun i _ -> [i]), [0; 0; 0; 0]), [0; 1; 2; 3])
      ]
      |> List.map Fun.(test_case ++ test_concat_mapi)
    )
    ; "index_of" >::: (
      [ (((fun x -> x mod 2 = 0), [1; 2; 3]), Option.some 1)
      ; (((fun x -> x mod 2 = 0), [1; 3]), Option.none)
      ; (((fun x -> x mod 2 != 0), [1; 3]), Option.some 0)
      ; (((Fun.const true), []), Option.none)
      ]
      |> List.map Fun.(test_case ++ test_index_of)
    )
  ; "index" >::: (
      [ ([1; 2; 3], [(0, 1); (1, 2); (2, 3)])
      ; ([1], [(0, 1)])
      ; ([], [])
      ]
      |> List.map Fun.(test_case ++ test_index)
    )
  ; "mapi2" >:::
    ("raises `Invalid_argument \"List.mapi2\"` on lists of different lengths" >::: (
        [ ((fun _ _ _ -> ()), [1; 2], [1])
        ; ((fun _ _ _ -> ()), [1], [1; 2])
        ; ((fun _ _ _ -> ()), [], [1])
        ; ((fun _ _ _ -> ()), [1], [])
        ] |> List.map
          (fun (f, l1, l2) ->
            test_case (fun _ ->
              assert_raises
              (Invalid_argument "List.mapi2")
                (fun () -> List.mapi2 f l1 l2))
          )
      )
      ) :: (
      [ (((fun i _ _ -> i), [1; 2], [1; 2]), [0; 1])
      ; (((fun _ x y -> (x + y)), [1; 2], [3; 4]), [4; 6])
      ]
      |> List.map Fun.(test_case ++ test_mapi2)
    )
  ; "ap" >::: (
      [ (([1; 2; 3], [Fun.id; Fun.id; Fun.id]), [1; 2; 3])
      ]
      |> List.map Fun.(test_case ++ test_ap)
    )
  ]
