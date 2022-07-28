open OUnit2
open Support

let int_option_printer = Format.asprintf "%a" (Option.pp Int.pp)

let assert_int_option_equal =
  assert_equal ~cmp:(Option.equal Int.equal) ~printer:int_option_printer

let unit_option_printer =
  Format.asprintf "%a" (Option.pp (fun ppf () -> Format.fprintf ppf "()"))

let assert_unit_option_equal =
  assert_equal ~cmp:(Option.equal Stdlib.( = )) ~printer:unit_option_printer

let test_from_predicate (predicate, value, expected) _ =
  assert_int_option_equal expected (Option.from_predicate predicate value)

let test_lazy_alt_does_not_initialy_force_arguments _ =
  let o1 = lazy (Option.some 1)
  and o2 = lazy (Option.some 2) in
  let o = Option.lazy_alt o1 o2 in
  assert_bool "result is forced" (Bool.not @@ Lazy.is_val o);
  assert_bool "first argument is forced" (Bool.not @@ Lazy.is_val o1);
  assert_bool "second argument is forced" (Bool.not @@ Lazy.is_val o2)

let test_lazy_alt_does_not_unnecessarily_force_second_argument _ =
  let o1 = lazy (Option.some 1)
  and o2 = lazy (Option.some 2) in
  ignore (Lazy.force @@ Option.lazy_alt o1 o2 : Int.t Option.t);
  assert_bool "first argument is not forced" (Lazy.is_val o1);
  assert_bool "second argument is forced" (Bool.not @@ Lazy.is_val o2)

let test_lazy_alt (o1, o2, expected) _ =
  assert_int_option_equal (Lazy.force expected)
    (Lazy.force @@ Option.lazy_alt o1 o2)

let tests =
  "Option"
  >::: [ "[from_predicate p o]"
         >::: ([ ((fun x -> Int.(x >= 0)), 0, Option.some 0)
               ; ((fun x -> Int.(x >= 0)), -1, Option.none)
               ]
              |> List.map Fun.(test_from_predicate >> OUnit2.test_case))
       ; "[of_bool b]"
         >::: [ ( "is [Some ()] if [b] is [true]" >:: fun _ ->
                  assert_unit_option_equal (Option.some ())
                    (Option.of_bool true) )
              ; ( "is [None] if [b] is [false]" >:: fun _ ->
                  assert_unit_option_equal Option.none (Option.of_bool false)
                )
              ]
       ; "[lazy_alt o1 o2]"
         >::: [ "does not force [o1] or [o2] when called"
                >:: test_lazy_alt_does_not_unnecessarily_force_second_argument
              ; "does not force [o2] if [o1] is [Some v]"
                >:: test_lazy_alt_does_not_unnecessarily_force_second_argument
              ]
              @ ([ ( lazy (Option.some 1)
                   , lazy (Option.some 2)
                   , lazy (Option.some 1) )
                 ; ( lazy (Option.some 1)
                   , lazy Option.none
                   , lazy (Option.some 1) )
                 ; ( lazy Option.none
                   , lazy (Option.some 2)
                   , lazy (Option.some 2) )
                 ; (lazy Option.none, lazy Option.none, lazy Option.none)
                 ]
                |> List.map Fun.(test_lazy_alt >> OUnit2.test_case))
       ]