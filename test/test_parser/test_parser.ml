open OUnit2

let () =
  run_test_tt_main
    ("Parser"
    >::: [ "Shunting-yard" >::: Test_shunting_yard.tests
         ; "Sub-parsers" >::: Test_sub_parsers.tests
         ; "Parsing pretty-printed signatures" >::: Test_pp.tests
         ])
