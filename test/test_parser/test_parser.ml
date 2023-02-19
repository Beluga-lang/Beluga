open OUnit2

let () =
  run_test_tt_main
    ("Parser"
    >::: [ "Sub-parsers" >::: Test_sub_parsers.tests
         ; "Parsing pretty-printed signatures" >::: Test_pp.tests
         ])
