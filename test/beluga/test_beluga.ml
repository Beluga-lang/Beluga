open OUnit2

let () =
  run_test_tt_main
    ("Beluga"
    >::: [ Test_ShuntingYard.tests
         ; Test_parser_dictionary.tests
         ; Test_LF_parser.tests
         ])