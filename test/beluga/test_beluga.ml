open OUnit2

let () =
  run_test_tt_main
    ("Beluga"
    >::: [ Test_ShuntingYard.tests
         ; Test_qualified_identifier.tests
         ; Test_LF_parser.tests
         ; Test_CLF_parser.tests
         ; Test_prettyext'.tests
         ])
