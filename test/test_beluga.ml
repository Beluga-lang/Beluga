let () =
  let open OUnit2 in
  run_test_tt_main
    ("Beluga" >::: [ Test_support.tests (); Test_parser.tests () ])
