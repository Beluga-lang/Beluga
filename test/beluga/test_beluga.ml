open OUnit2

let () = run_test_tt_main ("Beluga" >::: [ Test_ShuntingYard.tests ])
