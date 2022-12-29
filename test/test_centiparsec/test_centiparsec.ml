open OUnit2

let () = run_test_tt_main ("Centiparsec" >::: [ Test_shunting_yard.tests ])
