open OUnit2

let () =
  run_test_tt_main ("Support" >::: [ Test_list.tests; Test_list1.tests ])
