open OUnit2

let tests () =
  "Support"
  >::: [ Test_list.tests
       ; Test_list1.tests
       ; Test_list2.tests
       ; Test_option.tests
       ]
