open OUnit2

let tests () =
  "Parser"
  >::: [ "Sub-parsers" >::: Test_sub_parsers.tests ()
       ; "Parsing pretty-printed signatures" >::: Test_pp.tests ()
       ; "Test HTML pretty-printing" >::: Test_html_pp.tests ()
       ]
