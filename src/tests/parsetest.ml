open Core
open Frontend
open OUnit

let path = "../../examples/LF/"

let assert_is_parsable file_name =
  let parse file_name =
    match Parser.parse_file ~name:(path ^ file_name) Parser.p_sgn_eoi with
      | Common.InL _ -> false  (* parsing failed  *)
      | Common.InR _ -> true   (* parsing succeed *) in
  let failure_msg = "failure parsing: '" ^ file_name ^ "'" in
    bracket
      (fun  ()         -> file_name)
      (fun  file_name' -> assert_bool failure_msg (parse file_name'))
      (fun _file_name' -> Store.clear ())

let tests = "Parsing Test Suite" >:::
  [
    "arith.lf"         >:: assert_is_parsable "arith.lf"
  ; "cut-elim.lf"      >:: assert_is_parsable "cut-elim.lf"
  ; "kindtest.lf"      >:: assert_is_parsable "kindtest.lf"
  ; "lambda.lf"        >:: assert_is_parsable "lambda.lf"
  ; "mini-ml.lf"       >:: assert_is_parsable "mini-ml.lf"
  ; "simple-typing.lf" >:: assert_is_parsable "simple-typing.lf"
  ; "tpcert.lf"        >:: assert_is_parsable "tpcert.lf"
  ; "tpeval.lf"        >:: assert_is_parsable "tpeval.lf"
  ; "vsound.lf"        >:: assert_is_parsable "vsound.lf"
  ; "vsound2.lf"       >:: assert_is_parsable "vsound2.lf"
  ]

let run_tests () =
    Printf.printf "Testing Parser\n"
  ; ignore (run_test_tt tests)
  ; print_newline ()
