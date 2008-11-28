open Core
open Frontend
open OUnit

let path = "../../examples/LF/"

let assert_is_parsable file_name =
  let parse file_name =
    Parser.parse_file ~name:(path ^ file_name) Parser.p_sgn_eoi in
  let check file_name =
    match parse file_name with
      | Common.InL _exn  -> false
      | Common.InR decls ->
          try
            let internal_decls = List.map Reconstruct.reconstruct_sgn_decl decls in
                Core.Check.check_sgn_decls internal_decls
              ; true
          with
            | _ -> false in
  let failure_msg = "failure checking: '" ^ file_name ^ "'" in
    bracket
      (fun  ()         -> file_name)
      (fun  file_name' -> assert_bool failure_msg (check file_name'))
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
    Printf.printf "Testing Checker\n"
  ; ignore (run_test_tt tests)
  ; print_newline ()
