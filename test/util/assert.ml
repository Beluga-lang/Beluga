open Support
open Beluga_syntax

exception Did_not_raise

let null_formatter = Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())

let assert_exn f =
  try
    ignore (f ());
    raise Did_not_raise
  with
  | Did_not_raise ->
      OUnit2.assert_failure "Expected an exception to be raised"
  | exn -> (
      try
        (* For coverage analysis, find a printer for the uncaught
           exception *)
        let printer = Error.find_printer exn in
        Format.fprintf null_formatter "%t@." printer
      with
      | _ -> ())

let show_json = Format.stringify (Yojson.Safe.pretty_print ~std:true)

let assert_json_equal ~expected ~actual =
  OUnit2.assert_equal ~printer:show_json ~cmp:Yojson.Safe.equal expected
    actual

let assert_equal_as_json to_json ~expected ~actual =
  let expected_json = to_json expected in
  let actual_json = to_json actual in
  assert_json_equal ~expected:expected_json ~actual:actual_json
