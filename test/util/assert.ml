open Support

let assert_exn f =
  try
    ignore (f ());
    OUnit2.assert_failure "Expected an exception to be raised"
  with
  | _ -> ()

let show_json = Format.stringify (Yojson.Safe.pretty_print ~std:true)

let assert_json_equal ~expected ~actual =
  OUnit2.assert_equal ~printer:show_json ~cmp:Yojson.Safe.equal expected
    actual

let assert_equal_as_json to_json ~expected ~actual =
  let expected_json = to_json expected in
  let actual_json = to_json actual in
  assert_json_equal ~expected:expected_json ~actual:actual_json
