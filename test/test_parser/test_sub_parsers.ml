open Test_beluga_parser_fixtures_lib
open Support
open Beluga_syntax
open Util
open Assert
open Beluga_parser
open Parser

let parse_only_lf_kind =
  parse_and_disambiguate
    ~parser:Parsing.(only lf_kind)
    ~disambiguator:Disambiguation.disambiguate_lf_kind

let parse_only_lf_typ =
  parse_and_disambiguate
    ~parser:Parsing.(only lf_typ)
    ~disambiguator:Disambiguation.disambiguate_lf_typ

let parse_only_lf_term =
  parse_and_disambiguate
    ~parser:Parsing.(only lf_term)
    ~disambiguator:Disambiguation.disambiguate_lf_term

let parse_only_clf_typ =
  parse_and_disambiguate
    ~parser:Parsing.(only clf_typ)
    ~disambiguator:Disambiguation.disambiguate_clf_typ

let parse_only_clf_term =
  parse_and_disambiguate
    ~parser:Parsing.(only clf_term)
    ~disambiguator:Disambiguation.disambiguate_clf_term

let parse_only_meta_typ =
  parse_and_disambiguate
    ~parser:Parsing.(only meta_type)
    ~disambiguator:Disambiguation.disambiguate_meta_typ

let parse_only_meta_object =
  parse_and_disambiguate
    ~parser:Parsing.(only meta_object)
    ~disambiguator:Disambiguation.disambiguate_meta_object

let parse_only_schema =
  parse_and_disambiguate
    ~parser:Parsing.(only schema)
    ~disambiguator:Disambiguation.disambiguate_schema

let parse_only_comp_kind =
  parse_and_disambiguate
    ~parser:Parsing.(only comp_kind)
    ~disambiguator:Disambiguation.disambiguate_comp_kind

let parse_only_comp_typ =
  parse_and_disambiguate
    ~parser:Parsing.(only comp_typ)
    ~disambiguator:Disambiguation.disambiguate_comp_typ

let parse_only_comp_expression =
  parse_and_disambiguate
    ~parser:Parsing.(only comp_expression)
    ~disambiguator:Disambiguation.disambiguate_comp_expression

let parse_only_signature_file =
  parse_and_disambiguate
    ~parser:Parsing.(only signature_file)
    ~disambiguator:Disambiguation.disambiguate_signature_file

let make_parser_state disambiguation_state location input =
  let initial_location = Location.start_position_as_location location in
  make_initial_state_from_string ~disambiguation_state ~initial_location
    ~input

let parser_ok_tests ~disambiguation_state_configuration_filename
    ~ok_inputs_filename ~ok_outputs_filename parse json_of_parse =
  let disambiguation_state =
    Disambiguation_state_deserialization.read_disambiguation_state
      disambiguation_state_configuration_filename
  in
  let ok_inputs_basename = Filename.basename ok_inputs_filename in
  let ok_inputs =
    Util.Files.read_test_case_inputs ~filename:ok_inputs_filename
  in
  let ok_outputs =
    Yojson.Safe.from_file ok_outputs_filename |> Yojson.Safe.Util.to_list
  in
  let test_success disambiguation_state location input expected _test_ctxt =
    let state = make_parser_state disambiguation_state location input in
    let parsed = eval parse state in
    let actual = json_of_parse parsed in
    assert_json_equal ~expected ~actual
  in
  let success_test_cases = List.combine ok_inputs ok_outputs in
  success_test_cases
  |> List.map (fun ((location, input), expected) ->
         let location = Location.set_filename ok_inputs_basename location in
         let open OUnit2 in
         input >:: test_success disambiguation_state location input expected)

let parser_failure_tests ~disambiguation_state_configuration_filename
    ~error_inputs_filename parse =
  let disambiguation_state =
    Disambiguation_state_deserialization.read_disambiguation_state
      disambiguation_state_configuration_filename
  in
  let error_inputs_basename = Filename.basename error_inputs_filename in
  let error_inputs =
    Util.Files.read_test_case_inputs ~filename:error_inputs_filename
  in
  let test_failure disambiguation_state location input _test_ctxt =
    let state = make_parser_state disambiguation_state location input in
    assert_exn (fun () -> ignore (eval parse state))
  in
  let failure_test_cases = error_inputs in
  failure_test_cases
  |> List.map (fun (location, input) ->
         let location =
           Location.set_filename error_inputs_basename location
         in
         let open OUnit2 in
         input >:: test_failure disambiguation_state location input)

let test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename ~ok_inputs_basename
    ~ok_outputs_basename ~error_inputs_basename parse json_of_parse () =
  let disambiguation_state_configuration_filename =
    Filename.concat fixtures_directory
      disambiguation_state_configuration_basename
  in
  let ok_inputs_filename =
    Filename.concat fixtures_directory ok_inputs_basename
  in
  let ok_outputs_filename =
    Filename.concat fixtures_directory ok_outputs_basename
  in
  let error_inputs_filename =
    Filename.concat fixtures_directory error_inputs_basename
  in
  let success_tests =
    parser_ok_tests ~disambiguation_state_configuration_filename
      ~ok_inputs_filename ~ok_outputs_filename parse json_of_parse
  and failure_tests =
    parser_failure_tests ~disambiguation_state_configuration_filename
      ~error_inputs_filename parse
  in
  let open OUnit2 in
  [ "success" >::: success_tests ] @ [ "failure" >::: failure_tests ]

let fixtures_directory = "test_parser/fixtures"

let disambiguation_state_configuration_basename = "disambiguation_state.json"

let test_lf_kind =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"lf_kinds_ok.input.bel"
    ~ok_outputs_basename:"lf_kinds_ok.output.json"
    ~error_inputs_basename:"lf_kinds_error.input.bel" parse_only_lf_kind
    Util.Synext_json.json_of_lf_kind

let test_lf_typ =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"lf_types_ok.input.bel"
    ~ok_outputs_basename:"lf_types_ok.output.json"
    ~error_inputs_basename:"lf_types_error.input.bel" parse_only_lf_typ
    Util.Synext_json.json_of_lf_typ

let test_lf_term =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"lf_terms_ok.input.bel"
    ~ok_outputs_basename:"lf_terms_ok.output.json"
    ~error_inputs_basename:"lf_terms_error.input.bel" parse_only_lf_term
    Util.Synext_json.json_of_lf_term

let test_clf_typ =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"clf_types_ok.input.bel"
    ~ok_outputs_basename:"clf_types_ok.output.json"
    ~error_inputs_basename:"clf_types_error.input.bel" parse_only_clf_typ
    Util.Synext_json.json_of_clf_typ

let test_clf_term =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"clf_terms_ok.input.bel"
    ~ok_outputs_basename:"clf_terms_ok.output.json"
    ~error_inputs_basename:"clf_terms_error.input.bel" parse_only_clf_term
    Util.Synext_json.json_of_clf_term

let test_meta_typ =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"meta_types_ok.input.bel"
    ~ok_outputs_basename:"meta_types_ok.output.json"
    ~error_inputs_basename:"meta_types_error.input.bel" parse_only_meta_typ
    Util.Synext_json.json_of_meta_typ

let test_meta_object =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"meta_objects_ok.input.bel"
    ~ok_outputs_basename:"meta_objects_ok.output.json"
    ~error_inputs_basename:"meta_objects_error.input.bel"
    parse_only_meta_object Util.Synext_json.json_of_meta_object

let test_schema =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"schemas_ok.input.bel"
    ~ok_outputs_basename:"schemas_ok.output.json"
    ~error_inputs_basename:"schemas_error.input.bel" parse_only_schema
    Util.Synext_json.json_of_schema

let test_comp_kind =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"comp_kinds_ok.input.bel"
    ~ok_outputs_basename:"comp_kinds_ok.output.json"
    ~error_inputs_basename:"comp_kinds_error.input.bel" parse_only_comp_kind
    Util.Synext_json.json_of_comp_kind

let test_comp_typ =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"comp_types_ok.input.bel"
    ~ok_outputs_basename:"comp_types_ok.output.json"
    ~error_inputs_basename:"comp_types_error.input.bel" parse_only_comp_typ
    Util.Synext_json.json_of_comp_typ

let test_comp_expression =
  test_parser ~fixtures_directory
    ~disambiguation_state_configuration_basename
    ~ok_inputs_basename:"comp_expressions_ok.input.bel"
    ~ok_outputs_basename:"comp_expressions_ok.output.json"
    ~error_inputs_basename:"comp_expressions_error.input.bel"
    parse_only_comp_expression Util.Synext_json.json_of_comp_expression

let tests () =
  let open OUnit2 in
  [ "LF Parsers"
    >::: [ "LF kind" >::: test_lf_kind ()
         ; "LF type" >::: test_lf_typ ()
         ; "LF term" >::: test_lf_term ()
         ]
  ; "Contextual LF Parsers"
    >::: [ "Contextual LF type" >::: test_clf_typ ()
         ; "Contextual LF term" >::: test_clf_term ()
         ]
  ; "Meta-Level Parsers"
    >::: [ "Meta-type" >::: test_meta_typ ()
         ; "Meta-object" >::: test_meta_object ()
         ; "Schema" >::: test_schema ()
         ]
  ; "Computation-Level Parsers"
    >::: [ "Computation Kind" >::: test_comp_kind ()
         ; "Computation Type" >::: test_comp_typ ()
         ; "Computation Expression" >::: test_comp_expression ()
         ]
  ]
