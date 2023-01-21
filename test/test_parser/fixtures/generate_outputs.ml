open Test_beluga_parser_fixtures_lib
open Beluga_syntax
module Parser = Beluga_parser.Simple

let usage_message =
  {|
  generate_outputs
    --state=<file>
    --inputs=<file>
    --output=<file>
    --variant=<variant>


  <variant> can be one of:
    - "lf_kind"
    - "lf_type"
    - "lf_term"
    - "clf_type"
    - "clf_term"
    - "clf_term_pattern"
    - "meta_type"
    - "meta_object"
    - "schema"
  |}

let parse_lf_kind_to_json state =
  let kind = Beluga_parser.Simple.parse_only_lf_kind state in
  Util.Synext_json.json_of_lf_kind kind

let parse_lf_typ_to_json state =
  let typ = Beluga_parser.Simple.parse_only_lf_typ state in
  Util.Synext_json.json_of_lf_typ typ

let parse_lf_term_to_json state =
  let term = Beluga_parser.Simple.parse_only_lf_term state in
  Util.Synext_json.json_of_lf_term term

let parse_clf_typ_to_json state =
  let typ = Beluga_parser.Simple.parse_only_clf_typ state in
  Util.Synext_json.json_of_clf_typ typ

let parse_clf_term_to_json state =
  let term = Beluga_parser.Simple.parse_only_clf_term state in
  Util.Synext_json.json_of_clf_term term

let parse_meta_type_to_json state =
  let typ = Beluga_parser.Simple.parse_only_meta_typ state in
  Util.Synext_json.json_of_meta_typ typ

let parse_meta_object_to_json state =
  let object_ = Beluga_parser.Simple.parse_only_meta_object state in
  Util.Synext_json.json_of_meta_object object_

let parse_schema_to_json state =
  let schema = Beluga_parser.Simple.parse_only_schema state in
  Util.Synext_json.json_of_schema schema

let parse_comp_kind_to_json state =
  let kind = Beluga_parser.Simple.parse_only_comp_kind state in
  Util.Synext_json.json_of_comp_kind kind

let parse_comp_typ_to_json state =
  let typ = Beluga_parser.Simple.parse_only_comp_typ state in
  Util.Synext_json.json_of_comp_typ typ

exception Unsupported_variant of string

let lookup_parser variant =
  match variant with
  | "lf_kind" -> parse_lf_kind_to_json
  | "lf_type" -> parse_lf_typ_to_json
  | "lf_term" -> parse_lf_term_to_json
  | "clf_type" -> parse_clf_typ_to_json
  | "clf_term" -> parse_clf_term_to_json
  | "meta_type" -> parse_meta_type_to_json
  | "meta_object" -> parse_meta_object_to_json
  | "schema" -> parse_schema_to_json
  | "comp_kind" -> parse_comp_kind_to_json
  | "comp_typ" -> parse_comp_typ_to_json
  | variant -> raise (Unsupported_variant variant)

let generate_outputs ~state_filename ~input_filename ~output_filename
    ~variant =
  let parse_test_case = lookup_parser variant in
  let test_cases =
    Util.Files.read_test_case_inputs ~filename:input_filename
  in
  let disambiguation_state =
    Disambiguation_state_deserialization.read_disambiguation_state
      state_filename
  in
  let input_basename = Filename.basename input_filename in
  let outputs =
    `List
      (List.map
         (fun (location, input) ->
           let initial_location =
             location |> Location.start_position_as_location
             |> Location.set_filename input_basename
           in
           let state =
             Parser.make_initial_state_from_string ~disambiguation_state
               ~initial_location ~input
           in
           parse_test_case state)
         test_cases)
  in
  Support.Files.with_pp_to_file output_filename (fun ppf ->
      Yojson.Safe.pretty_print ~std:true ppf outputs)

let () =
  let state_filename = ref "" in
  let input_filename = ref "" in
  let output_filename = ref "" in
  let variant = ref "" in
  let cli_arguments_specification =
    [ ("--state", Arg.Set_string state_filename, "Disambiguation state file")
    ; ("--inputs", Arg.Set_string input_filename, "Parser inputs file")
    ; ( "--output"
      , Arg.Set_string output_filename
      , "Serialized ASTs output file" )
    ; ("--variant", Arg.Set_string variant, "Parser variant to use")
    ]
  in
  Arg.parse cli_arguments_specification
    (fun argument -> raise (Invalid_argument argument))
    usage_message;
  Format.fprintf Format.std_formatter "Regenerating \"%s\" ...@."
    !output_filename;
  generate_outputs ~state_filename:!state_filename
    ~input_filename:!input_filename ~output_filename:!output_filename
    ~variant:!variant
