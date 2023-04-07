open Test_beluga_parser_fixtures_lib
open Beluga_syntax
open Util.Synext_json
open Beluga_parser.Mutable

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
    - "comp_kind"
    - "comp_typ"
    - "comp_expression"
  |}

let parse_lf_kind_to_json = parse_only_lf_kind $> json_of_lf_kind

let parse_lf_typ_to_json = parse_only_lf_typ $> json_of_lf_typ

let parse_lf_term_to_json = parse_only_lf_term $> json_of_lf_term

let parse_clf_typ_to_json = parse_only_clf_typ $> json_of_clf_typ

let parse_clf_term_to_json = parse_only_clf_term $> json_of_clf_term

let parse_meta_type_to_json = parse_only_meta_typ $> json_of_meta_typ

let parse_meta_object_to_json = parse_only_meta_object $> json_of_meta_object

let parse_schema_to_json = parse_only_schema $> json_of_schema

let parse_comp_kind_to_json = parse_only_comp_kind $> json_of_comp_kind

let parse_comp_typ_to_json = parse_only_comp_typ $> json_of_comp_typ

let parse_comp_expression_to_json =
  parse_only_comp_expression $> json_of_comp_expression

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
  | "comp_expression" -> parse_comp_expression_to_json
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
             make_initial_state_from_string ~disambiguation_state
               ~initial_location ~input
           in
           eval parse_test_case state)
         test_cases)
  in
  Support.Files.with_pp_to_file output_filename (fun ppf ->
      Format.fprintf ppf "%a@." (Yojson.Safe.pretty_print ~std:true) outputs)

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
