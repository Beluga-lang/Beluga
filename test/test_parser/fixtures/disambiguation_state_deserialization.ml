open Beluga_syntax
module Disambiguation_state = Beluga_parser.Simple_disambiguation_state

exception Unsupported_sort of string

exception Unsupported_fixity of string

exception Unsupported_associativity of string

let fixity_of_json json =
  let open Yojson.Safe.Util in
  match json |> to_string with
  | "prefix" -> Fixity.prefix
  | "infix" -> Fixity.infix
  | "postfix" -> Fixity.postfix
  | fixity -> Error.raise (Unsupported_fixity fixity)

let associativity_of_json json =
  let open Yojson.Safe.Util in
  match json |> to_string with
  | "left_associative" -> Associativity.left_associative
  | "right_associative" -> Associativity.right_associative
  | "non_associative" -> Associativity.non_associative
  | associativity -> Error.raise (Unsupported_associativity associativity)

let rec disambiguation_state_of_json json =
  let open Disambiguation_state in
  let open Yojson.Safe.Util in
  let entries = json |> member "entries" |> to_list in
  traverse_list_void add_json_entry entries

and add_json_entry json =
  let open Disambiguation_state in
  let open Yojson.Safe.Util in
  let sort = json |> member "sort" |> to_string in
  match sort with
  | "lf_type_constant" -> (
      let identifier = json |> member "identifier" |> to_string in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      match fixity with
      | Fixity.Prefix ->
          let arity = json |> member "arity" |> to_int in
          let operator = Operator.make_prefix ~arity ~precedence in
          add_lf_type_constant operator (Identifier.make identifier)
      | Fixity.Infix ->
          let associativity =
            json |> member "associativity" |> associativity_of_json
          in
          let operator = Operator.make_infix ~associativity ~precedence in
          add_lf_type_constant operator (Identifier.make identifier)
      | Fixity.Postfix ->
          let operator = Operator.make_postfix ~precedence in
          add_lf_type_constant operator (Identifier.make identifier))
  | "lf_term_constant" -> (
      let identifier = json |> member "identifier" |> to_string in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      match fixity with
      | Fixity.Prefix ->
          let arity = json |> member "arity" |> to_int in
          let operator = Operator.make_prefix ~arity ~precedence in
          add_lf_term_constant operator (Identifier.make identifier)
      | Fixity.Infix ->
          let associativity =
            json |> member "associativity" |> associativity_of_json
          in
          let operator = Operator.make_infix ~associativity ~precedence in
          add_lf_term_constant operator (Identifier.make identifier)
      | Fixity.Postfix ->
          let operator = Operator.make_postfix ~precedence in
          add_lf_term_constant operator (Identifier.make identifier))
  | "module" ->
      let identifier = json |> member "identifier" |> to_string in
      let module_state = exec (disambiguation_state_of_json json) empty in
      add_module module_state (Identifier.make identifier)
  | "parameter_variable" ->
      let identifier = json |> member "identifier" |> to_string in
      add_parameter_variable (Identifier.make identifier)
  | "context_variable" ->
      let identifier = json |> member "identifier" |> to_string in
      add_context_variable (Identifier.make identifier)
  | "schema_constant" ->
      let identifier = json |> member "identifier" |> to_string in
      add_schema_constant (Identifier.make identifier)
  | sort -> Error.raise (Unsupported_sort sort)

let read_disambiguation_state filename =
  let open Disambiguation_state in
  let json = Yojson.Safe.from_file filename in
  exec (disambiguation_state_of_json json) empty
