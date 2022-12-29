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
  | fixity -> raise (Unsupported_fixity fixity)

let associativity_of_json json =
  let open Yojson.Safe.Util in
  match json |> to_string with
  | "left_associative" -> Associativity.left_associative
  | "right_associative" -> Associativity.right_associative
  | "non_associative" -> Associativity.non_associative
  | associativity -> raise (Unsupported_associativity associativity)

let rec disambiguation_state_of_json json =
  let open Yojson.Safe.Util in
  let entries = json |> member "entries" |> to_list in
  List.fold_right add_json_entry entries Disambiguation_state.empty

and add_json_entry json disambiguation_state =
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
          Disambiguation_state.add_prefix_lf_type_constant
            (Identifier.make identifier)
            ~arity ~precedence disambiguation_state
      | Fixity.Infix ->
          let associativity =
            json |> member "associativity" |> associativity_of_json
          in
          Disambiguation_state.add_infix_lf_type_constant
            (Identifier.make identifier)
            ~associativity ~precedence disambiguation_state
      | Fixity.Postfix ->
          Disambiguation_state.add_postfix_lf_type_constant
            (Identifier.make identifier)
            ~precedence disambiguation_state)
  | "lf_term_constant" -> (
      let identifier = json |> member "identifier" |> to_string in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      match fixity with
      | Fixity.Prefix ->
          let arity = json |> member "arity" |> to_int in
          Disambiguation_state.add_prefix_lf_term_constant
            (Identifier.make identifier)
            ~arity ~precedence disambiguation_state
      | Fixity.Infix ->
          let associativity =
            json |> member "associativity" |> associativity_of_json
          in
          Disambiguation_state.add_infix_lf_term_constant
            (Identifier.make identifier)
            ~associativity ~precedence disambiguation_state
      | Fixity.Postfix ->
          Disambiguation_state.add_postfix_lf_term_constant
            (Identifier.make identifier)
            ~precedence disambiguation_state)
  | "module" ->
      let identifier = json |> member "identifier" |> to_string in
      let entries = disambiguation_state_of_json json in
      Disambiguation_state.add_module
        (Disambiguation_state.get_bindings entries)
        (Identifier.make identifier)
        disambiguation_state
  | "context_variable" ->
      let identifier = json |> member "identifier" |> to_string in
      Disambiguation_state.add_context_variable
        (Identifier.make identifier)
        disambiguation_state
  | "schema_constant" ->
      let identifier = json |> member "identifier" |> to_string in
      Disambiguation_state.add_schema_constant
        (Identifier.make identifier)
        disambiguation_state
  | sort -> raise (Unsupported_sort sort)

let read_disambiguation_state filename =
  let json = Yojson.Safe.from_file filename in
  disambiguation_state_of_json json
