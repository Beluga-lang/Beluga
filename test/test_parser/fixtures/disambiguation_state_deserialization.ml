open Beluga_syntax
module Disambiguation_state = Beluga_parser.Simple_disambiguation_state

exception Unsupported_sort of string

exception Unsupported_fixity of string

exception Unsupported_associativity of string

exception Missing_fixity_or_precedence

let identifier_of_json json =
  let open Yojson.Safe.Util in
  json |> to_string |> Identifier.make

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

let rec add_json_entries json =
  let open Disambiguation_state in
  let open Yojson.Safe.Util in
  let entries = json |> member "entries" |> to_list in
  traverse_list_void add_json_entry entries

and add_json_entry json =
  let open Disambiguation_state in
  let open Yojson.Safe.Util in
  let sort = json |> member "sort" |> to_string in
  match sort with
  | "lf_type_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      let operator =
        match fixity with
        | Fixity.Prefix ->
            let arity = json |> member "arity" |> to_int in
            Operator.make_prefix ~arity ~precedence
        | Fixity.Infix ->
            let associativity =
              json |> member "associativity" |> associativity_of_json
            in
            Operator.make_infix ~associativity ~precedence
        | Fixity.Postfix -> Operator.make_postfix ~precedence
      in
      add_lf_type_constant operator identifier <& add_declaration identifier
  | "lf_term_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      let operator =
        match fixity with
        | Fixity.Prefix ->
            let arity = json |> member "arity" |> to_int in
            Operator.make_prefix ~arity ~precedence
        | Fixity.Infix ->
            let associativity =
              json |> member "associativity" |> associativity_of_json
            in
            Operator.make_infix ~associativity ~precedence
        | Fixity.Postfix -> Operator.make_postfix ~precedence
      in
      add_lf_term_constant operator identifier <& add_declaration identifier
  | "module" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let* () =
        with_module_inner_declarations ~declarations:(add_json_entries json)
          ~module_identifier:identifier
      in
      add_declaration identifier
  | "parameter_variable" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_parameter_variable identifier
  | "context_variable" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_context_variable identifier
  | "schema_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_schema_constant identifier <& add_declaration identifier
  | "comp_inductive_type_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      let operator =
        match fixity with
        | Fixity.Prefix ->
            let arity = json |> member "arity" |> to_int in
            Operator.make_prefix ~arity ~precedence
        | Fixity.Infix ->
            let associativity =
              json |> member "associativity" |> associativity_of_json
            in
            Operator.make_infix ~associativity ~precedence
        | Fixity.Postfix -> Operator.make_postfix ~precedence
      in
      add_inductive_computation_type_constant operator identifier
      <& add_declaration identifier
  | "comp_constructor" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let fixity = json |> member "fixity" |> fixity_of_json in
      let precedence = json |> member "precedence" |> to_int in
      let operator =
        match fixity with
        | Fixity.Prefix ->
            let arity = json |> member "arity" |> to_int in
            Operator.make_prefix ~arity ~precedence
        | Fixity.Infix ->
            let associativity =
              json |> member "associativity" |> associativity_of_json
            in
            Operator.make_infix ~associativity ~precedence
        | Fixity.Postfix -> Operator.make_postfix ~precedence
      in
      add_computation_term_constructor operator identifier
      <& add_declaration identifier
  | "comp_destructor" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_computation_term_destructor identifier
      <& add_declaration identifier
  | "program_constant" -> (
      let identifier = json |> member "identifier" |> identifier_of_json in
      match (member "fixity" json, member "precedence" json) with
      | `Null, `Null ->
          add_program_constant identifier <& add_declaration identifier
      | `Null, _
      | _, `Null ->
          Error.raise Missing_fixity_or_precedence
      | _ ->
          let fixity = json |> member "fixity" |> fixity_of_json in
          let precedence = json |> member "precedence" |> to_int in
          let operator =
            match fixity with
            | Fixity.Prefix ->
                let arity = json |> member "arity" |> to_int in
                Operator.make_prefix ~arity ~precedence
            | Fixity.Infix ->
                let associativity =
                  json |> member "associativity" |> associativity_of_json
                in
                Operator.make_infix ~associativity ~precedence
            | Fixity.Postfix -> Operator.make_postfix ~precedence
          in
          add_program_constant ~operator identifier
          <& add_declaration identifier)
  | sort -> Error.raise (Unsupported_sort sort)

let read_disambiguation_state filename =
  let open Disambiguation_state in
  let json = Yojson.Safe.from_file filename in
  exec (add_json_entries json) initial
