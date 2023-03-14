open Support
open Beluga_syntax
open Beluga_parser
module Disambiguation_state = Simple.Disambiguation_state

exception Unsupported_sort of string

exception Unsupported_fixity of string

exception Unsupported_associativity of string

exception Missing_fixity_or_precedence

let identifier_of_json = Fun.(Yojson.Safe.Util.to_string >> Identifier.make)

let fixity_of_string = function
  | "prefix" -> Fixity.prefix
  | "infix" -> Fixity.infix
  | "postfix" -> Fixity.postfix
  | fixity -> Error.raise (Unsupported_fixity fixity)

let associativity_of_string = function
  | "left_associative" -> Associativity.left_associative
  | "right_associative" -> Associativity.right_associative
  | "non_associative" -> Associativity.non_associative
  | associativity -> Error.raise (Unsupported_associativity associativity)

let associativity_of_json =
  Fun.(Yojson.Safe.Util.to_string >> associativity_of_string)

let operator_opt_of_json json =
  let open Yojson.Safe.Util in
  match json |> member "fixity" |> to_string_option with
  | Option.None -> Option.none
  | Option.Some fixity ->
      let fixity' = fixity_of_string fixity in
      let precedence = json |> member "precedence" |> to_int in
      let operator =
        match fixity' with
        | Fixity.Prefix -> Operator.make_prefix ~precedence
        | Fixity.Infix ->
            let associativity =
              json |> member "associativity" |> associativity_of_json
            in
            Operator.make_infix ~associativity ~precedence
        | Fixity.Postfix -> Operator.make_postfix ~precedence
      in
      Option.some operator

let set_operator identifier operator_opt =
  let open Disambiguation_state in
  let qualified_identifier = Qualified_identifier.make_simple identifier in
  match operator_opt with
  | Option.None -> return ()
  | Option.Some operator -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
          add_prefix_notation
            ~precedence:(Operator.precedence operator)
            qualified_identifier
      | Fixity.Infix ->
          add_infix_notation
            ~precedence:(Operator.precedence operator)
            ~associativity:(Operator.associativity operator)
            qualified_identifier
      | Fixity.Postfix ->
          add_postfix_notation
            ~precedence:(Operator.precedence operator)
            qualified_identifier)

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
      let arity = json |> member "arity" |> to_int_option in
      let operator_opt = operator_opt_of_json json in
      add_lf_type_constant ?arity identifier
      <& set_operator identifier operator_opt
  | "lf_term_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let arity = json |> member "arity" |> to_int_option in
      let operator_opt = operator_opt_of_json json in
      add_lf_term_constant ?arity identifier
      <& set_operator identifier operator_opt
  | "module" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_module identifier (add_json_entries json)
  | "parameter_variable" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_parameter_variable identifier
  | "context_variable" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_context_variable identifier
  | "schema_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_schema_constant identifier
  | "comp_inductive_type_constant" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let arity = json |> member "arity" |> to_int_option in
      let operator_opt = operator_opt_of_json json in
      add_inductive_computation_type_constant ?arity identifier
      <& set_operator identifier operator_opt
  | "comp_constructor" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      let arity = json |> member "arity" |> to_int_option in
      let operator_opt = operator_opt_of_json json in
      add_computation_term_constructor ?arity identifier
      <& set_operator identifier operator_opt
  | "comp_destructor" ->
      let identifier = json |> member "identifier" |> identifier_of_json in
      add_computation_term_destructor identifier
  | "program_constant" -> (
      let identifier = json |> member "identifier" |> identifier_of_json in
      match (member "fixity" json, member "precedence" json) with
      | `Null, `Null -> add_program_constant identifier
      | `Null, _
      | _, `Null ->
          Error.raise Missing_fixity_or_precedence
      | _ ->
          let arity = json |> member "arity" |> to_int_option in
          let operator_opt = operator_opt_of_json json in
          add_program_constant ?arity identifier
          <& set_operator identifier operator_opt)
  | sort -> Error.raise (Unsupported_sort sort)

let read_disambiguation_state filename =
  let open Disambiguation_state in
  let json = Yojson.Safe.from_file filename in
  exec (add_json_entries json) initial_state
