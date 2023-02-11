[@@@warning "-A"]

open Support
open Beluga_syntax
open Util
open Assert
module Parser = Beluga_parser.Simple

type entry =
  | File of string
  | Directory of string * entry list

let rec read_file_structure ~directory =
  let direct_entries =
    List.map
      (Filename.concat directory)
      (Array.to_list (Sys.readdir directory))
  in
  let nested_entries =
    List.map
      (fun entry ->
        if Sys.is_directory entry then
          match read_file_structure ~directory:entry with
          | File file -> File (Filename.concat entry file)
          | Directory (directory, files) ->
              Directory (Filename.concat entry directory, files)
        else File entry)
      direct_entries
  in
  Directory (directory, nested_entries)

let is_beluga_file path = Filename.check_suffix path ".bel"

let is_configuration_file path = Filename.check_suffix path ".cfg"

let rec find_compiler_tests_in_structure = function
  | File path -> if is_beluga_file path then [ path ] else []
  | Directory (_directory_path, entries) ->
      let configuration_files =
        List.filter_map
          (function
            | File path ->
                if is_configuration_file path then Option.some path
                else Option.none
            | Directory _ -> Option.none)
          entries
      in
      if List.null configuration_files then
        List.concat_map find_compiler_tests_in_structure entries
      else configuration_files

let find_compiler_tests ~directory =
  let structure = read_file_structure ~directory in
  let test_files = find_compiler_tests_in_structure structure in
  List.sort String.compare test_files

let examples_directory = "../../examples"

let compiler_tests = find_compiler_tests ~directory:examples_directory

let make_compiler_test compiler_test_file =
  let beluga_source_files =
    Beluga_parser.Config_parser.read_configuration
      ~filename:compiler_test_file
  in
  match beluga_source_files with
  | [] -> assert false
  | x :: xs ->
      let signature_source_files = List1.map Pair.snd (List1.from x xs) in
      let open OUnit2 in
      compiler_test_file >:: fun _test_ctxt ->
      let signature =
        Parser.parse_multi_file_signature signature_source_files
      in
      let printed_signature =
        Format.asprintf "%a@." Synext.pp_signature signature
      in
      let signature' =
        Parser.parse_only_signature
          (Parser.make_initial_state_from_string
             ~disambiguation_state:
               Beluga_parser.Simple_disambiguation_state.initial
             ~initial_location:Location.ghost ~input:printed_signature)
      in
      assert_json_equal
        ~expected:
          (Base_json.without_locations
             (Synext_json.json_of_signature signature))
        ~actual:
          (Base_json.without_locations
             (Synext_json.json_of_signature signature'))

let tests = List.map make_compiler_test compiler_tests