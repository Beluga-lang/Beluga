open Support
open Beluga_syntax
open Util
open Base_json
open Synext_json
open Assert

exception Empty_configuration_file

let pp_json_signature_file ppf signature_file =
  Yojson.Safe.pretty_print ~std:true ppf
    (Base_json.without_locations
       (Synext_json.json_of_signature_file signature_file))

let pp_json_signature ppf signature =
  Yojson.Safe.pretty_print ~std:true ppf
    (Base_json.without_locations (Synext_json.json_of_signature signature))

let pp_html_signature ppf signature =
  let module Printing_state = Beluga_html.Persistent_html_state in
  let module Printer = Beluga_html.Make (Printing_state) in
  let open Printing_state in
  let open Printer in
  eval (pp_signature signature ++ pp_newline) (initial ppf)

let save_signature_file_json ~filename signature_file =
  Support.Files.with_pp_to_file filename (fun ppf ->
      Format.fprintf ppf "%a@." pp_json_signature_file signature_file)

let save_signature_html ~filename signature =
  Support.Files.with_pp_to_file filename (fun ppf ->
      pp_html_signature ppf signature)

let json_filename location =
  Filename.remove_extension (Location.filename location) ^ ".json"

let pp_filename location =
  Filename.remove_extension (Location.filename location) ^ ".pp"

let html_filename location =
  Filename.remove_extension (Location.filename location) ^ ".html"

let save_signature_files_json =
  List1.iter (fun signature_file ->
      save_signature_file_json
        ~filename:(json_filename signature_file.Synext.Signature.location)
        signature_file)

let save_signature_file_pp x state =
  let module Printing_state = Synext.Printing_state in
  let module Printer = Synext.Make_pretty_printer (Printing_state) in
  let open Printing_state in
  let open Printer in
  Support.Files.with_pp_to_file (pp_filename x.Synext.Signature.location)
    (fun ppf ->
      run (set_formatter ppf &> pp_signature_file x ++ pp_newline) state)

let save_signature_files_pp (List1.T (x, xs)) =
  let module Printing_state = Synext.Printing_state in
  let module Printer = Synext.Make_pretty_printer (Printing_state) in
  let open Printing_state in
  let open Printer in
  let state, () =
    Support.Files.with_pp_to_file (pp_filename x.Synext.Signature.location)
      (fun ppf -> run (save_signature_file_pp x) (initial ppf))
  in
  eval (traverse_list_void save_signature_file_pp xs) state

let pp_and_parse_signature_files (List1.T (x, xs)) =
  let module Printing_state = Synext.Printing_state in
  let module Parser_state = Beluga_parser.Simple.Parser_state in
  let module Disambiguation_state = Beluga_parser.Simple.Disambiguation_state
  in
  let module Printer = Synext.Make_pretty_printer (Printing_state) in
  let module Parser = Beluga_parser.Simple in
  let buffer = Buffer.create 16 in
  let printing_state =
    Printing_state.initial (Format.formatter_of_buffer buffer)
  in
  let printing_state', () =
    Printing_state.(
      Printer.(run (pp_signature_file x ++ pp_newline) printing_state))
  in
  let parser_state, y =
    Parser.run Parser.parse_only_signature_file
      (Parser.make_initial_state_from_string
         ~disambiguation_state:Disambiguation_state.initial
         ~initial_location:Location.ghost ~input:(Buffer.contents buffer))
  in
  let _printing_state'', _parser_state', ys_rev =
    List.fold_left
      (fun (printing_state, parser_state, ys_rev) x ->
        Buffer.clear buffer;
        let printing_state', () =
          Printing_state.(
            Printer.(run (pp_signature_file x ++ pp_newline) printing_state))
        in
        let parser_state', () =
          Parser.put_parser_state
            (Parser.make_initial_parser_state_from_string
               ~initial_location:Location.ghost (Buffer.contents buffer))
            parser_state
        in
        let parser_state'', y =
          Parser.run Parser.parse_only_signature_file parser_state'
        in
        (printing_state', parser_state'', y :: ys_rev))
      (printing_state', parser_state, [])
      xs
  in
  List1.from y (List.rev ys_rev)

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

let assert_equal_as_json f ~expected ~actual =
  assert_json_equal ~expected:(f expected) ~actual:(f actual)

let examples_directory = "../../examples"

let compiler_tests = find_compiler_tests ~directory:examples_directory

let make_compiler_test ?(save_json_to_file = false)
    ?(save_pp_to_file = false) compiler_test_file =
  let open OUnit2 in
  compiler_test_file >:: fun _test_ctxt ->
  let beluga_source_files =
    Beluga_parser.Config_parser.read_configuration
      ~filename:compiler_test_file
  in
  match beluga_source_files with
  | [] -> Error.raise Empty_configuration_file
  | x :: xs ->
      let signature_source_files = List1.map Pair.snd (List1.from x xs) in
      let signature_files =
        Beluga_parser.Simple.parse_multi_file_signature
          signature_source_files
      in
      if save_json_to_file then save_signature_files_json signature_files;
      if save_pp_to_file then save_signature_files_pp signature_files;
      let signature' = pp_and_parse_signature_files signature_files in
      assert_equal_as_json
        Fun.(json_of_signature >> without_locations)
        ~expected:signature_files ~actual:signature'

let make_html_test ?(save_html_to_file = false) compiler_test_file =
  let open OUnit2 in
  compiler_test_file >:: fun _test_ctxt ->
  let beluga_source_files =
    Beluga_parser.Config_parser.read_configuration
      ~filename:compiler_test_file
  in
  match beluga_source_files with
  | [] -> Error.raise Empty_configuration_file
  | x :: xs ->
      let signature_source_files = List1.map Pair.snd (List1.from x xs) in
      let signature =
        Beluga_parser.Simple.parse_multi_file_signature
          signature_source_files
      in
      if save_html_to_file then
        save_signature_html
          ~filename:(Filename.remove_extension compiler_test_file ^ ".html")
          signature;
      ignore (Format.asprintf "%a@." pp_html_signature signature : string)

let tests =
  let open OUnit2 in
  [ "Pretty-printing" >::: List.map make_compiler_test compiler_tests
  ; "HTML pretty-printing" >::: List.map make_html_test compiler_tests
  ]
