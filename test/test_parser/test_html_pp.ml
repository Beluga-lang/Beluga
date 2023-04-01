open Support
open Beluga_syntax
open Util

exception Empty_configuration_file

let save_signature_html ~filename signature =
  Support.Files.with_pp_to_file filename (fun ppf ->
      Format.fprintf ppf "%a@." Beluga_html.pp_signature signature)

let replace_filename_extension filename ~extension =
  Filename.remove_extension filename ^ extension

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
        Beluga_parser.Simple.read_multi_file_signature signature_source_files
      in
      if save_html_to_file then
        save_signature_html
          ~filename:
            (replace_filename_extension compiler_test_file ~extension:".html")
          signature;
      ignore
        (Format.asprintf "%a@." Beluga_html.pp_signature signature : string)

let examples_directory = "../examples"

let tests () =
  let compiler_tests =
    Files.find_compiler_tests ~directory:examples_directory
  in
  List.map make_html_test compiler_tests
