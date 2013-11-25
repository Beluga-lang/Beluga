open Ocamlbuild_plugin
open Unix

let hardcoded_version_file = ".version"
let version_file = "src/core/version.ml"

let get_version_from_git () =
  try
    let i = open_process_in "git describe --dirty" in
    let l = input_line i in
    let s = close_process_in i in
    if s = WEXITED 0 then
      l
    else
      "Unknown"
  with
  | _ -> "Unknowable"

let hardcoded_version_exists () =
  Sys.file_exists hardcoded_version_file

let get_hardcoded_version () =
  let i = open_in hardcoded_version_file in
  let s = input_line i in
  close_in i ; s

let get_version () =
  if hardcoded_version_exists () then
    get_hardcoded_version ()
  else
    get_version_from_git ()

let make_content version = 
  "let beluga_version = \"" ^ version ^ "\"\n"

let make_version () = 
  let content = make_content (get_version()) in
  let o = open_out version_file in
  output_string o content ;
  close_out o

let _ = make_version ()
