open Ocamlbuild_plugin
open Unix

let version_file = "src/core/version.ml"

let get_version () =
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

let make_content version = 
  "let beluga_version = \"" ^ version ^ "\"\n"

let make_version () = 
  let content = make_content (get_version()) in
  let o = open_out version_file in
  output_string o content ;
  close_out o

let _ = make_version ()
