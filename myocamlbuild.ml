open Ocamlbuild_plugin
open Unix

let hardcoded_version_file = "VERSION"
let version_file = "src/core/version.ml"

let version_content () =
  let version_from_git () =
    let i = open_process_in "git describe --dirty" in
    let l = input_line i in
    if close_process_in i = WEXITED 0 then l
    else raise Not_found in
  let hardcoded_version () =
    let i = open_in hardcoded_version_file in
    let s = input_line i in
    close_in i; s in
  let version =
    try version_from_git () with _ ->
      try hardcoded_version () with _ ->
        failwith "Unable to determine version" in
  "let beluga_version = \"" ^ version ^ "\"\n"

let () =
  dispatch begin function
    | After_options ->
      pflag ["ocaml"; "compile"] "warn" (fun s -> S[A"-w"; A s]);
      pflag ["ocaml"; "compile"] "warn-error" (fun s -> S[A"-warn-error"; A s]);
      rule "Version file" ~deps:[hardcoded_version_file] ~prods:[version_file]
        (fun env _ -> Echo ([version_content ()], version_file));
      ocaml_lib "src/support/support";
      ocaml_lib "src/core/core"
    | _ -> ()
  end
