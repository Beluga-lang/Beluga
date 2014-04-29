open Ocamlbuild_plugin
open Unix

let hardcoded_version_file = ".version"
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
    try hardcoded_version () with _ ->
      try version_from_git () with _ ->
        failwith "Unable to determine version" in
  "let beluga_version = \"" ^ version ^ "\"\n"

let () =
  dispatch begin function
    | After_options ->
      pflag ["ocaml"; "compile"] "warn" (fun s -> S[A"-w"; A s]);
      pflag ["ocaml"; "compile"] "warn-error" (fun s -> S[A"-warn-error"; A s]);
      copy_rule "The Beluga executable" "src/beluga/main.native" "beluga";
      copy_rule "The Beli executable" "src/beli/main.native" "beli";
      rule "Version file" ~prods:[version_file] (fun env _ -> Echo ([version_content ()], version_file))
    | _ -> ()
  end
