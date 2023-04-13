open Support
open Beluga_syntax
module Synext_html_pp_state = Synext_html_pp_state
module Synext_html_pp = Synext_html_pp

let replace_filename_extension filename ~extension =
  Filename.remove_extension filename ^ extension

let location_html_filename location =
  replace_filename_extension (Location.filename location) ~extension:".html"

let pp_signature_to_files ~directory signature =
  let open Synext_html_pp.Html_printer in
  let open Synext_html_pp_state.Html_printing_state in
  let (List1.T (x, xs)) = signature in
  let state =
    let x_html_page = location_html_filename x.Synext.Signature.location in
    Files.with_pp_to_file (Filename.concat directory x_html_page) (fun ppf ->
        let state = create_initial_state ~current_page:x_html_page ppf in
        pp_signature_file state x;
        Format.pp_print_newline ppf ();
        state)
  in
  traverse_list_void state
    (fun state signature_file ->
      let html_page =
        location_html_filename signature_file.Synext.Signature.location
      in
      Files.with_pp_to_file (Filename.concat directory html_page) (fun ppf ->
          set_formatter state ppf;
          set_current_page state html_page;
          pp_signature_file state signature_file;
          Format.pp_print_newline ppf ()))
    xs

let pp_signature ppf signature =
  let open Synext_html_pp.Html_printer in
  pp_signature (create_initial_state ~current_page:"" ppf) signature
