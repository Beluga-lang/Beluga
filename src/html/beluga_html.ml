module Synext_html_pp_state = Synext_html_pp_state
module Synext_html_pp = Synext_html_pp

let pp_signature ppf signature =
  let open Synext_html_pp.Html_printer in
  eval (pp_signature signature) (make_initial_state ppf)
