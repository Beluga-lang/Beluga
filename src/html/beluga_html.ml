module Printing_state = Synext_html_pp_state.Persistent_html_state
module Printer = Synext_html_pp.Make (Printing_state)
open Printing_state
open Printer
module Synext_html_pp_state = Synext_html_pp_state
module Synext_html_pp = Synext_html_pp

let pp_signature ppf signature =
  eval (pp_signature signature) (make_initial_state ppf)
