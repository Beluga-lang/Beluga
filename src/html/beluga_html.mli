(** Pretty-printing of concrete Beluga signatures to HTML.

    @author Marc-Antoine Ouimet *)

open Beluga_syntax
module Synext_html_pp_state = Synext_html_pp_state
module Synext_html_pp = Synext_html_pp

(** [pp_signature ppf signature] pretty-prints [signature] to [ppf] as an
    HTML page. *)
val pp_signature : Format.formatter -> Synext.signature -> Unit.t
