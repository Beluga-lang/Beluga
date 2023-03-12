(** Stateful pretty-printing of concrete Beluga signatures to HTML.

    @author Marc-Antoine Ouimet *)

open Support
open Synext_html_pp_state

module type BELUGA_HTML = sig
  (** @closed *)
  include State.STATE

  val pp_signature : Synext.signature -> Unit.t t
end

module Make (Html_state : HTML_PRINTING_STATE) :
  BELUGA_HTML with type state = Html_state.state
