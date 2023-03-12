(** Stateful pretty-printing of concrete Beluga signatures to HTML.

    @author Marc-Antoine Ouimet *)

open Support
open Synext_html_pp_state

(** Abstract definition for HTML pretty-printing concrete Beluga signatures. *)
module type HTML_PRINTER = sig
  (** @closed *)
  include State.STATE

  (** [pp_signature_file signature_file state] pretty-prints [signature_file]
      to HTML as the concatenation of its signature files and returns
      [(state', ())]. *)
  val pp_signature_file : Synext.signature_file -> Unit.t t

  (** [pp_signature signature state] pretty-prints [signature] to HTML as the
      concatenation of its signature files and returns [(state', ())]. *)
  val pp_signature : Synext.signature -> Unit.t t
end

module Make_html_printer (Html_printing_state : HTML_PRINTING_STATE) :
  HTML_PRINTER with type state = Html_printing_state.state

(** Concrete implementation of HTML pretty-printing for Beluga signatures. *)
module Html_printer : module type of Make_html_printer (Html_printing_state)
