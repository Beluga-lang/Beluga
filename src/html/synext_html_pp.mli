(** Stateful pretty-printing of concrete Beluga signatures to HTML.

    @author Marc-Antoine Ouimet *)

open Support
open Synext_html_pp_state

(** Abstract definition for HTML pretty-printing concrete Beluga signatures. *)
module type HTML_PRINTER = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** [pp_signature_file state signature_file] pretty-prints [signature_file]
      to HTML as the concatenation of its signature files. *)
  val pp_signature_file : state -> Synext.signature_file -> Unit.t

  (** [pp_signature state signature] pretty-prints [signature] to HTML as the
      concatenation of its signature files. *)
  val pp_signature : state -> Synext.signature -> Unit.t
end

module Make_html_printer (Html_printing_state : HTML_PRINTING_STATE) :
  HTML_PRINTER with type state = Html_printing_state.state

(** Concrete implementation of HTML pretty-printing for Beluga signatures. *)
module Html_printer : sig
  (** @closed *)
  include module type of Make_html_printer (Html_printing_state)

  (** @closed *)
  include module type of Html_printing_state
end
