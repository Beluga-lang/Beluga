(** Stateful pretty-printing of concrete Beluga signatures.

    @author Marc-Antoine Ouimet *)

open Support
open Synext_definition
open Synext_pp_state

(** Abstract definition for pretty-printing Beluga signatures. *)
module type PRINTER = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** [pp_signature_file state signature_file] pretty-prints [signature_file]
      with respect to the pretty-printing state [state]. *)
  val pp_signature_file : state -> signature_file -> Unit.t

  (** [pp_signature signature state] pretty-prints [signature] as the
      concatenation of its signature files, and with respect to [state]. *)
  val pp_signature : state -> signature -> Unit.t
end

module Make_printer (Printing_state : PRINTING_STATE) :
  PRINTER with type state = Printing_state.state

(** Concrete implementation of pretty-printing for Beluga signatures. *)
module Printer : sig
  (** @closed *)
  include module type of Make_printer (Printing_state)

  (** @closed *)
  include module type of Printing_state
end
