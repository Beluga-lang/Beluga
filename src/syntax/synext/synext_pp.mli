(** Stateful pretty-printing of concrete Beluga signatures.

    @author Marc-Antoine Ouimet *)

open Support
open Synext_definition
open Synext_pp_state

(** Abstract definition for pretty-printing Beluga signatures. *)
module type PRINTER = sig
  (** @closed *)
  include State.STATE

  (** [pp_signature_file signature_file state] pretty-prints a
      [signature_file] to [state], and returns [(state', ())]. *)
  val pp_signature_file : signature_file -> Unit.t t

  (** [pp_signature signature state] pretty-prints [signature] as the
      concatenation of its signature files and returns [(state', ())]. *)
  val pp_signature : signature -> Unit.t t
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
