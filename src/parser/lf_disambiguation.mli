open Support
open Beluga_syntax
open Disambiguation_state

module type LF_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_lf_kind : Synprs.lf_object -> Synext.lf_kind t

  val disambiguate_lf_typ : Synprs.lf_object -> Synext.lf_typ t

  val disambiguate_lf_term : Synprs.lf_object -> Synext.lf_term t
end

module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  LF_DISAMBIGUATION with type state = Disambiguation_state.state
