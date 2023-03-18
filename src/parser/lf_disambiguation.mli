open Support
open Beluga_syntax
open Disambiguation_state

(** Abstract definition of stateful disambiguation from the parser syntax to
    the external syntax for pure LF kinds, types and terms. *)
module type LF_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  (** [disambiguate_lf_kind object_ kind] is [(state', kind')] where [kind']
      is the LF kind disambiguated from [kind] in the disambiguation state
      [state]. *)
  val disambiguate_lf_kind : Synprs.lf_object -> Synext.lf_kind t

  (** [disambiguate_lf_typ typ state] is [(state', typ')] where [typ'] is the
      LF type disambiguated from [typ] in the disambiguation state [state]. *)
  val disambiguate_lf_typ : Synprs.lf_object -> Synext.lf_typ t

  (** [disambiguate_lf_term term state] is [(state', term')] where [term'] is
      the LF term disambiguated from [term] in the disambiguation state
      [state]. *)
  val disambiguate_lf_term : Synprs.lf_object -> Synext.lf_term t
end

(** Functor building an instance of LF disambiguation. *)
module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  LF_DISAMBIGUATION with type state = Disambiguation_state.state
