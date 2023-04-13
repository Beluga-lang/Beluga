open Support
open Beluga_syntax
open Disambiguation_state

(** Abstract definition of stateful disambiguation from the parser syntax to
    the external syntax for pure LF kinds, types and terms. *)
module type LF_DISAMBIGUATION = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  (** [disambiguate_lf_kind state object_] is [kind'], the LF kind
      disambiguated from [kind] in the disambiguation state [state]. *)
  val disambiguate_lf_kind : state -> Synprs.lf_object -> Synext.lf_kind

  (** [disambiguate_lf_typ state typ] is [typ'], the LF type disambiguated
      from [typ] in the disambiguation state [state]. *)
  val disambiguate_lf_typ : state -> Synprs.lf_object -> Synext.lf_typ

  (** [disambiguate_lf_term state term] is [term'], the LF term disambiguated
      from [term] in the disambiguation state [state]. *)
  val disambiguate_lf_term : state -> Synprs.lf_object -> Synext.lf_term
end

(** Functor building an instance of LF disambiguation. *)
module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  LF_DISAMBIGUATION with type state = Disambiguation_state.state
