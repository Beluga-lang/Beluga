open Support
open Beluga_syntax
open Disambiguation_state

module type CLF_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_clf_typ : Synprs.clf_object -> Synext.clf_typ t

  val disambiguate_clf_term : Synprs.clf_object -> Synext.clf_term t

  val disambiguate_clf_substitution :
    Synprs.clf_context_object -> Synext.clf_substitution t

  val with_disambiguated_clf_context :
    Synprs.clf_context_object -> (Synext.clf_context -> 'a t) -> 'a t

  val disambiguate_clf_term_pattern :
    Synprs.clf_object -> Synext.clf_term_pattern t

  val disambiguate_clf_substitution_pattern :
    Synprs.clf_context_object -> Synext.clf_substitution_pattern t

  val with_disambiguated_clf_context_pattern :
    Synprs.clf_context_object -> (Synext.clf_context_pattern -> 'a t) -> 'a t

  val disambiguate_clf_context_pattern :
    Synprs.clf_context_object -> Synext.clf_context_pattern t
end

module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  CLF_DISAMBIGUATION with type state = Disambiguation_state.state
