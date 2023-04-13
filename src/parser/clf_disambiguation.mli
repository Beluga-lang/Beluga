open Support
open Beluga_syntax
open Disambiguation_state

module type CLF_DISAMBIGUATION = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_clf_typ : state -> Synprs.clf_object -> Synext.clf_typ

  val disambiguate_clf_term : state -> Synprs.clf_object -> Synext.clf_term

  val disambiguate_clf_substitution :
    state -> Synprs.clf_context_object -> Synext.clf_substitution

  val with_disambiguated_clf_context :
       state
    -> Synprs.clf_context_object
    -> (state -> Synext.clf_context -> 'a)
    -> 'a

  val disambiguate_clf_term_pattern :
    state -> Synprs.clf_object -> Synext.clf_term_pattern

  val disambiguate_clf_substitution_pattern :
    state -> Synprs.clf_context_object -> Synext.clf_substitution_pattern

  val with_disambiguated_clf_context_pattern :
       state
    -> Synprs.clf_context_object
    -> (state -> Synext.clf_context_pattern -> 'a)
    -> 'a

  val disambiguate_clf_context_pattern :
    state -> Synprs.clf_context_object -> Synext.clf_context_pattern
end

module Make (Disambiguation_state : DISAMBIGUATION_STATE) :
  CLF_DISAMBIGUATION with type state = Disambiguation_state.state
