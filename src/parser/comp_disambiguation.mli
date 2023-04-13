open Support
open Disambiguation_state

module type COMP_DISAMBIGUATION = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind :
    state -> Synprs.comp_sort_object -> Synext.comp_kind

  val disambiguate_comp_typ :
    state -> Synprs.comp_sort_object -> Synext.comp_typ

  val disambiguate_comp_expression :
    state -> Synprs.comp_expression_object -> Synext.comp_expression

  val disambiguate_comp_pattern :
    state -> Synprs.comp_pattern_object -> Synext.comp_pattern

  val disambiguate_comp_copattern :
    state -> Synprs.comp_copattern_object List1.t -> Synext.comp_copattern

  val with_disambiguated_comp_context :
       state
    -> Synprs.comp_context_object
    -> (state -> Synext.comp_context -> 'a)
    -> 'a
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
