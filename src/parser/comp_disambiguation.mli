open Support
open Disambiguation_state

module type COMP_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind : Synprs.comp_sort_object -> Synext.comp_kind t

  val disambiguate_comp_typ : Synprs.comp_sort_object -> Synext.comp_typ t

  val disambiguate_comp_expression :
    Synprs.comp_expression_object -> Synext.comp_expression t

  val disambiguate_comp_pattern :
    Synprs.comp_pattern_object -> Synext.comp_pattern t

  val disambiguate_comp_copattern :
    Synprs.comp_copattern_object List1.t -> Synext.comp_copattern t

  val with_disambiguated_comp_context :
    Synprs.comp_context_object -> (Synext.comp_context -> 'a t) -> 'a t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
