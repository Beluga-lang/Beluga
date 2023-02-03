open Support
open Common_disambiguation

module type COMP_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_comp_kind : Synprs.comp_sort_object -> Synext.comp_kind t

  val disambiguate_comp_typ : Synprs.comp_sort_object -> Synext.comp_typ t

  val disambiguate_comp_expression :
    Synprs.comp_expression_object -> Synext.comp_expression t

  val with_disambiguated_comp_context :
    Synprs.comp_context_object -> (Synext.comp_context -> 'a t) -> 'a t
end

module type COMP_PATTERN_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val with_disambiguated_meta_context :
    Synprs.meta_context_object -> (Synext.meta_context -> 'a t) -> 'a t

  val disambiguate_comp_pattern :
    Synprs.comp_pattern_object -> Synext.comp_pattern t

  val disambiguate_comp_copattern :
    Synprs.comp_copattern_object List1.t -> Synext.comp_copattern t
end

module Make
    (Bindings_state : BINDINGS_STATE)
    (Pattern_disambiguation_state : PATTERN_DISAMBGUATION_STATE
                                      with module S = Bindings_state)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Bindings_state.state)
    (Comp_pattern_disambiguator : COMP_PATTERN_DISAMBIGUATION
                                    with type state =
                                      Pattern_disambiguation_state.state) :
  COMP_DISAMBIGUATION with type state = Bindings_state.state
[@@warning "-67"]

module Make_pattern_disambiguator
    (Bindings_state : BINDINGS_STATE)
    (Pattern_disambiguation_state : PATTERN_DISAMBGUATION_STATE
                                      with module S = Bindings_state)
    (Meta_disambiguator : Meta_disambiguation.META_DISAMBIGUATION
                            with type state = Bindings_state.state)
    (Meta_pattern_disambiguator : Meta_disambiguation
                                  .META_PATTERN_DISAMBIGUATION
                                    with type state =
                                      Pattern_disambiguation_state.state) :
  COMP_PATTERN_DISAMBIGUATION
    with type state = Pattern_disambiguation_state.state
[@@warning "-67"]
