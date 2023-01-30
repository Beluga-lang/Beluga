open Support
open Beluga_syntax
open Common_disambiguation

module type META_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_meta_typ : Synprs.meta_thing -> Synext.meta_typ t

  val disambiguate_meta_object : Synprs.meta_thing -> Synext.meta_object t

  val disambiguate_schema : Synprs.schema_object -> Synext.schema t

  val with_disambiguated_meta_context :
    Synprs.meta_context_object -> (Synext.meta_context -> 'a t) -> 'a t
end

module Make
    (Bindings_state : BINDINGS_STATE)
    (Clf_disambiguator : Clf_disambiguation.CLF_DISAMBIGUATION
                           with type state = Bindings_state.state) :
  META_DISAMBIGUATION with type state = Bindings_state.state
[@@warning "-67"]

module type META_PATTERN_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_meta_pattern :
    Synprs.meta_thing -> Synext.Meta.Pattern.t t
end

module Make_pattern_disambiguator
    (Bindings_state : BINDINGS_STATE)
    (Pattern_disambiguation_state : PATTERN_DISAMBGUATION_STATE
                                      with module S = Bindings_state)
    (Clf_pattern_disambiguator : Clf_disambiguation
                                 .CLF_PATTERN_DISAMBIGUATION
                                   with type state =
                                     Pattern_disambiguation_state.state) :
  META_PATTERN_DISAMBIGUATION
    with type state = Pattern_disambiguation_state.state
[@@warning "-67"]
