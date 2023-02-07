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
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Clf_disambiguator : Clf_disambiguation.CLF_DISAMBIGUATION
                           with type state = Disambiguation_state.state) :
  META_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]

module type META_PATTERN_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_meta_typ : Synprs.meta_thing -> Synext.meta_typ t

  val disambiguate_meta_object : Synprs.meta_thing -> Synext.meta_object t

  val disambiguate_meta_pattern :
    Synprs.meta_thing -> Synext.Meta.Pattern.t t

  val with_disambiguated_meta_context :
    Synprs.meta_context_object -> (Synext.meta_context -> 'a t) -> 'a t
end

module Make_pattern_disambiguator
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Clf_pattern_disambiguator : Clf_disambiguation
                                 .CLF_PATTERN_DISAMBIGUATION
                                   with type state =
                                     Disambiguation_state.state) :
  META_PATTERN_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
