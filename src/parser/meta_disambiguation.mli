open Support
open Beluga_syntax
open Disambiguation_state

module type META_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_meta_typ : Synprs.meta_thing -> Synext.meta_typ t

  val disambiguate_meta_object : Synprs.meta_thing -> Synext.meta_object t

  val disambiguate_meta_pattern :
    Synprs.meta_thing -> Synext.Meta.Pattern.t t

  val disambiguate_schema : Synprs.schema_object -> Synext.schema t

  val with_disambiguated_meta_context :
    Synprs.meta_context_object -> (Synext.meta_context -> 'a t) -> 'a t

  val with_disambiguated_meta_context_pattern :
    Synprs.meta_context_object -> (Synext.meta_context -> 'a t) -> 'a t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Lf_disambiguation : Lf_disambiguation.LF_DISAMBIGUATION
                           with type state = Disambiguation_state.state)
    (Clf_disambiguator : Clf_disambiguation.CLF_DISAMBIGUATION
                           with type state = Disambiguation_state.state) :
  META_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
