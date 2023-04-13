open Support
open Beluga_syntax
open Disambiguation_state

module type META_DISAMBIGUATION = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_meta_typ : state -> Synprs.meta_thing -> Synext.meta_typ

  val disambiguate_meta_object :
    state -> Synprs.meta_thing -> Synext.meta_object

  val disambiguate_meta_pattern :
    state -> Synprs.meta_thing -> Synext.Meta.Pattern.t

  val disambiguate_schema : state -> Synprs.schema_object -> Synext.schema

  val with_disambiguated_meta_context :
       state
    -> Synprs.meta_context_object
    -> (state -> Synext.meta_context -> 'a)
    -> 'a

  val with_disambiguated_meta_context_pattern :
       state
    -> Synprs.meta_context_object
    -> (state -> Synext.meta_context -> 'a)
    -> 'a
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Lf_disambiguation : Lf_disambiguation.LF_DISAMBIGUATION
                           with type state = Disambiguation_state.state)
    (Clf_disambiguator : Clf_disambiguation.CLF_DISAMBIGUATION
                           with type state = Disambiguation_state.state) :
  META_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
