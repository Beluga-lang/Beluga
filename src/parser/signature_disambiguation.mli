open Support
open Beluga_syntax.Synext
open Disambiguation_state

module type SIGNATURE_DISAMBIGUATION = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_pragma :
    state -> Synprs.signature_pragma -> Synext.signature_pragma

  val disambiguate_global_pragma :
    state -> Synprs.signature_global_pragma -> Synext.signature_global_pragma

  val disambiguate_totality_declaration :
       state
    -> Synprs.signature_totality_declaration
    -> Synext.signature_totality_declaration

  val disambiguate_numeric_totality_order :
       state
    -> Int.t Synprs.signature_totality_order
    -> Int.t Synext.signature_totality_order

  val disambiguate_named_totality_order :
       state
    -> Identifier.t Synprs.signature_totality_order
    -> Identifier.t Synext.signature_totality_order

  val disambiguate_declaration :
    state -> Synprs.signature_declaration -> Synext.signature_declaration

  val disambiguate_signature_file :
    state -> Synprs.signature_file -> Synext.signature_file

  val disambiguate_signature : state -> Synprs.signature -> Synext.signature
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Lf_disambiguation : Lf_disambiguation.LF_DISAMBIGUATION
                           with type state = Disambiguation_state.state)
    (Clf_disambiguation : Clf_disambiguation.CLF_DISAMBIGUATION
                            with type state = Disambiguation_state.state)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Harpoon_disambiguation : Harpoon_disambiguation.HARPOON_DISAMBIGUATION
                                with type state = Disambiguation_state.state) :
  SIGNATURE_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
