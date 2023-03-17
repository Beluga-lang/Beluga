open Support
open Beluga_syntax
open Disambiguation_state

module type SIGNATURE_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_pragma :
    Synprs.signature_pragma -> Synext.signature_pragma t

  val disambiguate_global_pragma :
    Synprs.signature_global_pragma -> Synext.signature_global_pragma t

  val disambiguate_totality_declaration :
       Synprs.signature_totality_declaration
    -> Synext.signature_totality_declaration t

  val disambiguate_numeric_totality_order :
       Int.t Synprs.signature_totality_order
    -> Int.t Synext.signature_totality_order t

  val disambiguate_named_totality_order :
       Identifier.t Synprs.signature_totality_order
    -> Identifier.t Synext.signature_totality_order t

  val disambiguate_declaration :
    Synprs.signature_declaration -> Synext.signature_declaration t

  val disambiguate_signature_file :
    Synprs.signature_file -> Synext.signature_file t

  val disambiguate_signature : Synprs.signature -> Synext.signature t
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Lf_disambiguation : Lf_disambiguation.LF_DISAMBIGUATION
                           with type state = Disambiguation_state.state)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Harpoon_disambiguation : Harpoon_disambiguation.HARPOON_DISAMBIGUATION
                                with type state = Disambiguation_state.state) :
  SIGNATURE_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
