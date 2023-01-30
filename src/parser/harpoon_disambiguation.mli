open Support
open Beluga_syntax
open Common_disambiguation

module type HARPOON_DISAMBIGUATION = sig
  (** @closed *)
  include State.STATE

  (** {1 Disambiguation} *)

  val disambiguate_harpoon_proof :
    Synprs.harpoon_proof -> Synext.harpoon_proof t

  val disambiguate_harpoon_command :
    Synprs.harpoon_command -> Synext.harpoon_command t

  val disambiguate_harpoon_directive :
    Synprs.harpoon_directive -> Synext.harpoon_directive t

  val disambiguate_harpoon_split_branch :
    Synprs.harpoon_split_branch -> Synext.harpoon_split_branch t

  val disambiguate_harpoon_suffices_branch :
    Synprs.harpoon_suffices_branch -> Synext.harpoon_suffices_branch t

  val disambiguate_harpoon_hypothetical :
    Synprs.harpoon_hypothetical -> Synext.harpoon_hypothetical t

  val disambiguate_harpoon_repl_command :
    Synprs.harpoon_repl_command -> Synext.harpoon_repl_command t
end

module Make
    (Bindings_state : BINDINGS_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Bindings_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Bindings_state.state) :
  HARPOON_DISAMBIGUATION with type state = Bindings_state.state
[@@warning "-67"]
