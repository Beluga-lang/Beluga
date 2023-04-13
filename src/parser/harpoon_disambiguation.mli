open Support
open Beluga_syntax
open Disambiguation_state

module type HARPOON_DISAMBIGUATION = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** {1 Disambiguation} *)

  val disambiguate_harpoon_proof :
    state -> Synprs.harpoon_proof -> Synext.harpoon_proof

  val with_disambiguated_harpoon_command :
       state
    -> Synprs.harpoon_command
    -> (state -> Synext.harpoon_command -> 'a)
    -> 'a

  val disambiguate_harpoon_directive :
    state -> Synprs.harpoon_directive -> Synext.harpoon_directive

  val disambiguate_harpoon_split_branch :
    state -> Synprs.harpoon_split_branch -> Synext.harpoon_split_branch

  val disambiguate_harpoon_suffices_branch :
    state -> Synprs.harpoon_suffices_branch -> Synext.harpoon_suffices_branch

  val disambiguate_harpoon_hypothetical :
    state -> Synprs.harpoon_hypothetical -> Synext.harpoon_hypothetical

  val disambiguate_harpoon_repl_command :
    state -> Synprs.harpoon_repl_command -> Synext.harpoon_repl_command
end

module Make
    (Disambiguation_state : DISAMBIGUATION_STATE)
    (Meta_disambiguation : Meta_disambiguation.META_DISAMBIGUATION
                             with type state = Disambiguation_state.state)
    (Comp_disambiguation : Comp_disambiguation.COMP_DISAMBIGUATION
                             with type state = Disambiguation_state.state) :
  HARPOON_DISAMBIGUATION with type state = Disambiguation_state.state
[@@warning "-67"]
