open Support
open Beluga_syntax

module type SIGNATURE_RECONSTRUCTION_STATE = sig
  include State.STATE

  val get_leftover_vars :
    (Abstract.free_var Synint.LF.ctx * Location.t) List.t t

  val add_leftover_vars :
    Abstract.free_var Synint.LF.ctx -> Location.t -> Unit.t t

  (** [disable_lf_strengthening ~location] disables the strengthening of LF
      terms and types during LF reconstruction.

      [location] is the location to use for error-reporting in case of
      failure to perform [disable_lf_strengthening ~location]. *)
  val with_disabled_lf_strengthening : location:Location.t -> 'a t -> 'a t

  (** [with_warn_on_coverage_error ~location] sets the error-reporting mode
      of pattern coverage-checking to `warn'.

      [location] is the location to use for error-reporting in case of
      failure to perform [with_warn_on_coverage_error ~location]. *)
  val with_warn_on_coverage_error : location:Location.t -> 'a t -> 'a t

  (** [with_coverage_checking ~location] enables coverage-checking.

      [location] is the location to use for error-reporting in case of
      failure to perform [with_coverage_checking ~location]. *)
  val with_coverage_checking : location:Location.t -> 'a t -> 'a t

  (** [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant]
      sets the naming convention for name generation of meta-level and
      computation-level variables using [meta_variable_base] and
      [computation_variable_base] respectively for a type-level constant
      [constant].

      [location] is the location to use for error-reporting in case of
      failure to perform
      [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant].*)
  val set_name_generation_bases :
       location:Location.t
    -> meta_variable_base:Identifier.t
    -> ?computation_variable_base:Identifier.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_default_associativity :
    ?location:Location.t -> Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val set_default_precedence : ?location:Location.t -> Int.t -> Unit.t t

  val get_default_precedence : Int.t t

  val set_operator_prefix :
       ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_operator_infix :
       ?location:Location.t
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_operator_postfix :
       ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t t

  val open_module :
    ?location:Location.t -> Qualified_identifier.t -> Unit.t t

  val add_module_abbreviation :
       ?location:Location.t
    -> Qualified_identifier.t
    -> abbreviation:Identifier.t
    -> Unit.t t

  (** [with_checkpoint m state] is [(state, x)] where [x] is the result of
      running [m] with [state]. Note that the state is rolled back entirely. *)
  val with_checkpoint : 'a t -> 'a t

  (** {1 ID Allocation} *)

  val next_module_id : Id.module_id t

  (** {1 Indexing} *)

  (** [index_lf_kind kind state] is [(state', kind')] where [kind'] is [kind]
      indexed with respect to [state]. Free variables in [kind] are discarded
      in [state']. *)
  val index_lf_kind : Synext.lf_kind -> Synapx.LF.kind t

  val index_lf_typ : Synext.lf_typ -> Synapx.LF.typ t

  val index_schema : Synext.schema -> Synapx.LF.schema t

  val index_meta_context : Synext.meta_context -> Synapx.LF.mctx t

  val index_comp_kind : Synext.comp_kind -> Synapx.Comp.kind t

  val index_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  val index_closed_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  val index_comp_expression : Synext.comp_expression -> Synapx.Comp.exp t

  val index_comp_typedef :
       Synext.comp_typ
    -> Synext.comp_kind
    -> (Synapx.Comp.typ * Synapx.Comp.kind) t

  val index_comp_theorem : Synext.comp_expression -> Synapx.Comp.thm t

  val index_harpoon_proof : Synext.harpoon_proof -> Synapx.Comp.thm t

  (** Adding a constant or module introduces an identifier in the state.
      Whenever an extensible declaration is shadowed, it is frozen. *)

  (** [add_lf_type_constant ?location identifier id] adds the LF type
      constant having identifier [identifier], ID [cid] and binding site
      [location] to the state. If [location = Option.None], then the
      identifier's location is used as binding site. *)
  val add_lf_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t t

  val add_schema_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t t

  val add_prog :
    ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t t

  val add_comp_val :
    ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t t

  val add_comp_typedef :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typdef -> Unit.t t

  val add_comp_inductive_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typ -> Unit.t t

  val add_comp_stratified_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typ -> Unit.t t

  val add_comp_cotype_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_cotyp -> Unit.t t

  val add_comp_constructor :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_const -> Unit.t t

  val add_comp_destructor :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_dest -> Unit.t t

  (** [add_module ?location identifier m] adds the module having identifier
      [identifier] and bindinng site [location] to the state. The action [m]
      is executed in the module's state. [m] is typically the reconstruction
      of the module's entries. *)
  val add_module :
    ?location:Location.t -> Identifier.t -> Id.module_id -> 'a t -> 'a t
end

module Make_signature_reconstruction_state (Index_state : sig
  include Index_state.INDEXING_STATE

  val start_module : Unit.t t

  val stop_module :
    ?location:Location.t -> Identifier.t -> Id.module_id -> Unit.t t
end)
(Index : Index.INDEXER with type state = Index_state.state) : sig
  include SIGNATURE_RECONSTRUCTION_STATE

  val initial_state : Index_state.state -> state
end
[@@warning "-67"]

module Signature_reconstruction_state :
    module type of
      Make_signature_reconstruction_state
        (Index_state.Persistent_indexing_state)
        (Index.Indexer)
