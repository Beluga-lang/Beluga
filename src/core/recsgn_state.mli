open Support
open Beluga_syntax.Syncom

module type SIGNATURE_RECONSTRUCTION_STATE = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  val get_leftover_vars :
    state -> (Abstract.free_var Synint.LF.ctx * Location.t) List.t

  val add_leftover_vars :
    state -> Abstract.free_var Synint.LF.ctx -> Location.t -> Unit.t

  (** [disable_lf_strengthening state ~location] disables the strengthening
      of LF terms and types during LF reconstruction.

      [location] is the location to use for error-reporting in case of
      failure to perform [disable_lf_strengthening ~location]. *)
  val with_disabled_lf_strengthening :
    state -> location:Location.t -> (state -> 'a) -> 'a

  (** [with_warn_on_coverage_error state ~location] sets the error-reporting
      mode of pattern coverage-checking to `warn'.

      [location] is the location to use for error-reporting in case of
      failure to perform [with_warn_on_coverage_error ~location]. *)
  val with_warn_on_coverage_error :
    state -> location:Location.t -> (state -> 'a) -> 'a

  (** [with_coverage_checking state ~location] enables coverage-checking.

      [location] is the location to use for error-reporting in case of
      failure to perform [with_coverage_checking ~location]. *)
  val with_coverage_checking :
    state -> location:Location.t -> (state -> 'a) -> 'a

  (** [set_name_generation_bases state ~location ~meta_variable_base ?computation_variable_base constant]
      sets the naming convention for name generation of meta-level and
      computation-level variables using [meta_variable_base] and
      [computation_variable_base] respectively for a type-level constant
      [constant].

      [location] is the location to use for error-reporting in case of
      failure to perform
      [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant].*)
  val set_name_generation_bases :
       state
    -> location:Location.t
    -> meta_variable_base:Identifier.t
    -> ?computation_variable_base:Identifier.t
    -> Qualified_identifier.t
    -> Unit.t

  val set_default_associativity :
    state -> ?location:Location.t -> Associativity.t -> Unit.t

  val get_default_associativity : state -> Associativity.t

  val set_default_precedence :
    state -> ?location:Location.t -> Int.t -> Unit.t

  val get_default_precedence : state -> Int.t

  val add_prefix_notation :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t

  val add_infix_notation :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  val add_postfix_notation :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [add_postponed_prefix_notation state ?location ?precedence identifier]
      adds a postponed prefix notation for [identifier]. If
      [precedence = Option.None], then {!get_default_precedence} is used
      instead.

      This notation is postponed, meaning that it only applies once
      {!val:apply_postponed_fixity_pragmas} is called. *)
  val add_postponed_prefix_notation :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [add_postponed_infix_notation state ?location ?precedence ?associativity identifier]
      adds a postponed infix notation for [identifier]. If
      [precedence = Option.None], then {!get_default_precedence} is used
      instead. Likewise, if [associativity = Option.None], then
      {!get_default_associativity} is used instead.

      This notation is postponed, meaning that it only applies once
      {!val:apply_postponed_fixity_pragmas} is called. *)
  val add_postponed_infix_notation :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [add_postponed_postfix_notation state ?location ?precedence identifier]
      adds a postponed postfix notation for [identifier]. If
      [precedence = Option.None], then {!get_default_precedence} is used
      instead.

      This notation is postponed, meaning that it only applies once
      {!val:apply_postponed_fixity_pragmas} is called. *)
  val add_postponed_postfix_notation :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [apply_postponed_fixity_pragmas state] adds in scope the postponed
      prefix, infix and postfix fixity pragmas. This function should be
      called only when the targets of those postponed pragmas are in scope.
      That is, postponed fixity pragmas are applied after the subsequent
      declaration is added, or after a group of mutually recursive
      declarations are added. *)
  val apply_postponed_fixity_pragmas : state -> unit

  (** [apply_postponed_fixity_pragmas_for_constant state identifier] adds in
      scope the postponed fixity pragmas for the constant having identifier
      [identifier]. *)
  val apply_postponed_fixity_pragmas_for_constant :
    state -> Identifier.t -> unit

  val open_module :
    state -> ?location:Location.t -> Qualified_identifier.t -> Unit.t

  val add_module_abbreviation :
       state
    -> ?location:Location.t
    -> Qualified_identifier.t
    -> abbreviation:Identifier.t
    -> Unit.t

  (** [with_checkpoint state m] is the result of running [m] with [state].
      Note that the state is rolled back entirely. *)
  val with_checkpoint : state -> (state -> 'a) -> 'a

  (** {1 ID Allocation} *)

  val next_module_id : state -> Id.module_id

  (** {1 Indexing} *)

  (** [index_lf_kind state kind] is [kind] indexed with respect to [state].
      Free variables in [kind] are discarded. *)
  val index_lf_kind : state -> Synext.lf_kind -> Synapx.LF.kind

  val index_lf_typ : state -> Synext.lf_typ -> Synapx.LF.typ

  val index_schema : state -> Synext.schema -> Synapx.LF.schema

  val index_comp_kind : state -> Synext.comp_kind -> Synapx.Comp.kind

  val index_comp_typ : state -> Synext.comp_typ -> Synapx.Comp.typ

  val index_comp_expression :
    state -> Synext.comp_expression -> Synapx.Comp.exp

  val index_comp_typedef :
       state
    -> Synext.comp_typ
    -> Synext.comp_kind
    -> Synapx.Comp.typ * Synapx.Comp.kind

  val index_comp_theorem : state -> Synext.comp_expression -> Synapx.Comp.thm

  val index_harpoon_proof : state -> Synext.harpoon_proof -> Synapx.Comp.thm

  (** Adding a constant or module introduces an identifier in the state.
      Whenever an extensible declaration is shadowed, it is frozen. *)

  (** [add_lf_type_constant state ?location identifier id] adds the LF type
      constant having identifier [identifier], ID [cid] and binding site
      [location] to the state. If [location = Option.None], then the
      identifier's location is used as binding site. *)
  val add_lf_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t

  val add_lf_term_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t

  val add_schema_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t

  val add_prog :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t

  val add_comp_val :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t

  val add_comp_typedef :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typdef
    -> Unit.t

  val add_comp_inductive_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_comp_stratified_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_comp_cotype_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_cotyp
    -> Unit.t

  val add_comp_constructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_const
    -> Unit.t

  val add_comp_destructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_dest
    -> Unit.t

  (** [add_module state ?location identifier cid m] adds the module having
      identifier [identifier] and binding site [location] to the state. The
      action [m] is executed in the module's state. [m] is typically the
      reconstruction of the module's entries. *)
  val add_module :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.module_id
    -> (state -> 'a)
    -> 'a

  (** [freeze_all_unfrozen_declarations state] freezes all the unfrozen
      declarations. Unfrozen declarations are LF type families in oldstyle
      syntax, and to which new LF term-level constants may be added. *)
  val freeze_all_unfrozen_declarations : state -> Unit.t
end

module Make_signature_reconstruction_state
    (Index_state : Index_state.INDEXING_STATE)
    (Index : Index.INDEXER with type state = Index_state.state) : sig
  include SIGNATURE_RECONSTRUCTION_STATE

  val create_initial_state : Index_state.state -> state

  val clear_state :
    clear_index_state:(Index_state.state -> unit) -> state -> unit
end
[@@warning "-67"]

module Signature_reconstruction_state :
    module type of
      Make_signature_reconstruction_state
        (Index_state.Indexing_state)
        (Index.Indexer)
