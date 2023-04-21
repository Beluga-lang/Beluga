(** State definition for the indexing phase.

    @author Marc-Antoine Ouimet *)

open Support
open Beluga_syntax

module type INDEXING_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  (** [fresh_identifier state] is an identifier that is not bound in [state].
      This is used in the indexing of arrow types to Pi-types, and to
      generate parameter identifiers for lambda abstractions that omit the
      parameter identifier.

      In order to avoid potential captures, [identifier] is not a
      syntactically valid identifier. That is, [identifier] printed as is
      cannot be parsed into an identifier.

      For debugging purposes, [identifier] is of the form ["\"i#"] where
      ['#'] is a positive integer. Ideally, fresh name generation would not
      be needed, but that would require that every AST node in the concrete
      syntax is directly expressible in the approximate and internal
      syntaxes. *)
  val fresh_identifier : state -> Identifier.t

  (** [fresh_identifier_opt state identifier_opt] is [fresh_identifier state]
      if [identifier_opt = Option.None], and [identifier] if
      [identifier_opt = Option.Some identifier]. *)
  val fresh_identifier_opt : state -> Identifier.t Option.t -> Identifier.t

  (** {1 Index of Constants} *)

  val index_of_constant :
       state
    -> Qualified_identifier.t
    -> [ `Lf_type_constant of Id.cid_typ
       | `Lf_term_constant of Id.cid_term
       | `Computation_inductive_type_constant of Id.cid_comp_typ
       | `Computation_stratified_type_constant of Id.cid_comp_typ
       | `Computation_coinductive_type_constant of Id.cid_comp_cotyp
       | `Computation_abbreviation_type_constant of Id.cid_comp_typdef
       | `Computation_term_constructor of Id.cid_comp_const
       | `Computation_term_destructor of Id.cid_comp_dest
       | `Schema_constant of Id.cid_schema
       | `Program_constant of Id.cid_prog
       | `Module of Id.module_id
       ]

  val index_of_lf_type_constant :
    state -> Qualified_identifier.t -> Id.cid_typ

  val index_of_lf_term_constant :
    state -> Qualified_identifier.t -> Id.cid_term

  val index_of_inductive_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typ

  val index_of_stratified_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typ

  val index_of_coinductive_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_cotyp

  val index_of_abbreviation_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typdef

  val index_of_schema_constant :
    state -> Qualified_identifier.t -> Id.cid_schema

  val index_of_comp_constructor :
    state -> Qualified_identifier.t -> Id.cid_comp_const

  val index_of_comp_destructor :
    state -> Qualified_identifier.t -> Id.cid_comp_dest

  val index_of_comp_program : state -> Qualified_identifier.t -> Id.cid_prog

  (** {1 Index of Variables} *)

  (** [index_of_lf_variable state identifier] is the LF-bound de Bruijn index
      of [identifier] in [state].

      If [identifier] is unbound, then an exception is raised. *)
  val index_of_lf_variable : state -> Identifier.t -> Id.offset

  (** [index_of_lf_variable_opt state identifier] is the LF-bound de Bruijn
      index of [identifier] in [state].

      If [identifier] is unbound, then [offset_opt = Option.None].

      If [state] is a pattern state, then [offset_opt] is additionally
      [Option.None] if it is not an inner bound variable. *)
  val index_of_lf_variable_opt : state -> Identifier.t -> Id.offset Option.t

  (** [index_of_meta_variable state identifier] is the meta-level de Bruijn
      index of [identifier] in [state].

      If [identifier] is unbound, bound to a different entry than a
      meta-variable, or bound to a meta-variable of unknown de Bruijn level,
      then an exception is raised. *)
  val index_of_meta_variable : state -> Identifier.t -> Id.offset

  (** [index_of_meta_variable_opt state identifier] is the meta-level de
      Bruijn index of [identifier] in [state].

      - If [identifier] is unbound, then [offset_opt = Option.None].
      - If [identifier] is a bound meta-variable whose de Bruijn level is
        unknown (i.e. its binder is a meta-variable in a pattern), then
        [offset_opt = Option.None].
      - If [state] is a pattern state, then [offset_opt = Option.None] if it
        is not an inner bound variable. *)
  val index_of_meta_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_parameter_variable : state -> Identifier.t -> Id.offset

  val index_of_parameter_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_substitution_variable : state -> Identifier.t -> Id.offset

  val index_of_substitution_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_context_variable : state -> Identifier.t -> Id.offset

  val index_of_context_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_comp_variable : state -> Identifier.t -> Id.offset

  (** {1 Binding Variables} *)

  (** [with_bound_lf_variable state identifier m] runs [m] in a state where
      [identifier] is a bound LF variable.

      If [state] is a pattern state, then [identifier] is additionally
      considered as an inner bound variable. *)
  val with_bound_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_bound_contextual_variable state identifier m] runs [m] in a state
      where [identifier] is either a bound meta, parameter, substitution or
      context variable. This is necessary for [mlam]-expressions

      If [state] is a pattern state, then [identifier] is additionally
      considered as an inner bound variable. *)
  val with_bound_contextual_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_comp_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_shifted_lf_context state m] is like
      [with_bound_lf_variable state _ m] without adding any identifier in the
      namespace. That is, LF context de Bruijn indices looked up in [m] are
      [+ 1] of what they were in [state]. This is used for omitted parameters
      to lambda terms, like [\_. x]. *)
  val with_shifted_lf_context : state -> (state -> 'a) -> 'a

  val with_shifted_meta_context : state -> (state -> 'a) -> 'a

  val with_shifted_comp_context : state -> (state -> 'a) -> 'a

  val add_lf_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t

  val add_lf_term_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t

  val add_schema_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t

  val add_inductive_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_stratified_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_coinductive_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_cotyp
    -> Unit.t

  val add_abbreviation_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typdef
    -> Unit.t

  val add_computation_term_constructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_const
    -> Unit.t

  val add_computation_term_destructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_dest
    -> Unit.t

  val add_program_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t

  val start_module : state -> Unit.t

  val stop_module :
    state -> ?location:Location.t -> Identifier.t -> Int.t -> Unit.t

  val add_module :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.module_id
    -> (state -> 'a)
    -> 'a

  val open_module :
    state -> ?location:Location.t -> Qualified_identifier.t -> Unit.t

  val add_module_abbreviation :
       state
    -> ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t

  val with_scope : state -> (state -> 'a) -> 'a

  val with_parent_scope : state -> (state -> 'a) -> 'a

  (** [with_bindings_checkpoint state m] runs [m] with a checkpoint on the
      bindings' state to backtrack to in case [m] raises an exception. *)
  val with_bindings_checkpoint : state -> (state -> 'a) -> 'a

  (** {1 Pattern Variables} *)

  (** [with_free_variables_as_pattern_variables state ~pattern ~expression]
      runs [pattern] while keeping track of free and pattern variables, then
      runs [expression] with the free and pattern variables as bound
      variables. *)
  val with_free_variables_as_pattern_variables :
    state -> pattern:(state -> 'a) -> expression:(state -> 'a -> 'b) -> 'b

  val add_computation_pattern_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** {1 Free Variables} *)

  (** [add_free_lf_variable state identifier] adds [identifier] as a free LF
      variable.

      If [identifier] is a free variable in [state] of a different kind than
      LF variables, then an exception is raised. *)
  val add_free_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_context_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val with_bound_pattern_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [allow_free_variables state m] runs [m] and discards the tracked free
      variables therein. *)
  val allow_free_variables : state -> (state -> 'a) -> 'a

  (** [disallow_free_variables state m] runs [m] and raises an exception if
      [m] adds a free variable to the state. *)
  val disallow_free_variables : state -> (state -> 'a) -> 'a

  (** {1 Interoperability} *)

  (** [add_all_bvar_store state store] adds all LF-bound variables in
      [store]. *)
  val add_all_bvar_store : state -> Store.BVar.t -> Unit.t

  (** [add_all_cvar_store state store] adds all contextual variables in
      [store]. *)
  val add_all_cvar_store : state -> Store.CVar.t -> Unit.t

  (** [add_all_var_store state store] adds all computation-level variables in
      [store]. *)
  val add_all_var_store : state -> Store.Var.t -> Unit.t

  (** [add_all_mctx state cD] adds all contextual variables in [cD]. *)
  val add_all_mctx : state -> Synint.LF.mctx -> Unit.t

  (** [add_all_gctx state cG] adds all computation-level variables in [cG]. *)
  val add_all_gctx : state -> Synint.Comp.gctx -> Unit.t
end

module Indexing_state : sig
  include INDEXING_STATE

  val start_module : state -> Unit.t

  val stop_module :
    state -> ?location:Location.t -> Identifier.t -> Id.module_id -> Unit.t

  val create_initial_state : Unit.t -> state
end
