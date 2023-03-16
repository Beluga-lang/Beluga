(** State definition for the indexing phase.

    @author Marc-Antoine Ouimet *)

open Support
open Beluga_syntax

module type INDEXING_STATE = sig
  include State.STATE

  (** [fresh_identifier state] is [(state', identifier)] where [identifier]
      is an identifier that is not bound in [state]. This is used in the
      indexing of arrow types to Pi-types, and to generate parameter
      identifiers for lambda abstractions that omit the parameter identifier.

      In order to avoid potential captures, [identifier] is not a
      syntactically valid identifier. That is, [identifier] printed as is
      cannot be parsed into an identifier.

      For debugging purposes, [identifier] is of the form ["\"i#"] where
      ['#'] is a positive integer. Ideally, fresh name generation would not
      be needed, but that would require that every AST node in the concrete
      syntax is directly expressible in the approximate and internal
      syntaxes. *)
  val fresh_identifier : Identifier.t t

  val fresh_identifier_opt : Identifier.t Option.t -> Identifier.t t

  (** {1 Index of Constants} *)

  val index_of_lf_typ_constant : Qualified_identifier.t -> Id.cid_typ t

  val index_of_lf_term_constant : Qualified_identifier.t -> Id.cid_term t

  val index_of_inductive_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typ t

  val index_of_stratified_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typ t

  val index_of_coinductive_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_cotyp t

  val index_of_abbreviation_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typdef t

  val index_of_schema_constant : Qualified_identifier.t -> Id.cid_schema t

  val index_of_comp_constructor :
    Qualified_identifier.t -> Id.cid_comp_const t

  val index_of_comp_destructor : Qualified_identifier.t -> Id.cid_comp_dest t

  val index_of_comp_program : Qualified_identifier.t -> Id.cid_prog t

  (** {1 Index of Variables} *)

  (** [index_of_lf_variable identifier state] is [(state', offset)] where
      [offset] is the LF-bound de Bruijn index of [identifier] in [state].

      If [identifier] is unbound, then an exception is raised. *)
  val index_of_lf_variable : Identifier.t -> Id.offset t

  (** [index_of_lf_variable_opt identifier state] is [(state', offset_opt)]
      where [offset_opt] is the LF-bound de Bruijn index of [identifier] in
      [state].

      If [identifier] is unbound, then [offset_opt = Option.None].

      If [state] is a pattern state, then [offset_opt] is additionally
      [Option.None] if it is not an inner bound variable. *)
  val index_of_lf_variable_opt : Identifier.t -> Id.offset Option.t t

  (** [index_of_meta_variable identifier state] is [(state', offset)] where
      [offset] is the meta-level de Bruijn index of [identifier] in [state].

      If [identifier] is unbound, then an exception is raised. *)
  val index_of_meta_variable : Identifier.t -> Id.offset t

  (** [index_of_meta_variable_opt identifier state] is [(state', offset_opt)]
      where [offset_opt] is the meta-level de Bruijn index of [identifier] in
      [state].

      If [identifier] is unbound, then [offset_opt = Option.None].

      If [state] is a pattern state, then [offset_opt] is additionally
      [Option.None] if it is not an inner bound variable. *)
  val index_of_meta_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_parameter_variable : Identifier.t -> Id.offset t

  val index_of_parameter_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_substitution_variable : Identifier.t -> Id.offset t

  val index_of_substitution_variable_opt :
    Identifier.t -> Id.offset Option.t t

  val index_of_context_variable : Identifier.t -> Id.offset t

  val index_of_context_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_comp_variable : Identifier.t -> Id.offset t

  (** {1 Binding Variables} *)

  (** [with_bound_lf_variable identifier m state] runs [m] in a state where
      [identifier] is a bound LF variable.

      If [state] is a pattern state, then [identifier] is additionally
      considered as an inner bound variable. *)
  val with_bound_lf_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  (** [with_bound_contextual_variable identifier m state] runs [m] in a state
      where [identifier] is either a bound meta, parameter, substitution or
      context variable. This is necessary for [mlam]-expressions

      If [state] is a pattern state, then [identifier] is additionally
      considered as an inner bound variable. *)
  val with_bound_contextual_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_comp_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  (** [with_shifted_lf_context m state] is like
      [with_bound_lf_variable _ m state] without adding any identifier in the
      namespace. That is, LF context de Bruijn indices looked up in [m] are
      [+ 1] of what they were in [state]. This is used for omitted parameters
      to lambda terms, like [\_. x]. *)
  val with_shifted_lf_context : 'a t -> 'a t

  val with_shifted_meta_context : 'a t -> 'a t

  val with_shifted_comp_context : 'a t -> 'a t

  val add_lf_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t t

  val add_schema_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t t

  val add_inductive_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typ -> Unit.t t

  val add_stratified_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typ -> Unit.t t

  val add_coinductive_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_cotyp -> Unit.t t

  val add_abbreviation_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typdef -> Unit.t t

  val add_computation_term_constructor :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_const -> Unit.t t

  val add_computation_term_destructor :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_dest -> Unit.t t

  val add_program_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t t

  val start_module : Unit.t t

  val stop_module :
    ?location:Location.t -> Identifier.t -> Id.module_id -> Unit.t t

  val add_module :
    ?location:Location.t -> Identifier.t -> Id.module_id -> 'a t -> 'a t

  val with_scope : 'a t -> 'a t

  val with_parent_scope : 'a t -> 'a t

  (** {1 Pattern Variables} *)

  (** [with_free_variables_as_pattern_variables ~pattern ~expression] runs
      [pattern] while keeping track of free and pattern variables, then runs
      [expression] with the free and pattern variables as bound variables. *)
  val with_free_variables_as_pattern_variables :
    pattern:'a t -> expression:('a -> 'b t) -> 'b t

  val add_computation_pattern_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** {1 Free Variables} *)

  (** [add_free_lf_variable identifier state] is [(state', ())] where
      [state'] is derived from [state] by the addition of [identifier] as a
      free LF variable.

      If [identifier] is a free variable in [state] of a different kind than
      LF variables, then an exception is raised. *)
  val add_free_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_meta_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_context_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [allow_free_variables m] runs [m] and discards the tracked free
      variables therein. *)
  val allow_free_variables : 'a t -> 'a t

  (** [disallow_free_variables m] runs [m] and raises an exception if [m]
      adds a free variable to the state. *)
  val disallow_free_variables : 'a t -> 'a t

  (* TODO: Interoperability with {!Store} *)
end

module Persistent_indexing_state : sig
  include INDEXING_STATE

  val initial_state : state
end
