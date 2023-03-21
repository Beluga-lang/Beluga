(** Name resolution and translation from the concrete syntax to the
    approximate syntax.

    @author Marie-Andrée B. Langlois
    @author Esma Balkir
    @author Olivier Belanger Savary
    @author Mathieu Boespflug
    @author Costin Bădescu
    @author Andrew Cave
    @author Scott Cooper
    @author Jacob Errington
    @author Francisco Ferreira
    @author Philipp Haselwarter G.
    @author Junyoung Jang Clare
    @author Aidan Marchildon
    @author Agata Murawska
    @author Marc-Antoine Ouimet
    @author Brigitte Pientka
    @author David Thibodeau
    @author Tao Xue *)

open Support
open Beluga_syntax

module type INDEXER = sig
  include State.STATE

  (** [index_lf_typ_constant_kind kind state] is [(state', kind')] where
      [kind'] is [kind] with bound variables and constants replaced with de
      Bruijn indices and IDs respectively.

      [kind] appears in LF type-level constant declarations, so it may
      contain free variables. *)
  val index_lf_typ_constant_kind : Synext.lf_kind -> Synapx.LF.kind t

  (** [index_lf_term_constant_typ typ state] is [(state', typ')] where [typ']
      is [typ] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively.

      [typ] appears in LF term-level constant declarations, so it may contain
      free variables. *)
  val index_lf_term_constant_typ : Synext.lf_typ -> Synapx.LF.typ t

  (** [index_comp_typ_constant_kind kind state] is [(state', kind')] where
      [kind'] is [kind] with bound variables and constants replaced with de
      Bruijn indices and IDs respectively.

      [kind] appears in computation-level type constant declarations, so it
      may contain free variables. *)
  val index_comp_typ_constant_kind : Synext.comp_kind -> Synapx.Comp.kind t

  (** [index_comp_term_constant_typ typ state] is [(state', typ')] where
      [typ'] is [typ] with bound variables and constants replaced with de
      Bruijn indices and IDs respectively.

      [typ] appears in computation-level constructor or destructor constant
      declarations, so it may contain free variables. *)
  val index_comp_term_constant_typ : Synext.comp_typ -> Synapx.Comp.typ t

  (** [index_comp_expression expression state] is [(state', expression')]
      where [expression'] is [expression] with bound variables and constants
      replaced with de Bruijn indices and IDs respectively.

      [expression] appears in value or function declarations, so free
      variables are disallowed, such that an exception is raised if
      [expression] contains free variables. *)
  val index_comp_expression : Synext.comp_expression -> Synapx.Comp.exp t

  (** [index_comp_typ typ state] is [(state', typ')] where [typ'] is [typ]
      with bound variables and constants replaced with de Bruijn indices and
      IDs respectively.

      [typ] appears in value or function declarations, so free variables are
      disallowed, such that an exception is raised if [typ] contains free
      variables. *)
  val index_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  val index_schema : Synext.schema -> Synapx.LF.schema t

  val index_comp_theorem : Synext.comp_expression -> Synapx.Comp.thm t

  val index_harpoon_proof : Synext.harpoon_proof -> Synapx.Comp.thm t

  val index_computation_typ_abbreviation :
       Synext.comp_typ
    -> Synext.comp_kind
    -> (Synapx.Comp.typ * Synapx.Comp.kind) t
end

module Make_indexer (Indexing_state : Index_state.INDEXING_STATE) :
  INDEXER with type state = Indexing_state.state

module Indexer : sig
  (** @closed *)
  include module type of Make_indexer (Index_state.Persistent_indexing_state)

  (** @closed *)
  include module type of Index_state.Persistent_indexing_state
end
