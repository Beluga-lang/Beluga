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

  (** [index_open_lf_kind kind state] is [(state', kind')] where [kind'] is
      [kind] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are allowed in [kind] with
      respect to [state]. *)
  val index_open_lf_kind : Synext.lf_kind -> Synapx.LF.kind t

  (** [index_closed_lf_kind kind state] is [(state', kind')] where [kind'] is
      [kind] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are disallowed in [kind]
      with respect to [state]. *)
  val index_closed_lf_kind : Synext.lf_kind -> Synapx.LF.kind t

  (** [index_open_lf_typ typ state] is [(state', typ')] where [typ'] is [typ]
      with bound variables and constants replaced with de Bruijn indices and
      IDs respectively. Free variables are allowed in [typ] with respect to
      [state] *)
  val index_open_lf_typ : Synext.lf_typ -> Synapx.LF.typ t

  (** [index_closed_lf_typ typ state] is [(state', typ')] where [typ'] is
      [typ] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are disallowed in [typ]
      with respect to [state] *)
  val index_closed_lf_typ : Synext.lf_typ -> Synapx.LF.typ t

  (** [index_open_comp_kind kind state] is [(state', kind')] where [kind'] is
      [kind] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are allowed in [kind] with
      respect to [state]. *)
  val index_open_comp_kind : Synext.comp_kind -> Synapx.Comp.kind t

  (** [index_closed_comp_kind kind state] is [(state', kind')] where [kind']
      is [kind] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are disallowed in [kind]
      with respect to [state]. *)
  val index_closed_comp_kind : Synext.comp_kind -> Synapx.Comp.kind t

  (** [index_open_comp_typ typ state] is [(state', typ')] where [typ'] is
      [typ] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are allowed in [typ] with
      respect to [state]. *)
  val index_open_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  (** [index_closed_comp_typ typ state] is [(state', typ')] where [typ'] is
      [typ] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are disallowed in [typ]
      with respect to [state]. *)
  val index_closed_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  (** [index_comp_expression expression state] is [(state', expression')]
      where [expression'] is [expression] with bound variables and constants
      replaced with de Bruijn indices and IDs respectively. Free variables
      are disallowed in [expression] with respect to [state]. *)
  val index_comp_expression : Synext.comp_expression -> Synapx.Comp.exp t

  (** [index_schema schema state] is [(state', schema')] where [schema'] is
      [schema] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are disallowed in [schema]
      with respect to [state]. *)
  val index_schema : Synext.schema -> Synapx.LF.schema t

  (** [index_comp_theorem theorem state] is [(state', theorem')] where
      [theorem'] is [theorem] with bound variables and constants replaced
      with de Bruijn indices and IDs respectively. Free variables are
      disallowed in [theorem] with respect to [state]. *)
  val index_comp_theorem : Synext.comp_expression -> Synapx.Comp.thm t

  (** [index_harpoon_proof proof state] is [(state', proof')] where [proof']
      is [proof] with bound variables and constants replaced with de Bruijn
      indices and IDs respectively. Free variables are disallowed in [proof]
      with respect to [state]. *)
  val index_harpoon_proof : Synext.harpoon_proof -> Synapx.Comp.thm t

  (** [index_computation_typ_abbreviation typ kind] is
      [(state', (typ', kind'))] where [kind'] is [kind] and [typ'] is [typ],
      both with bound variables and constants replaced with de Bruijn indices
      and IDs respectively. Overall, free variables are disallowed with
      respect to [state]. Variables bound in Pi-kinds in [kind] count as
      bound in [typ]. *)
  val index_computation_typ_abbreviation :
       Synext.comp_typ
    -> Synext.comp_kind
    -> (Synapx.Comp.typ * Synapx.Comp.kind) t

  (** [index_lf_query meta_context typ state] is
      [(state', (meta_context', typ'))] where [meta_context'] is
      [meta_context] and [typ'] is [typ], both with bound variables and
      constants replaced with de Bruijn indices and IDs respectively.
      Overall, free variables are allowed with respect to [state]. Variables
      bound in [meta_context] count as bound in [typ]. *)
  val index_lf_query :
       Synext.meta_context
    -> Synext.clf_typ
    -> (Synapx.LF.mctx * Synapx.LF.typ) t
end

module Make_indexer (Indexing_state : Index_state.INDEXING_STATE) :
  INDEXER with type state = Indexing_state.state

module Indexer : sig
  (** @closed *)
  include module type of Make_indexer (Index_state.Persistent_indexing_state)

  (** @closed *)
  include module type of Index_state.Persistent_indexing_state
end
