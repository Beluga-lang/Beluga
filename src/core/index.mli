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
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** [index_open_lf_kind state kind] is [kind] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are allowed in [kind] with respect to [state]. *)
  val index_open_lf_kind : state -> Synext.lf_kind -> Synapx.LF.kind

  (** [index_closed_lf_kind state kind] is [kind] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are disallowed in [kind] with respect to [state]. *)
  val index_closed_lf_kind : state -> Synext.lf_kind -> Synapx.LF.kind

  (** [index_open_lf_typ state typ] is [typ] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are allowed in [typ] with respect to [state] *)
  val index_open_lf_typ : state -> Synext.lf_typ -> Synapx.LF.typ

  (** [index_closed_lf_typ state typ] is [typ] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are disallowed in [typ] with respect to [state] *)
  val index_closed_lf_typ : state -> Synext.lf_typ -> Synapx.LF.typ

  (** [index_open_comp_kind state kind] is [kind] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are allowed in [kind] with respect to [state]. *)
  val index_open_comp_kind : state -> Synext.comp_kind -> Synapx.Comp.kind

  (** [index_closed_comp_kind state kind] is [kind] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are disallowed in [kind] with respect to [state]. *)
  val index_closed_comp_kind : state -> Synext.comp_kind -> Synapx.Comp.kind

  (** [index_open_comp_typ state typ] is [typ] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are allowed in [typ] with respect to [state]. *)
  val index_open_comp_typ : state -> Synext.comp_typ -> Synapx.Comp.typ

  (** [index_closed_comp_typ state typ] is [typ] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are disallowed in [typ] with respect to [state]. *)
  val index_closed_comp_typ : state -> Synext.comp_typ -> Synapx.Comp.typ

  (** [index_comp_expression state expression] is [expression] with bound
      variables and constants replaced with de Bruijn indices and IDs
      respectively. Free variables are disallowed in [expression] with
      respect to [state]. *)
  val index_comp_expression :
    state -> Synext.comp_expression -> Synapx.Comp.exp

  (** [index_schema state schema] is [schema] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are allowed in [schema] with respect to [state]. *)
  val index_schema : state -> Synext.schema -> Synapx.LF.schema

  (** [index_comp_theorem state theorem] is [theorem] with bound variables
      and constants replaced with de Bruijn indices and IDs respectively.
      Free variables are disallowed in [theorem] with respect to [state]. *)
  val index_comp_theorem : state -> Synext.comp_expression -> Synapx.Comp.thm

  (** [index_harpoon_proof state proof] is [proof] with bound variables and
      constants replaced with de Bruijn indices and IDs respectively. Free
      variables are disallowed in [proof] with respect to [state]. *)
  val index_harpoon_proof : state -> Synext.harpoon_proof -> Synapx.Comp.thm

  (** [index_computation_typ_abbreviation state typ kind] is [(typ', kind')]
      where [kind'] is [kind] and [typ'] is [typ], both with bound variables
      and constants replaced with de Bruijn indices and IDs respectively.
      Overall, free variables are disallowed with respect to [state].
      Variables bound in Pi-kinds in [kind] count as bound in [typ]. *)
  val index_computation_typ_abbreviation :
       state
    -> Synext.comp_typ
    -> Synext.comp_kind
    -> Synapx.Comp.typ * Synapx.Comp.kind
end

module Make_indexer (Indexing_state : Index_state.INDEXING_STATE) :
  INDEXER with type state = Indexing_state.state

module Indexer : sig
  (** @closed *)
  include INDEXER with type state = Index_state.Indexing_state.state

  (** @closed *)
  include Index_state.INDEXING_STATE with type state := state
end
