(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html

    @author Darin Morrison
*)



open Format



type lvl

val std_lvl : lvl



module Id : sig

  open Core.Id



  (********************************)
  (* Format Based Pretty Printers *)
  (********************************)

  val fmt_ppr_name     : formatter -> name     -> unit

  val fmt_ppr_cid_typ  : formatter -> cid_typ  -> unit

  val fmt_ppr_cid_term : formatter -> cid_term -> unit



  (***************************)
  (* Default Pretty Printers *)
  (***************************)

  val ppr_name     : name     -> unit

  val ppr_cid_typ  : cid_typ  -> unit

  val ppr_cid_term : cid_term -> unit

end



module Ext : sig

  open Core.Syntax.Ext



  (*******************************************)
  (* Contextual Format Based Pretty Printers *)
  (*******************************************)

  val fmt_ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

  val fmt_ppr_kind     : lvl -> formatter -> kind     -> unit

  val fmt_ppr_typ      : lvl -> formatter -> typ      -> unit

  val fmt_ppr_term     : lvl -> formatter -> term     -> unit

  val fmt_ppr_head     :        formatter -> head     -> unit

  val fmt_ppr_spine    : lvl -> formatter -> spine    -> unit



  (***************************)
  (* Default Pretty Printers *)
  (***************************)

  val ppr_sgn_decl : sgn_decl -> unit

  val ppr_kind     : kind     -> unit

  val ppr_type     : typ      -> unit

  val ppr_term     : term     -> unit

  val ppr_head     : head     -> unit

  val ppr_spine    : spine    -> unit

end



module Int : sig

  open Core.Syntax.Int



  (*******************************************)
  (* Contextual Format Based Pretty Printers *)
  (*******************************************)

  val fmt_ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

  val fmt_ppr_kind     : lvl -> formatter -> kind     -> unit

  val fmt_ppr_typ      : lvl -> formatter -> typ      -> unit

  val fmt_ppr_term     : lvl -> formatter -> term     -> unit

  val fmt_ppr_head     :        formatter -> head     -> unit

  val fmt_ppr_spine    : lvl -> formatter -> spine    -> unit



  (***************************)
  (* Default Pretty Printers *)
  (***************************)

  val ppr_sgn_decl : sgn_decl -> unit

  val ppr_kind     : kind     -> unit

  val ppr_type     : typ      -> unit

  val ppr_term     : term     -> unit

  val ppr_head     : head     -> unit

  val ppr_spine    : spine    -> unit

end
