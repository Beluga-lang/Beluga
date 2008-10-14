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

  val ppr_name : formatter -> name -> unit

end



module Ext : sig

  open Core.Syntax.Ext

  val ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

  val ppr_kind     : lvl -> formatter -> kind     -> unit

  val ppr_type     : lvl -> formatter -> typ      -> unit

  val ppr_term     : lvl -> formatter -> term     -> unit

  val ppr_head     :        formatter -> head     -> unit

  val ppr_spine    : lvl -> formatter -> spine    -> unit

end



(* module Int : sig *)

(*   val ppr_sgn_decl : Format.formatter -> Int.sgn_decl -> unit *)

(*   val ppr_kind     : Format.formatter -> Int.kind     -> unit *)

(*   val ppr_type     : Format.formatter -> Int.typ      -> unit *)

(*   val ppr_term     : Format.formatter -> Int.term     -> unit *)

(*   val ppr_head     : Format.formatter -> Int.head     -> unit *)

(*   val ppr_spine    : Format.formatter -> Int.spine    -> unit *)

(* end *)
