(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
   @author Renaud Germain
*)



open Syntax



(* The following functions just translate the external syntax to
   internal syntax, performing scope checking along the way *)

val internalize_sgn_decl :                 Ext.sgn_decl -> Int.sgn_decl

val internalize_kind     : Store.BVar.t -> Ext.kind     -> Int.kind

val internalize_typ      : Store.BVar.t -> Ext.typ      -> Int.typ

val internalize_term     : Store.BVar.t -> Ext.normal   -> Int.normal

val internalize_head     : Store.BVar.t -> Ext.head     -> Int.head

val internalize_spine    : Store.BVar.t -> Ext.spine    -> Int.spine
