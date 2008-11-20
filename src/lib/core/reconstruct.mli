(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)

open Syntax



(* The following functions just translate the external syntax to
   internal syntax, performing scope checking along the way *)

val internalize_sgn_decl :                 Ext.LF.sgn_decl -> Int.LF.sgn_decl

val internalize_kind     : Store.BVar.t -> Ext.LF.kind     -> Int.LF.kind

val internalize_typ      : Store.BVar.t -> Ext.LF.typ      -> Int.LF.typ

val internalize_term     : Store.BVar.t -> Ext.LF.normal   -> Int.LF.normal

val internalize_head     : Store.BVar.t -> Ext.LF.head     -> Int.LF.head

val internalize_spine    : Store.BVar.t -> Ext.LF.spine    -> Int.LF.spine

(* type reconstruction *)
val reconstruct_sgn_decl : Ext.LF.sgn_decl -> Int.LF.sgn_decl
