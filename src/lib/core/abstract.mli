(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int 

val abstrKind : LF.kind -> LF.kind * Id.offset

val abstrTyp  : LF.typ  -> LF.typ  * Id.offset

val abstractMSub : Comp.msub -> Comp.msub * LF.mctx
