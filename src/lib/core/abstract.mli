(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int 

val abstrKind     : LF.kind -> LF.kind * Id.offset

val abstrTyp      : LF.typ  -> LF.typ  * Id.offset

val abstractMSub  : Comp.msub -> Comp.msub * LF.mctx

val abstrCompTyp  : Comp.typ  -> Comp.typ * Id.offset

val abstrExp      : Comp.exp_chk  -> Comp.exp_chk

val abstrPattern  : LF.mctx -> LF.dctx -> (LF.psi_hat * LF.normal) -> LF.typ -> 
                    LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) * LF.typ
