(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

open Context
open Syntax.Int

val id   : Comp.msub
val shift: Comp.msub -> int -> Comp.msub
val shiftTerm: LF.normal -> int -> LF.normal
val shiftTyp : LF.typ  -> int -> LF.typ

val mvar_dot1  : LF.psi_hat -> Comp.msub -> Comp.msub
val pvar_dot1  : LF.psi_hat -> Comp.msub -> Comp.msub
val ctxvar_dot1: Comp.msub -> Comp.msub

val comp: Comp.msub -> Comp.msub -> Comp.msub

val cnorm   : LF.normal * Comp.msub -> LF.normal
val cnormTyp: LF.typ  * Comp.msub -> LF.typ
val cnormTypRec: LF.typ_rec * Comp.msub -> LF.typ_rec
val cnormDCtx  : LF.dctx * Comp.msub -> LF.dctx

val cwhnfCTyp  : Comp.typ * Comp.msub -> Comp.typ * Comp.msub
val cnormExp   : Comp.exp_chk * Comp.msub -> Comp.exp_chk
val cnormCtx   : (Id.name * Comp.typ) LF.ctx * Comp.msub -> (Id.name * Comp.typ) LF.ctx

val convCTyp   : (Comp.typ * Comp.msub) -> (Comp.typ * Comp.msub) -> bool

