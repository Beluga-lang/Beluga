(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

open Context
open Syntax.Int

val id   : Comp.msub
val mshift: Comp.msub -> int -> Comp.msub
val mshiftTerm: LF.normal -> int -> LF.normal
val mshiftTyp : LF.typ  -> int -> LF.typ

val mvar_dot1  : Comp.msub -> Comp.msub
val pvar_dot1  : Comp.msub -> Comp.msub

val mcomp      : Comp.msub -> Comp.msub -> Comp.msub

val cnorm      : LF.normal * Comp.msub -> LF.normal
val cnormTyp   : LF.typ  * Comp.msub -> LF.typ
val cnormTypRec: LF.typ_rec * Comp.msub -> LF.typ_rec
val cnormDCtx  : LF.dctx * Comp.msub -> LF.dctx

val cwhnfCTyp  : Comp.typ * Comp.msub -> Comp.typ * Comp.msub
val cwhnfCtx   : (Id.name * Comp.typ) LF.ctx * Comp.msub -> (Id.name * Comp.typ) LF.ctx

val cnormExp   : Comp.exp_chk * Comp.msub -> Comp.exp_chk

val convCTyp   : (Comp.typ * Comp.msub) -> (Comp.typ * Comp.msub) -> bool

val csub_ctyp  : LF.dctx -> int -> Comp.typ -> Comp.typ
val csub_msub  : LF.dctx -> int -> Comp.msub -> Comp.msub
