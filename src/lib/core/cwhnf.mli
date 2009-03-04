(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

open Context
open Syntax.Int

exception Fmvar_not_found
exception FreeMVar of LF.head
exception NonInvertible 


val id   : Comp.msub
val mshift: Comp.msub -> int -> Comp.msub
val mshiftTerm: LF.normal -> int -> LF.normal
val mshiftTyp : LF.typ  -> int -> LF.typ

val mvar_dot1  : Comp.msub -> Comp.msub
val pvar_dot1  : Comp.msub -> Comp.msub

val mcomp      : Comp.msub -> Comp.msub -> Comp.msub

val invert     : Comp.msub -> Comp.msub

val invExp     : Comp.exp_chk * Comp.msub -> int -> Comp.exp_chk 
val invTerm    : LF.normal    * Comp.msub -> int -> LF.normal

val mctxMDec   : LF.mctx -> int -> LF.typ * LF.dctx
val mctxPDec   : LF.mctx -> int -> LF.typ * LF.dctx


val mctxMVarPos : LF.mctx -> Id.name -> (Id.offset * (LF.typ * LF.dctx))
val mctxPVarPos : LF.mctx -> Id.name -> (Id.offset * (LF.typ * LF.dctx))

val applyMSub   : Id.offset -> Comp.msub -> Comp.mfront


val cnorm      : LF.normal * Comp.msub -> LF.normal
val cnormTyp   : LF.typ  * Comp.msub -> LF.typ
val cnormTypRec: LF.typ_rec * Comp.msub -> LF.typ_rec
val cnormDCtx  : LF.dctx * Comp.msub -> LF.dctx

val cnormMSub  : Comp.msub -> Comp.msub

val cnormCTyp  : Comp.typ * Comp.msub -> Comp.typ
val cwhnfCTyp  : Comp.typ * Comp.msub -> Comp.typ * Comp.msub
val cwhnfCtx   : Comp.gctx * Comp.msub -> Comp.gctx

val cnormExp   : Comp.exp_chk * Comp.msub -> Comp.exp_chk
val cnormExp'  : Comp.exp_syn * Comp.msub -> Comp.exp_syn

val normCtx    : Comp.gctx -> Comp.gctx
val normCTyp   : Comp.typ  -> Comp.typ


val convCTyp   : (Comp.typ * Comp.msub) -> (Comp.typ * Comp.msub) -> bool

val csub_ctyp  : LF.dctx -> int -> Comp.typ -> Comp.typ
val csub_msub  : LF.dctx -> int -> Comp.msub -> Comp.msub

