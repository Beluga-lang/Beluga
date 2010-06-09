(**
   @author Brigitte Pientka
*)

open Context
open Syntax.Int

exception Fmvar_not_found
exception FreeMVar of LF.head
exception NonInvertible 


val m_id   : LF.msub
val mshift: LF.msub -> int -> LF.msub
val mshiftTerm: LF.normal -> int -> LF.normal
val mshiftTyp : LF.typ  -> int -> LF.typ

val mvar_dot1  : LF.msub -> LF.msub
val pvar_dot1  : LF.msub -> LF.msub

val mcomp      : LF.msub -> LF.msub -> LF.msub

val invert     : LF.msub -> LF.msub

val invExp     : Comp.exp_chk * LF.msub -> int -> Comp.exp_chk 
val invTerm    : LF.normal    * LF.msub -> int -> LF.normal

val mctxMDec   : LF.mctx -> int -> LF.typ * LF.dctx
val mctxPDec   : LF.mctx -> int -> LF.typ * LF.dctx


val mctxMVarPos : LF.mctx -> Id.name -> (Id.offset * (LF.typ * LF.dctx))
val mctxPVarPos : LF.mctx -> Id.name -> (Id.offset * (LF.typ * LF.dctx))

val applyMSub   : Id.offset -> LF.msub -> LF.mfront


val cnorm      : LF.normal * LF.msub -> LF.normal
val cnormTyp   : LF.typ  * LF.msub -> LF.typ
val cnormTypRec: LF.typ_rec * LF.msub -> LF.typ_rec
val cnormDCtx  : LF.dctx * LF.msub -> LF.dctx

val cnormMSub  : LF.msub -> LF.msub

val cnormCTyp  : Comp.typ * LF.msub -> Comp.typ
val cwhnfCTyp  : Comp.typ * LF.msub -> Comp.typ * LF.msub
val cwhnfCtx   : Comp.gctx * LF.msub -> Comp.gctx

val cnormExp   : Comp.exp_chk * LF.msub -> Comp.exp_chk
val cnormExp'  : Comp.exp_syn * LF.msub -> Comp.exp_syn

val normCtx    : Comp.gctx -> Comp.gctx
val normCTyp   : Comp.typ  -> Comp.typ


val convCTyp   : (Comp.typ * LF.msub) -> (Comp.typ * LF.msub) -> bool

val csub_ctyp  : LF.dctx -> int -> Comp.typ -> Comp.typ
val csub_msub  : LF.dctx -> int -> LF.msub -> LF.msub

