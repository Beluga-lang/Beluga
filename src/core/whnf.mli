(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int.LF
open Syntax.Int
open Context 

open Error

exception Error of Syntax.Loc.t option * error
exception Violation of string


val whnf       : nclo -> nclo
val whnfTyp    : tclo -> tclo
val norm       : nclo -> normal
val normKind   : (kind * sub) -> kind
val normTyp    : tclo -> typ
val normTypRec : trec_clo -> typ_rec
val normSub    : sub  -> sub
val normSpine  : sclo -> spine
val normDCtx   : dctx -> dctx
val normMCtx   : mctx -> mctx
val reduce     : nclo -> spine -> normal
val whnfRedex  : nclo *  sclo  -> nclo

(* conv* : true iff arguments are alpha-convertible *)
val conv        : nclo         -> nclo         -> bool
val convHead    : (head * sub) -> (head * sub) -> bool
val convTyp     : tclo         -> tclo         -> bool
val convTypRec  : trec_clo     -> trec_clo     -> bool
val convSchElem : sch_elem     -> sch_elem     -> bool
val prefixSchElem : sch_elem     -> sch_elem     -> bool
val convSub     : sub          -> sub          -> bool
val convMSub    : msub         -> msub         -> bool
val convDCtx    : dctx         -> dctx         -> bool
val convCtx     : typ_decl ctx -> typ_decl ctx -> bool

(*************************************)
(* Creating new contextual variables *)
(*************************************)

val newMMVar    : mctx * dctx * typ -> mm_var
val newMVar     : dctx * typ -> cvar
val newPVar     : dctx * typ -> cvar

val raiseType   : dctx -> typ -> typ 


(*************************************)
(* Other operations *)
(*************************************)

val etaExpandMV  : dctx -> tclo -> sub -> normal
val etaExpandMMV : Syntax.Loc.t option -> mctx -> dctx -> tclo -> sub -> normal

exception Fmvar_not_found
exception FreeMVar of head
exception NonInvertible 


val m_id   : msub
val mshift: msub -> int -> msub
val mshiftTerm: normal -> int -> normal
val mshiftTyp : typ  -> int -> typ

val mvar_dot1  : msub -> msub
val pvar_dot1  : msub -> msub
val mvar_dot   : msub -> mctx -> msub

val mcomp      : msub -> msub -> msub

val m_invert     : msub -> msub

(* val invExp     : Comp.exp_chk * msub -> int -> Comp.exp_chk 
val invTerm    : normal    * msub -> int -> normal
*)
val mctxMDec   : mctx -> int -> Id.name * typ * dctx
val mctxPDec   : mctx -> int -> Id.name * typ * dctx


val mctxMVarPos : mctx -> Id.name -> (Id.offset * (typ * dctx))
val mctxPVarPos : mctx -> Id.name -> (Id.offset * (typ * dctx))


val cnorm      : normal * msub -> normal
val cnormSub   : sub * msub -> sub
val cnormTyp   : typ  * msub -> typ
val cnormTypRec: typ_rec * msub -> typ_rec
val cnormDCtx  : dctx * msub -> dctx

val cnormCtx  :  Comp.gctx * msub -> Comp.gctx

val cnormMSub  : msub -> msub

val cnormCTyp  : Comp.typ * msub -> Comp.typ
val cwhnfCTyp  : Comp.typ * msub -> Comp.typ * msub
val cwhnfCtx   : Comp.gctx * msub -> Comp.gctx

val cnormExp   : Comp.exp_chk * msub -> Comp.exp_chk
val cnormExp'  : Comp.exp_syn * msub -> Comp.exp_syn

val normCtx    : Comp.gctx -> Comp.gctx
val normCTyp   : Comp.typ  -> Comp.typ


val convCTyp   : (Comp.typ * msub) -> (Comp.typ * msub) -> bool

val closed     : nclo -> bool
val closedTyp  : tclo -> bool
val closedDCtx : dctx -> bool

val constraints_solved : cnstr list -> bool
