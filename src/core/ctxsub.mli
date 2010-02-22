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

val csub_ctyp  : mctx -> dctx -> int -> Comp.typ -> Comp.typ
val csub_msub  : dctx -> int -> msub -> msub
val csub_exp_chk : dctx -> int -> Comp.exp_chk -> Comp.exp_chk
val csub_exp_syn : dctx -> int -> Comp.exp_syn -> Comp.exp_syn


val ctxnorm_typ : typ  * csub -> typ
val ctxnorm     : normal * csub -> normal
val ctxnorm_psihat: psi_hat * csub -> psi_hat
val ctxnorm_dctx: dctx * csub -> dctx
val ctxnorm_mctx: mctx * csub -> mctx
val ctxnorm_gctx: Comp.gctx * csub -> Comp.gctx

val ctxnorm_msub: msub * csub -> msub

val cdot1       : csub -> csub
val id_csub     : mctx -> csub
val apply_csub  : ctx_var -> csub -> dctx

val inst_csub   : dctx -> Id.offset -> csub -> mctx (* cO *) -> (mctx * csub)
val ccomp       : csub -> csub -> csub
