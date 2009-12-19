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


val applyCtxCoe    : Id.cid_coercion -> mctx -> dctx -> dctx
val applyInvCtxCoe : Id.cid_coercion -> mctx -> dctx -> dctx

val coerceTyp   : id_coercion -> tclo -> typ
val coerceTypRec: id_coercion -> trec_clo -> typ_rec
val coerceSub   : id_coercion -> sub -> sub

val coeTypRec    : coercion -> mctx -> (dctx * trec_clo) -> trec_clo
val invcoeTypRec : coercion -> mctx -> (dctx * trec_clo) -> trec_clo
