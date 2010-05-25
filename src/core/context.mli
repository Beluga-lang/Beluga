(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)
 
(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF
open Syntax.Int
open Error

exception Error of error
exception NoTypAvailable


val dctxToHat   : dctx -> psi_hat
val addToHat   : psi_hat -> psi_hat   (* Lengthen by one declaration *)
val hatToDCtx   : psi_hat -> dctx
(* Declaration Contexts *)
val ctxDec      : dctx -> int -> typ_decl
val ctxSigmaDec : dctx -> int -> typ_decl
val ctxVar      : dctx -> ctx_var option
val hasCtxVar   : dctx -> bool         (* true if ctxVar dctx = Some _ *)

val append      : 'a ctx -> 'a ctx -> 'a ctx
val length      : 'a ctx -> int


val getNameDCtx : dctx -> int -> Id.name
val getNameMCtx : mctx -> int -> Id.name
val getNameCtx  : Comp.gctx -> int -> Id.name

val projectCtxIntoDctx : typ_decl ctx -> dctx 

val lookup : Comp.gctx -> int -> Comp.typ option

val lookupSchema : mctx -> int -> Id.cid_schema
val lookupCtxVar : mctx -> ctx_var -> Id.name * Id.cid_schema
val lookupCtxVarSchema : mctx -> ctx_var -> Id.cid_schema
