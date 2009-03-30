(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)
 
(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF
open Syntax.Int
open Error

exception Error of error

val dctxToHat   : dctx -> psi_hat
val addToHat   : psi_hat -> psi_hat   (* Lengthen by one declaration *)
val hatToDCtx   : psi_hat -> dctx
(* Declaration Contexts *)
val ctxDec      : dctx -> int -> typ_decl
val ctxSigmaDec : dctx -> int -> typ_decl
val ctxVar      : dctx -> ctx_var option

val append      : 'a ctx -> 'a ctx -> 'a ctx
val length      : 'a ctx -> int

val getNameDCtx : dctx -> int -> Id.name
val getNameMCtx : mctx -> int -> Id.name
val getNameCtx  : Comp.gctx -> int -> Id.name
