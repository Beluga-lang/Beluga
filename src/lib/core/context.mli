(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF
open Error

exception Error of error


val dctxToHat   : dctx -> psi_hat



(************************)
(* Declaration Contexts *)
(************************)

val ctxDec      : dctx -> int -> typ_decl
val ctxSigmaDec : dctx -> int -> sigma_decl
val ctxVar      : dctx -> ctx_var option

val append      : 'a ctx -> 'a ctx -> 'a ctx

val length      : 'a ctx -> int
