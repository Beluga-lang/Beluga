(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF



val dctxToHat   : dctx -> psi_hat



(************************)
(* Declaration Contexts *)
(************************)

val ctxDec      : dctx -> int -> typ_decl
val ctxSigmaDec : dctx -> int -> sigma_decl
val ctxVar      : dctx -> cvar option

val mctxMDec    : mctx -> int -> typ * dctx
val mctxPDec    : mctx -> int -> typ * dctx



(*************************************)
(* Creating new contextual variables *)
(*************************************)

val newMVar     : dctx * typ -> cvar
val newPVar     : dctx * typ -> cvar
