(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int.LF
open Error

exception Error of error

val whnf       : nclo -> nclo
val whnfTyp    : tclo -> tclo
val norm       : nclo -> normal
val normKind   : kind -> kind
val normTyp    : tclo -> typ
val normSub    : sub  -> sub
val normSpine  : sclo -> spine
val normDCtx   : dctx -> dctx
val reduce     : nclo -> spine -> normal
val whnfRedex  : nclo *  sclo  -> nclo

(* conv* : true iff arguments are alpha-convertible *)
val conv       : nclo -> nclo -> bool
val convTyp    : tclo -> tclo -> bool
val convTypRec : trec_clo -> trec_clo -> bool
val convSchElem : sch_elem -> sch_elem -> bool
val convSub    : sub -> sub -> bool
val convDCtx   : dctx -> dctx -> bool
val convCtx    : typ_decl ctx -> typ_decl ctx -> bool

(*************************************)
(* Creating new contextual variables *)
(*************************************)

val newMVar     : dctx * typ -> cvar
val newPVar     : dctx * typ -> cvar

val raiseType   : dctx -> typ -> typ 


(*************************************)
(* Other operations *)
(*************************************)

val etaExpandMV : dctx -> tclo -> sub -> normal
