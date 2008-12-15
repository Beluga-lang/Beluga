(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int.LF

type error =
  | ConstraintsLeft
  | NotPatSub

exception Error of error

val whnf       : nclo -> nclo
val whnfTyp    : tclo -> tclo
val norm       : nclo -> normal
val reduce     : nclo -> spine -> normal
val whnfRedex  : nclo *  sclo  -> nclo

val conv       : nclo -> nclo -> bool
val convTyp    : tclo -> tclo -> bool
val convTypRec : trec_clo -> trec_clo -> bool
val convSub    : sub -> sub -> bool
val convDCtx   : dctx -> dctx -> bool
val convCtx    : typ_decl ctx -> typ_decl ctx -> bool
