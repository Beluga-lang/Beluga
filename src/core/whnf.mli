(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   @author Darin Morrison
*)

open Syntax.Int

val whnf     : nclo -> nclo
val whnfTyp  : tclo -> tclo
val norm     : nclo -> normal

val conv       : nclo -> nclo -> bool
val convTyp    : tclo -> tclo -> bool
val convTypRec : trec_clo -> trec_clo -> bool
val convSub    : sub -> sub -> bool
