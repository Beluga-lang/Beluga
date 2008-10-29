(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Joshua Dunfield
   @author Darin Morrison
   @author Brigitte Pientka
*)

open Syntax.Int



type error =
  | TypingAmbiguous
  | NotPatSub

exception Error of error

val whnf     : nclo -> nclo
val whnfTyp  : tclo -> tclo
val norm     : nclo -> normal

val conv       : nclo -> nclo -> bool
val convTyp    : tclo -> tclo -> bool
val convTypRec : trec_clo -> trec_clo -> bool
val convSub    : sub -> sub -> bool
