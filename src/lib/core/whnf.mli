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

val whnf    : nclo -> nclo
val whnfTyp : tclo -> tclo
val norm    : nclo -> normal
val reduce  : nclo -> spine -> normal

val conv       : nclo -> nclo -> bool
val convTyp    : tclo -> tclo -> bool
val convTypRec : trec_clo -> trec_clo -> bool
val convSub    : sub -> sub -> bool
