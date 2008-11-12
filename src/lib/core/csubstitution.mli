(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Substitutions

    @author Brigitte Pientka
*)

open Syntax.Int.LF



(*********************************)
(* Explicit Modual Substitutions *)
(*********************************)

val m_id      : msub
val m_shift    : msub


val mvarMSub   : int       -> msub -> mfront
val mfrontMSub : mfront    -> msub -> mfront
val mdecMSub   : ctyp_decl -> msub -> ctyp_decl
val m_comp     : msub -> msub -> msub
val m_dot1     : msub -> msub

 
