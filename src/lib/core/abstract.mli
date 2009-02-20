(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int 

exception Error of string

type free_var =
  (* Free variables (references): unnamed *)
  | MV of LF.head       
  | PV of LF.head       

  (* Free named variables *)
  | FV of Id.name * LF.typ option 
  | FMV of Id.name * (LF.typ * LF.dctx) option 
  | FPV of Id.name * (LF.typ * LF.dctx) option 


val abstrKind     : LF.kind -> LF.kind * Id.offset

val abstrTyp      : LF.typ  -> LF.typ  * Id.offset

val abstractMSub  : Comp.msub -> Comp.msub * LF.mctx

val abstrCompTyp  : Comp.typ  -> Comp.typ * Id.offset

val abstrExp      : Comp.exp_chk  -> Comp.exp_chk

val abstrPattern  : LF.mctx -> LF.dctx -> (LF.psi_hat * LF.normal) -> LF.typ -> 
                    LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) * LF.typ

val collectTerm'   : (LF.psi_hat * LF.normal) -> free_var LF.ctx
val printCollection : free_var LF.ctx -> unit

val printFreeMVars : LF.psi_hat -> LF.normal -> unit   
