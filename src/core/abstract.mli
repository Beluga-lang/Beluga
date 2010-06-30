(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int 

exception Error of string

type marker = Pure | Impure 

type free_var =
  (* Free variables (references): unnamed *)
  | MMV of marker * LF.head       
  | MV  of marker * LF.head       
  | PV  of marker * LF.head       

  (* Free named variables *)
  | FV  of marker * Id.name * LF.typ option 
  | FMV of marker * Id.name * (LF.typ * LF.dctx) option 
  | FPV of marker * Id.name * (LF.typ * LF.dctx) option 



val cnstr_ctyp : Comp.typ  -> bool

val abstrKind     : LF.kind -> LF.kind * Id.offset

val abstrTyp      : LF.typ  -> LF.typ  * Id.offset

val abstrSchema   : LF.schema  -> LF.schema

val abstractMSub  : LF.msub -> LF.msub * LF.mctx

val abstrCompTyp  : Comp.typ  -> Comp.typ * Id.offset

val abstrExp      : Comp.exp_chk  -> Comp.exp_chk
(* val abstrBranch   : (LF.dctx * (LF.psi_hat * LF.normal) * LF.typ) -> Comp.exp_chk  -> LF.msub 
                  -> LF.mctx * (LF.dctx * (LF.psi_hat * LF.normal) * LF.typ) * Comp.exp_chk * LF.msub

val abstrExpMSub  : Comp.exp_chk  -> LF.msub -> LF.mctx * LF.msub * Comp.exp_chk
*)
val abstrPattern  : LF.mctx -> LF.dctx -> (LF.psi_hat * LF.normal) -> LF.typ -> (LF.csub * LF.csub) -> 
                    LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) * LF.typ * LF.csub * LF.csub


val abstrSubPattern  : LF.mctx -> LF.dctx -> LF.sub -> LF.dctx -> 
                    LF.mctx * LF.dctx * LF.sub * LF.dctx

val collectTerm'   : (LF.psi_hat * LF.normal) -> (free_var LF.ctx * LF.normal)
val closedTyp      : (LF.dctx * LF.typ) -> bool
val printCollection : free_var LF.ctx -> unit

val printFreeMVars : LF.psi_hat -> LF.normal -> unit   
