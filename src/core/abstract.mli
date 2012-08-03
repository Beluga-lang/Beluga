(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int

type error =
    LeftoverCV
  | LeftoverMV
  | LeftoverMMV
  | LeftoverMPV
  | LeftoverConstraints
  | CyclicDependencyFV
  | CyclicDependencyFCV
  | CyclicDependencyMMV
  | CyclicDependencyMPV
  | CyclicDependencyMV
  | CyclicDependencyFMV
  | CyclicDependencyPV
  | CyclicDependencyFPV
  | UnknownIdentifier

exception Error of Syntax.Loc.t * error

val cnstr_ctyp : Comp.typ  -> bool

val abstrKind     : LF.kind -> LF.kind * Id.offset

val abstrTyp      : LF.typ  -> LF.typ  * Id.offset

val abstrCovGoal  : LF.dctx -> LF.normal -> LF.typ -> LF.msub ->
                      LF.mctx * LF.dctx * LF.normal * LF.typ * LF.msub

val abstrCovPatt  : Comp.gctx -> Comp.pattern -> Comp.typ -> LF.msub -> 
                     LF.mctx * Comp.gctx * Comp.pattern * Comp.typ * LF.msub

val abstrSchema   : LF.schema  -> LF.schema

val abstractMSub  : LF.msub -> LF.msub * LF.mctx

val abstrCompKind  : Comp.kind  -> Comp.kind * Id.offset

val abstrCompTyp  : Comp.typ  -> Comp.typ * Id.offset

val abstrExp      : Comp.exp_chk  -> Comp.exp_chk
(* val abstrBranch   : (LF.dctx * (LF.psi_hat * LF.normal) * LF.typ) -> Comp.exp_chk  -> LF.msub
                  -> LF.mctx * (LF.dctx * (LF.psi_hat * LF.normal) * LF.typ) * Comp.exp_chk * LF.msub

val abstrExpMSub  : Comp.exp_chk  -> LF.msub -> LF.mctx * LF.msub * Comp.exp_chk
*)


val abstrPattern  : LF.mctx -> LF.dctx -> (LF.psi_hat * LF.normal) -> LF.typ ->
                    LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) * LF.typ

val abstrPatObj  : LF.mctx -> Comp.gctx -> Comp.pattern -> Comp.typ ->
                    LF.mctx * Comp.gctx * Comp.pattern * Comp.typ

val abstrSubPattern  : LF.mctx -> LF.dctx -> LF.sub -> LF.dctx ->
                    LF.mctx * LF.dctx * LF.sub * LF.dctx

val closedTyp      : (LF.dctx * LF.typ) -> bool


val printFreeMVars : LF.psi_hat -> LF.normal -> unit
