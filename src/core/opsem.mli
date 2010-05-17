open Syntax.Int
open Id
open Error

exception Error of Syntax.Loc.t option * error

val eval : Comp.exp_chk -> Comp.exp_chk


val cctxToCSub : LF.mctx -> LF.mctx -> LF.dctx -> LF.csub
