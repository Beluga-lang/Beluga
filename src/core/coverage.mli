open Syntax.Int

type error =
    NoCover of string
  | MatchError of string
  | NothingToRefine
  | NoCoverageGoalsGenerated

type gctx = (Id.name * Comp.typ) list

type cov_goal =  CovGoal of LF.dctx * LF.normal * LF.tclo
                            (*  cPsi |- tR <= sP *)
		 | CovCtx of LF.dctx
		 | CovPatt of gctx * Comp.pattern * Comp.tclo


exception Error of Syntax.Loc.t * error

val enableCoverage : bool ref
val warningOnly : bool ref
val no_covers : int ref

type problem

val make : Syntax.Loc.t
        -> Pragma.case_pragma
        -> LF.mctx            (* cD *)
        -> Comp.branch list   (* branches *)
        -> Comp.typ (* type of object being case-analyzed *)
        -> problem

type coverage_result =
  | Success
  | Failure of string

(* val clear  : unit -> unit
val stage  : problem -> unit *)
val force  : (coverage_result -> 'a) -> 'a list

(* val covers : problem -> coverage_result *)
val process : problem -> int option -> unit   (* check coverage immediately *)
(* val etaExpandMVstr     : sub -> dctx -> tclo -> normal *)
val genPatCGoals : LF.mctx -> gctx -> Comp.typ -> gctx -> (LF.mctx * cov_goal * LF.msub) list
val genCtxGoals : LF.mctx -> LF.ctyp_decl -> (LF.mctx * LF.dctx * LF.msub) list
val genCovGoals : (LF.mctx * LF.dctx * LF.typ) -> (LF.mctx * cov_goal * LF.msub) list
