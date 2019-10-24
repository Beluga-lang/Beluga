open Syntax.Int

type error =
    NoCover of string
  | MatchError of string
  | NothingToRefine
  | NoCoverageGoalsGenerated

type gctx = (Id.name * Comp.typ * Comp.wf_tag) list

type cov_goal =
  | CovGoal of LF.dctx * LF.normal * LF.tclo (*  cPsi |- tR <= sP *)
	| CovCtx of LF.dctx
	| CovSub of LF.dctx * LF.sub * LF.cltyp
	| CovPatt of gctx * Comp.pattern * Comp.tclo


exception Error of Syntax.Loc.t * error

val enableCoverage : bool ref
val warningOnly : bool ref
val no_covers : int ref

type problem

val make : Syntax.Loc.t
        -> Comp.case_pragma
        -> LF.mctx              (* cD *)
        -> Comp.branch list     (* branches *)
        -> Comp.typ             (* type of object being case-analyzed *)
        -> Comp.meta_obj option
        (* ^ scrutinee of the case. Provided only if it as a normal LF
         * object, as this will eliminate certain cases from the
         * generated splits. *)
        -> problem

type coverage_result =
  | Success
  | Failure of string

type depend   = Atomic | Dependent



(* val clear  : unit -> unit
val stage  : problem -> unit *)
val map  : (coverage_result -> 'a) -> 'a list
val iter : (coverage_result -> unit) -> unit

(* val covers : problem -> coverage_result *)
val process : problem -> int option -> unit   (* check coverage immediately *)

val genPatCGoals    : LF.mctx -> gctx -> Comp.typ -> gctx -> (LF.mctx * cov_goal * LF.msub) list
(* val genCtxGoals     : LF.mctx -> LF.ctyp_decl -> (LF.mctx * LF.dctx * LF.msub) list *)
val genContextGoals : LF.mctx -> LF.ctyp_decl -> (LF.mctx * cov_goal * LF.msub) list
val genCGoals       : LF.mctx -> LF.ctyp -> (LF.mctx * cov_goal * LF.msub) list * depend
val genCovGoals     : (LF.mctx * LF.dctx * LF.typ) -> (LF.mctx * cov_goal * LF.msub)  list
val genBCovGoals    : (LF.mctx * LF.dctx * LF.typ) -> (LF.mctx * cov_goal * LF.msub) list

val addToMCtx : LF.mctx -> (LF.ctyp_decl list * LF.msub) -> LF.mctx * LF.msub

val compgctx_of_gctx : gctx -> Comp.gctx
val gctx_of_compgctx : Comp.gctx -> gctx

(** Decide whether a given computational type is impossible. *)
val is_impossible : LF.mctx -> Comp.typ -> bool
