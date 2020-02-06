module Comp = Syntax.Int.Comp
module LF = Syntax.Int.LF

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

(** genPVarGoal sch_elem cD cPsi psi = (cD', cPsi', h, tA', t)
    calculates a preliminary branch context for a parameter variable
    referring to the given schema element, without taking projection
    into account.

    cD |- cPsi ctx
    cD |- psi ctxvar
    cD' |- t : cD
    cD' |- cPsi' ctx
    cD'; cPsi' |- h <= tA'
    and h is an LF head, namely the PVar for this case.

    The resulting meta-context cD' will contain an entry for the PVar
    itself as well as for any existential variables bound by the
    schema element. The returned substitution t is an appropriate
    weakening.
 *)
val genPVarGoal : LF.sch_elem -> LF.mctx -> LF.dctx -> LF.ctx_var ->
                  LF.mctx * LF.dctx * LF.head * LF.typ * LF.msub

(** genObj (cD, cPsi, tP) (tH, tA) = (cD', CovGoal (cPsi', tR, tP'), ms)

    if cD; cPsi |- tH => tA
    and there exists a spine tS s.t.  cD; cPsi |- tS : tA > tP
    then
    tR = Root (tH, tS)
    and cD'; [t]cPsi |- tR <= [t]tP
    and cD' |- t : cD

    Concretely, this function is used to generate a pattern for a
    meta-object in splitting.
    tP is the type of the scrutinee, which is unified against the
    conclusion type of tA.
    tA, being the type of the head tH, is typically a pi-type, so we
    walk it to construct a spine by calling genSpine.
    Together with the given head, this generated spine is used to form
    the normal tR that is returned.
    Since this unification can eliminate variables, the resulting
    normal makes sense inside the "branch context" cD', so the msub t
    together with its target context cD' are also returned.
 *)
val genObj : LF.mctx * LF.dctx * LF.typ -> LF.head * LF.typ ->
             (LF.mctx * (LF.dctx * LF.normal * LF.tclo) * LF.msub) option

(** genPatt (cD, tau_i) (c, tau_c)
    = None | Some (cD', (cG, pat, ttau_p), t)
    generates a pattern with the given constructor c that matches the type tau_i.

    If cD |- tau_i <= type
       .; . |- c <= tau_c

    then genPatt tries to generate a spine S such that
    pat = c S

    cD'; cG |- pat <= ttau_p
    cD' |- t : cD
    (cD' |- ttau_p <= type)
    (cD' |- cG <= gctx)

    This process can fail, if ttau_p is not unifiable with the
    conclusion type of tau_c, in which case the constructor `c` is
    impossible for the scrutinee type `tau_i`.
 *)
val genPatt : LF.mctx * Comp.typ ->
              Id.cid_comp_typ * Comp.typ ->
              (LF.mctx * (gctx * Comp.pattern * Comp.tclo) * LF.msub) option

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
