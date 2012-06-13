open Syntax.Int

type error =
    NoCover of string
  | MatchError of string
  | NothingToRefine
  | NoCoverageGoalsGenerated

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

val clear  : unit -> unit
val stage  : problem -> unit
val force  : (coverage_result -> 'a) -> 'a list

(* val covers : problem -> coverage_result *)
val process : problem -> unit   (* check coverage immediately *)
