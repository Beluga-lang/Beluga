(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

open Syntax.Int

val enableCoverage : bool ref
val warningOnly : bool ref
val no_covers : int ref

type problem

val make : Parser.Grammar.Loc.t option
        -> Pragma.case_pragma
        -> LF.mctx            (* cO *)
        -> LF.mctx            (* cD *)
        -> Comp.branch list   (* branches *)
        -> (LF.typ * LF.dctx) (* type of object being case-analyzed *)
        -> problem

type coverage_result =
  | Success
  | Failure of (unit -> string)

exception NoCover of (unit -> string)


val clear  : unit -> unit
val stage  : problem -> unit
val force  : (coverage_result -> 'a) -> 'a list


(* val covers : problem -> coverage_result *)
val process : problem -> unit   (* check coverage immediately *)
