(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int

type kind =
  | MMV of (Id.name * LF.iterm option ref)
  | FV of Id.name

type error =
  | LeftoverVars
  | LeftoverConstraints
  | CyclicDependency of kind
  | UnknownIdentifier
  | UnknownMTyp of Id.name

type sort =
  | LFTyp of LF.typ
  | MetaTyp of LF.ctyp * LF.depend
type marker =
  | Pure of sort
  | Impure

type free_var =
  | FDecl of kind * marker
  | CtxV of (Id.name * Id.cid_schema * LF.depend)

type fctx = free_var LF.ctx


exception Error of Syntax.Loc.t * error

val kind : LF.kind -> LF.kind * Id.offset
val typ : LF.typ -> LF.typ * Id.offset

val covgoal : LF.dctx -> LF.normal -> LF.typ -> LF.msub
              -> LF.mctx * LF.dctx * LF.normal * LF.typ * LF.msub
val covpatt : Comp.gctx -> Comp.pattern -> Comp.typ -> LF.msub
              -> LF.mctx * Comp.gctx * Comp.pattern * Comp.typ * LF.msub

val schema : LF.schema -> LF.schema
val msub : LF.msub -> LF.msub * LF.mctx

val compkind : Comp.kind -> Comp.kind * Id.offset
val comptyp : Comp.typ -> Comp.typ * Id.offset
val codatatyp : LF.mctx -> Comp.typ -> Comp.typ -> LF.mctx * Comp.typ * Comp.typ * Id.offset
val exp : Comp.exp_chk -> fctx * Comp.exp_chk
val thm : Comp.thm -> fctx * Comp.thm

val patobj : Syntax.Loc.t -> LF.mctx -> Comp.gctx -> Comp.pattern
             -> Id.name list -> Comp.typ
             -> LF.mctx * Comp.gctx * Comp.pattern * Comp.typ
val pattern_spine: Syntax.Loc.t -> LF.mctx -> Comp.gctx -> Comp.pattern_spine
                   -> Id.name list -> Comp.typ
                   -> LF.mctx * Comp.gctx * Comp.pattern_spine * Comp.typ

val closedTyp : (LF.dctx * LF.typ) -> bool

val printFreeMVars : LF.dctx_hat -> LF.normal -> unit

val fmt_ppr_collection : Format.formatter -> fctx -> unit
