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

type sort = LFTyp of LF.typ | MetaTyp of LF.ctyp * LF.depend
type marker = Pure of sort | Impure

type free_var =
  | FDecl of kind * marker
  | CtxV of (Id.name * Id.cid_schema * LF.depend)


exception Error of Syntax.Loc.t * error

val cnstr_ctyp : Comp.typ -> bool

val kind    : LF.kind -> LF.kind * Id.offset
val typ     : LF.typ  -> LF.typ  * Id.offset

val covgoal : LF.dctx -> LF.normal -> LF.typ -> LF.msub ->
              LF.mctx * LF.dctx * LF.normal * LF.typ * LF.msub
val covpatt : Comp.gctx -> Comp.pattern -> Comp.typ -> LF.msub ->
              LF.mctx * Comp.gctx * Comp.pattern * Comp.typ * LF.msub

val schema : LF.schema -> LF.schema
val msub   : LF.msub -> LF.msub * LF.mctx

val compkind : Comp.kind -> Comp.kind * Id.offset
val comptyp  : Comp.typ -> Comp.typ * Id.offset
val exp      : Comp.exp_chk -> free_var LF.ctx * Comp.exp_chk

val pattern    : LF.mctx -> LF.dctx -> (LF.psi_hat * LF.normal) -> LF.typ ->
                 LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) * LF.typ
val mobj       : LF.mctx -> Comp.meta_obj -> Comp.meta_typ ->
                 LF.mctx * Comp.meta_obj * Comp.meta_typ
val patobj     : Syntax.Loc.t -> LF.mctx -> Comp.gctx -> Comp.pattern -> Comp.typ ->
                 LF.mctx * Comp.gctx * Comp.pattern * Comp.typ
val subpattern : LF.mctx -> LF.dctx -> LF.sub -> LF.dctx ->
                 LF.mctx * LF.dctx * LF.sub * LF.dctx

val copattern_spine: LF.mctx -> Comp.copattern_spine -> Comp.typ -> LF.msub -> 
                         LF.mctx * Comp.copattern_spine * Comp.typ * LF.msub

val closedTyp : (LF.dctx * LF.typ) -> bool

val printFreeMVars : LF.psi_hat -> LF.normal -> unit
