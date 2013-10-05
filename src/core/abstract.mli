(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int

type varvariant =
    VariantFV | VariantFCV | VariantMMV | VariantMPV
  | VariantMV | VariantFMV | VariantPV | VariantFPV | VariantSV
  | VariantFSV

type error =
  | LeftoverVars of varvariant
  | LeftoverConstraints
  | CyclicDependency of varvariant
  | UnknownIdentifier
  | UnknownSchemaCtx of Id.name


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
val exp      : Comp.exp_chk -> Comp.exp_chk

val pattern    : LF.mctx -> LF.dctx -> (LF.psi_hat * LF.normal) -> LF.typ ->
                 LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) * LF.typ
val patobj     : Syntax.Loc.t -> LF.mctx -> Comp.gctx -> Comp.pattern -> Comp.typ ->
                 LF.mctx * Comp.gctx * Comp.pattern * Comp.typ
val subpattern : LF.mctx -> LF.dctx -> LF.sub -> LF.dctx ->
                 LF.mctx * LF.dctx * LF.sub * LF.dctx

val closedTyp : (LF.dctx * LF.typ) -> bool

val printFreeMVars : LF.psi_hat -> LF.normal -> unit
