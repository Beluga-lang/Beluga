(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Support
open Beluga_syntax.Common
open Syntax.Int

type kind =
  | MMV of (Name.t * LF.iterm option ref)
  | FV of Name.t

type error =
  | LeftoverVars
  | LeftoverConstraints
  | CyclicDependency of kind
  | UnknownIdentifier
  | UnknownMTyp of Name.t

type sort =
  | LFTyp of LF.typ
  | MetaTyp of LF.ctyp * Plicity.t * Inductivity.t

type marker =
  | Pure of sort
  | Impure

type free_var =
  | FDecl of kind * marker
  | CtxV of (Name.t * Id.cid_schema * Plicity.t * Inductivity.t)

type fctx = free_var LF.ctx

exception Error of Location.t * error

val kind :
     LF.kind
  -> LF.kind
     * Id.offset (* where the offset indicates the #implicit arguments *)

val typ :
     LF.typ
  -> LF.typ
     * Id.offset (* where the offset indicates the #implicit arguments *)

val covgoal :
     LF.dctx
  -> LF.normal
  -> LF.typ
  -> LF.msub
  -> LF.mctx * LF.dctx * LF.normal * LF.typ * LF.msub

val covpatt :
     Comp.gctx
  -> Comp.pattern
  -> Comp.typ
  -> LF.msub
  -> LF.mctx * Comp.gctx * Comp.pattern * Comp.typ * LF.msub

val schema : LF.schema -> LF.schema

val msub : LF.msub -> LF.msub * LF.mctx

val compkind :
     Comp.kind
  -> Comp.kind
     * Id.offset (* where the offset indicates the #implicit arguments *)

val comptyp :
     Comp.typ
  -> Comp.typ
     * Id.offset (* where the offset indicates the #implicit arguments *)

val comptyp_cD : LF.mctx -> Comp.typ -> Comp.typ * Id.offset

val codatatyp :
     LF.mctx
  -> Comp.typ
  -> Comp.typ
  -> LF.mctx * Comp.typ * Comp.typ * Id.offset

val exp : Comp.exp -> fctx * Comp.exp

val thm : Comp.thm -> fctx * Comp.thm

val patobj :
     Location.t
  -> LF.mctx
  -> Comp.gctx
  -> Comp.pattern
  -> Name.t list
  -> Comp.typ
  -> LF.mctx * Comp.gctx * Comp.pattern * Comp.typ

val pattern_spine :
     Location.t
  -> LF.mctx
  -> Comp.gctx
  -> Comp.pattern_spine
  -> Name.t list
  -> Comp.typ
  -> LF.mctx * Comp.gctx * Comp.pattern_spine * Comp.typ

val closedTyp : LF.dctx * LF.typ -> bool

val printFreeMVars : LF.dctx_hat -> LF.normal -> unit

val fmt_ppr_collection : Format.formatter -> fctx -> unit
