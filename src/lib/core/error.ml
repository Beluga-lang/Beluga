(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int

type typeVariant = Cross | Arrow | CtxPi | PiBox

type error =
  | UnboundName      of Id.name

  | CtxVarMismatch   of LF.mctx * LF.ctx_var * LF.schema
  | SigmaIllTyped    of LF.mctx * LF.mctx * LF.dctx * LF.trec_clo * LF.trec_clo
  | KindMismatch     of LF.mctx * LF.dctx * LF.tclo
  | TypMismatch      of LF.mctx * LF.mctx * LF.dctx * LF.nclo * LF.tclo * LF.tclo
  | IllTyped         of LF.mctx * LF.mctx * LF.dctx * LF.nclo * LF.tclo

  | LeftoverConstraints of Id.name
  | IllTypedIdSub

  | ValueRestriction of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * Comp.tclo
  | CompIllTyped     of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_chk * Comp.tclo
  | CompMismatch     of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * typeVariant * Comp.tclo
  | UnboundIdSub

  | ConstraintsLeft
  | NotPatSub

  | LeftoverUndef
  | SubIllTyped
  | LeftoverFVar
