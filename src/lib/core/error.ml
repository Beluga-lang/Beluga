(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int
open Id

type error =
  | UnboundName         of name

  | CtxVarMismatch      of LF.ctx_var * LF.schema
  | SigmaIllTyped       of LF.mctx * LF.dctx * LF.trec_clo * LF.trec_clo
  | KindMismatch        of LF.dctx * LF.tclo
  | TypMismatch         of LF.dctx * LF.nclo * LF.tclo * LF.tclo
  | IllTyped            of LF.dctx * LF.nclo * LF.tclo

  | LeftoverConstraints of name
  | IllTypedIdSub
  | ValueRestriction
  | CompIllTyped        of Comp.exp_chk * Comp.typ

  | ConstraintsLeft
  | NotPatSub

  | LeftoverUndef
  | SubIllTyped
  | IndexError          of int * LF.dctx
