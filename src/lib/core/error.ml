(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int

type typeVariant = Cross | Arrow | CtxPi | PiBox | Box

type error =
  | UnboundName      of Id.name
  | UnknownCidTyp    of Id.cid_typ

  | CtxVarMismatch   of LF.mctx * LF.ctx_var * LF.schema
  | SigmaIllTyped    of LF.mctx * LF.mctx * LF.dctx * LF.trec_clo * LF.trec_clo
  | KindMismatch     of LF.mctx * LF.dctx * LF.sclo * (LF.kind * LF.sub)
  | TypMismatch      of LF.mctx * LF.mctx * LF.dctx * LF.nclo * LF.tclo * LF.tclo
  | IllTyped         of LF.mctx * LF.mctx * LF.dctx * LF.nclo * LF.tclo
  | IllTypedElab     of LF.mctx * LF.mctx * LF.dctx * LF.tclo

  | SpineIllTyped    
  | EtaExpandBV      of Id.offset * LF.mctx * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFMV     of Id.name * LF.mctx * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFV      of Id.name * LF.mctx * LF.mctx * LF.dctx * LF.tclo

  | LeftoverConstraints of Id.name
  | IllTypedIdSub

  | ValueRestriction of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * Comp.tclo
  | CompIllTyped     of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_chk * Comp.tclo * Comp.tclo
  | CompMismatch     of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * typeVariant * Comp.tclo
  | CompPattMismatch of (LF.mctx * LF.mctx * LF.dctx * LF.normal * LF.tclo) * 
                        (LF.mctx * LF.mctx * LF.dctx * LF.tclo)  

  | CompFreeMVar     of  Id.name
  | CompScrutineeTyp of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * LF.tclo * LF.dctx 

  | CompTypAnn       

  | UnboundIdSub

  | ConstraintsLeft
  | NotPatSub

  | LeftoverUndef
  | SubIllTyped
  | LeftoverFVar
