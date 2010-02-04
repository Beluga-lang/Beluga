(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int

type typeVariant = Cross | Arrow | CtxPi | PiBox | Box

type error =
  | UnboundName      of Id.name
  | UnboundCoName    of Id.name
  | UnboundCtxName   of Id.name
  | UnboundCtxSchemaName   of Id.name
  | UnboundCompName  of Id.name
  | UnknownCidTyp    of Id.cid_typ
  | CoercionMismatch of Id.cid_coercion * Id.cid_coercion

  | CtxVarMismatch   of LF.mctx * LF.ctx_var * LF.schema
  | SigmaIllTyped    of LF.mctx * LF.mctx * LF.dctx * LF.trec_clo * LF.trec_clo
  | KindMismatch     of LF.mctx * LF.dctx * LF.sclo * (LF.kind * LF.sub)
  | TypMismatch      of LF.mctx * LF.mctx * LF.dctx * LF.nclo * LF.tclo * LF.tclo
  | TypMismatchElab  of LF.mctx * LF.mctx * LF.dctx * LF.tclo * LF.tclo
  | IllTyped         of LF.mctx * LF.mctx * LF.dctx * LF.nclo * LF.tclo
  | IllTypedElab     of LF.mctx * LF.mctx * LF.dctx * LF.tclo

  | SpineIllTyped    
  | EtaExpandBV      of Id.offset * LF.mctx * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFMV     of Id.name * LF.mctx * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFV      of Id.name * LF.mctx * LF.mctx * LF.dctx * LF.tclo

  | LeftoverConstraints of Id.name
  | IllTypedIdSub
  | IllTypedCoIdSub                   

  | ValueRestriction of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * Comp.tclo
  | CompIllTyped     of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_chk * Comp.tclo * Comp.tclo
  | CompMismatch     of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * typeVariant * Comp.tclo
  | CompPattMismatch of (LF.mctx * LF.mctx * LF.dctx * LF.normal * LF.tclo) * 
                        (LF.mctx * LF.mctx * LF.dctx * LF.tclo)  

  | CompBoxCtxMismatch  of LF.mctx * LF.mctx * LF.dctx * (LF.psi_hat * LF.normal)

  | CompFreeMVar     of  Id.name
  | CompScrutineeTyp of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * LF.tclo * LF.dctx 


  | CompCtxFunMismatch of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompFunMismatch    of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompMLamMismatch   of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompPairMismatch   of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompBoxMismatch    of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompIfMismatch     of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompSynMismatch    of  LF.mctx * LF.mctx * Comp.tclo (* expected *) * Comp.tclo (* inferred *)
  | CompEqMismatch     of  LF.mctx * LF.mctx * Comp.tclo (* arg1 *) * Comp.tclo (* arg2 *)
  | CompEqTyp          of  LF.mctx * LF.mctx * Comp.tclo 

  | CompTypAnn       

  | UnboundIdSub

  | ConstraintsLeft
  | NotPatSub
  | NotPatternSpine

  | LeftoverUndef
  | SubIllTyped
  | LeftoverFVar
