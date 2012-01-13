(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

open Syntax.Int


module type SIG = sig
  type error

  val error_location : error -> Syntax.Loc.t
  val report_error : Format.formatter -> error -> unit
end

type typeVariant = Cross | Arrow | CtxPi | PiBox | Box

type error =
  | CtxReconstruct
  | UnboundName      of Id.name
  | UnboundCtxName   of Id.name
  | UnboundCtxSchemaName of Id.name
  | UnboundCompName  of Id.name
  | UnknownCidTyp    of Id.cid_typ

  | PruningFailed

  | FrozenType of Id.cid_typ

  | CtxVarMismatch   of LF.mctx * LF.ctx_var * LF.schema
  | CtxVarDiffer     of LF.mctx * LF.ctx_var * LF.ctx_var

  | SigmaIllTyped    of LF.mctx * LF.dctx * LF.trec_clo * LF.trec_clo
  | KindMismatch     of LF.mctx * LF.dctx * LF.sclo * (LF.kind * LF.sub)
  | TypMismatch      of LF.mctx * LF.dctx * LF.nclo * LF.tclo * LF.tclo
  | TypMismatchElab  of LF.mctx * LF.dctx * LF.tclo * LF.tclo
  | IllTyped         of LF.mctx * LF.dctx * LF.nclo * LF.tclo
  | IllTypedElab     of LF.mctx * LF.dctx * LF.tclo

  | SpineIllTyped    
  | EtaExpandBV      of Id.offset * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFMV     of Id.name * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFV      of Id.name * LF.mctx * LF.dctx * LF.tclo

  | LeftoverConstraints of Id.name
  | IllTypedIdSub

  | PatIllTyped     of LF.mctx * Comp.gctx * Comp.pattern * Comp.tclo * Comp.tclo
  | ValueRestriction of LF.mctx * Comp.gctx * Comp.exp_syn * Comp.tclo
  | CompIllTyped     of LF.mctx * Comp.gctx * Comp.exp_chk * Comp.tclo * Comp.tclo
  | CompMismatch     of LF.mctx * Comp.gctx * Comp.exp_syn * typeVariant * Comp.tclo
  | CompPattMismatch of (LF.mctx * LF.dctx * LF.normal option * LF.tclo) * 
                        (LF.mctx * LF.dctx * LF.tclo)  

  | CompSubPattMismatch of (LF.mctx * LF.dctx * LF.sub * LF.dctx) * 
                        (LF.mctx * LF.dctx * LF.dctx)  

  | CompBoxCtxMismatch  of LF.mctx * LF.dctx * (LF.psi_hat * LF.normal)

  | CompFreeMVar     of  Id.name
  | CompScrutineeTyp    of LF.mctx * Comp.gctx * Comp.exp_syn * LF.tclo * LF.dctx 
  | CompScrutineeSubTyp of LF.mctx * Comp.gctx * Comp.exp_syn * LF.dctx * LF.dctx 


  | CompCtxFunMismatch of  LF.mctx * Comp.gctx  * Comp.tclo 
  | CompFunMismatch    of  LF.mctx * Comp.gctx  * Comp.tclo 
  | CompMLamMismatch   of  LF.mctx * Comp.gctx  * Comp.tclo 
  | CompPairMismatch   of  LF.mctx * Comp.gctx  * Comp.tclo 
  | CompBoxMismatch    of  LF.mctx * Comp.gctx  * Comp.tclo 
  | CompSBoxMismatch   of  LF.mctx * Comp.gctx  * LF.dctx  * LF.dctx
  | CompIfMismatch     of  LF.mctx * Comp.gctx  * Comp.tclo 
  | CompSynMismatch    of  LF.mctx * Comp.tclo (* expected *) * Comp.tclo (* inferred *)
  | CompEqMismatch     of  LF.mctx * Comp.tclo (* arg1 *) * Comp.tclo (* arg2 *)
  | CompEqTyp          of  LF.mctx * Comp.tclo 
  | CompMAppMismatch   of  LF.mctx * (Comp.meta_typ * LF.msub)
  | CompAppMismatch    of  LF.mctx * (Comp.meta_typ * LF.msub)

  | CompTypAnn       

  | PatVarNotUnique
  | PatCtxRequired
  | CompEmptyPattBranch

  | UnboundIdSub

  | ConstraintsLeft
  | NotPatSub
  | NotPatternSpine

  | NoCover of string

  | LeftoverCV
  | LeftoverMV
  | LeftoverMMV
  | LeftoverConstraintsAbstract
  | CyclicDependencyFV
  | CyclicDependencyFCV
  | CyclicDependencyMMV
  | CyclicDependencyMV
  | CyclicDependencyFMV
  | CyclicDependencyPV
  | CyclicDependencyFPV
  | UnknownIdentifier

  | LeftoverUndef
  | SubIllTyped
  | LeftoverFVar

exception Error of Syntax.Loc.t * error
exception Violation of string
exception NotImplemented

let information = ref []

let getInformation () =
  match List.rev !information with
    | [] -> ""
    | information ->
        (List.fold_left (fun acc s -> acc ^ "\n" ^ s) "" information) ^ "\n"

let addInformation message =
  information := message :: !information
