(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

open Syntax.Int

type typeVariant = Cross | Arrow | CtxPi | PiBox | Box

type error =
  (* indexing errors *)
  | UnboundName of Id.name
  | UnboundCtxName   of Id.name
  | UnboundCtxSchemaName   of Id.name
  | UnboundCompName  of Id.name
  | UnknownCidTyp  of Id.cid_typ

  (* LF typechecking errors *)
  | FrozenType of Id.cid_typ

  | CtxVarMismatch of LF.mctx          (* ???                                 *)
      * LF.ctx_var * LF.schema

  | CtxVarDiffer     of LF.mctx * LF.ctx_var * LF.ctx_var

  | SigmaIllTyped of                   (* ???                                 *)
      LF.mctx * LF.mctx  * LF.dctx
      * LF.trec_clo (* inferred *) 
      * LF.trec_clo (* expected *)

  | KindMismatch   of LF.mctx * LF.dctx * LF.sclo  * (LF.kind * LF.sub)


  | TypMismatch of LF.mctx             (* cO ; cD ; cPsi |- sR => sP          *)
      * LF.mctx *  LF.dctx * LF.nclo   (* but sP =/= sA                       *)
      * LF.tclo (* expected *) 
      * LF.tclo (* inferred *)

  | TypMismatchElab  of LF.mctx 
      * LF.mctx * LF.dctx * LF.tclo (* expected *) * LF.tclo (* inferred *)

  | IllTyped of                        (* cO ; cD ; cPsi |- sM <=/= sA        *)
      LF.mctx * LF.mctx * LF.dctx             
      * LF.nclo * LF.tclo

  | IllTypedElab     of LF.mctx * LF.mctx * LF.dctx * LF.tclo

  | SpineIllTyped

  | EtaExpandBV        of Id.offset * LF.mctx * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFMV       of Id.name * LF.mctx * LF.mctx * LF.dctx * LF.tclo
  | EtaExpandFV        of Id.name * LF.mctx * LF.mctx * LF.dctx * LF.tclo

  | LeftoverConstraints of Id.name     (* constraints left after 
                                          reconstruction of variable x        *)
  | IllTypedIdSub                      (* ???, not used yet                   *)



  (* Comp level typechecking errors *)
  | ValueRestriction of                (* pat. match. on a non-box expression *)
      LF.mctx * LF.mctx * Comp.gctx    (* cO ; cD ; cG |- i =/=> A[Psi]       *)
      * Comp.exp_syn * Comp.tclo

  | CompIllTyped of                    (* cO ; cD ; cG |- e <=/= tau_theta    *)
      LF.mctx * LF.mctx * Comp.gctx
      * Comp.exp_chk * Comp.tclo (* expected *) * Comp.tclo (*inferred *)

  | CompMismatch of                    (* cO ; cD ; cG |- i => tau_theta,     *)                             
      LF.mctx * LF.mctx * Comp.gctx    (* but tau_theta is of unexpected form *)
      * Comp.exp_syn
      * typeVariant (* expected *) 
      * Comp.tclo (* inferred*)

  | CompPattMismatch of 
      (* Pattern : inferred *)
      (LF.mctx * LF.mctx * LF.dctx * LF.normal * LF.tclo) * 
      (* Type of scrutinee : expected *)
        (LF.mctx * LF.mctx * LF.dctx * LF.tclo)  

  | CompSubPattMismatch of (LF.mctx * LF.mctx * LF.dctx * LF.sub * LF.dctx) * 
                        (LF.mctx * LF.mctx * LF.dctx * LF.dctx)  


  | CompBoxCtxMismatch  of LF.mctx * LF.mctx * LF.dctx * (LF.psi_hat * LF.normal) 

  | CompFreeMVar     of  Id.name

  | CompScrutineeTyp of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * LF.tclo * LF.dctx 
  | CompScrutineeSubTyp of LF.mctx * LF.mctx * Comp.gctx * Comp.exp_syn * LF.dctx * LF.dctx 

  | CompCtxFunMismatch of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompFunMismatch    of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompMLamMismatch   of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompPairMismatch   of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompBoxMismatch    of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompSBoxMismatch   of  LF.mctx * LF.mctx * Comp.gctx  * LF.dctx  * LF.dctx
  | CompIfMismatch    of  LF.mctx * LF.mctx * Comp.gctx  * Comp.tclo 
  | CompSynMismatch    of  LF.mctx * LF.mctx * Comp.tclo (* expected *) * Comp.tclo (* inferred *)
  | CompEqMismatch     of  LF.mctx * LF.mctx * Comp.tclo (* arg1 *) * Comp.tclo (* arg2 *)
  | CompEqTyp          of  LF.mctx * LF.mctx * Comp.tclo 

  | CompTypAnn

  | UnboundIdSub                       (* id sub used in empty omega context  *)

  (* whnf errors *)
  | ConstraintsLeft                    (* unclear if this can be raised       *)
  | NotPatSub                          (* ???                                 *)
  | NotPatternSpine

  (* Coverage errors *)
  | NoCover of string

  (* Beluga errors *)
  | LeftoverUndef                      (* encountered Undef after unification *)
  | SubIllTyped                        (* TODO                                *)
  | LeftoverFVar                       (* encountered FVar after 
                                          reconstruction                      *)


exception Error of Syntax.Loc.t option * error
exception Violation of string


val getInformation : unit -> string

val addInformation : string -> unit

