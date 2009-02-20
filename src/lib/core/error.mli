(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int

type typeVariant = Cross | Arrow | CtxPi | PiBox

type error =
  (* indexing errors *)
  | UnboundName of Id.name

  (* LF typechecking errors *)
  | CtxVarMismatch of LF.mctx          (* ???                                 *)
      * LF.ctx_var * LF.schema

  | SigmaIllTyped of                   (* ???                                 *)
      LF.mctx * LF.mctx  * LF.dctx
      * LF.trec_clo (* inferred *) 
      * LF.trec_clo (* expected *)

  | KindMismatch   of LF.mctx * LF.dctx * LF.sclo  * (LF.kind * LF.sub)

      (* cO ; cD ; cPsi |- sA <=/= Typ                 *)
(*  | TypMismatch    of LF.mctx * LF.mctx *  LF.dctx        (* cO ; cD ; cPsi |- sR => sP but sP =/= sA      *)
                     * LF.nclo * LF.tclo (* expected *) * LF.tclo (* inferred *)
 *)
 
  | TypMismatch of LF.mctx             (* cO ; cD ; cPsi |- sR => sP          *)
      * LF.mctx *  LF.dctx * LF.nclo   (* but sP =/= sA                       *)
      * LF.tclo (* expected *) 
      * LF.tclo (* inferred *)

  | IllTyped of                        (* cO ; cD ; cPsi |- sM <=/= sA        *)
      LF.mctx * LF.mctx * LF.dctx             
      * LF.nclo * LF.tclo

  | LeftoverConstraints of Id.name     (* constraints left after 
                                          reconstruction of variable x        *)
  | IllTypedIdSub                      (* ???, not used yet                   *)

  (* Comp level typechecking errors *)
  | ValueRestriction of                (* pat. match. on a non-box expression *)
      LF.mctx * LF.mctx * Comp.gctx    (* cO ; cD ; cG |- i =/=> A[Psi]       *)
      * Comp.exp_syn * Comp.tclo

  | CompIllTyped of                    (* cO ; cD ; cG |- e <=/= tau_theta    *)
      LF.mctx * LF.mctx * Comp.gctx
      * Comp.exp_chk * Comp.tclo

  | CompMismatch of                    (* cO ; cD ; cG |- i => tau_theta,     *)                             
      LF.mctx * LF.mctx * Comp.gctx    (* but tau_theta is of unexpected form *)
      * Comp.exp_syn
      * typeVariant (* expected *) 
      * Comp.tclo (* inferred*)

  | UnboundIdSub                       (* id sub used in empty omega context  *)

  (* whnf errors *)
  | ConstraintsLeft                    (* unclear if this can be raised       *)
  | NotPatSub                          (* ???                                 *)

  (* beluga errors *)
  | LeftoverUndef                      (* encountered Undef after unification *)
  | SubIllTyped                        (* TODO                                *)
  | LeftoverFVar                       (* encountered FVar after 
                                          reconstruction                      *)
