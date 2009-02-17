(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int
open Id

type error =
  (* indexing errors *)
  | UnboundName of name

  (* reconstruction errors *)
  | CtxVarMismatch of LF.mctx * LF.ctx_var * LF.schema
  | SigmaIllTyped  of LF.mctx * LF.mctx  * LF.dctx * 
                      LF.trec_clo (* inferred *) * LF.trec_clo (* expected *)

  | KindMismatch   of LF.mctx * LF.dctx * LF.tclo         (* cO ; cD ; cPsi |- sA <=/= Typ                 *)
  | TypMismatch    of LF.mctx * LF.mctx *  LF.dctx        (* cO ; cD ; cPsi |- sR => sP but sP =/= sA      *)
                     * LF.nclo * LF.tclo (* expected *) * LF.tclo (* inferred *)

  | IllTyped    of LF.mctx * LF.mctx * LF.dctx             (* cO ; cD ; cPsi |- sM <=/= sA                  *)
                   * LF.nclo * LF.tclo

  | LeftoverConstraints of name        (* constraints left after reconstruction of variable x *)
  | IllTypedIdSub                      (* ???, not used yet                   *)
  | ValueRestriction                   (* pat. match. on a non-box expression *)
  | CompIllTyped of Comp.exp_chk  * Comp.typ

  (* whnf errors *)
  | ConstraintsLeft                    (* unclear if this can be raised       *)
  | NotPatSub                          (* ???                                 *)

  (* beluga errors *)
  | LeftoverUndef                      (* encountered Undef after unification *)
  | SubIllTyped                        (* TODO                                *)
