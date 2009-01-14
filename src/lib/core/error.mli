(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax
open Id

type error =
  | CtxVarMisMatch of Int.LF.cvar * Int.LF.cvar
  | SigmaIllTyped of Int.LF.mctx * Int.LF.dctx 
      * Int.LF.trec_clo (* inferred *) * Int.LF.trec_clo (* expected *)
  | ExpAppNotFun  
  | ExpNilNotAtom
  | KindMisMatch 
  | SubIllTyped      
  | TypIllTyped of Int.LF.mctx * Int.LF.dctx
      * Int.LF.tclo (* inferred *) * Int.LF.tclo (* expected *) 
  | TypMisMatch of (* Int.LF.mctx * *) Int.LF.dctx * Int.LF.tclo * Int.LF.tclo
  | IllTyped of (* Int.LF.mctx * *) Int.LF.dctx * Apx.LF.normal * Int.LF.tclo

  | UnboundName of name
  | LeftOverConstraints
  | LeftOverUndef
  | IllTypedIdSub
  | ValueRestriction
  | CompIllTyped

  (* whnf errors *)
  | ConstraintsLeft
  | NotPatSub
