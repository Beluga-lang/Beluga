(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax
open Id

type error =
  | CtxVarMismatch of Int.LF.cvar * Int.LF.cvar
  | SigmaIllTyped of Int.LF.mctx * Int.LF.dctx 
      * Int.LF.trec_clo (* inferred *) * Int.LF.trec_clo (* expected *)
  | ExpAppNotFun  
  | ExpNilNotAtom
  | KindMismatch 
  | SubIllTyped      
  | TypIllTyped of Int.LF.mctx * Int.LF.dctx
      * Int.LF.tclo (* inferred *) * Int.LF.tclo (* expected *) 
  | TypMismatch of (* Int.LF.mctx * *) Int.LF.dctx * Int.LF.tclo * Int.LF.tclo
  | IllTyped of (* Int.LF.mctx * *) Int.LF.dctx * Int.LF.nclo * Int.LF.tclo

  | UnboundName of name
  | LeftoverConstraints
  | LeftoverUndef
  | IllTypedIdSub
  | ValueRestriction
  | CompIllTyped

  (* whnf errors *)
  | ConstraintsLeft
  | NotPatSub
