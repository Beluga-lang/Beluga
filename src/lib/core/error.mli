(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax

module Error : sig

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
    | TypMisMatch of Int.LF.mctx * Int.LF.dctx * Int.LF.tclo * Int.LF.tclo
    | IllTyped of Int.LF.mctx * Int.LF.dctx * Int.LF.nclo * Int.LF.tclo

end
