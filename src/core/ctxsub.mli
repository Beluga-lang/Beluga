(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int.LF
open Syntax.Int

(* Moved from reconstruct.ml: *)

val ctxShift : dctx -> sub

(* ctxToSub' cD cPhi cPsi = s

   if x1:A1, ... xn:An = cPsi
   then D = u1:A1[cPhi], ... un:An[cPhi]

   s.t. D; cPhi |- u1[id]/x1 ... un[id]/xn : cPsi
*)
val ctxToSub' : mctx -> dctx -> dctx -> sub
val ctxToSub_mclosed : mctx  -> dctx -> dctx -> mctx * sub * int

val mctxToMSub  : mctx -> msub
val mctxToMMSub : mctx -> mctx -> msub

val isomorphic : mctx -> mctx -> bool

(* lookupSchemaOpt cO psi_offset *)
(* val lookupSchemaOpt : mctx -> int -> schema option *)
