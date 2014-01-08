(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int.LF
open Syntax.Int

val csub_ckind : mctx -> dctx -> int -> Comp.kind -> Comp.kind
val csub_ctyp  : mctx -> dctx -> int -> Comp.typ -> Comp.typ
val csub_msub  : dctx -> int -> msub -> msub
val csub_exp_chk : dctx -> int -> Comp.exp_chk -> Comp.exp_chk
val csub_exp_syn : dctx -> int -> Comp.exp_syn -> Comp.exp_syn


val ctxnorm_typ : typ  * csub -> typ
val ctxnorm     : normal * csub -> normal
val ctxnorm_sub : sub * csub    -> sub
val ctxnorm_psihat: psi_hat * csub -> psi_hat
val ctxnorm_dctx: dctx * csub -> dctx
val ctxnorm_mctx: mctx * csub -> mctx
val ctxnorm_gctx: Comp.gctx * csub -> Comp.gctx
val ctxnorm_ctyp : Comp.typ  * csub -> Comp.typ
val ctxnorm_exp_chk : Comp.exp_chk  * csub -> Comp.exp_chk

val ctxnorm_msub: msub * csub -> msub

val cdot1       : csub -> csub
val id_csub     : mctx -> csub
val apply_csub  : ctx_var -> csub -> dctx

val inst_csub   : dctx -> Id.offset -> csub -> mctx (* cO *) -> (mctx * csub)
val ccomp       : csub -> csub -> csub

val ctxnorm_csub : csub -> csub


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
val cctxToCSub  : mctx -> mctx -> csub

val isomorphic : mctx -> mctx -> bool

(* lookupSchemaOpt cO psi_offset *)
(* val lookupSchemaOpt : mctx -> int -> schema option *)
