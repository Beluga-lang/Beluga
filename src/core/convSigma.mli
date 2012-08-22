(**
   @author Brigitte Pientka
*)

open Syntax


type error =
  | BlockInDctx of Int.LF.mctx * Int.LF.head * Int.LF.typ * Int.LF.dctx

exception Error of Syntax.Loc.t * error

val strans_typ  : Int.LF.mctx -> Int.LF.tclo  -> Id.offset list -> Int.LF.typ
val strans_norm : Int.LF.mctx -> Int.LF.nclo  -> Id.offset list -> Int.LF.normal
val strans_sub  : Int.LF.mctx -> Int.LF.sub   -> Id.offset list -> Int.LF.sub
val new_index   : Id.offset    -> Id.offset list -> int

val flattenDCtx : Int.LF.mctx -> Int.LF.dctx -> Int.LF.dctx * Id.offset list

val gen_conv_sub: Id.offset list -> Int.LF.sub


