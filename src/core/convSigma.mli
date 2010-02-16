(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

open Syntax

val strans_typ  : Int.LF.tclo  -> Id.offset list -> Int.LF.typ
val strans_norm : Int.LF.nclo  -> Id.offset list -> Int.LF.normal
val strans_sub  : Int.LF.sub   -> Id.offset list -> Int.LF.sub
val new_index   : Id.offset    -> Id.offset list -> int

val flattenDCtx : Int.LF.dctx -> Int.LF.dctx * Id.offset list

val gen_conv_sub: Id.offset list -> Int.LF.sub


