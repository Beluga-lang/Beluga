(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Joshua Dunfield
   @author Darin Morrison
   @author Brigitte Pientka
*)

open Syntax.Int



type error =
  | CtxVarMisMatch of cvar * cvar
  | DeclIllTyped
  | ExpAppNotFun
  | KindMisMatch
  | SubIllTyped
  | TypMisMatch    of tclo * tclo

exception Error of error

val check : mctx -> dctx -> nclo -> tclo -> unit

val check_sgn_decls : sgn_decl list -> unit
