(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

open Syntax.Int


type error =
  | CtxVarMisMatch of cvar * cvar
  | SigmaIllTyped of mctx * dctx * 
                     trec_clo (* inferred *) * trec_clo (* expected *)
  | ExpAppNotFun  
  | KindMisMatch 
  | SubIllTyped      
  | TypIllTyped of mctx * dctx * 
                   tclo (* inferred *) * tclo (* expected *) 
  | TypMisMatch  of mctx * dctx * tclo * tclo
  | IllTyped of mctx * dctx * nclo * tclo

exception Error of error

val check : mctx -> dctx -> nclo -> tclo -> unit

val check_sgn_decls : sgn_decl list -> unit
