(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

module LF : sig 

  open Syntax.Int.LF

  exception Error of string

  val check       : mctx -> mctx -> dctx -> nclo -> tclo -> unit
  val checkTyp    : mctx -> mctx -> dctx -> tclo         -> unit
  val checkKind   : mctx -> mctx -> dctx -> kind         -> unit
  val checkDCtx   : mctx -> mctx -> dctx                 -> unit

end


module Comp : sig 

  open Syntax.Int
  open Syntax.Int.Comp

  val check       : LF.mctx -> LF.mctx -> gctx -> exp_chk -> tclo -> unit
  val syn         : LF.mctx -> LF.mctx -> gctx -> exp_syn -> tclo

  val checkSchema : LF.mctx -> LF.mctx -> LF.dctx -> LF.schema -> unit
  val checkTyp    : LF.mctx -> LF.mctx -> typ                  -> unit

end


module Sgn : sig

  open Syntax.Int.Sgn

  val check_sgn_decls :  decl list -> unit

end
