(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

module LF : sig 

  open Syntax.Int.LF

  exception Violation of string
  exception Error of Syntax.Loc.t option * Error.error


  val check       : mctx -> mctx -> dctx -> nclo -> tclo -> unit
  val checkTyp    : mctx -> mctx -> dctx -> tclo         -> unit
  val checkKind   : mctx -> mctx -> dctx -> kind         -> unit
  val checkDCtx   : mctx -> mctx -> dctx                 -> unit

  val checkSchema : mctx -> mctx -> dctx -> schema -> unit
  val checkTypeAgainstElement : mctx -> mctx -> dctx -> tclo -> sch_elem -> unit
  val checkTypeAgainstElementProjection : mctx -> mctx -> dctx -> tclo -> (head * int) -> sch_elem -> unit

end


module Comp : sig 

  open Syntax.Int
  open Syntax.Int.Comp

  exception Violation of string
  exception Error of Error.error

  val check       : LF.mctx -> LF.mctx -> gctx -> exp_chk -> tclo -> unit
  val syn         : LF.mctx -> LF.mctx -> gctx -> exp_syn -> tclo
  val checkTyp    : LF.mctx -> LF.mctx -> typ                  -> unit

end


module Sgn : sig

  open Syntax.Int.Sgn

  val check_sgn_decls :  decl list -> unit

end
