(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Substitutions

    @author Brigitte Pientka
*)

open Syntax.Int.LF

module LF : sig

  (**************************)
  (* Explicit Substitutions *)
  (**************************)

  val id       : sub
  val shift    : sub
  val invShift : sub

  val bvarSub  : int      -> sub -> front
  val frontSub : front    -> sub -> front
  val decSub   : typ_decl -> sub -> typ_decl
  val comp     : sub -> sub -> sub
  val dot1     : sub -> sub
  val invDot1  : sub -> sub

  val isPatSub : sub -> bool



  (***************************)
  (* Inverting Substitutions *)
  (***************************)

  val invert     : sub -> sub
  val strengthen : sub -> dctx -> dctx
  val isId       : sub -> bool

  val compInv    : sub -> sub -> sub

end


module Ctx : sig 


  (*********************************)
  (* Explicit Modual Substitutions *)
  (*********************************)

  val id         : msub
  val shift      : msub


  val mvarMSub   : int       -> msub -> mfront
  val mfrontMSub : mfront    -> msub -> mfront
  val mdecMSub   : ctyp_decl -> msub -> ctyp_decl
  val comp       : msub -> msub -> msub
  val dot1       : msub -> msub

 
end
