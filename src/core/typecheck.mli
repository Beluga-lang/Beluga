(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @Brigitte Pientka
   @author Darin Morrison
*)

  open Syntax.Int

  exception Error of string

  val check : mctx -> dctx -> nclo -> tclo -> unit

  val check_sgn_decls : sgn_decl list -> unit

(*

module Cmp : sig
end
*)
