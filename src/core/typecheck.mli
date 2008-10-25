(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Joshua Dunfield
   @author Darin Morrison
   @author Brigitte Pientka
*)

open Syntax.Int

exception Error of string

val check : mctx -> dctx -> nclo -> tclo -> unit

val check_sgn_decls : sgn_decl list -> unit
