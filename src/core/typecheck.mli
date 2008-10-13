(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @Brigitte Pientka
   @author Darin Morrison
*)




(* Type Checker for LF and computations *)
(* Author: Brigitte Pientka, Darin Morrison *)

module LF : sig

  open Syntax.LF

  exception Error of string

  val check : ctx_mdl * ctx_lf * tm_clo * tp_clo -> unit

end



module Cmp : sig
end
