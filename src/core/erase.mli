(** Erasure from internal syntax to external syntax. *)

open Syntax
open Store

module LF : sig
end

module Comp : sig
  val meta_obj : CVar.t -> Int.Comp.meta_obj -> Ext.Comp.meta_obj
  val exp : CVar.t -> Var.t -> Int.Comp.exp_chk -> Ext.Comp.exp_chk
  val exp' : CVar.t -> Var.t -> Int.Comp.exp_syn -> Ext.Comp.exp_syn
  val thm : CVar.t -> Var.t -> Int.Comp.thm -> Ext.Comp.thm
end
