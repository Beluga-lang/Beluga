module Ext = Syntax.Ext
module Apx = Syntax.Apx

type open_or_closed =
  [ `open_term
  | `closed_term
  ]

type fvars =
  { open_flag : open_or_closed
  ; vars : Store.CVar.cvar list
  }

type name_disambiguator
val disambiguate_to_fvars : name_disambiguator
val disambiguate_to_fmvars : name_disambiguator

val kind     : name_disambiguator ->
               Ext.LF.kind -> fvars * Apx.LF.kind

val typ      : name_disambiguator ->
               Ext.LF.typ -> fvars * Apx.LF.typ

val schema   : Ext.LF.schema -> Apx.LF.schema

val mctx     : Ext.LF.mctx -> Apx.LF.mctx

val compkind : Ext.Comp.kind -> Apx.Comp.kind

val comptyp  : Ext.Comp.typ -> Apx.Comp.typ
val hcomptyp  : Store.CVar.t -> Ext.Comp.typ -> Apx.Comp.typ

val comptypdef : Ext.Comp.typ * Ext.Comp.kind
              -> Apx.Comp.typ * Apx.Comp.kind

val exp      : Store.Var.t -> Ext.Comp.exp_chk -> Apx.Comp.exp_chk
val exp'     : Store.Var.t -> Ext.Comp.exp_syn -> Apx.Comp.exp_syn
val hexp     : Store.CVar.t -> Store.Var.t -> Ext.Comp.exp_chk -> Apx.Comp.exp_chk
val hexp'    : Store.CVar.t -> Store.Var.t -> Ext.Comp.exp_syn -> Apx.Comp.exp_syn
val thm      : Store.Var.t -> Ext.Comp.thm -> Apx.Comp.thm
