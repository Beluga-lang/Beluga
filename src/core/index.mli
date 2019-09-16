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
               Syntax.Ext.LF.kind -> fvars * Syntax.Apx.LF.kind

val typ      : name_disambiguator ->
               Syntax.Ext.LF.typ -> fvars * Syntax.Apx.LF.typ

val schema   : Syntax.Ext.LF.schema -> Syntax.Apx.LF.schema

val mctx     : Syntax.Ext.LF.mctx -> Syntax.Apx.LF.mctx

val compkind : Syntax.Ext.Comp.kind -> Syntax.Apx.Comp.kind

val comptyp  : Syntax.Ext.Comp.typ -> Syntax.Apx.Comp.typ

val comptypdef : Syntax.Ext.Comp.typ * Syntax.Ext.Comp.kind
              -> Syntax.Apx.Comp.typ * Syntax.Apx.Comp.kind

val exp      : Store.Var.t -> Syntax.Ext.Comp.exp_chk -> Syntax.Apx.Comp.exp_chk
val exp'     : Store.Var.t -> Syntax.Ext.Comp.exp_syn -> Syntax.Apx.Comp.exp_syn
val hexp     : Store.CVar.t ->  Store.Var.t -> Syntax.Ext.Comp.exp_chk -> Syntax.Apx.Comp.exp_chk
val hexp'    : Store.CVar.t ->  Store.Var.t -> Syntax.Ext.Comp.exp_syn -> Syntax.Apx.Comp.exp_syn
