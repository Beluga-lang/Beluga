type free_cvars

val kind :
  Store.CVar.t ->
  Syntax.Apx.LF.ctx_var option * Store.BVar.t ->
  free_cvars list ->
  Syntax.Ext.LF.kind -> Syntax.Apx.LF.kind * free_cvars list

val typ :
  Store.CVar.t ->
  Syntax.Apx.LF.ctx_var option * Store.BVar.t ->
  free_cvars list -> Syntax.Ext.LF.typ -> Syntax.Apx.LF.typ * free_cvars list

val term :
  Store.CVar.t ->
  Syntax.Apx.LF.ctx_var option * Store.BVar.t ->
  free_cvars list ->
  Syntax.Ext.LF.normal -> Syntax.Apx.LF.normal * free_cvars list

val schema : Syntax.Ext.LF.schema -> Syntax.Apx.LF.schema

val compkind :
  Store.CVar.t ->
  Store.CVar.t ->
  free_cvars list -> Syntax.Ext.Comp.kind -> Syntax.Apx.Comp.kind

val comptyp :
  Store.CVar.t ->
  Store.CVar.t ->
  free_cvars list -> Syntax.Ext.Comp.typ -> Syntax.Apx.Comp.typ

val exp :
  Store.CVar.t ->
  Store.CVar.t ->
  Store.Var.t ->
  free_cvars list * 'a -> Syntax.Ext.Comp.exp_chk -> Syntax.Apx.Comp.exp_chk

val exp' :
  Store.CVar.t ->
  Store.CVar.t ->
  Store.Var.t ->
  free_cvars list * 'a -> Syntax.Ext.Comp.exp_syn -> Syntax.Apx.Comp.exp_syn
