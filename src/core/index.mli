type fcvars

val kind     : Syntax.Ext.LF.kind -> Syntax.Apx.LF.kind * fcvars 

val typ      : Syntax.Ext.LF.typ -> Syntax.Apx.LF.typ * fcvars 

val schema   : Syntax.Ext.LF.schema -> Syntax.Apx.LF.schema

val compkind : Syntax.Ext.Comp.kind -> Syntax.Apx.Comp.kind

val comptyp  : Syntax.Ext.Comp.typ -> Syntax.Apx.Comp.typ

val exp      : Store.Var.t -> Syntax.Ext.Comp.exp_chk -> Syntax.Apx.Comp.exp_chk

val exp'     : Store.Var.t -> Syntax.Ext.Comp.exp_syn -> Syntax.Apx.Comp.exp_syn
