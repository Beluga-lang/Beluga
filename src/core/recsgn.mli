open Syntax

type leftoverVars = (Abstract.free_var Int.LF.ctx * Loc.t) list

val recSgnDecls : Syntax.Ext.Sgn.decl list -> Syntax.Int.Sgn.decl list * leftoverVars option

val print_leftoverVars : leftoverVars -> unit
