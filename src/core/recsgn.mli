open Syntax

type leftoverVars = (Abstract.free_var Int.LF.ctx * Loc.t) list

(** Processes global pragmas, which must appear at the beginning of
    the list, and returns the remaining declarations. *)
val apply_global_pragmas : Syntax.Ext.Sgn.decl list -> Syntax.Ext.Sgn.decl list

val recSgnDecls : Syntax.Ext.Sgn.decl list -> Syntax.Int.Sgn.decl list * leftoverVars option

val print_leftoverVars : leftoverVars -> unit
