open Support
open Syntax

type leftover_vars = (Abstract.free_var Int.LF.ctx * Location.t) list

(** Processes global pragmas, which must appear at the beginning of
    the list, and returns the remaining declarations. *)
val apply_global_pragmas : Syntax.Ext.Sgn.decl list -> Syntax.Ext.Sgn.decl list

val recSgnDecls : Syntax.Ext.Sgn.decl list -> Syntax.Int.Sgn.decl list * leftover_vars option

val fmt_ppr_leftover_vars : Format.formatter -> leftover_vars -> unit
val ppr_leftover_vars : leftover_vars -> unit
