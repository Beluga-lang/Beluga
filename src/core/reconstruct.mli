open Syntax

val solve_fvarCnstr : Lfrecon.reconType -> unit
val reset_fvarCnstr : unit -> unit

val kind : Apx.LF.kind -> Int.LF.kind
val typ : Lfrecon.reconType -> Apx.LF.typ -> Int.LF.typ
val schema : Apx.LF.schema -> Int.LF.schema
val compkind : Apx.Comp.kind -> Int.Comp.kind
val comptyp : Apx.Comp.typ -> Int.Comp.typ
val exp : Int.Comp.ctyp_decl Int.LF.ctx -> Apx.Comp.exp_chk -> Int.Comp.typ * Int.LF.msub -> Int.Comp.exp_chk
val exp' : Int.Comp.ctyp_decl Int.LF.ctx -> Apx.Comp.exp_syn -> Int.Comp.exp_syn * Int.Comp.tclo
