open Syntax

val solve_fvarCnstr : Lfrecon.reconType -> unit
val reset_fvarCnstr : unit -> unit

val kind : Apx.LF.kind -> Int.LF.kind
val typ : Lfrecon.reconType -> Apx.LF.typ -> Int.LF.typ
val schema : Apx.LF.schema -> Int.LF.schema
val mctx   : Apx.LF.mctx   -> Int.LF.mctx
val compkind : Apx.Comp.kind -> Int.Comp.kind
val comptyp : Apx.Comp.typ -> Int.Comp.typ
val comptyp_cD : Int.LF.mctx -> Apx.Comp.typ -> Int.Comp.typ
val comptypdef : Syntax.Loc.t ->
                 Id.name -> (Apx.Comp.typ * Apx.Comp.kind) ->
                 (Int.LF.mctx * Int.Comp.typ) * Id.offset * Int.Comp.kind
val elExp  : Int.LF.mctx ->
             Int.Comp.gctx ->
             Apx.Comp.exp_chk ->
             Int.Comp.typ * Int.LF.msub ->
             Int.Comp.exp_chk

val elExp' : Int.LF.mctx ->
             Int.Comp.gctx ->
             Apx.Comp.exp_syn ->
             Int.Comp.exp_syn * Int.Comp.tclo

val exp  : Int.Comp.gctx -> Apx.Comp.exp_chk -> Int.Comp.typ * Int.LF.msub -> Int.Comp.exp_chk
val exp' : Int.Comp.gctx -> Apx.Comp.exp_syn -> Int.Comp.exp_syn * Int.Comp.tclo
