open Syntax.Int

val none : unit -> bool
val collect : Syntax.Loc.t * LF.mctx * LF.dctx * LF.tclo -> unit
val printAll : unit -> unit
