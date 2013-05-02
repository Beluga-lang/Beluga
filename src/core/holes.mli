open Syntax.Int

val none : unit -> bool
val collect : Syntax.Loc.t * LF.mctx * Comp.gctx * (Comp.typ * LF.msub) -> unit
val printAll : unit -> unit
val printOneHole : int -> unit
val printNumHoles : unit -> unit
val printHolePos : int -> unit

