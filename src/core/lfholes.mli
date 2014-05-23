open Syntax.Int

val none : unit -> bool
val collect : Syntax.Loc.t * LF.mctx * LF.dctx * LF.tclo -> unit
val printAll : unit -> unit
val getNumHoles : unit -> int
val printOneHole : int -> unit
val getHolePos : int -> Camlp4.PreCast.Loc.t option