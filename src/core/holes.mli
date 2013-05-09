open Syntax.Int

type hole

val none : unit -> bool
val collect : Syntax.Loc.t * LF.mctx * Comp.gctx * (Comp.typ * LF.msub) -> unit
val printAll : unit -> unit
val printOneHole : int -> unit


val getNumHoles : unit -> int
val getHolePos : int -> Camlp4.PreCast.Loc.t option
