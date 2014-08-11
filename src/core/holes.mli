open Syntax.Int

type hole = Loc.t * LF.mctx * Comp.gctx * (Comp.typ * LF.msub)

val none : unit -> bool
val collect : Syntax.Loc.t * LF.mctx * Comp.gctx * (Comp.typ * LF.msub) -> unit
val printAll : unit -> unit
val printOneHole : int -> unit
val getOneHole : int -> Loc.t * LF.mctx * Comp.gctx * (Comp.typ * LF.msub)

val locWithin : Loc.t -> Loc.t -> bool
val getHoleNum : Loc.t -> int
val getNumHoles : unit -> int
val getHolePos : int -> Syntax.Loc.t option
val destroyHoles : Loc.t -> unit

val commitHoles : unit -> unit
val stashHoles : unit -> unit
val getStagedHoleNum : Loc.t -> int
val setStagedHolePos : int -> Loc.t -> unit

val clear : unit -> unit