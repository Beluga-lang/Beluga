open Syntax.Int

val none : unit -> bool
val collect : Syntax.Loc.t * LF.mctx * LF.dctx * LF.tclo -> unit
val printAll : unit -> unit
val getNumHoles : unit -> int
val printOneHole : int -> unit
val getHolePos : int -> Syntax.Loc.t option
val getOneHole : int -> Loc.t * LF.mctx * LF.dctx * LF.tclo
val locWithin : Loc.t -> Loc.t -> bool
val destroyHoles : Loc.t -> unit
val commitHoles : unit -> unit
val stashHoles : unit -> unit
val getStagedHoleNum : Loc.t -> int
val setStagedHolePos : int -> Loc.t -> unit
val clear : unit -> unit