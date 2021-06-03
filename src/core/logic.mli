open Syntax.Int

type goal
type query
type mquery
   

module Options : sig
  val enableLogic : bool ref
end

module Convert : sig
  val comptypToCompGoal : Comp.typ -> comp_goal 
  val typToQuery : LF.mctx -> LF.dctx -> LF.typ * Id.offset
                   -> query * LF.typ * LF.sub * (Id.name * LF.normal) list
  val comptypToMQuery : Comp.typ * Id.offset -> mquery * Comp.typ * LF.msub * (Id.name * Comp.meta_obj) list
end

module Frontend : sig
  exception Done
end

module Solver : sig
  val solve : LF.mctx -> LF.dctx -> query -> (LF.dctx * LF.normal -> unit) -> unit
end

module CSolver : sig
  val cgSolve : comp_goal list -> LF.mctx -> mquery -> (LF.mctx -> (LF.dctx * LF.normal) -> unit) -> unit
end 

type bound = int option

val storeQuery : Id.name option -> LF.typ * Id.offset -> LF.mctx -> bound -> bound -> unit
val storeMQuery: Comp.typ * Id.offset -> bound -> bound -> bound -> unit
val runLogic : unit -> unit
val runLogicOn : Id.name option -> LF.typ * Id.offset -> LF.mctx -> bound -> bound -> unit
(** Clears the local storage of the logic programming engine,
 * and loads the LF signature.
 *)
val prepare : unit -> unit
