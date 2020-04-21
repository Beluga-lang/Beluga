open Syntax.Int

type goal
type query

module Options : sig
  val enableLogic : bool ref
end

module Convert : sig
  val typToQuery : LF.dctx -> LF.mctx -> LF.typ * Id.offset
                   -> query * LF.typ * LF.sub * (Id.name * LF.normal) list
end

module Frontend : sig
  exception Done
end

module Solver : sig
  val solve : LF.mctx -> LF.dctx -> query -> (LF.dctx * LF.normal -> unit) -> unit
end

type bound = int option

val storeQuery : Id.name option -> LF.typ * Id.offset -> bound -> bound -> unit
val runLogic : unit -> unit
val runLogicOn : Id.name option -> LF.typ * Id.offset -> bound -> bound -> unit
(** Clears the local storage of the logic programming engine,
 * and loads the LF signature.
 *)
val prepare : unit -> unit
