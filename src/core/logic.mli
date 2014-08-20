open Syntax.Int

module Options :
sig
  val enableLogic : bool ref
end

type bound = int option

val storeQuery : Id.name option -> LF.typ * Id.offset -> bound -> bound -> unit
val runLogic : unit -> unit
val runLogicOn : Id.name option -> LF.typ * Id.offset -> bound -> bound -> unit
