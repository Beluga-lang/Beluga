module Comp = Syntax.Int.Comp
module Command = Syntax.Ext.Harpoon

type t =
  Theorem.t -> Comp.proof_state -> bool

module State : sig
  type t

  val make : unit -> t
  val serialize : Format.formatter -> t -> unit
end

val toggle : State.t -> Command.automation_kind -> Command.automation_change -> unit
val execute : State.t -> t
