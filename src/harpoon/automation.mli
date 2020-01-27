module Comp = Beluga.Syntax.Int.Comp
module Command = Beluga.Syntax.Ext.Harpoon

type t =
  Theorem.t -> Comp.proof_state -> bool

module State : sig
  type t

  val make : unit -> t
end

val toggle : State.t -> Command.automation_kind -> Command.automation_change -> unit
val execute : State.t -> t
