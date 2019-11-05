module Comp = Beluga.Syntax.Int.Comp
module Command = Beluga.Syntax.Ext.Harpoon

type t =
  Theorem.t -> Comp.proof_state -> bool

type automation_state

val make_automation_state : unit -> automation_state

val toggle_automation : automation_state -> Command.automation_kind -> Command.automation_change -> unit
val exec_automation : automation_state -> t
