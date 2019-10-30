module Comp = Beluga.Syntax.Int.Comp
module Command = Beluga.Syntax.Ext.Harpoon

type t =
  Comp.proof_state -> Tactic.tactic_context -> bool

type automation_info = bool ref * t
type automation_state =
  (Command.automation_kind, automation_info) Hashtbl.t

val make_automation_state : unit -> automation_state

val toggle_automation : automation_state -> Command.automation_kind -> Command.automation_change -> unit
val exec_automation : automation_state -> t
