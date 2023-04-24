module Comp = Beluga_syntax.Synint.Comp
module Command = Beluga_syntax.Ext.Harpoon

type t =
  Theorem.t -> Comp.proof_state -> bool

module State : sig
  type t

  val make : unit -> t
  val serialize : Format.formatter -> t -> unit
end

val toggle : State.t -> [ `auto_intros | `auto_solve_trivial ] -> [ `on | `off | `toggle ] -> unit
val execute : State.t -> t
