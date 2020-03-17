open Beluga

module Error : sig
  type t
  exception E of t
  val fmt_ppr : Format.formatter -> t -> unit
end

(** Executes a single Harpoon interactive command on the given
    state.
    May raise {!Error.E}.
 *)
val process_command : State.t -> State.triple ->
                      Syntax.Ext.Harpoon.command ->
                      unit
