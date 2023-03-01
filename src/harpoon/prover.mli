open Beluga_syntax

module Error : sig
  type t

  exception E of t

  val error_printer : t -> Format.formatter -> unit
end

(** Executes a single Harpoon interactive command on the given state. May
    raise {!Error.E}. *)
val process_command :
  HarpoonState.t -> HarpoonState.triple -> Synext.harpoon_repl_command -> unit
