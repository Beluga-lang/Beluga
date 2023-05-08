open Beluga
open Beluga_syntax

exception Prover_error of exn

(** Executes a single Harpoon interactive command on the given state. May
    raise a {!exn:Prover_error}. *)
val process_command :
     Beluga_parser.Parser.Disambiguation_state.state
     * Index_state.Indexing_state.state
     * HarpoonState.t
     * HarpoonState.substate
  -> Location.t
  -> string
  -> unit
