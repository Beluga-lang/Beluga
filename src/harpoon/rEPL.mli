(** Main Harpoon REPL module. *)

open Beluga_syntax

module Disambiguation_state =
  Beluga_parser.Disambiguation_state.Disambiguation_state

module Indexing_state = Beluga.Index_state.Indexing_state

(** The input prompt for the Harpoon toplevel. See main.ml and linenoise
    library document for details. *)
val start :
     Disambiguation_state.state Id.Prog.Hashtbl.t * Disambiguation_state.state
  -> Indexing_state.state Id.Prog.Hashtbl.t * Indexing_state.state
  -> Options.save_mode
  -> Options.interaction_mode
  -> string
  -> (* the path to the signature that was loaded *)
     string list
  -> (* the resolved paths from the signature *)
     Synint.Comp.open_subgoal list
  -> (* the open subgoals to recover *)
     IO.t
  -> (* IO capabilities *)
     unit
