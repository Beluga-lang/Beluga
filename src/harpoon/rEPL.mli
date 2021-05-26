(** Main Harpoon REPL module. *)

(** The input prompt for the Harpoon toplevel.
    See main.ml and linenoise library document for details. *)
val start : Options.save_mode ->
            Options.interaction_mode ->
            string -> (* the path to the signature that was loaded *)
            string list -> (* the resolved paths from the signature *)
            Syntax.Int.Comp.open_subgoal list -> (* the open subgoals to recover *)
            IO.t -> (* IO capabilities *)
            unit
