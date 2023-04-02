(** Clears all internal state and loads the given path to a [.cfg] or [.bel]
    file. The list of resolved paths (paths to [.bel] files) is returned. *)
val load : string -> string list
