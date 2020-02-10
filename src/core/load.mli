(** Loads one file *on top* of what has already been loaded. *)
val load_one : Format.formatter -> string -> unit

(** Clears all internal state and loads the given path to a cfg or bel
    file.
    The list of resolved paths (paths to bel files) is returned.
 *)
val load : Format.formatter -> string -> string list
