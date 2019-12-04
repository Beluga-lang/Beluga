module Id = Beluga.Id
module Comp = Beluga.Syntax.Int.Comp

(** The input prompt for the Harpoon toplevel.
    See main.ml and linenoise library document for details.

    The `stop and `go_on flag control what happens in the presence of errors.
    In particular, the `stop flag will cause Harpoon to exit as soon
    as an error in encountered instead of continuing to process
    commands which may not make sense anymore.
    This is especially important when running tests.
 *)
val start_toplevel : [ `stop | `go_on ] -> InputPrompt.t -> Format.formatter -> unit
