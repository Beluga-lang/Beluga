module Id = Beluga.Id
module Comp = Beluga.Syntax.Int.Comp

(** The input prompty for the Harpoon toplevel.
    See main.ml and linenoise library document for details.
 *)
val start_toplevel : InputPrompt.t -> Format.formatter -> unit
