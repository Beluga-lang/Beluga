module Id = Beluga.Id
module Comp = Beluga.Syntax.Int.Comp

(** The input prompty for the Harpoon toplevel.
    See main.ml and linenoise library document for details.
 *)
type prompt = string -> string option -> unit -> string option

val start_toplevel : prompt -> Format.formatter -> unit
