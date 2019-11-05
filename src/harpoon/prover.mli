module Id = Beluga.Id
module Comp = Beluga.Syntax.Int.Comp

(** The input source for the Harpoon toplevel.
    It's simply a generator of lines.
    See helpers in Support.Misc.Gen.
 *)
type input_source = string Gen.t

val start_toplevel : input_source -> Format.formatter -> unit
