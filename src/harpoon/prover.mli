module Id = Beluga.Id
module Comp = Beluga.Syntax.Int.Comp

val start_toplevel : Format.formatter -> Id.name -> Comp.tclo -> Comp.order option -> unit
