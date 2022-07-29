module LF : sig
  val elaborate_kind : Synprs.LF.kind -> Synext.LF.kind

  val elaborate_typ : Synprs.LF.typ -> Synext.LF.typ

  val elaborate_term : Synprs.LF.term -> Synext.LF.normal
end

module Comp : sig
  val elaborate_kind : Synprs.Comp.kind -> Synext.Comp.kind

  val elaborate_typ : Synprs.Comp.typ -> Synext.Comp.typ

  val elaborate_exp : Synprs.Comp.exp -> Synext.Comp.exp

  val elaborate_pattern : Synprs.Comp.pattern -> Synext.Comp.pattern
end

module Harpoon : sig
  val elaborate_command : Synprs.Harpoon.command -> Synext.Harpoon.command
end

module Sgn : sig
  val elaborate_sgn : Synprs.Sgn.sgn -> Synext.Sgn.sgn
end
