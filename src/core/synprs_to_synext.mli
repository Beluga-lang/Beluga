module LF : sig
  val elaborate_kind : Synprs.LF.Object.t -> Synext.LF.kind

  val elaborate_typ : Synprs.LF.Object.t -> Synext.LF.typ

  val elaborate_term : Synprs.LF.Object.t -> Synext.LF.normal
end

module Comp : sig
  val elaborate_kind : Synprs.Comp.Sort_object.t -> Synext.Comp.kind

  val elaborate_typ : Synprs.Comp.Sort_object.t -> Synext.Comp.typ

  val elaborate_exp : Synprs.Comp.Expression_object.t -> Synext.Comp.exp

  val elaborate_pattern : Synprs.Comp.Pattern_object.t -> Synext.Comp.pattern

  val elaborate_numeric_order :
    Synprs.Comp.Totality.Declaration.t -> Synext.Comp.numeric_order
end

module Harpoon : sig
  val elaborate_repl_command :
    Synprs.Harpoon.Repl.Command.t -> Synext.Harpoon.command
end

module Sgn : sig
  val elaborate_sgn : Synprs.Sgn.t -> Synext.Sgn.sgn
end

val name_of_identifier : Identifier.t -> Name.t

val name_of_qualified_identifier : QualifiedIdentifier.t -> Name.t
