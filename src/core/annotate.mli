module Comp : sig
  val ann : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
	    -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
	    -> Syntax.Int.Comp.exp_chk
	    -> (Syntax.Int.Comp.typ * Syntax.Int.LF.msub)
	    ->  Annotated.Comp.exp_chk
end
