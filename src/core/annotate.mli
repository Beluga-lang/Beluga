module PrettyAnn : sig
  val fresh_name_dctx : Syntax.Int.LF.dctx -> Id.name -> Id.name
  val fresh_name_mctx : Syntax.Int.LF.mctx -> Id.name -> Id.name
  val fresh_name_gctx : Syntax.Int.Comp.gctx -> Id.name -> Id.name

  val expChkToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
		       -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
		       -> Annotated.Comp.exp_chk -> string

  val expSynToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
               -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
               -> Annotated.Comp.exp_syn -> string
end

module Comp : sig
  val ann : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
	    -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
	    -> Syntax.Int.Comp.exp_chk
	    -> (Syntax.Int.Comp.typ * Syntax.Int.LF.msub)
	    ->  Annotated.Comp.exp_chk
end