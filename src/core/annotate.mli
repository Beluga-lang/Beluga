module PrettyAnn : sig
  val fresh_name_dctx : Syntax.Int.LF.dctx -> Id.name -> Id.name
  val fresh_name_mctx : Syntax.Int.LF.mctx -> Id.name -> Id.name
  val fresh_name_gctx : Syntax.Int.Comp.gctx -> Id.name -> Id.name
  val phatToDCtx : Syntax.Int.LF.psi_hat -> Syntax.Int.LF.dctx

  val expChkToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
		       -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
		       -> Annotated.Comp.exp_chk -> string

  val expSynToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
           -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
           -> Annotated.Comp.exp_syn -> string

  val metaObjToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
           -> Annotated.Comp.meta_obj -> string

  val normalToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
           -> Syntax.Int.LF.dctx -> Annotated.LF.normal
           -> string

  val headToString : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
           -> Syntax.Int.LF.dctx -> string -> ?mathcal:bool
           -> Syntax.Int.LF.head -> string
end

module Comp : sig
  val ann : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
	    -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
	    -> Syntax.Int.Comp.exp_chk
	    -> (Syntax.Int.Comp.typ * Syntax.Int.LF.msub)
	    ->  Annotated.Comp.exp_chk
end