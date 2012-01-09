(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

module LF : sig 

  open Syntax.Int.LF

  val check       : mctx -> dctx -> nclo -> tclo -> unit
  val syn         : mctx -> dctx -> nclo -> tclo
  val checkTyp    : mctx -> dctx -> tclo         -> unit
  val checkKind   : mctx -> dctx -> kind         -> unit
  val checkDCtx   : mctx -> dctx                 -> unit

  val checkSchemaWf : schema -> unit
  val checkSchema : mctx -> dctx -> schema -> unit
  val subsumes    : mctx -> ctx_var -> ctx_var -> bool

  val checkTypeAgainstSchema: mctx -> dctx -> typ -> sch_elem list -> (typ_rec * sub)
  val instanceOfSchElem     : mctx -> dctx -> tclo -> sch_elem ->  (typ_rec * sub)
  val instanceOfSchElemProj : mctx -> dctx -> tclo -> (head * int) -> sch_elem -> (typ_rec * sub)

  val checkMSub   : mctx -> msub -> mctx -> unit

end


module Comp : sig 

  open Syntax.Int
  open Syntax.Int.Comp

  val check       : LF.mctx -> gctx -> exp_chk -> tclo -> unit
  val syn         : LF.mctx -> gctx -> exp_syn -> tclo
  val checkTyp    : LF.mctx -> typ                  -> unit

end


module Sgn : sig

  open Syntax.Int.Sgn

  val check_sgn_decls :  decl list -> unit

end
