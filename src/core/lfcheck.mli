  open Syntax.Int.LF

  exception Violation of string
  exception Error of Syntax.Loc.t option * Error.error

  val check       : mctx -> dctx -> nclo -> tclo -> unit
  val syn         : mctx -> dctx -> nclo -> tclo
  val checkTyp    : mctx -> dctx -> tclo         -> unit
  val checkKind   : mctx -> dctx -> kind         -> unit
  val checkDCtx   : mctx -> dctx                 -> unit

  val checkSub    : Syntax.Loc.t option -> mctx -> dctx -> sub -> dctx -> unit
  val inferHead   : Syntax.Loc.t option -> mctx -> dctx -> head -> typ

  val checkSchemaWf : schema -> unit
  val checkSchema : mctx -> dctx -> schema -> unit
  val subsumes    : mctx -> ctx_var -> ctx_var -> bool

  val synCtxSchema  : mctx -> ctx_var -> Id.cid_schema

  val checkTypeAgainstSchema: mctx -> dctx -> typ -> sch_elem list -> (typ_rec * sub)
  val instanceOfSchElem     : mctx -> dctx -> tclo -> sch_elem ->  (typ_rec * sub)
  val instanceOfSchElemProj : mctx -> dctx -> tclo -> (head * int) -> sch_elem -> (typ_rec * sub)

  val checkMSub   : mctx -> msub -> mctx -> unit
