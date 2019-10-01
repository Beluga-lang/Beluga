(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

module LF : sig

  open Syntax.Int.LF

  type error =
    | CtxVarMisCheck   of mctx * dctx * tclo * schema
    | CtxVarMismatch   of mctx * ctx_var * schema
    | CtxVarDiffer     of mctx * ctx_var * ctx_var
    | CheckError       of mctx * dctx * nclo * tclo
    | TupleArity       of mctx * dctx * nclo * trec_clo
    | SigmaMismatch    of mctx * dctx * trec_clo * trec_clo
    | KindMismatch     of mctx * dctx * sclo * (kind * sub)
    | TypMismatch      of mctx * dctx * nclo * tclo * tclo
    | IllTypedSub      of mctx * dctx * sub * dctx
    | SpineIllTyped    of int * int
    | LeftoverFV
    | ParamVarInst     of mctx * dctx * tclo
    | CtxHatMismatch  of mctx * dctx (* expected *) * dctx_hat (* found *) * (Syntax.Loc.t * mfront)
    | IllTypedMetaObj of mctx * clobj * dctx * cltyp
    | TermWhenVar      of mctx * dctx * normal
    | SubWhenRen       of mctx * dctx * sub
    | MissingType of string

  exception Error of Syntax.Loc.t * error

  val check       : mctx -> dctx -> nclo -> tclo -> unit

  val syn         : mctx -> dctx -> nclo -> tclo
  val checkTyp    : mctx -> dctx -> tclo         -> unit
  val checkKind   : mctx -> dctx -> kind         -> unit
  val checkDCtx   : mctx -> dctx                 -> unit

  val checkSchemaWf : schema -> unit
  val checkSchema : Syntax.Loc.t -> mctx -> dctx -> schema -> unit
  val subsumes    : mctx -> ctx_var -> ctx_var -> bool

  val checkTypeAgainstSchema: Syntax.Loc.t ->  mctx -> dctx -> typ -> sch_elem list -> (typ_rec * sub)
  val instanceOfSchElem     : mctx -> dctx -> tclo -> sch_elem ->  (typ_rec * sub)
  val instanceOfSchElemProj : mctx -> dctx -> tclo -> (head * int) -> sch_elem -> (typ_rec * sub)

  val checkMSub   : Syntax.Loc.t -> mctx -> msub -> mctx -> unit

end

module Comp : sig
  open Syntax.Int.Comp
  open Syntax.Int

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type mismatch_kind =
    [ `fn
    | `mlam
    | `box
    | `ctxfun
    | `pair
    ]

  type error =
    | IllegalParamTyp of LF.mctx * LF.dctx * LF.typ
    | MismatchChk     of LF.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of LF.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of LF.mctx * gctx * pattern * tclo * tclo
    | BasicMismatch   of mismatch_kind * LF.mctx * gctx * tclo
    | SBoxMismatch    of LF.mctx * gctx  * LF.dctx  * LF.dctx
    | SynMismatch     of LF.mctx * tclo (* expected *) * tclo (* inferred *)
    | BoxCtxMismatch  of LF.mctx * LF.dctx * (LF.dctx_hat * LF.normal)
    | PattMismatch    of (LF.mctx * meta_obj * meta_typ) * (LF.mctx * meta_typ)
(*    | PattMismatch    of (LF.mctx * LF.dctx * LF.normal option * LF.tclo) *
                         (LF.mctx * LF.dctx * LF.tclo)*)
    | MAppMismatch    of LF.mctx * (meta_typ * LF.msub)
    | AppMismatch     of LF.mctx * (meta_typ * LF.msub)
    | CtxMismatch     of LF.mctx * LF.dctx (* expected *) * LF.dctx (* found *) * meta_obj
    | TypMismatch     of LF.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name option * string
    | InvalidRecCall
    | MissingTotal    of Id.cid_prog

  exception Error of Syntax.Loc.t * error

  val check :
    LF.mctx ->
    (* ^ The meta context *)
    gctx ->
    (* ^ The computation context *)
    Total.dec list ->
    (* ^ the group of mutual recursive functions the expression is being checked in *)
    ?cIH: gctx ->
    (* ^ the context of available induction hypotheses *)
    exp_chk ->
    (* ^ The expression to check *)
    tclo ->
    (* ^ The type it should have *)
    unit

  val syn :
    LF.mctx ->
    (* ^ The meta context *)
    gctx ->
    (* ^ The computation context *)
    Total.dec list ->
    (* ^ The group of mutual recursive functions the expression is being checked in *)
    ?cIH: gctx ->
    (* ^ The context of available induction hypotheses *)
    exp_syn ->
    (* ^ The expression whose type to synthesize *)
    gctx option * tclo
  (* ^ A possibly refined context of induction hypotheses and the synthesized type *)

  val checkKind   : LF.mctx -> kind                -> unit
  val checkTyp    : LF.mctx -> typ                  -> unit
  val wf_mctx     : LF.mctx -> unit

  (** Transforms the given meta-context by marking all meta-variables
      appearing in the pattern as Inductive.

      This function relies on numerous (non-exported; 87 lines total)
      helpers to traverse the syntax tree. I believe that there is an
      opportunity to refactor this and move it to a different
      module. -je
   *)
  val mvars_in_patt : LF.mctx -> pattern -> LF.mctx

  (** Transfers inductivity annotations from a source context to a
      target context related by a meta-substitution.
   *)
  val id_map_ind : LF.mctx -> LF.msub -> LF.mctx -> LF.mctx
end
