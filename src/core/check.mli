(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

module LF : sig

  open Syntax
  open Int.LF

  type error =
    | CtxVarMisCheck of mctx * dctx * tclo * Id.name * schema
    | CtxVarMismatch of mctx * ctx_var * Id.name * schema
    | CtxVarDiffer of mctx * ctx_var * ctx_var
    | CheckError of mctx * dctx * nclo * tclo
    | TupleArity of mctx * dctx * nclo * trec_clo
    | SigmaMismatch of mctx * dctx * trec_clo * trec_clo
    | KindMismatch of mctx * dctx * sclo * (kind * sub)
    | TypMismatch of mctx * dctx * nclo * tclo * tclo
    | IllTypedSub of mctx * dctx * sub * dctx * normal option
    | SpineIllTyped of int * int
    | LeftoverFV of Id.name
    | ParamVarInst of mctx * dctx * tclo
    | CtxHatMismatch
      of mctx
         * dctx (* expected *)
         * dctx_hat (* found *)
         * (Loc.t * mfront)
    | IllTypedMetaObj of mctx * clobj * dctx * cltyp
    | TermWhenVar of mctx * dctx * normal
    | SubWhenRen of mctx * dctx * sub
    | MissingType of string

  exception Error of Loc.t * error

  val throw : Loc.t -> error -> 'a

  val check : mctx -> dctx -> nclo -> tclo -> unit

  val syn : mctx -> dctx -> nclo -> tclo
  val checkTyp : mctx -> dctx -> tclo -> unit
  val checkKind : mctx -> dctx -> kind -> unit
  val checkDCtx : mctx -> dctx -> unit

  val checkSchemaWf : schema -> unit
  val checkSchema : Loc.t -> mctx -> dctx -> Id.name -> schema -> unit
  val subsumes : mctx -> ctx_var -> ctx_var -> bool

  (** Checks that a type exists within a given schema.
      checkTypeAgainstSchema loc cD cPsi tA name es = (tR, s)
      if cD; cPsi |- tA <== type
      and tA is an instance of one of the schema elements es.
      If not, an error will the raised with the given location.
      The input name will be a part of the error message, and should
      be the declared name of the schema.
   *)
  val checkTypeAgainstSchema: Syntax.Loc.t -> mctx -> dctx -> typ -> Id.name -> sch_elem list
                              -> typ_rec * sub
  val instanceOfSchElem : mctx -> dctx -> tclo -> sch_elem -> (typ_rec * sub)
  val instanceOfSchElemProj : mctx -> dctx -> tclo -> (head * int) -> sch_elem -> (typ_rec * sub)

  val checkMSub : Loc.t -> mctx -> msub -> mctx -> unit

end

module Comp : sig
  open Syntax.Int.Comp
  open Syntax.Int

  type typeVariant =
    | VariantCross
    | VariantArrow
    | VariantCtxPi
    | VariantPiBox
    | VariantBox

  type mismatch_kind =
    [ `fn
    | `mlam
    | `box
    | `ctxfun
    | `pair
    ]

  type error =
    | IllegalParamTyp of LF.mctx * LF.dctx * LF.typ
    | MismatchChk of LF.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn of LF.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped of LF.mctx * gctx * pattern * tclo * tclo
    | BasicMismatch of mismatch_kind * LF.mctx * gctx * tclo
    | SBoxMismatch of LF.mctx * gctx * LF.dctx * LF.dctx
    | SynMismatch of LF.mctx * tclo (* expected *) * tclo (* inferred *)
    | TypMismatch of LF.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name option * string
    | InvalidRecCall
    | MissingTotal of Id.cid_prog
    | NotImpossible of LF.mctx * gctx * typ * exp_syn
    | InvalidHypotheses
      of hypotheses (* expected *)
         * hypotheses (* actual *)
    | SufficesDecompositionFailed of LF.mctx * typ
    | SufficesLengthsMismatch
      of LF.mctx
         * typ (* type that was decomposed *)
         * int (* number of simple arguments in that type *)
         * int (* number of given types *)
    | SufficesBadAnnotation
      of LF.mctx
         * typ (* suffices scrutinee's type *)
         * int (* index of the scrutinee premise that didn't unify *)
         * typ (* type annotation given by the user (valid in cD) *)
    | SufficesBadGoal
      of LF.mctx
         * typ (* scrutinee type *)
         * typ (* goal type *)
    | SufficesPremiseNotClosed
      of LF.mctx
         * int (* premise index *)
         * suffices_typ (* given type annotation *)

  exception Error of Loc.t * error

  (** Raises an error from this module. *)
  val throw : Loc.t -> error -> 'a

  (** Appends two sets of hypotheses.
      Appropriately MShifts the left contexts and applies an
      appropriate totality shift.
   *)
  val append_hypotheses : Comp.hypotheses -> Comp.hypotheses -> Comp.hypotheses

  (** Transforms the given contextual type according the an unboxing
      modifier.
      The returned substitution witnesses the transformation of the type.
      It should be applied to the metavariable of the computed type in
      order for it to make sense in the original context.
      For example, suppose apply_unbox_modifier cD `strengthen cU = cU', s
      If we want X : cU' to make sense in its original LF context,
      then it suffices to apply X[s].
      This substitution is used by the translation from proofs into
      programs.
   *)
  val apply_unbox_modifier : LF.mctx -> unbox_modifier -> LF.ctyp -> LF.ctyp * LF.sub

  (** Variant of apply_unbox_modifier that is the identity when no modifier is specified. *)
  val apply_unbox_modifier_opt : LF.mctx -> unbox_modifier option -> LF.ctyp -> LF.ctyp * LF.sub

  (** Verifies that the pairs of contexts are convertible.
      It is a user error InvalidHypotheses if they are not.
      If the contexts are convertible, then they are merged, using
      plicity and type information from the context on the left, but
      the entry name from the context on the right.
   *)
  val validate_contexts : Loc.t -> LF.mctx * LF.mctx -> gctx * gctx -> LF.mctx * gctx

  (** Checks a theorem in the given contexts against the given type.
      The given list of total declarations is used for totality checking.
      The cid_comp_const parameter is used for registering Harpoon
      subgoals. For ordinary Beluga programs or for complete Harpoon
      proofs, this argument can be None.
   *)
  val thm : Id.cid_prog option (* cid of the theorem being checked, if any *)
            -> LF.mctx
            -> gctx
            -> total_dec list
            -> ?cIH: ihctx
            -> thm
            -> tclo
            -> unit

  val check : Id.cid_prog option (* cid of the theorem being checked, if any *)
              -> LF.mctx
              (* ^ The meta context *)
              -> gctx
              (* ^ The computation context *)
              -> total_dec list
              (* ^ the group of mutual recursive functions the expression is being checked in *)
              -> ?cIH: ihctx
              (* ^ the context of available induction hypotheses *)
              -> exp_chk
              (* ^ The expression to check *)
              -> tclo
              (* ^ The type it should have *)
              -> unit

  val syn : Id.cid_prog option (* cid of the theorem being checked, if any *)
            -> LF.mctx
            (* ^ The meta context *)
            -> gctx
            (* ^ The computation context *)
            -> total_dec list
            (* ^ The group of mutual recursive functions the expression is being checked in *)
            -> ?cIH: ihctx
            (* ^ The context of available induction hypotheses *)
            -> exp_syn
            (* ^ The expression whose type to synthesize *)
            -> ihctx option * tclo
            (* ^ A possibly refined context of induction hypotheses and the synthesized type *)

  val checkKind : LF.mctx -> kind -> unit
  val checkTyp : LF.mctx -> typ -> unit
  val wf_mctx : LF.mctx -> unit

  (** Transforms the given meta-context by marking all meta-variables
      appearing in the pattern as Inductive.

      This function relies on numerous (non-exported; 87 lines total)
      helpers to traverse the syntax tree. I believe that there is an
      opportunity to refactor this and move it to a different
      module. -je
   *)
  val mvars_in_patt : LF.mctx -> pattern -> LF.mctx

  (** Analyzes a contextual object to decide whether it's a
      (contextual) variable and rewrites its type from MTyp to PTyp if
      necessary. This is crucial for coverage checking of a case analysis
      on a parameter variable.
      Also returns the index of the variable (so we can later decide
      if it's a variable we're doing induction on) as well what
      projection, if any, is applied to the parameter variable.
   *)
  val fixParamTyp : LF.mfront -> Comp.meta_typ -> int option * Comp.meta_typ * int option

  (** Transfers inductivity annotations from a source context to a
      target context related by a meta-substitution.

      id_map_ind cD' t cD = cD'*
      where cD' |- t : cD
   *)
  val id_map_ind : LF.mctx -> LF.msub -> LF.mctx -> LF.mctx

  (** unroll cD cG cIH tau = (cD', cG', cIH', tau', t)
      where cD |- cG <= ctx
      and   cD |- tau <= type
      s.t. cD' extends cD
      and  cG' extends cG
      and tau' is a subterm of tau
      and tau' is not an arrow nor a PiBox type
      and cD' |- t : cD is a weakening meta-substitution.
      and cD' |- cIH' ihctx
      and cIH' is appropriately shifted
   *)
  val unroll : LF.mctx -> gctx -> ihctx -> typ -> LF.mctx * gctx * ihctx * typ * LF.msub

  (** Requires that the given type be a box-type.
      require_syn_typbox cD cG loc i (tau, t) = (cU, t) if tau = [cU];
      else, raises a synthesis mismatch error for the expression i
      saying that the type of i is expected to be a box-type.
   *)
  val require_syn_typbox : LF.mctx -> gctx -> Loc.t -> exp_syn -> tclo -> meta_typ * LF.msub


  (** Processes all leading PiBoxes to replace them with unification
      variables in the following type, and returns a further
      decomposition of the type remaining after all these PiBoxes, which
      must consist only of simple function types (or a base type).

      Given cD |- tau <= type
      and tau = Pi X_1:U_1. ... Pi X_n:U_n. tau'
      and tau' = tau_1 -> tau_2 -> ... -> tau_k
      (so cD, X_1:U_1, ..., X_n:U_n |- tau' <= type)
      `decompose_function_type cD tau` calculates an msub
      t such that
      cD |- t : cD, X_1:U_1, ..., X_n:U_n
      that replaces each X_i with a fresh unification variable ?X_i.
      The msub t is applied to tau' and tau' is further decomposed into
      a list l = [[t]tau_1; [t]tau_2; ...; [t]tau_(k-1)].
      This list is returned together with the type [t]tau_k.
      If the decomposition fails due to an interleaving of PiBox-types
      and arrow-types, None is returned.
   *)
  val decompose_function_type : LF.mctx -> typ -> (typ list * typ) option

  (** Checks that the given type annotations are compatible with a
      given function type.

      unify_suffices cD tau_i tau_anns tau_g
      requires
      1. cD |- tau_i <= type
      2. for each stau in tau_anns,
         if stau = `exact tau, then cD |- tau <= type (for each type in the list)
      3. cD |- tau_g <= type
      It decomposes the function type tau_i (see decompose_function_type)
      and appropriately unifies the decomposition with the given type
      annotations so as to pin down all instantiations of universally
      quantified variables.
      Some type annotations may be omitted. The interpretation of an
      omitted annotation is that that annotation is not necessary (the
      type of that argument is already determined by unification of
      the goal, or other annotations).

      Returns the list of elaborated premise types, which are
      guaranteed to be closed (no MMVars).

      The provided location is used when raising errors.
   *)
  val unify_suffices : Loc.t -> LF.mctx
                       -> typ (* scrutinee type; to be decomposed *)
                       -> suffices_typ list (* type annotations *)
                       -> typ (* goal type; to match against
                                 decomposed conclusion *)
                       -> typ list (* list of determined premise types *)

  (** Generates a meta-application spine consisting of unification
      variables to eliminate leading PiBox types.
      Returns the number of generated unification variables as well as
      the type (together with a delayed meta-substitution) of the
      produced expression.
   *)
  val genMApp : Loc.t -> (LF.ctyp_decl -> bool) -> LF.mctx -> exp_syn * tclo -> int * (exp_syn * tclo)
end
