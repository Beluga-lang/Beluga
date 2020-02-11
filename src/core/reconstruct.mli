open Syntax

val solve_fvarCnstr : Lfrecon.reconType -> unit
val reset_fvarCnstr : unit -> unit

(** Type of case to reconstruct. Either a plain data object, or an index object.
    In the case of an index object, we store the scrutinee in order to
    correctly implement dependent pattern matching.
 *)
type case_type

(** Analyzes the given case scrutinee to decide what kind of case we
    have.
    The case type is used by other elaboration functions to
    generate appropriate substitutions.
    (Specifically, see synPatRefine, which is the main consumer of
    case_type.)

    The given pattern is passed lazily as it is only needed when the
    synthesizable expression happens to be a box. (This is related to
    the implementation of dependent pattern matching.)
    If you know that the synthesizable expression is definitely not a
    box, then you can pass
    lazy (Error.violation "appropriate message")
    as the pattern.
 *)
val case_type : Int.Comp.pattern Lazy.t -> Int.Comp.exp_syn -> case_type

(** Transforms a case_type if it was actually an index object. *)
val map_case_type : (Int.Comp.pattern * Int.Comp.meta_obj ->
                     Int.Comp.pattern * Int.Comp.meta_obj) ->
                    case_type -> case_type

(** Constructs the refinement substitution for a case analysis.
    If
      * cD; cG |- tau_s <= type
      * cD'; cG' |- tau_p <= type
      * cD' |- t : cD
      * if caseT = IndexObj C then
        - tau_s = [U]
        - cD; cG |- C <= U
    then
      synPatRefine' loc caseT (cD, cD') t (tau_s, tau_p)
              =
      t', t1', cD''
    such that
      * cD'' |- t' : cD
      * cD'' |- t1' : cD'

    Remark:
      * cD'' is the meta-context in which the branch of the case
        should be elaborated.
      * t' is just t1' composed with t.
 *)
val synPatRefine : Loc.t -> case_type ->
                   Int.LF.mctx * Int.LF.mctx ->
                   Int.LF.msub ->
                   Int.Comp.typ * Int.Comp.typ ->
                   Int.LF.msub * Int.LF.msub * Int.LF.mctx

val kind : Apx.LF.kind -> Int.LF.kind
val typ : Lfrecon.reconType -> Apx.LF.typ -> Int.LF.typ
val schema : Apx.LF.schema -> Int.LF.schema
val mctx   : Apx.LF.mctx   -> Int.LF.mctx
val compkind : Apx.Comp.kind -> Int.Comp.kind
val comptyp : Apx.Comp.typ -> Int.Comp.typ
val comptyp_cD : Int.LF.mctx -> Apx.Comp.typ -> Int.Comp.typ
val comptypdef : Syntax.Loc.t ->
                 Id.name -> (Apx.Comp.typ * Apx.Comp.kind) ->
                 (Int.LF.mctx * Int.Comp.typ) * Id.offset * Int.Comp.kind
val elExp  : Int.LF.mctx ->
             Int.Comp.gctx ->
             Apx.Comp.exp_chk ->
             Int.Comp.typ * Int.LF.msub ->
             Int.Comp.exp_chk

val elExp' : Int.LF.mctx ->
             Int.Comp.gctx ->
             Apx.Comp.exp_syn ->
             Int.Comp.exp_syn * Int.Comp.tclo

val exp  : Int.Comp.gctx -> Apx.Comp.exp_chk -> Int.Comp.typ * Int.LF.msub -> Int.Comp.exp_chk
val exp' : Int.Comp.gctx -> Apx.Comp.exp_syn -> Int.Comp.exp_syn * Int.Comp.tclo

val thm : Int.Comp.gctx -> Apx.Comp.thm -> Int.Comp.typ * Int.LF.msub -> Int.Comp.thm

val numeric_order : Int.Comp.typ -> Ext.Comp.numeric_order -> Int.Comp.order
