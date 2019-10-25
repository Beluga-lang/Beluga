open Syntax

val solve_fvarCnstr : Lfrecon.reconType -> unit
val reset_fvarCnstr : unit -> unit

(** Type of case to reconstruct. Either a plain data object, or an index object.
    In the case of an index object, we store the scrutinee in order to
    correctly implement dependent pattern matching.
 *)
type case_type =
  | IndexObj of Int.Comp.meta_obj
  | DataObj

(** Analyzes the given case scrutinee to decide what kind of case we
    have.
    The case type is used by other elaboration functions to
    generate appropriate substittions.
 *)
val case_type : Int.Comp.exp_syn -> case_type

(** Refines a pattern according to the given case type, computing a
    refinement substitution with which to elaborate the branch body.

    synPatRefine l ct (cD, cD1') pat1 (tau_s, tau1) = (t', t1, cD1'', pat1')
    such that
    cD1'  |- tau1 <= type
    cD1'  |- pat1 : tau1
    cD1'' |- t' : cD
    cD1'' |- t1 : cD, cD1'
    where cD is the meta-context of the scrutinee
          cD1' is the meta-context of the pattern
    (So t1 is actually an extension of t'.)
    And cD1'' is the meta-context in which to elaborate the branch
    body.
 *)
val synPatRefine : Loc.t -> case_type ->
                   Int.LF.mctx * Int.LF.mctx ->
                   Int.Comp.pattern ->
                   Int.Comp.typ * Int.Comp.typ ->
                   Int.LF.msub * Int.LF.msub * Int.LF.mctx * Int.Comp.pattern

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
