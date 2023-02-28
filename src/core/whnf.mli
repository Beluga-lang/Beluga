(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)
open Beluga_syntax
open Syntax.Int.LF
open Syntax.Int


val whnf : nclo -> nclo
val whnfTyp : tclo -> tclo
val norm : nclo -> normal
val normKind : (kind * sub) -> kind
val normTyp : tclo -> typ
val normFt' : front * sub -> front
val normClTyp : cltyp * sub -> cltyp
val normTypRec : trec_clo -> typ_rec
val normSub : sub -> sub
val normSpine : sclo -> spine
val normDCtx : dctx -> dctx
val normMCtx : mctx -> mctx
val reduce : nclo -> spine -> normal
val whnfRedex : nclo * sclo -> nclo

(* conv* : true iff arguments are alpha-convertible *)
val conv : nclo -> nclo -> bool
val convHead : (head * sub) -> (head * sub) -> bool
val convTyp : tclo -> tclo -> bool
val convTypRec : trec_clo -> trec_clo -> bool
val convSchElem : sch_elem -> sch_elem -> bool
val prefixSchElem : sch_elem -> sch_elem -> bool
val convSub : sub -> sub -> bool
val convITerm : iterm -> iterm -> bool
val convMSub : msub -> msub -> bool
val convCtxVar : ctx_var -> ctx_var -> bool
val convDCtx : dctx -> dctx -> bool
val convDCtxHat : dctx_hat -> dctx_hat -> bool

(*************************************)
(* Creating new contextual variables *)
(*************************************)

val newMMVar' : Name.t option -> mctx * ctyp -> Plicity.t -> Inductivity.t -> mm_var
val newMMVar : Name.t option -> mctx * dctx * typ -> Plicity.t -> Inductivity.t -> mm_var
val newMPVar : Name.t option -> mctx * dctx * typ -> Plicity.t -> Inductivity.t -> mm_var
val newMSVar : Name.t option
               -> mctx (* cD *)
                  * svar_class
                  * dctx (* cPsi *)
                  * dctx (* cPhi *)
               -> Plicity.t
               -> Inductivity.t
               -> mm_var
               (* cD ; cPsi |- msvar : cPhi *)

val newMVar : Name.t option -> dctx * typ -> Plicity.t -> Inductivity.t -> cvar
val newCVar : Name.t option -> mctx -> Id.cid_schema option -> Plicity.t -> Inductivity.t -> ctx_var

val raiseType : dctx -> typ -> typ

(*************************************)
(* Other operations *)
(*************************************)

val etaExpandMV : dctx -> tclo -> Name.t -> sub -> Plicity.t -> Inductivity.t -> normal

val etaExpandMMV : Location.t -> mctx -> dctx -> tclo -> Name.t -> sub -> Plicity.t -> Inductivity.t -> normal


exception Fmvar_not_found
exception FreeMVar of head
exception NonInvertible
exception InvalidLFHole of Location.t

val newMTypName : ctyp -> Name.name_guide

val m_id : msub
(* val mshift: msub -> int -> msub
val mshiftTerm: normal -> int -> normal
val mshiftHead: head -> int -> head
val mshiftSpine: spine -> int -> spine
val mshiftTyp : typ -> int -> typ
val mshiftDCtx : dctx -> int -> dctx
*)
val mvar_dot1 : msub -> msub
val pvar_dot1 : msub -> msub
val mvar_dot : msub -> mctx -> msub

(** mcomp t1 t2 = t'
    Eagerly composes the modal substitutions t1 and t2.

    If   cD_2 |- t1 : cD_1
    and  cD_3 |- t2 : cD_2
    then cD_3 |- t' : cD_1
    where t' = mcomp t1 t2

    For example, suppose
    cD |- tau <= type      for some tau
    cD' |- t' : cD
    cD'' |- t'' : cD'

    cnormCTyp (tau, mcomp t' t'')
    =
    cnormCTyp (cnormCTyp (tau, t'), t'')

    That is, applying a composition of substitutions is equivalent to
    applying the composed substitutions from *left-to-right*.

*)
val mcomp : msub -> msub -> msub

(** Flipped version of mcomp which is more useful as a higher-order function.

    If   cD_2 |- t1 : cD_1
    and  cD_3 |- t2 : cD_2
    then cD_3 |- t' : cD_1
    where t' = mcomp' t2 t1
 *)
val mcomp' : msub -> msub -> msub

val m_invert : msub -> msub

(* val invExp : Comp.exp * msub -> int -> Comp.exp
val invTerm : normal * msub -> int -> normal
*)
val mctxLookup : mctx -> int -> Name.t * ctyp
val mctxLookupDep : mctx -> int -> Name.t * ctyp * Plicity.t * Inductivity.t
val mctxMDec : mctx -> int -> Name.t * typ * dctx
val mctxPDec : mctx -> int -> Name.t * typ * dctx
val mctxSDec : mctx -> int -> Name.t * dctx * svar_class * dctx
val mctxCDec : mctx -> int -> Name.t * Id.cid_schema

val mctxMVarPos : mctx -> Name.t -> Id.offset * ctyp

val cnorm : normal * msub -> normal
val cnormHead : head * msub -> head
val cnormHead' : head * msub -> front
val cnormSpine : spine * msub -> spine
val cnormSub : sub * msub -> sub
val cnormTyp : typ * msub -> typ
val cnormTypRec: typ_rec * msub -> typ_rec
val cnormDCtx : dctx * msub -> dctx
val cnormMTyp : ctyp * msub -> ctyp
val cnormClTyp : cltyp * msub -> cltyp
val cnorm_psihat: dctx_hat -> msub -> dctx_hat
val cnormGCtx : Comp.gctx * msub -> Comp.gctx
val cnormIHCtx : Comp.ihctx * msub -> Comp.ihctx

val cnormPattern : Comp.pattern * msub -> Comp.pattern
val cnormPatSpine : Comp.pattern_spine * msub -> Comp.pattern_spine

val cnormMetaObj : Comp.meta_obj * msub -> Comp.meta_obj

val cnormClObj : clobj -> msub -> clobj
val cnormMFt : mfront -> msub -> mfront
val cnormMSub : msub -> msub

val cnormCCDecl : Comp.ctyp_decl * msub -> Comp.ctyp_decl
val cnormCKind : Comp.kind * msub -> Comp.kind
val cnormCTyp : Comp.typ * msub -> Comp.typ
val cnormCDecl : LF.ctyp_decl * msub -> LF.ctyp_decl
val cwhnfCTyp : Comp.typ * msub -> Comp.typ * msub
val cwhnfCtx : Comp.gctx * msub -> Comp.gctx

val cnormExp : Comp.exp * msub -> Comp.exp
val cnormThm : Comp.thm * msub -> Comp.thm

val normGCtx : Comp.gctx -> Comp.gctx
val normIHCtx : Comp.ihctx -> Comp.ihctx
val normCTyp : Comp.typ -> Comp.typ

val convMTyp : ctyp -> ctyp -> bool
val convCTypDecl : ctyp_decl -> ctyp_decl -> bool
val convCTyp : Comp.typ * msub -> Comp.typ * msub -> bool
val convMetaObj: Comp.meta_obj -> Comp.meta_obj -> bool
val convCompCTypDecl : Comp.ctyp_decl -> Comp.ctyp_decl -> bool

(* CLOSEDNESS CHECKING
   Verifies that the given object does not contain any unification
   variables.
 *)

val closed : nclo -> bool
val closedTyp : tclo -> bool
val closedDCtx : dctx -> bool
val closedCTyp : Comp.typ -> bool
val closedGCtx : Comp.gctx -> bool
val closedMetaObj : Comp.meta_obj -> bool
val closedExp : Comp.exp -> bool

val constraints_solved : cnstr list -> bool

(** Convert a meta-context to a list of declarations in which the
  * types have been shifted to make sense in the whole context.
  *
  * This would go in Context, but we need to invoke Whnf to perform
  * the shifting, and Whnf depends on Context.
 *)
val mctx_to_list_shifted : mctx -> ctyp_decl list

(** Eliminates the level of indirection from having a Sigma with just
    one component. *)
val collapse_sigma : typ_rec -> typ

val conv_subgoal_path : Comp.SubgoalPath.t -> Comp.SubgoalPath.t -> bool
val conv_subgoal_path_builder : Comp.SubgoalPath.builder -> Comp.SubgoalPath.builder -> bool

(** Checks strong convertibility between two meta-contexts.
    We say _strong_ because reordering of entries is forbidden.
  *)
val convMCtx : mctx -> mctx -> bool

(** Checks strong convertibility between two computational contexts.
    We say _strong_ because reordering of entries is forbidden.
  *)
val convGCtx : Comp.gctx * msub -> Comp.gctx * msub -> bool

(** lowerTyp cPsi (tA, s) = (cPsi', (tA', s'))
    where
      - cPsi |- s : cPhi
      - cPsi |- tA[s] <= type
      - cPsi' |- tA'[s'] <= type
      - cPsi' is an extension of cPsi formed by shifting all Pi-type
        declarations in tA to cPsi.
 *)
val lowerTyp : dctx -> tclo -> dctx * tclo

(** Converts an MMVar to a contextual object according to its
    contextual type. *)
val mmVarToClObj : Location.t -> mm_var -> cltyp -> clobj

(** Converts an MMVar to a meta object according to its meta type. *)
val mmVarToMFront : Location.t -> mm_var -> Comp.meta_typ -> mfront

val dotMMVar : Location.t -> mctx -> msub -> Name.t * ctyp * Plicity.t * Inductivity.t
               -> Comp.meta_obj * msub

val extend_mctx : mctx -> (LF.ctyp_decl * msub ) -> mctx

val extend_gctx : Comp.gctx -> (Comp.ctyp_decl * msub) -> Comp.gctx
