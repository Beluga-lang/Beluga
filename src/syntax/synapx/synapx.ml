(** Approximate Syntax *)

open Support
open Syncom
open Id

module Int = Synint

(** Approximate LF Syntax *)
module LF = struct
  type 'a ctx = 'a Synint.LF.ctx =       (* Generic context declaration    *)
    | Empty                              (* C ::= Empty                    *)
    | Dec of 'a ctx * 'a                 (*   | C, x:'a                    *)

  type svar_class = Synint.LF.svar_class =
    | Ren
    | Subst

  type kind =
    | Typ
    | PiKind of (typ_decl * Depend.t * Plicity.t) * kind

  and typ_decl =
    | TypDecl of Name.t * typ
    | TypDeclOpt of Name.t

  and cltyp =
    | MTyp of typ
    | PTyp of typ
    | STyp of svar_class * dctx

  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of cid_schema

  and ctyp_decl =
    | Decl of Name.t * ctyp * Plicity.t (* TODO: Annotate with [Depend.t] *)
    | DeclOpt of Name.t (* TODO: Annotate with [Depend.t] *)

  and typ =
    | Atom of Location.t * cid_typ * spine
    | PiTyp of (typ_decl * Depend.t * Plicity.t) * typ
    | Sigma of typ_rec

  and typ_rec =
    | SigmaLast of Name.t option * typ
    | SigmaElem of Name.t * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and normal =
    | Lam of Location.t * Name.t * normal
    | Root of Location.t * head * spine
    | LFHole of Location.t * string option
    | Tuple of Location.t * tuple
    | Ann of Location.t * normal * typ

  and head =
    | BVar of offset
    | Const of cid_term
    | MVar of cvar * sub option
    | Proj of head * proj
    | Hole
    | PVar of cvar * sub option
    | FVar of Name.t
    | FMVar of Name.t * sub option
    | FPVar of Name.t * sub option

  and proj =
    | ByPos of int
    | ByName of Name.t

  and spine =
    | Nil
    | App of normal * spine

  and sub =
    | EmptySub
    | Id
    | Dot of front * sub
    | SVar of cvar * sub option
    | FSVar of Name.t * sub option

  and front =
    | Head of head
    | Obj of normal

  and cvar =
    | Offset of offset
    | MInst of Int.LF.clobj * Int.LF.ctyp

  and dctx =
    | Null
    | CtxVar of ctx_var
    | DDec of dctx * typ_decl
    | CtxHole

  and ctx_var =
    | CtxName of Name.t
    | CtxOffset of offset

  and mctx = ctyp_decl ctx

  and sch_elem =
    | SchElem of typ_decl ctx * typ_rec

  and schema =
    | Schema of sch_elem list

  and psi_hat = Int.LF.ctx_var option * offset

  and mfront =
    | ClObj of dctx * sub
        (** Either a contextual term, plain substitution or renaming
            substitution. *)
    | CObj of dctx  (** Context meta-object. *)
end


(** Approximate Computation Syntax *)
module Comp = struct
  type unbox_modifier =
    [ `Strengthened
    ]

  type case_pragma = Synint.Comp.case_pragma =
    | PragmaCase
    | PragmaNotCase

  type context_case = Synint.Comp.context_case =
    | EmptyContext of Location.t
    | ExtendedBy of Location.t * int (* specifies a schema element *)

  type case_label = Synint.Comp.case_label =
    | Lf_constant of Location.t * Name.t * Id.cid_term
    | Comp_constant of Location.t * Name.t * Id.cid_comp_const
    | BVarCase of Location.t
    | ContextCase of context_case
    | PVarCase
      of Location.t
         * int (* schema element number (1-based) *)
         * int option (* the number of the projection, if any (1-based) *)

  type 'a generic_order = 'a Synint.Comp.generic_order =
    | Arg of 'a                                    (* O ::= x                    *)
    | Lex of 'a generic_order list                 (*     | {O1 .. On}           *)
    | Simul of 'a generic_order list               (*     | [O1 .. On]           *)
  (* Note: Simul is currently unused. It doesn't even have a parser. -je *)

  (** Type specified in an interactive use of `suffices` *)
  type 'a generic_suffices_typ =
    [ `exact of 'a (* user specified an exact type annotation *)
    | `infer of Location.t (* user specified `_` and expects the type to be known *)
    ]

  let map_suffices_typ (f : 'a -> 'b) : 'a generic_suffices_typ -> 'b generic_suffices_typ =
    function
    | `exact x -> `exact (f x)
    | `infer loc -> `infer loc

  let rec map_order (f : 'a -> 'b) : 'a generic_order -> 'b generic_order =
    function
    | Arg x -> Arg (f x)
    | Lex xs -> Lex (List.map (map_order f) xs)
    | Simul xs -> Simul (List.map (map_order f) xs)

  type kind =
    | Ctype of Location.t
    | PiKind of Location.t * LF.ctyp_decl * kind

  type meta_typ = Location.t * LF.ctyp

  type meta_obj = Location.t * LF.mfront

  type meta_spine =
    | MetaNil
    | MetaApp of meta_obj * meta_spine

  type typ =
    | TypBase of Location.t * cid_comp_typ * meta_spine
    | TypCobase of Location.t * cid_comp_cotyp * meta_spine
    | TypDef of Location.t * cid_comp_typdef * meta_spine
    | TypBox of Location.t * meta_typ
    | TypArr of Location.t * typ * typ
    | TypCross of Location.t * typ List2.t
    | TypPiBox of Location.t * LF.ctyp_decl * typ
    | TypInd of typ

  (** Computation-level terms *)
  and exp =                                                       (* e ::=                              *)
    | Fn         of Location.t * Name.t * exp                     (*   | fn x => e                      *)
    | Fun        of Location.t * fun_branches                     (*   | fun   fbranches                *)
    | MLam       of Location.t * Name.t * exp                     (*   | mlam f => e                    *)
    | Tuple      of Location.t * exp List2.t                      (*   | (e1, e2, ..., en)              *)
    | LetTuple   of Location.t * exp * (Name.t List2.t * exp)     (*   | let (x1, x2, ..., xn) = i in e *)
    | Let        of Location.t * exp * (Name.t * exp)             (*   | let x = i in e                 *)
    | Box        of Location.t * meta_obj                         (*   | box (Psi hat. M)               *)
    | Case       of Location.t * case_pragma * exp * branch list  (*   | case i of bs                   *)
    | Impossible of Location.t * exp                              (*   | impossible i                   *)
    | Hole       of Location.t * string option                    (*   | ?name                          *)
    | BoxHole    of Location.t                                    (*   | _                              *)
    | Var        of Location.t * offset                           (*   | x                              *)
    | DataConst  of Location.t * cid_comp_const                   (*   | c                              *)
    | Obs        of Location.t * exp * cid_comp_dest              (*   | e.d                            *)
    | Const      of Location.t * cid_prog                         (*   | c                              *)
    | Apply      of Location.t * exp * exp                        (*   | i e                            *)
    | Ann        of Location.t * exp * typ                        (*   | e : tau                        *)

  and pattern =
    | PatMetaObj of Location.t * meta_obj
    | PatConst   of Location.t * cid_comp_const * pattern_spine
    | PatFVar    of Location.t * Name.t (* used only temporarily during indexing *)
    | PatVar     of Location.t * Name.t * offset (* This offset is with respect to the pattern-matching branch expression *)
    | PatTuple   of Location.t * pattern List2.t
    | PatAnn     of Location.t * pattern * typ

  and pattern_spine =
    | PatNil of Location.t
    | PatApp of Location.t * pattern * pattern_spine
    | PatObs of Location.t * cid_comp_dest * pattern_spine

  and branch =
    | Branch of Location.t * LF.ctyp_decl LF.ctx * pattern * exp

  and fun_branches =
    | NilFBranch  of Location.t
    | ConsFBranch of Location.t * (pattern_spine * exp) * fun_branches

  type ctyp_decl =
    | CTypDecl of Name.t * typ

  type gctx = ctyp_decl LF.ctx

  type hypotheses =
    { cD : LF.mctx
    ; cG : gctx
    }

  type proof =
    | Incomplete of Location.t * string option
    | Command of Location.t * command * proof
    | Directive of Location.t * directive

  and command =
    | By of Location.t * exp * Name.t
    | Unbox of Location.t * exp * Name.t * unbox_modifier option

  and directive =
    | Intros   of Location.t * hypothetical
    | Solve    of Location.t * exp
    | Split    of Location.t * exp * split_branch list
    | Suffices of Location.t * exp * suffices_arg list

  and suffices_arg = Location.t * typ * proof

  and split_branch =
    { case_label : case_label
    (* we don't index the case label yet since we don't know whether
       it should be comp constructors or LF constructors,
       so this is deferred till type reconstruction when we know the
       scrutinee's type.
     *)
    ; branch_body : hypothetical
    ; split_branch_loc : Location.t
    }

  and hypothetical =
    { hypotheses : hypotheses
    ; proof : proof
    ; hypothetical_loc : Location.t
    }

  type thm =
    | Program of exp
    | Proof of proof

  let loc_of_exp = function
   | Fn (loc, _, _)
   | Fun (loc, _)
   | MLam (loc, _, _)
   | Tuple (loc, _)
   | LetTuple (loc, _, _)
   | Let (loc, _, _)
   | Box (loc, _)
   | Case (loc, _, _, _)
   | Impossible (loc, _)
   | Hole (loc, _)
   | BoxHole loc
   | Var (loc, _)
   | DataConst (loc, _)
   | Obs (loc, _, _)
   | Const (loc, _)
   | Apply (loc, _, _)
   | Ann (loc, _, _) -> loc
end
