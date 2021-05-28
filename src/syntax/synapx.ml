(** Approximate Syntax *)

(** Approximate LF Syntax *)
open Support
open Id

module Int = Synint

module LF = struct
  include Syncom.LF

  type kind =
    | Typ
    | PiKind of (typ_decl * depend) * kind

  and typ_decl =
    | TypDecl of name * typ
    | TypDeclOpt of name

  and cltyp =
    | MTyp of typ
    | PTyp of typ
    | STyp of svar_class * dctx

  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of cid_schema

  and ctyp_decl =
    | Decl of name * ctyp * depend
    | DeclOpt of name

  and typ =
    | Atom of Location.t * cid_typ * spine
    | PiTyp of (typ_decl * depend) * typ
    | Sigma of typ_rec

  and typ_rec =
    | SigmaLast of name option * typ
    | SigmaElem of name * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and normal =
    | Lam of Location.t * name * normal
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
    | FVar of name
    | FMVar of name * sub option
    | FPVar of name * sub option

  and proj =
    | ByPos of int
    | ByName of name

  and spine =
    | Nil
    | App of normal * spine

  and sub =
    | EmptySub
    | Id
    | Dot of front * sub
    | SVar of cvar * sub option
    | FSVar of name * sub option

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
    | CtxName of name
    | CtxOffset of offset

  and mctx = ctyp_decl ctx

  and sch_elem =
    | SchElem of typ_decl ctx * typ_rec

  and schema =
    | Schema of sch_elem list

  and psi_hat = Int.LF.ctx_var option * offset
end


(** Approximate Computation Syntax *)
module Comp = struct
  include Syncom.Comp

  type kind =
    | Ctype of Location.t
    | PiKind of Location.t * LF.ctyp_decl * kind

  type meta_typ = Location.t * LF.ctyp

  type mfront =
    | ClObj of LF.dctx * LF.sub
    | CObj of LF.dctx

  type meta_obj = Location.t * mfront

  type meta_spine =
    | MetaNil
    | MetaApp of meta_obj * meta_spine

  type typ =
    | TypBase of Location.t * cid_comp_typ * meta_spine
    | TypCobase of Location.t * cid_comp_cotyp * meta_spine
    | TypDef of Location.t * cid_comp_typ * meta_spine
    | TypBox of Location.t * meta_typ
    | TypArr of Location.t * typ * typ
    | TypCross of Location.t * typ * typ
    | TypPiBox of Location.t * LF.ctyp_decl * typ
    | TypInd of typ

  and exp_chk =
     | Syn of Location.t * exp_syn
     | Fn of Location.t * name * exp_chk                             (* fn x => e           *)
     | Fun of Location.t * fun_branches                              (* fun   fbranches     *)
     | MLam of Location.t * name * exp_chk                           (* mlam f => e         *)
     | Pair of Location.t * exp_chk * exp_chk                        (* (e1 , e2)           *)
     | LetPair of Location.t * exp_syn * (name * name * exp_chk)     (* let (x,y) = i in e  *)
     | Let of Location.t * exp_syn * (name * exp_chk)                (* let x = i in e      *)
     | Box of Location.t * meta_obj                                  (* box (Psi hat. M)    *)
     | Case of Location.t * case_pragma * exp_syn * branch list      (* case i of bs *)
     | Impossible of Location.t * exp_syn                            (* impossible i *)
     | Hole of Location.t * string option                            (* ?name *)
     | BoxHole of Location.t                                         (* _ *)

  and exp_syn =
    | Var of Location.t * offset                                    (* x              *)
     | FVar of name                                                 (* x              *)
     | DataConst of Location.t * cid_comp_const                     (* c              *)
     | Obs of Location.t * exp_chk * cid_comp_dest                  (* e.d            *)
     | Const of Location.t * cid_prog                               (* c              *)
     | Apply of Location.t * exp_syn * exp_chk                      (* i e            *)
     | BoxVal of Location.t * meta_obj
     | PairVal of Location.t * exp_syn * exp_syn
     | Ann of exp_chk * typ                                         (* e : tau        *)

  and pattern =
    | PatMetaObj of Location.t * meta_obj
    | PatConst of Location.t * cid_comp_const * pattern_spine
    | PatFVar of Location.t * name (* used only temporarily during indexing *)
    | PatVar of Location.t * name * offset
    | PatPair of Location.t * pattern * pattern
    | PatAnn of Location.t * pattern * typ

  and pattern_spine =
    | PatNil of Location.t
    | PatApp of Location.t * pattern * pattern_spine
    | PatObs of Location.t * cid_comp_dest * pattern_spine

  and branch =
    | Branch of Location.t * LF.ctyp_decl LF.ctx * pattern * exp_chk

  and fun_branches =
    | NilFBranch of Location.t
    | ConsFBranch of Location.t * (pattern_spine * exp_chk) * fun_branches


  (* the definition of branch_pattern will be removed and replaced by the more general notion of patterns;
     it remains currently so we can still use the old parser without modifications -bp *)
  and branch_pattern =
     | NormalPattern of LF.normal * exp_chk
     | EmptyPattern

  type ctyp_decl =
    | CTypDecl of name * typ

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
    | By of Location.t * exp_syn * name
    | Unbox of Location.t * exp_syn * name * unbox_modifier option

  and directive =
    | Intros of Location.t * hypothetical
    | Solve of Location.t * exp_chk
    | Split of Location.t * exp_syn * split_branch list
    | Suffices of Location.t * exp_syn * suffices_arg list

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
    | Program of exp_chk
    | Proof of proof
end
