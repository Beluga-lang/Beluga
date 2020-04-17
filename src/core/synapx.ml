(** Approximate Syntax *)

(** Approximate LF Syntax *)
open Id

module Loc = Location
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
    | Atom of Loc.t * cid_typ * spine
    | PiTyp of (typ_decl * depend) * typ
    | Sigma of typ_rec

  and typ_rec =
    | SigmaLast of name option * typ
    | SigmaElem of name * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and normal =
    | Lam of Loc.t * name * normal
    | Root of Loc.t * head * spine
    | LFHole of Loc.t * string option
    | Tuple of Loc.t * tuple
    | Ann of Loc.t * normal * typ

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
    | Ctype of Loc.t
    | PiKind of Loc.t * LF.ctyp_decl * kind

  type meta_typ = Loc.t * LF.ctyp

  type mfront =
    | ClObj of LF.dctx * LF.sub
    | CObj of LF.dctx

  type meta_obj = Loc.t * mfront

  type meta_spine =
    | MetaNil
    | MetaApp of meta_obj * meta_spine

  type typ =
    | TypBase of Loc.t * cid_comp_typ * meta_spine
    | TypCobase of Loc.t * cid_comp_cotyp * meta_spine
    | TypDef of Loc.t * cid_comp_typ * meta_spine
    | TypBox of Loc.t * meta_typ
    | TypArr of Loc.t * typ * typ
    | TypCross of Loc.t * typ * typ
    | TypPiBox of Loc.t * LF.ctyp_decl * typ
    | TypInd of typ

  and exp_chk =
     | Syn of Loc.t * exp_syn
     | Fn of Loc.t * name * exp_chk                             (* fn x => e           *)
     | Fun of Loc.t * fun_branches                              (* fun   fbranches     *)
     | MLam of Loc.t * name * exp_chk                           (* mlam f => e         *)
     | Pair of Loc.t * exp_chk * exp_chk                        (* (e1 , e2)           *)
     | LetPair of Loc.t * exp_syn * (name * name * exp_chk)     (* let (x,y) = i in e  *)
     | Let of Loc.t * exp_syn * (name * exp_chk)                (* let x = i in e      *)
     | Box of Loc.t * meta_obj                                  (* box (Psi hat. M)    *)
     | Case of Loc.t * case_pragma * exp_syn * branch list      (* case i of bs *)
     | Impossible of Loc.t * exp_syn                            (* impossible i *)
     | Hole of Loc.t * string option                            (* ?name *)
     | BoxHole of Loc.t                                         (* _ *)

  and exp_syn =
     | Var of Loc.t * offset                                        (* x              *)
     | FVar of name                                                 (* x              *)
     | DataConst of Loc.t * cid_comp_const                          (* c              *)
     | Obs of Loc.t * exp_chk * cid_comp_dest                       (* e.d            *)
     | Const of Loc.t * cid_prog                                    (* c              *)
     | Apply of Loc.t * exp_syn * exp_chk                           (* i e            *)
     | BoxVal of Loc.t * meta_obj
     | PairVal of Loc.t * exp_syn * exp_syn
     | Ann of exp_chk * typ                                         (* e : tau        *)

  and pattern =
    | PatMetaObj of Loc.t * meta_obj
    | PatConst of Loc.t * cid_comp_const * pattern_spine
    | PatFVar of Loc.t * name (* used only temporarily during indexing *)
    | PatVar of Loc.t * name * offset
    | PatPair of Loc.t * pattern * pattern
    | PatAnn of Loc.t * pattern * typ

  and pattern_spine =
    | PatNil of Loc.t
    | PatApp of Loc.t * pattern * pattern_spine
    | PatObs of Loc.t * cid_comp_dest * pattern_spine

  and branch =
    | Branch of Loc.t * LF.ctyp_decl LF.ctx * pattern * exp_chk

  and fun_branches =
    | NilFBranch of Loc.t
    | ConsFBranch of Loc.t * (pattern_spine * exp_chk) * fun_branches


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
    | Incomplete of Loc.t * string option
    | Command of Loc.t * command * proof
    | Directive of Loc.t * directive

  and command =
    | By of Loc.t * exp_syn * name
    | Unbox of Loc.t * exp_syn * name * unbox_modifier option

  and directive =
    | Intros of Loc.t * hypothetical
    | Solve of Loc.t * exp_chk
    | Split of Loc.t * exp_syn * split_branch list
    | Suffices of Loc.t * exp_syn * suffices_arg list

  and suffices_arg = Loc.t * typ * proof

  and split_branch =
    { case_label : case_label
    (* we don't index the case label yet since we don't know whether
       it should be comp constructors or LF constructors,
       so this is deferred till type reconstruction when we know the
       scrutinee's type.
     *)
    ; branch_body : hypothetical
    ; split_branch_loc : Loc.t
    }

  and hypothetical =
    { hypotheses : hypotheses
    ; proof : proof
    ; hypothetical_loc : Loc.t
    }

  type thm =
    | Program of exp_chk
    | Proof of proof
end
