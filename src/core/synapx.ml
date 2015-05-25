(** Approximate Syntax *)

(** Approximate LF Syntax *)
open Id
open Pragma

module Loc = Camlp4.PreCast.Loc
module Int = Synint

module LF = struct

  type depend =
    | No
    | Maybe
    | Inductive

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

  and svar_class = 
    | Ren
    | Subst

  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of cid_schema

  and ctyp_decl =
    | Decl of name * ctyp * depend
    | DeclOpt of name

  and typ =
    | Atom  of Loc.t * cid_typ * spine
    | PiTyp of (typ_decl * depend) * typ
    | Sigma of typ_rec

  and typ_rec =
    | SigmaLast of name option * typ
    | SigmaElem of name * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and normal =
    | Lam  of Loc.t * name * normal
    | Root of Loc.t * head * spine
    | LFHole of Loc.t
    | Tuple of Loc.t * tuple
    | Ann of Loc.t * normal * typ

  and head =
    | BVar  of offset
    | Const of cid_term
    | MVar  of cvar * sub
    | Proj  of head * proj
    | Hole
    | PVar  of cvar * sub
    | FVar  of name
    | FMVar of name   * sub
    | FPVar of name   * sub

  and proj = 
    | ByPos of int
    | ByName of name

  and spine =
    | Nil
    | App of normal * spine

  and sub =
    | EmptySub
    | Id    
    | RealId
    | Dot   of front * sub
    | SVar  of cvar * sub
    | FSVar of name * sub

  and front =
    | Head of head
    | Obj  of normal

  and cvar =
    | Offset of offset
    | MInst  of Int.LF.normal * Int.LF.typ * Int.LF.dctx
    | PInst  of Int.LF.head * Int.LF.typ * Int.LF.dctx
    | SInst  of Int.LF.sub * Int.LF.dctx * Int.LF.dctx

  and dctx =
    | Null
    | CtxVar   of ctx_var
    | DDec     of dctx * typ_decl
    | CtxHole

  and ctx_var =
    | CtxName   of name
    | CtxOffset of offset

  and 'a ctx =
    | Empty
    | Dec of 'a ctx * 'a

  and mctx = ctyp_decl ctx

  and sch_elem =
    | SchElem of typ_decl ctx * typ_rec

  and schema =
    | Schema of sch_elem list

 and psi_hat = (Int.LF.ctx_var) option * offset


end


(** Approximate Computation Syntax *)
module Comp = struct

 type  kind =
   | Ctype of Loc.t
   | PiKind  of Loc.t * LF.ctyp_decl * kind

 type cltyp =
   | PTyp of LF.typ
   | MTyp of LF.typ
   | STyp of LF.dctx

 type meta_typ =
   | MetaSchema of Loc.t * name
   | ClTyp of Loc.t * cltyp * LF.dctx 

 type mfront = 
   | MObj of LF.normal
   | SObj of LF.sub

 type hat_or_dctx =
   | Hat of LF.psi_hat
   | DCtx of LF.dctx

 type meta_obj =
   | MetaCtx of Loc.t * LF.dctx
   | MetaObj of Loc.t * hat_or_dctx * mfront

 type meta_spine =
   | MetaNil
   | MetaApp of meta_obj * meta_spine

  type typ =
   | TypBase of Loc.t * cid_comp_typ * meta_spine
   | TypCobase of Loc.t * cid_comp_cotyp * meta_spine
   | TypDef of Loc.t * cid_comp_typ * meta_spine
   | TypBox of Loc.t * meta_typ
   | TypArr     of typ * typ
   | TypCross   of typ * typ
   | TypPiBox   of LF.ctyp_decl * typ
   | TypBool
   | TypInd of typ 

  and exp_chk =
     | Syn    of Loc.t * exp_syn
     | Fun    of Loc.t * name * exp_chk                         (* fn   f => e         *)
     | Cofun  of Loc.t * (copattern_spine * exp_chk) list       (* Cofun hd => e | tl => e' *)
     | MLam   of Loc.t * name * exp_chk                         (* mlam f => e         *)
     | Pair   of Loc.t * exp_chk * exp_chk                      (* (e1 , e2)           *)
     | LetPair of Loc.t * exp_syn * (name * name * exp_chk)     (* let (x,y) = i in e  *)
     | Let    of Loc.t * exp_syn * (name * exp_chk)             (* let x = i in e      *)
     | Box    of Loc.t * meta_obj                               (* box (Psi hat. M)    *)
     | Case   of Loc.t * case_pragma * exp_syn * branch list
     | If     of Loc.t * exp_syn * exp_chk * exp_chk
     | Hole   of Loc.t

  and exp_syn =
     | Var    of Loc.t * offset                                     (* x              *)
     | FVar   of name                                       (* x              *)
     | DataConst of Loc.t * cid_comp_const                          (* c              *)
     | DataDest of Loc.t * cid_comp_dest                            (* c              *)
     | Const  of Loc.t * cid_prog                                   (* c              *)
     | Apply  of Loc.t * exp_syn * exp_chk                  (* i e            *)
     | BoxVal of Loc.t * meta_obj 
     | PairVal of Loc.t * exp_syn * exp_syn
     | Ann    of exp_chk * typ                                  (* e : tau        *)
     | Equal  of Loc.t  * exp_syn * exp_syn
     | Boolean of Loc.t * bool

 and pattern =
   | PatEmpty   of Loc.t * LF.dctx
   | PatMetaObj of Loc.t * meta_obj
   | PatConst   of Loc.t * cid_comp_const * pattern_spine
   | PatFVar    of Loc.t * name
   | PatVar     of Loc.t * name * offset
   | PatPair    of Loc.t * pattern * pattern
   | PatTrue    of Loc.t
   | PatFalse   of Loc.t
   | PatAnn     of Loc.t * pattern * typ

 and pattern_spine =
   | PatNil of Loc.t
   | PatApp of Loc.t * pattern * pattern_spine

  and branch =
    | EmptyBranch of Loc.t * LF.ctyp_decl LF.ctx * pattern
    | Branch of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx * pattern * exp_chk


  (* the definition of branch_pattern will be removed and replaced by the more general notion of patterns;
     it remains currently so we can still use the old parser without modifications -bp *)
  and branch_pattern =
     | NormalPattern of LF.normal * exp_chk
     | EmptyPattern

  and copattern_spine =
    | CopatNil of Loc.t
    | CopatApp of Loc.t * cid_comp_dest * copattern_spine
    | CopatMeta of Loc.t * meta_obj * copattern_spine

end
