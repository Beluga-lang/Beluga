(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)

open Id



module Loc : Camlp4.Sig.Loc

(** External Syntax *)
module Ext : sig

  module LF : sig

    type kind =
      | Typ     of Loc.t
      | ArrKind of Loc.t * typ * kind
      | PiKind  of Loc.t * typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and typ =
      | Atom   of Loc.t * name * spine
      | ArrTyp of Loc.t * typ * typ
      | PiTyp  of Loc.t * typ_decl * typ

    and normal =
      | Lam  of Loc.t * name * normal
      | Root of Loc.t * head * spine

    and head =
      | Name of Loc.t * name

    and spine =
      | Nil
      | App of Loc.t * normal * spine

    type sgn_decl =
      | SgnTyp   of Loc.t * name * kind
      | SgnConst of Loc.t * name * typ

  end

end



(** Internal Syntax *)
module Int : sig

  module LF : sig

    type kind =
      | Typ
      | PiKind of typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and sigma_decl =
      | SigmaDecl of name * typ_rec

    and ctyp_decl =
      | MDecl of name * typ  * dctx
      | PDecl of name * typ  * dctx
      | SDecl of name * dctx * dctx

    and typ =
      | Atom  of cid_typ * spine
      | PiTyp of typ_decl * typ
      | TClo  of typ * sub

    and normal =
      | Lam  of name * normal
      | Root of head * spine
      | Clo  of (normal * sub)

    and head =
      | BVar  of offset
      | Const of cid_term
      | MVar  of cvar * sub
      | PVar  of cvar * sub
      | AnnH  of head * typ
      | Proj  of head * int

    and spine =
      | Nil
      | App of normal * spine
      | SClo of spine * sub

    and sub =
      | Shift of offset
      | SVar  of cvar * sub
      | Dot   of front * sub

    and front =
      | Head of head
      | Obj  of normal
      | Undef

    and msub =                  
      | MShift of offset           
      | MDot   of mfront * msub     

    and mfront =
      | Id   of offset
      | MObj of psi_hat * normal
      | PObj of psi_hat * offset
      | CObj of dctx                      

    and cvar =
      | Offset of offset
      | Inst   of normal option ref * dctx * typ * (constrnt ref) list ref
      | PInst  of head   option ref * dctx * typ * (constrnt ref) list ref
      | CInst  of dctx   option ref * schema

    and constrnt =
      | Solved
      | Eqn of psi_hat * normal * normal
      | Eqh of psi_hat * head * head

    and cnstr    = constrnt ref

    and dctx =
      | Null
      | CtxVar   of cvar
      | DDec     of dctx * typ_decl
      | SigmaDec of dctx * sigma_decl

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of typ ctx * sigma_decl

    and schema =
      | Schema of sch_elem list

    and psi_hat = cvar option * offset

    and typ_rec = typ list

    type sgn_decl =
      | SgnTyp   of cid_typ  * kind
      | SgnConst of cid_term * typ



    (**********************)
    (* Type Abbreviations *)
    (**********************)

    type nclo     = normal  * sub
    type sclo     = spine   * sub
    type tclo     = typ     * sub
    type trec_clo = typ_rec * sub
    type mctx     = ctyp_decl ctx

  end



  module Comp : sig

    type typ =
      | TypBox   of LF.typ * LF.dctx
      | TypSBox  of LF.dctx * LF.dctx
      | TypArr   of typ * typ
      | TypCtxPi of (name * LF.schema) * typ
      | TypPiBox of LF.ctyp_decl * typ
      | TypClo   of typ * LF.msub

    and exp =
      | Rec    of name * exp
      | Fun    of name * exp
      | CtxFun of name * exp
      | MLam   of name * exp
      | Box    of LF.psi_hat * LF.normal
      | SBox   of LF.psi_hat * LF.sub
      | Case   of exp * branch list
      | Var    of offset
      | Apply  of exp * exp
      | CtxApp of exp * LF.dctx
      | MApp   of exp * (LF.psi_hat * LF.normal)
      | Ann    of exp * typ

    and branch =
      | BranchBox  of LF.ctyp_decl LF.ctx
          * (LF.psi_hat * LF.normal * (LF.typ * LF.dctx))
          * exp

      | BranchSBox of LF.ctyp_decl LF.ctx
          * (LF.psi_hat * LF.sub    * (LF.dctx * LF.dctx))
          * exp

  end

end
