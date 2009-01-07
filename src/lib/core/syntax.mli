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
      | ArrKind of Loc.t * typ      * kind
      | PiKind  of Loc.t * typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and sigma_decl =
      | SigmaDecl of name * typ_rec

    and ctyp_decl =
      | MDecl of Loc.t * name * typ  * dctx
      | PDecl of Loc.t * name * typ  * dctx
(*       | SDecl of Loc.t * name * dctx * dctx *)

    and typ =
      | Atom   of Loc.t * name * spine
      | ArrTyp of Loc.t * typ      * typ
      | PiTyp  of Loc.t * typ_decl * typ

    and normal =
      | Lam  of Loc.t * name * normal
      | Root of Loc.t * head * spine

    and head =
      | Name of Loc.t * name
      | MVar of Loc.t * name * sub
      | PVar of Loc.t * name * sub

    and spine =
      | Nil
      | App of Loc.t * normal * spine

    and sub =
      | Dot    of Loc.t
      | Normal of Loc.t * sub * normal
      | Id     of Loc.t 

    and typ_rec = typ list

    and dctx =
      | Null
      | CtxVar   of name
      | DDec     of dctx * typ_decl
(*       | SigmaDec of dctx * sigma_decl *)

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of Loc.t * typ_decl ctx * sigma_decl

    and schema =
      | Schema of sch_elem list

    and psi_hat = name list

    and prag =
      | PragUnifyTerm of
            unify_decl list
          * normal
          * normal
      | PragUnifyTyp of
            unify_decl list
          * typ
          * typ

    and unify_decl =
      | UnifyTermDecl of name          * typ
      | UnifyTermDefn of name * normal * typ
      | UnifyTypeDecl of name          * kind
      | UnifyTypeDefn of name * typ    * kind

  end



  module Comp : sig


    type typ =                            
      | TypBox   of Loc.t * LF.typ  * LF.dctx     
(*    | TypSBox  of LF.dctx * LF.dctx             *)
      | TypArr   of Loc.t * typ * typ             
      | TypCtxPi of Loc.t * (name * name) * typ  
      | TypPiBox of Loc.t * LF.ctyp_decl * typ   


    and exp_chk =
       | Syn    of Loc.t * exp_syn               
(*        | Rec    of Loc.t * name * exp_chk     *)
       | Fun    of Loc.t * name * exp_chk        
       | CtxFun of Loc.t * name * exp_chk         
       | MLam   of Loc.t * name * exp_chk         
       | Box    of Loc.t * LF.psi_hat * LF.normal 
(*        | SBox   of LF.psi_hat * LF.sub *)
       | Case   of Loc.t * exp_syn * branch list 

    and exp_syn =
       | Var    of Loc.t * name                  
       | Apply  of Loc.t * exp_syn * exp_chk     
       | CtxApp of Loc.t * exp_syn * LF.dctx     
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal) 
       | Ann    of Loc.t * exp_chk * typ                      

    and branch =
      | BranchBox of Loc.t * LF.ctyp_decl LF.ctx
          * (LF.psi_hat * LF.normal * (LF.typ * LF.dctx))
          * exp_chk

(*       | BranchSBox of LF.ctyp_decl LF.ctx *)
(*           * (LF.psi_hat * LF.sub    * (LF.dctx * LF.dctx)) *)
(*           * exp_chk *)


  end



  module Sgn : sig

    type decl =
      | Const  of Loc.t * name * LF.typ
      | Typ    of Loc.t * name * LF.kind
      | Schema of Loc.t * name * LF.schema

      | Pragma of Loc.t * LF.prag

      | Rec    of Loc.t * name * Comp.typ * Comp.exp_chk


    type sgn = decl list

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
      | CDecl of name * cid_schema

    and typ =
      | Atom  of cid_typ * spine
      | PiTyp of typ_decl * typ
      | TClo  of (typ * sub)

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
      | FVar  of name

    and spine =
      | Nil
      | App of normal * spine
      | SClo of (spine * sub)

    and sub =
      | Shift of offset
      | SVar  of cvar * sub
      | Dot   of front * sub

    and front =
      | Head of head
      | Obj  of normal
      | Undef

    and cvar =
      | Offset of offset
      | Inst   of normal option ref * dctx * typ * (constrnt ref) list ref
      | PInst  of head   option ref * dctx * typ * (constrnt ref) list ref
      | CInst  of dctx   option ref * cid_schema

    and constrnt =
      | Queued
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
      | SchElem of typ_decl ctx * sigma_decl

    and schema =
      | Schema of sch_elem list

    and psi_hat = cvar option * offset

    and typ_rec = typ list



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

   type mfront =              
     | MObj of LF.psi_hat * LF.normal 
     | PObj of LF.psi_hat * LF.head
     | MV   of offset

   type msub =                            
     | MShift of int
     | MDot   of mfront * msub

    type typ =
      | TypBox   of LF.typ * LF.dctx
      | TypSBox  of LF.dctx * LF.dctx
      | TypArr   of typ * typ
      | TypCtxPi of (name * cid_schema) * typ
      | TypPiBox of LF.ctyp_decl * typ
      | TypClo   of typ * msub


    and exp_chk =
       | Syn    of exp_syn
       | Rec    of name * exp_chk
       | Fun    of name * exp_chk
       | CtxFun of name * exp_chk
       | MLam   of name * exp_chk
       | Box    of LF.psi_hat * LF.normal
       | SBox   of LF.psi_hat * LF.sub
       | Case   of exp_syn * branch list

    and exp_syn =
       | Var    of offset
       | Apply  of exp_syn * exp_chk
       | CtxApp of exp_syn * LF.dctx
       | MApp   of exp_syn * (LF.psi_hat * LF.normal)
       | Ann    of exp_chk * typ

    and branch =
      | BranchBox  of LF.ctyp_decl LF.ctx
          * (LF.psi_hat * LF.normal * (LF.typ * LF.dctx))
          * exp_chk

      | BranchSBox of LF.ctyp_decl LF.ctx
          * (LF.psi_hat * LF.sub    * (LF.dctx * LF.dctx))
          * exp_chk

    type gctx = (name * typ) LF.ctx
    type tclo = typ  * msub

  end



  module Sgn : sig

    type decl =
      | Typ   of cid_typ  * LF.kind
      | Const of cid_term * LF.typ
      | Schema of cid_schema * LF.schema
      | Rec    of cid_prog   * Comp.typ * Comp.exp_chk

    type sgn = decl list

  end

end
