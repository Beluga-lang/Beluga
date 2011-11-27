(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)

open Id



module Loc : Camlp4.Sig.Loc

type case_pragma = RegularCase | PragmaNotCase

(** Internal Syntax *)
module Int : sig

  module LF : sig

    type depend =
      | No       
      | Maybe        

    type kind =
      | Typ
      | PiKind of (typ_decl * depend) * kind

    and typ_decl =
      | TypDecl of name * typ
      | TypDeclOpt of name

    and ctyp_decl =
      | MDecl of name * typ  * dctx
      | PDecl of name * typ  * dctx
      | SDecl of name * dctx * dctx
      | CDecl of name * cid_schema
      | MDeclOpt of name
      | PDeclOpt of name 
      | CDeclOpt of name 


    and typ =
      | Atom  of Loc.t option * cid_typ * spine
      | PiTyp of (typ_decl * depend) * typ
      | Sigma of typ_rec
      | TClo  of (typ * sub)

    and normal =
      | Lam  of Loc.t option * name * normal
      | Root of Loc.t option * head * spine
      | Clo  of (normal * sub)
      | Tuple of Loc.t option * tuple

    and head =
      | BVar  of offset
      | Const of cid_term
      | MMVar of mm_var * (msub * sub)
      | MVar  of cvar * sub
      | PVar  of cvar * sub
      | AnnH  of head * typ
      | Proj  of head * int
      | FVar  of name
      | FMVar of name * sub
      | FPVar of name * sub

    and spine =
      | Nil
      | App of normal * spine
      | SClo of (spine * sub)

    and sub =
      | Shift of ctx_offset * offset
      | SVar  of cvar * sub
      | FSVar of name * sub
      | Dot   of front * sub

    and front =
      | Head of head
      | Obj  of normal
      | Undef

   and mfront =
     | MObj of psi_hat * normal 
     | PObj of psi_hat * head
     | MV   of offset
     | MUndef

   and msub =
     | MShift of int
     | MDot   of mfront * msub

   and csub =                                  
     | CShift of int                           
     | CDot   of dctx * csub                   

   and ctx_offset = 
      | CtxShift of ctx_var
      | NoCtxShift
      | NegCtxShift of ctx_var

    and cvar =
      | Offset of offset
      | Inst   of normal option ref * dctx * typ * (constrnt ref) list ref
      | PInst  of head   option ref * dctx * typ * (constrnt ref) list ref


    and mm_var  = 
      | MInst   of normal option ref * mctx * dctx * typ * cnstr list ref

    and tvar = 
      | TInst   of typ option ref * dctx * kind * cnstr list ref

    and typ_free_var = Type of typ | TypVar of tvar

    and constrnt =
      | Queued
      | Eqn of mctx * dctx * normal * normal
      | Eqh of mctx * dctx * head * head

    and cnstr    = constrnt ref

    and dctx =
      | Null
      | CtxVar   of ctx_var
      | DDec     of dctx * typ_decl

    and tuple =
      | Last of normal
      | Cons of normal * tuple

    and ctx_var = 
      | CtxName   of name
      | CtxOffset of offset
      | CInst  of dctx option ref * cid_schema * mctx * mctx

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of typ_decl ctx * typ_rec

    and schema =
      | Schema of sch_elem list

    and psi_hat = ctx_var option * offset

    and typ_rec =
      |  SigmaLast of typ
      |  SigmaElem of name * typ * typ_rec

    and mctx     = ctyp_decl ctx

    (**********************)
    (* Type Abbreviations *)
    (**********************)

    type nclo     = normal  * sub
    type sclo     = spine   * sub
    type tclo     = typ     * sub
    type trec_clo = typ_rec * sub


    type prag =
      | NamePrag of cid_typ 
      | NotPrag

    (* getType head s_recA target 1 *)
    val getType : head -> trec_clo -> int -> int -> tclo

    val blockLength : typ_rec -> int
  end (* Int.LF *)



  module Comp : sig

   type depend =
     | Implicit 
     | Explicit

   type meta_typ = 
     | MetaTyp of LF.typ * LF.dctx
     | MetaSchema of cid_schema 

   type typ =
     | TypBox   of Loc.t option * LF.typ * LF.dctx
     | TypSub   of Loc.t option * LF.dctx * LF.dctx
     | TypArr   of typ * typ
     | TypCross of typ * typ
     | TypCtxPi of (name * cid_schema * depend) * typ
     | TypPiBox of (LF.ctyp_decl * depend) * typ
     | TypClo   of typ * LF.msub
     | TypBool  
         
   type contextual_obj = NormObj of LF.normal | NeutObj of LF.head | SubstObj of LF.sub 

   type env = 
     | Empty
     | Cons of value * env

   and value = 
     | FunValue   of (Loc.t option * name * exp_chk) * LF.csub * LF.msub * env 
     | RecValue   of (cid_prog * exp_chk) * LF.csub  * LF.msub * env 
     | MLamValue  of (Loc.t option * name * exp_chk) * LF.csub * LF.msub * env
     | CtxValue   of (Loc.t option * name * exp_chk) * LF.csub * LF.msub * env
     | BoxValue   of LF.psi_hat * LF.normal 
     | ConstValue of cid_prog
     | BoolValue  of bool
  
   and exp_chk =
     | Syn     of Loc.t option * exp_syn
     | Rec     of Loc.t option * name * exp_chk
     | Fun     of Loc.t option * name * exp_chk
     | CtxFun  of Loc.t option * name * exp_chk
     | MLam    of Loc.t option * name * exp_chk
     | Pair    of Loc.t option * exp_chk * exp_chk     
     | LetPair of Loc.t option * exp_syn * (name * name * exp_chk) 
     | Let     of Loc.t option * exp_syn * (name * exp_chk)
     | Box     of Loc.t option * LF.psi_hat * LF.normal
     | SBox    of Loc.t option * LF.psi_hat * LF.sub
     | Case    of Loc.t option * case_pragma * exp_syn * branch list
     | If      of Loc.t option * exp_syn * exp_chk * exp_chk
     | Value   of value
         
   and exp_syn =
     | Var    of offset
     | Const  of cid_prog
     | Apply  of Loc.t option * exp_syn * exp_chk
     | CtxApp of Loc.t option * exp_syn * LF.dctx
     | MApp   of Loc.t option * exp_syn * (LF.psi_hat * contextual_obj)
     | Ann    of exp_chk * typ 
     | Equal  of Loc.t option * exp_syn * exp_syn
     | Boolean of bool

         
    and branch_pattern =
       | NormalPattern of LF.normal * exp_chk
       | EmptyPattern
    
    and branch =
      | BranchBox of LF.mctx * LF.mctx
          * (LF.dctx * branch_pattern * LF.msub * LF.csub)
      | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx 
          * (LF.dctx * LF.sub * LF.msub * LF.csub)
          * exp_chk

         
   type ctyp_decl =
     | CTypDecl of name * typ
     | CTypDeclOpt of name 
    
    type gctx = ctyp_decl LF.ctx
    type tclo = typ  * LF.msub

  end (* Int.Comp *)



  module Sgn : sig

    type decl =
      | Typ   of cid_typ  * LF.kind
      | Const of cid_term * LF.typ
      | Schema of cid_schema * LF.schema
      | Rec    of cid_prog   * Comp.typ * Comp.exp_chk
      | Pragma of LF.prag

    type sgn = decl list

  end (* Int.Sgn *)

end (* Int *)

(** External Syntax *)
module Ext : sig

  module LF : sig


    type kind =
      | Typ     of Loc.t
      | ArrKind of Loc.t * typ      * kind
      | PiKind  of Loc.t * typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and ctyp_decl =
      | MDecl of Loc.t * name * typ  * dctx
      | PDecl of Loc.t * name * typ  * dctx
      | SDecl of Loc.t * name * dctx * dctx
      | CDecl of Loc.t * name * name


    and typ =
      | Atom   of Loc.t * name * spine
      | ArrTyp of Loc.t * typ      * typ
      | PiTyp  of Loc.t * typ_decl * typ
      | Sigma  of Loc.t * typ_rec
      | Ctx    of Loc.t * dctx 

    and normal =
      | Lam  of Loc.t * name * normal
      | Root of Loc.t * head * spine
      | Tuple of Loc.t * tuple

    and head =
      | Name  of Loc.t * name
      | MVar  of Loc.t * name * sub
      | Hole  of Loc.t 
      | PVar  of Loc.t * name * sub
      | ProjName  of Loc.t * int * name
      | ProjPVar  of Loc.t * int * (name * sub)         
      | SVar  of Loc.t * name * sub  (* this needs to be be then turned into a subst. *)

    and spine =
      | Nil
      | App of Loc.t * normal * spine

    and sub =
      | EmptySub of Loc.t
      | Dot      of Loc.t * sub * front
      | Id       of Loc.t 

    and front = 
      | Head     of head
      | Normal   of normal

    and typ_rec =               (* Sigma x1:A1 ... xn:An. B *)
      | SigmaLast of typ                          (* ... . B *)
      | SigmaElem of name * typ * typ_rec         (* xk : Ak, ... *)

    and dctx =
      | Null
      | CtxVar   of Loc.t * name
      | DDec     of dctx * typ_decl

    and tuple =
      | Last of normal
      | Cons of normal * tuple

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of Loc.t * typ_decl ctx * typ_rec

    and schema =
      | Schema of sch_elem list

    and psi_hat = name list

    and mctx     = ctyp_decl ctx          

    and prag =
      | NamePrag of name * string * string option 
      | NotPrag

  end (* Ext.LF *)



  module Comp : sig

   type depend =  
     | Implicit
     | Explicit

    type typ =                            
      | TypBox   of Loc.t * LF.typ  * LF.dctx     
      | TypSub   of Loc.t * LF.dctx * LF.dctx             
      | TypArr   of Loc.t * typ * typ             
      | TypCross of Loc.t * typ * typ
      | TypCtxPi of Loc.t * (name * name * depend) * typ  
      | TypPiBox of Loc.t * LF.ctyp_decl * typ   
      | TypBool


    and exp_chk =
       | Syn     of Loc.t * exp_syn               
       | Fun     of Loc.t * name * exp_chk        
       | CtxFun  of Loc.t * name * exp_chk         
       | MLam    of Loc.t * name * exp_chk         
       | Pair    of Loc.t * exp_chk * exp_chk
       | LetPair of Loc.t * exp_syn * (name * name * exp_chk) 
       | Let     of Loc.t * exp_syn * (name * exp_chk)
       | Box     of Loc.t * LF.psi_hat * LF.normal 
       | SBox    of Loc.t * LF.psi_hat * LF.sub 
       | Case    of Loc.t * case_pragma * exp_syn * branch list 
       | If      of Loc.t * exp_syn * exp_chk * exp_chk

    and exp_syn =
       | Var    of Loc.t * name                  
       | Apply  of Loc.t * exp_syn * exp_chk     
       | CtxApp of Loc.t * exp_syn * LF.dctx     
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal) 
       | MAnnApp   of Loc.t * exp_syn * (LF.dctx * LF.normal) 
       | BoxVal of Loc.t * LF.dctx * LF.normal 
       | Ann    of Loc.t * exp_chk * typ                   
       | Equal   of Loc.t * exp_syn * exp_syn
       | Boolean of Loc.t * bool


    and branch_pattern =
       | NormalPattern of LF.normal * exp_chk
       | EmptyPattern
    
    and branch =
      | BranchBox of Loc.t * LF.mctx
          * (LF.dctx * branch_pattern * (LF.typ * LF.dctx) option)
      | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx
          * (LF.dctx * LF.sub * LF.dctx option)
          * exp_chk


   type rec_fun = RecFun of name * typ * exp_chk

   val synToString : exp_syn -> string
   val chkToString : exp_chk -> string
  end (* Ext.Comp *)



  module Sgn : sig

    type decl =
      | Const    of Loc.t * name * LF.typ
      | Typ      of Loc.t * name * LF.kind
      | Schema   of Loc.t * name * LF.schema
      | Pragma   of Loc.t * LF.prag
      | Rec      of Loc.t * Comp.rec_fun list
      | Val      of Loc.t * name * Comp.typ option * Comp.exp_syn 
      | Query    of Loc.t * name option * LF.typ * int option * int option


    type sgn = decl list

  end (* Ext.Sgn *)

end (* Ext *)

(** Approximate Simple Syntax *)
module Apx : sig

  module LF : sig

    type depend =
      | No       
      | Maybe        

    type kind =
      | Typ
      | PiKind of (typ_decl * depend) * kind

    and typ_decl =
      | TypDecl of name * typ

    and ctyp_decl =
      | MDecl of  name * typ  * dctx
      | PDecl of  name * typ  * dctx
      | MDeclOpt of name
      | SDecl of  name * dctx * dctx
      | CDecl of name * cid_schema

    and typ =
      | Atom  of Loc.t * cid_typ * spine
      | PiTyp of (typ_decl * depend) * typ
      | Sigma of typ_rec

    and typ_rec =
      | SigmaLast of typ
      | SigmaElem of name * typ * typ_rec

    and tuple =
      | Last of normal
      | Cons of normal * tuple

    and normal =
      | Lam  of Loc.t * name * normal
      | Root of Loc.t * head * spine
      | Tuple of Loc.t * tuple

    and head =
      | BVar  of offset
      | Const of cid_term
      | MVar  of cvar * sub
      | Proj  of head * int
      | Hole  
      | PVar  of cvar * sub
      | FVar  of name
      | FMVar of name * sub    
      | FPVar of name * sub 

    and spine =
      | Nil
      | App of normal * spine

    and sub =
      | EmptySub
      | Id    of ctx_var 
      | Dot  of front * sub
      | SVar of cvar * sub
      | FSVar of name * sub

    and front =
      | Head of head
      | Obj  of normal

    and cvar = 
      | Offset of offset
      | MInst  of Int.LF.normal * Int.LF.typ * Int.LF.dctx
      | PInst  of Int.LF.head * Int.LF.typ * Int.LF.dctx

    and dctx =
      | Null
      | CtxVar   of ctx_var
      | DDec     of dctx * typ_decl

    and ctx_var = 
      | CtxName   of name
      | CtxOffset of offset

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of typ_decl ctx * typ_rec

    and schema =
      | Schema of sch_elem list

    and psi_hat = (Int.LF.ctx_var) option * offset

  end (* Apx.LF *)

  module Comp : sig

   type depend =  
     | Implicit
     | Explicit

   type meta_obj = 
     | MetaCtx of LF.dctx 
     | MetaObj of LF.psi_hat * LF.normal

    type typ =
      | TypBox   of Loc.t * LF.typ  * LF.dctx
      | TypSub   of Loc.t * LF.dctx * LF.dctx
      | TypArr   of typ * typ
      | TypCross of typ * typ
      | TypCtxPi of (name * cid_schema * depend) * typ
      | TypPiBox of LF.ctyp_decl * typ
      | TypBool

    and exp_chk =
       | Syn     of Loc.t * exp_syn
       | Fun     of Loc.t * name * exp_chk              (* fn   f => e           *)
       | CtxFun  of Loc.t * name * exp_chk              (* FN   f => e           *)
       | MLam    of Loc.t * name * exp_chk              (* mlam u =>  e          *)
       | Pair    of Loc.t * exp_chk * exp_chk           (* (e1 , e2)             *)
       | LetPair of Loc.t * exp_syn * (name * name * exp_chk) 
                                                        (* let (x,y) = i in e    *)
       | Let     of Loc.t * exp_syn * (name * exp_chk)
                                                        (* let x = i in e        *)
       | Box     of Loc.t * LF.psi_hat * LF.normal      (* box (Psi hat. M)      *)
       | SBox    of Loc.t * LF.psi_hat * LF.sub         (* sbox (Psi hat. sigma) *)
       | Case    of Loc.t * case_pragma * exp_syn * branch list
       | If      of Loc.t * exp_syn * exp_chk * exp_chk

    and exp_syn =
       | Var    of offset                                     (* x                *)
       | Const  of cid_prog                                   (* c                *)
       | Apply  of Loc.t * exp_syn * exp_chk                  (* i e              *)
       | CtxApp of Loc.t * exp_syn * LF.dctx                  (* i [Psi]          *)
       | MApp   of Loc.t * exp_syn * meta_obj                 (* i [Psi hat. M]   *)
       | MAnnApp   of Loc.t * exp_syn * (LF.dctx * LF.normal) (* i [Psi. M]       *)
       | BoxVal of Loc.t * LF.dctx * LF.normal                (* box (psihat. tR) *)
       | Ann    of exp_chk * typ                              (* e : tau          *)
       | Equal  of Loc.t  * exp_syn * exp_syn
       | Boolean of Loc.t * bool


    and branch_pattern =
       | NormalPattern of LF.normal * exp_chk
       | EmptyPattern
    
    and branch =
      | BranchBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx 
          * (LF.dctx * branch_pattern * (LF.typ * LF.dctx) option)
      | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx 
          * (LF.dctx * LF.sub * LF.dctx option)
          * exp_chk

  end (* Apx.Comp *)

end (* Apx *)
