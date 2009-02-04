(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)

open Id

module Loc = Camlp4.PreCast.Loc

(** External Syntax *)
module Ext = struct

  module LF = struct

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
      | Name  of Loc.t * name
      | MVar  of Loc.t * name * sub
      | Hole  of Loc.t 
      | PVar  of Loc.t * name * sub

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

    and typ_rec =
      |  SigmaLast of typ
      |  SigmaElem of name * typ * typ_rec

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

    and mctx     = ctyp_decl ctx          

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



  module Comp = struct

    type typ =                                     (* Computation-level types *)
      | TypBox   of Loc.t * LF.typ  * LF.dctx      (* tau ::= A[Psi]          *)
(*    | TypSBox  of LF.dctx * LF.dctx              (\*    | Phi[Psi]      *\) *)
      | TypArr   of Loc.t * typ * typ              (*     | tau -> tau        *)
      | TypCtxPi of Loc.t * (name * name) * typ    (*     | Pi psi:(w)*. tau  *)
      | TypPiBox of Loc.t * LF.ctyp_decl * typ     (*     | Pi u::A[Psi].tau  *)

    and exp_chk =                            (* Computation-level expressions *)
       | Syn    of Loc.t * exp_syn                (*  e ::= i                 *)
(*     | Rec    of Loc.t * name * exp_chk         (\*   | rec f : tau = e *\) *)
       | Fun    of Loc.t * name * exp_chk         (*    | fn f => e           *)
       | CtxFun of Loc.t * name * exp_chk         (*    | FN f => e           *)
       | MLam   of Loc.t * name * exp_chk         (*    | mlam f => e         *)
       | Box    of Loc.t * LF.psi_hat * LF.normal (*    | box (Psi hat. M)    *)
(*        | SBox   of LF.psi_hat * LF.sub *)
       | Case   of Loc.t * exp_syn * branch list  (*    | case i of branches *)

    and exp_syn =
       | Var    of Loc.t * name                   (*  i ::= x                 *)
       | Apply  of Loc.t * exp_syn * exp_chk      (*    | i e                 *)
       | CtxApp of Loc.t * exp_syn * LF.dctx      (*    | i [Psi]             *)
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal)
                                                  (*    | i [Psi hat. M]      *)
       | Ann    of Loc.t * exp_chk * typ          (*    | e : tau             *)

    and branch =
      | BranchBox of Loc.t * LF.mctx
          * (LF.dctx * LF.normal * (LF.typ * LF.dctx) option)
          * exp_chk

(*       | BranchSBox of LF.ctyp_decl LF.ctx *)
(*           * (LF.psi_hat * LF.sub    * (LF.dctx * LF.dctx)) *)
(*           * exp_chk *)

  end



  module Sgn = struct

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
module Int = struct

  module LF = struct

    type kind =
      | Typ
      | PiKind of typ_decl * kind

    and typ_decl =                         (* LF Declarations                *)
      | TypDecl of name * typ              (* D := x:A                       *)

    and sigma_decl =
      | SigmaDecl of name * typ_rec        (* x:Sigma x1:A1 .... xk:Ak       *)

    and ctyp_decl =                        (* Contextual Declarations        *)
      | MDecl of name * typ  * dctx        (* D ::= u::A[Psi]                *)
      | PDecl of name * typ  * dctx        (*   |   p::A[Psi]                *)
      | SDecl of name * dctx * dctx        (*   |   s::A[Psi]                *)
      | CDecl of name * cid_schema
                                           (* Potentially, A is Sigma type? *)

    and typ =                              (* LF level                       *)
      | Atom  of cid_typ * spine           (* A ::= a M1 ... Mn              *)
      | PiTyp of typ_decl * typ            (*   | Pi x:A.B                   *)
      | TClo  of (typ * sub)               (*   | TClo(A,s)                  *)
      | TVar  of tvar * sub                (*   | TVar(a,s)                  *)

    and normal =                           (* normal terms                   *)
      | Lam  of Loc.t option * name * normal (* M ::= \x.M                     *)
      | Root of Loc.t option * head * spine  (*   | h . S                      *)
      | Clo  of (normal * sub)             (*   | Clo(N,s)                   *)

    and head =
      | BVar  of offset                    (* H ::= x                        *)
      | Const of cid_term                  (*   | c                          *)
      | MVar  of cvar * sub                (*   | u[s]                       *)
      | PVar  of cvar * sub                (*   | p[s]                       *)
      | AnnH  of head * typ                (*   | (H:A)                      *)
      | Proj  of head * int                (*   | #k(x) | #k(p[s])           *)

      | FVar  of name                      (* free variable for type
					      reconstruction                 *)
      | FMVar of name * sub                (* free meta-variable for type
					      reconstruction                 *)

      | FPVar of name * sub                (* free parameter variable for type
					      reconstruction                 *)

    and spine =                            (* spine                          *)
      | Nil                                (* S ::= Nil                      *)
      | App  of normal * spine             (*   | M . S                      *)
      | SClo of (spine * sub)              (*   | SClo(S,s)                  *)

    and sub =                              (* Substitutions                  *)
      | Shift of ctx_offset * offset       (* sigma ::= ^(psi,n)             *)
      | SVar  of cvar * sub                (*       | s[sigma]               *)
      | Dot   of front * sub               (*       | Ft . s                 *)

    and front =                            (* Fronts:                        *)
      | Head of head                       (* Ft ::= H                       *)
      | Obj  of normal                     (*    | N                         *)
      | Undef                              (*    | _                         *)

    and ctx_offset = 
      | CtxShift of ctx_var
      | NoCtxShift
      | NegCtxShift of ctx_var

    and cvar =                             (* Contextual Variables           *)
      | Offset of offset                   (* Bound Variables                *)
      | Inst   of normal option ref * dctx * typ * cnstr list ref
          (* D ; Psi |- M <= A
             provided constraint *)
      | PInst  of head   option ref * dctx * typ * cnstr list ref
          (* D ; Psi |- H => A
             provided constraint *)
      | CInst  of dctx   option ref * cid_schema
          (* D |- Psi : schema   *)

    and tvar =
      | TInst   of typ option ref * dctx * kind * cnstr list ref

    and constrnt =                         (* Constraint                     *)
      | Queued                             (* constraint ::= Queued          *)
      | Eqn of psi_hat * normal * normal   (*            | Psi |-(M1 == M2)  *)
      | Eqh of psi_hat * head * head       (*            | Psi |-(H1 == H2)  *)

    and cnstr = constrnt ref

    and dctx =                             (* LF Context                     *)
      | Null                               (* Psi ::= .                      *)
      | CtxVar   of ctx_var                (* | psi                          *)
      | DDec     of dctx * typ_decl        (* | Psi, x:A                     *)
      | SigmaDec of dctx * sigma_decl      (* | Psi, x:Sigma x1:A1...xn:An.A *)


    and ctx_var = 
      | CtxName   of name
      | CtxOffset of offset

    and 'a ctx =                           (* Generic context declaration    *)
      | Empty                              (* Context                        *)
      | Dec of 'a ctx * 'a                 (* C ::= Empty                    *)
                                           (* | C, x:'a                      *)

    and sch_elem =                         (* Schema Element                 *)
      | SchElem of typ_decl ctx * sigma_decl    (* Pi    x1:A1 ... xn:An.
                                              Sigma y1:B1 ... yk:Bk. B       *)
                                           (* Sigma-types not allowed in Ai  *)

    and schema =
      | Schema of sch_elem list

    and psi_hat = ctx_var option * offset  (* Psihat ::=         *)
                                           (*        | psi       *)
                                           (*        | .         *)
                                           (*        | Psihat, x *)

    and typ_rec =    (* Sigma x1:A1 ... xn:An. B *)
      |  SigmaLast of typ                             (* ... . B *)
      |  SigmaElem of name * typ * typ_rec            (* xk : Ak, ... *)




    (**********************)
    (* Type Abbreviations *)
    (**********************)

    type nclo     = normal  * sub          (* Ns = [s]N                      *)
    type sclo     = spine   * sub          (* Ss = [s]S                      *)
    type tclo     = typ     * sub          (* As = [s]A                      *)
    type trec_clo = typ_rec * sub          (* [s]Arec                        *)
    type mctx     = ctyp_decl ctx          (* Modal Context  D: CDec ctx     *)

  end


  module Comp = struct

   type mfront =                          (* Fronts:                        *)
     | MObj of LF.psi_hat * LF.normal     (* Mft::= Psihat.N                *)
     | PObj of LF.psi_hat * LF.head       (*    | Psihat.p[s] | Psihat.x    *)
     | MV   of offset                     (*    | u//u | p//p               *)
     | Undef 


   type msub =                            (* Contextual substitutions       *)
     | MShift of int                      (* theta ::= ^n                   *)
     | MDot   of mfront * msub            (*       | MFt . theta            *)

   type depend =  
     | Implicit 
     | Explicit

   type typ =
      | TypBox   of LF.typ  * LF.dctx
      | TypSBox  of LF.dctx * LF.dctx        (* Phi[Psi]    *)
      | TypArr   of typ * typ                (* tau -> tau  *)
      | TypCtxPi of (name * cid_schema) * typ (* {psi:W} tau *)
      | TypPiBox of (LF.ctyp_decl * depend) * typ
      | TypClo   of typ *  msub

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
      | Const  of cid_prog
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
    type tclo = typ * msub
  end



  module Sgn = struct

    type decl =
      | Typ    of cid_typ    * LF.kind
      | Const  of cid_term   * LF.typ
      | Schema of cid_schema * LF.schema
      | Rec    of cid_prog   * Comp.typ * Comp.exp_chk

    type sgn = decl list

  end

end

(** Approximate Simple Syntax *)
module Apx = struct

  module LF = struct

    type kind =
      | Typ
      | PiKind of typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and sigma_decl =
      | SigmaDecl of name * typ_rec

    and ctyp_decl =
      | MDecl of  name * typ  * dctx
      | PDecl of  name * typ  * dctx

    and typ =
      | Atom  of cid_typ * spine
      | PiTyp of typ_decl * typ

    and typ_rec =
      | SigmaLast of typ
      | SigmaElem of name * typ * typ_rec

    and normal =
      | Lam  of Loc.t * name * normal
      | Root of Loc.t * head * spine

    and head =
      | BVar  of offset
      | Const of cid_term
      | MVar  of offset * sub
      | Hole 
      | PVar  of offset * sub
      | FVar  of name
      | FMVar of name   * sub
      | FPVar of name   * sub

    and spine =
      | Nil
      | App of normal * spine

    and sub =
      | EmptySub
      | Id
      | Dot   of front * sub

    and front =
      | Head of head
      | Obj  of normal

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
      | SchElem of typ_decl ctx * sigma_decl

    and schema =
      | Schema of sch_elem list

    and psi_hat = (Int.LF.ctx_var) option * offset
  end

  module Comp = struct

    type typ =
      | TypBox   of LF.typ  * LF.dctx
      | TypArr   of typ * typ
      | TypCtxPi of (name * cid_schema) * typ
      | TypPiBox of LF.ctyp_decl * typ

    and exp_chk =
       | Syn    of exp_syn
       | Fun    of name * exp_chk         (* fn   f => e         *)
       | CtxFun of name * exp_chk         (* FN   f => e         *)
       | MLam   of name * exp_chk         (* mlam f => e         *)
       | Box    of LF.psi_hat * LF.normal (* box (Psi hat. M)    *)
       | Case   of exp_syn * branch list

    and exp_syn =
       | Var    of offset                             (* x              *)
       | Const  of cid_prog                           (* c              *)
       | Apply  of exp_syn * exp_chk                  (* i e            *)
       | CtxApp of exp_syn * LF.dctx                  (* i [Psi]        *)
       | MApp   of exp_syn * (LF.psi_hat * LF.normal) (* i [Psi hat. M] *)
       | Ann    of exp_chk * typ                      (* e : tau        *)

    and branch =
      | BranchBox of LF.ctyp_decl LF.ctx
          * (LF.dctx * LF.normal * (LF.typ * LF.dctx) option)
          * exp_chk

  end

end
