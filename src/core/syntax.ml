(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)

open Id

module Loc = Camlp4.PreCast.Loc

(** Internal Syntax *)
module Int = struct
  (** Internal LF Syntax *)
  module LF = struct

    type depend =
      | No       
      | Maybe        

    type kind =
      | Typ
      | PiKind of (typ_decl * depend) * kind

    and typ_decl =                         (* LF Declarations                *)
      | TypDecl of name * typ              (* D := x:A                       *)
      | TypDeclOpt of name                 (*   |  x:_                       *)

    and ctyp_decl =                        (* Contextual Declarations        *)
      | MDecl of name * typ  * dctx        (* D ::= u::A[Psi]                *)
      | PDecl of name * typ  * dctx        (*   |   p::A[Psi]                *)
      | SDecl of name * dctx * dctx        (*   |   s::A[Psi]                *)
      | CDecl of name * cid_schema
      | MDeclOpt of name 
      | PDeclOpt of name 
      | CDeclOpt of name 

                                           (* Potentially, A is Sigma type? *)

    and typ =                              (* LF level                       *)
      | Atom  of Loc.t option * cid_typ * spine (* A ::= a M1 ... Mn              *)
      | PiTyp of (typ_decl * depend) * typ (*   | Pi x:A.B                   *)
      | Sigma of typ_rec
      | TClo  of (typ * sub)               (*   | TClo(A,s)                  *)


    and normal =                            (* normal terms                   *)
      | Lam  of Loc.t option * name * normal(* M ::= \x.M                     *)
      | Root of Loc.t option * head * spine (*   | h . S                      *)
      | Clo  of (normal * sub)              (*   | Clo(N,s)                   *)
      | Tuple of Loc.t option * tuple

    and head =
      | BVar  of offset                    (* H ::= x                        *)
      | Const of cid_term                  (*   | c                          *)
      | MMVar of mm_var * (msub * sub)     (*   | u[t ; s]                   *)
      | MVar  of cvar * sub                (*   | u[s]                       *)
      | PVar  of cvar * sub                (*   | p[s]                       *)
      | AnnH  of head * typ                (*   | (H:A)                      *)
      | Proj  of head * int                (*   | x.k | #p.k s               *)
      | CoPVar of cid_coercion * cvar * int * sub
                                           (*   | c(#p)[s] | c(#p.k)[s]      *)

      | FVar  of name                      (* free variable for type 
                                              reconstruction                 *)
      | FMVar of name * sub                (* free meta-variable for type 
                                              reconstruction                 *)
      | FPVar of name * sub                (* free parameter variable for type
                                              reconstruction                 *)
      | CoFPVar of cid_coercion * name * int * sub
                                           (* free coerced parameter for type
                                              reconstruction                 *)
                                           (*   | c(#p)[s] | c(#p.k)[s]      *)

    and spine =                            (* spine                          *)
      | Nil                                (* S ::= Nil                      *)
      | App  of normal * spine             (*   | M . S                      *)
      | SClo of (spine * sub)              (*   | SClo(S,s)                  *)

    and sub =                              (* Substitutions                  *)
      | Shift of ctx_offset * offset       (* sigma ::= ^(psi,n)             *)
      | CoShift of id_coercion * ctx_offset * offset 
                                           (*       | coe^(coe_cid,psi,n)    *)
      | SVar  of cvar * sub                (*       | s[sigma]               *)
      | Dot   of front * sub               (*       | Ft . s                 *)

    and id_coercion = 
      | Coe of cid_coercion 
      | InvCoe of cid_coercion

    and front =                            (* Fronts:                        *)
      | Head of head                       (* Ft ::= H                       *)
      | Block of head * int                (*    | Block (h,i, length)       *)
      | Obj  of normal                     (*    | N                         *)
      | Undef                              (*    | _                         *)


  (* Note: Block (h,i, l) represents a tuple of length l where the i-th 
     position is instantiated with h; all other positions are undefined *)                         

                                          (* Contextual substitutions       *) 
   and mfront =                           (* Fronts:                        *)
     | MObj of psi_hat * normal           (* Mft::= Psihat.N                *)
     | PObj of psi_hat * head             (*    | Psihat.p[s] | Psihat.x    *)
     | MV   of offset                     (*    | u//u | p//p               *)
     | MUndef


   and msub =                             (* Contextual substitutions       *)
     | MShift of int                      (* theta ::= ^n                   *)
     | MDot   of mfront * msub            (*       | MFt . theta            *)

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

    and mm_var  =                             (* Meta² Variables            *)
      | MInst   of normal option ref * mctx * dctx * typ * cnstr list ref
          (* D ; Psi |- M <= A
             provided constraint *)


    and tvar =
      | TInst   of typ option ref * dctx * kind * cnstr list ref

    and typ_free_var = Type of typ | TypVar of tvar

    and constrnt =                          (* Constraint                     *)
      | Queued                              (* constraint ::= Queued          *)
      | Eqn of mctx * psi_hat * normal * normal
                                            (*            | Psi |-(M1 == M2)  *)
      | Eqh of mctx * psi_hat * head * head (*            | Psi |-(H1 == H2)  *)

    and cnstr = constrnt ref

    and dctx =                             (* LF Context                     *)
      | Null                               (* Psi ::= .                      *)
      | CtxVar   of ctx_var                (* | psi                          *)
      | DDec     of dctx * typ_decl        (* | Psi, x:A   or x:block ...    *)

    and ctx_var = 
      | CtxName   of name
      | CtxOffset of offset
      | CoCtx     of cid_coercion * ctx_var 

    and 'a ctx =                           (* Generic context declaration    *)
      | Empty                              (* Context                        *)
      | Dec of 'a ctx * 'a                 (* C ::= Empty                    *)
                                           (* | C, x:'a                      *)

    and sch_elem =                         (* Schema Element                 *)
      | SchElem of typ_decl ctx * typ_rec    (* Pi    x1:A1 ... xn:An.
                                              Sigma y1:B1 ... yk:Bk. B       *)
                                           (* Sigma-types not allowed in Ai  *)

    and schema =
      | Schema of sch_elem list

    and psi_hat = ctx_var option * offset  (* Psihat ::=         *)
                                           (*        | psi       *)
                                           (*        | .         *)
                                           (*        | Psihat, x *)


    and co_typ = CoTyp of cid_schema * cid_schema
                                           (* Coercion Type: cid_schema -> cid_schema *)

    and coercion   = co_branch list        (* Coercion definition         *)
    and co_branch  = CoBranch of typ_decl ctx * typ_rec * typ_rec option
                                           (* some [x1:A1,..xn:An] 
                                            *   block y1:B1 .. yl:Bn => z1:C1 .. yl:Cl
                                            *)  

    and typ_rec =    (* Sigma x1:A1 ... xn:An. B *)
      |  SigmaLast of typ                             (* ... . B *)
      |  SigmaElem of name * typ * typ_rec            (* xk : Ak, ... *)

    and tuple =
      | Last of normal
      | Cons of normal * tuple

    and mctx     = ctyp_decl ctx          (* Modal Context  D: CDec ctx     *)


    (**********************)
    (* Type Abbreviations *)
    (**********************)

    type nclo     = normal  * sub          (* Ns = [s]N                      *)
    type sclo     = spine   * sub          (* Ss = [s]S                      *)
    type tclo     = typ     * sub          (* As = [s]A                      *)
    type trec_clo = typ_rec * sub          (* [s]Arec                        *)



    type prag =
      | NamePrag of cid_typ 
      | NotPrag

    (* getType traverses the typ_rec from left to right;
       target is relative to the remaining suffix of the type 
 
       getType head s_recA target j = (tA, s')
       
       if  Psi(head) = Sigma recA'
           and [s]recA is a suffix of recA'
       then
           Psi |- [s']tA  <= type
    *)
    let rec getType head s_recA target j = match (s_recA, target) with
      | ((SigmaLast lastA, s), 1) ->
          (lastA, s)
            
      | ((SigmaElem (_x, tA, _recA), s), 1) -> 
          (tA, s)
            
      | ((SigmaElem (_x, _tA, recA), s), target) ->
          let tPj = Proj (head, j) in
            getType head (recA, Dot (Head tPj, s)) (target - 1) (j + 1)
  end


 (** Internal Computation Syntax *)
  module Comp = struct


   type depend =  
     | Implicit
     | Explicit

   type typ =
      | TypBox   of Loc.t option * LF.typ  * LF.dctx
      | TypSBox  of Loc.t option * LF.dctx * LF.dctx
      | TypArr   of typ * typ
      | TypCross of typ * typ
      | TypCtxPi of (name * cid_schema) * typ
      | TypPiBox of (LF.ctyp_decl * depend) * typ
      | TypClo   of typ *  LF.msub

    and exp_chk =
      | Syn    of Loc.t option * exp_syn
      | Rec    of Loc.t option * name * exp_chk
      | Fun    of Loc.t option * name * exp_chk
      | CtxFun of Loc.t option * name * exp_chk
      | MLam   of Loc.t option * name * exp_chk
      | Pair   of Loc.t option * exp_chk * exp_chk     
      | LetPair of Loc.t option * exp_syn * (name * name * exp_chk) 
      | Box    of Loc.t option * LF.psi_hat * LF.normal
      | SBox   of Loc.t option * LF.psi_hat * LF.sub
      | Case   of Loc.t option * exp_syn * branch list

    and exp_syn =
      | Var    of offset
      | Const  of cid_prog
      | Apply  of Loc.t option * exp_syn * exp_chk
      | CtxApp of Loc.t option * exp_syn * LF.dctx
      | MApp   of Loc.t option * exp_syn * (LF.psi_hat * LF.normal)
      | Ann    of exp_chk * typ

    and branch =
      | BranchBox  of LF.mctx
(*          * (LF.dctx * LF.normal * (LF.msub * LF.mctx)) *)
          * (LF.psi_hat * LF.normal * LF.msub) 
          * exp_chk

      | BranchSBox of LF.mctx
          * (LF.dctx * LF.sub    * LF.dctx * (LF.msub * LF.mctx))
          * exp_chk


   type ctyp_decl = 
     | CTypDecl of name * typ
     | CTypDeclOpt of name
    
    type gctx = ctyp_decl LF.ctx
    type tclo = typ * LF.msub
  end


 (** Internal Signature Syntax *)
  module Sgn = struct

    type decl =
      | Typ    of cid_typ    * LF.kind
      | Const  of cid_term   * LF.typ
      | Schema of cid_schema * LF.schema
      | Rec    of cid_prog   * Comp.typ * Comp.exp_chk
      | Pragma of LF.prag

    type sgn = decl list

  end

end




(** External Syntax *)
module Ext = struct
  (** External LF Syntax *)
  module LF = struct

    type kind =
      | Typ     of Loc.t
      | ArrKind of Loc.t * typ      * kind
      | PiKind  of Loc.t * typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and ctyp_decl =
      | MDecl of Loc.t * name * typ  * dctx
      | PDecl of Loc.t * name * typ  * dctx
(*       | SDecl of Loc.t * name * dctx * dctx *)

    and typ =
      | Atom   of Loc.t * name * spine
      | ArrTyp of Loc.t * typ      * typ
      | PiTyp  of Loc.t * typ_decl * typ
      | Sigma of Loc.t * typ_rec

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
      | CoPVar of Loc.t * name * name * int * sub

    and spine =
      | Nil
      | App of Loc.t * normal * spine

    and sub =
      | EmptySub of Loc.t
      | Dot      of Loc.t * sub * front
      | Id       of Loc.t
      | CoId     of Loc.t * name 

    and front =
      | Head     of head
      | Normal   of normal

    and typ_rec =
      | SigmaLast of typ
      | SigmaElem of name * typ * typ_rec

    and tuple =
      | Last of normal
      | Cons of normal * tuple

    and dctx =
      | Null
      | CtxVar   of Loc.t * name
      | CoCtx    of Loc.t * name * name
      | DDec     of dctx * typ_decl

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of Loc.t * typ_decl ctx * typ_rec

    and schema =
      | Schema of sch_elem list


    and psi_elem = VarName of name | CoName of name * name
    and psi_hat = psi_elem list

    and mctx     = ctyp_decl ctx          

    and prag =
      | NamePrag of name * string * string option 
      | NotPrag

    and co_typ = CoTyp of name * name 

    and coercion   = co_branch list
    and co_branch  = CoBranch of typ_decl ctx * typ_rec * typ_rec option

  end


  (** External Computation Syntax *)
  module Comp = struct

    type typ =                                     (* Computation-level types *)
      | TypBox   of Loc.t * LF.typ  * LF.dctx      (* tau ::= A[Psi]          *)
(*    | TypSBox  of LF.dctx * LF.dctx              (\*    | Phi[Psi]      *\) *)
      | TypArr   of Loc.t * typ * typ              (*     | tau -> tau        *)
      | TypCross of Loc.t * typ * typ              (*     | tau * tau        *)
      | TypCtxPi of Loc.t * (name * name) * typ    (*     | Pi psi:(w)*. tau  *)
      | TypPiBox of Loc.t * LF.ctyp_decl * typ     (*     | Pi u::A[Psi].tau  *)

    and exp_chk =                            (* Computation-level expressions *)
       | Syn    of Loc.t * exp_syn                (*  e ::= i                 *)
       | Fun    of Loc.t * name * exp_chk         (*    | fn f => e           *)
       | CtxFun of Loc.t * name * exp_chk         (*    | FN f => e           *)
       | MLam   of Loc.t * name * exp_chk         (*    | mlam f => e         *)
       | Pair   of Loc.t * exp_chk * exp_chk      (*    | (e1 , e2)           *)
       | LetPair of Loc.t * exp_syn * (name * name * exp_chk) 
                                                  (*    | let (x,y) = i in e  *)
       | Box    of Loc.t * LF.psi_hat * LF.normal (*    | box (Psi hat. M)    *)
(*        | SBox   of LF.psi_hat * LF.sub *)
       | Case   of Loc.t * exp_syn * branch list  (*    | case i of branches *)

    and exp_syn =
       | Var    of Loc.t * name                   (*  i ::= x                 *)
       | Apply  of Loc.t * exp_syn * exp_chk      (*    | i e                 *)
       | CtxApp of Loc.t * exp_syn * LF.dctx      (*    | i [Psi]             *)
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal)
                                                  (*    | i [Psi hat. M]      *)
       | BoxVal of Loc.t * LF.dctx * LF.normal 
       | Ann    of Loc.t * exp_chk * typ          (*    | e : tau             *)

    and branch =
      | BranchBox of Loc.t * LF.mctx
          * (LF.dctx * LF.normal * (LF.typ * LF.dctx) option)
          * exp_chk

(*       | BranchSBox of LF.ctyp_decl LF.ctx *)
(*           * (LF.psi_hat * LF.sub    * (LF.dctx * LF.dctx)) *)
(*           * exp_chk *)

   type rec_fun = RecFun of name * typ * exp_chk
  end


  (** External Signature Syntax *)
  module Sgn = struct

    type decl =
      | Const    of Loc.t * name * LF.typ
      | Typ      of Loc.t * name * LF.kind
      | Schema   of Loc.t * name * LF.schema
      | Coercion of Loc.t * name * LF.co_typ * LF.coercion
      | Pragma   of Loc.t * LF.prag
      | Rec      of Loc.t * Comp.rec_fun list   
       

    type sgn = decl list

  end

end



(** Approximate Syntax *)
module Apx = struct

  (** Approximate LF Syntax *)
  module LF = struct

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
      | FMVar of name   * sub
      | FPVar of name   * sub
      | CoFPVar of cid_coercion * name * int * sub
      | CoPVar of cid_coercion * cvar * int * sub

    and spine =
      | Nil
      | App of normal * spine

    and sub =
      | EmptySub
      | Id
      | CoId  of Loc.t * cid_coercion
      | Dot   of front * sub

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
      | CoCtx    of cid_coercion * ctx_var       

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of typ_decl ctx * typ_rec

    and schema =
      | Schema of sch_elem list

    and psi_hat = (Int.LF.ctx_var) option * offset

    and co_typ = CoTyp of cid_schema * cid_schema

    and coercion   = co_branch list
    and co_branch  = CoBranch of typ_decl ctx * typ_rec * typ_rec option

  end


  (** Approximate Computation Syntax *)
  module Comp = struct

    type typ =
      | TypBox     of Loc.t * LF.typ  * LF.dctx
      | TypArr     of typ * typ
      | TypCross   of typ * typ
      | TypCtxPi   of (name * cid_schema) * typ
      | TypPiBox   of LF.ctyp_decl * typ

    and exp_chk =
       | Syn    of Loc.t * exp_syn
       | Fun    of Loc.t * name * exp_chk         (* fn   f => e         *)
       | CtxFun of Loc.t * name * exp_chk         (* FN   f => e         *)
       | MLam   of Loc.t * name * exp_chk         (* mlam f => e         *)
       | Pair   of Loc.t * exp_chk * exp_chk      (* (e1 , e2)           *)
       | LetPair of Loc.t * exp_syn * (name * name * exp_chk) 
                                                  (* let (x,y) = i in e  *)
       | Box    of Loc.t * LF.psi_hat * LF.normal (* box (Psi hat. M)    *)
       | Case   of Loc.t * exp_syn * branch list

    and exp_syn =
       | Var    of offset                                     (* x              *)
       | Const  of cid_prog                                   (* c              *)
       | Apply  of Loc.t * exp_syn * exp_chk                  (* i e            *)
       | CtxApp of Loc.t * exp_syn * LF.dctx                  (* i [Psi]        *)
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal) (* i [Psi hat. M] *)
       | BoxVal of Loc.t * LF.dctx * LF.normal                (* box (Psi. tR)  *)
       | Ann    of exp_chk * typ                              (* e : tau        *)

    and branch =
      | BranchBox of Loc.t * LF.ctyp_decl LF.ctx
          * (LF.dctx * LF.normal * (LF.typ * LF.dctx) option)
          * exp_chk

  end

end
