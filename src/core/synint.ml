(** Internal Syntax *)
(** Internal LF Syntax *)
open Id
open Pragma


module Loc = Camlp4.PreCast.Loc

module LF = struct

  type depend =
    | No       
    | Maybe        
    

  type kind =
    | Typ
    | PiKind of (typ_decl * depend) * kind
  
  and typ_decl =                              (* LF Declarations                *)
    | TypDecl of name * typ                   (* D := x:A                       *)
    | TypDeclOpt of name                      (*   |  x:_                       *)

  and ctyp_decl =                             (* Contextual Declarations        *)
    | MDecl of name * typ  * dctx             (* D ::= u::A[Psi]                *)
    | PDecl of name * typ  * dctx             (*   |   p::A[Psi]                *)
    | SDecl of name * dctx * dctx             (*   |   s::A[Psi]                *)
    | CDecl of name * cid_schema * depend
    | MDeclOpt of name 
    | PDeclOpt of name 
    | CDeclOpt of name 

                                              (* Potentially, A is Sigma type? *)

  and typ =                                   (* LF level                       *)
    | Atom  of Loc.t option * cid_typ * spine (* A ::= a M1 ... Mn              *)
    | PiTyp of (typ_decl * depend) * typ      (*   | Pi x:A.B                   *)
    | Sigma of typ_rec
    | TClo  of (typ * sub)                    (*   | TClo(A,s)                  *)


  and normal =                                (* normal terms                   *)
    | Lam  of Loc.t option * name * normal    (* M ::= \x.M                     *)
    | Root of Loc.t option * head * spine     (*   | h . S                      *)
    | Clo  of (normal * sub)                  (*   | Clo(N,s)                   *)
    | Tuple of Loc.t option * tuple

  and head =
    | BVar  of offset                         (* H ::= x                        *)
    | Const of cid_term                       (*   | c                          *)
    | MMVar of mm_var * (msub * sub)          (*   | u[t ; s]                   *)
    | MVar  of cvar * sub                     (*   | u[s]                       *)
    | PVar  of cvar * sub                     (*   | p[s]                       *)
    | AnnH  of head * typ                     (*   | (H:A)                      *)
    | Proj  of head * int                     (*   | x.k | #p.k s               *)

    | FVar  of name                           (* free variable for type 
                                                 reconstruction                 *)
    | FMVar of name * sub                     (* free meta-variable for type 
                                                 reconstruction                 *)
    | FPVar of name * sub                     (* free parameter variable for type
                                                reconstruction                 *)

  and spine =                                 (* spine                          *)
    | Nil                                     (* S ::= Nil                      *)
    | App  of normal * spine                  (*   | M . S                      *)
    | SClo of (spine * sub)                   (*   | SClo(S,s)                  *)

  and sub =                                   (* Substitutions                  *)
    | Shift of ctx_offset * offset            (* sigma ::= ^(psi,n)             *)
    | SVar  of cvar * sub                     (*       | s[sigma]               *)
    | FSVar of name * sub                     (*       | s[sigma]               *)
    | Dot   of front * sub                    (*       | Ft . s                 *)

  and front =                                 (* Fronts:                        *)
    | Head of head                            (* Ft ::= H                       *)
    | Obj  of normal                          (*    | N                         *)
    | Undef                                   (*    | _                         *)

                                             (* Contextual substitutions       *) 
 and mfront =                                (* Fronts:                        *)
   | MObj of psi_hat * normal                (* Mft::= Psihat.N                *)
   | PObj of psi_hat * head                  (*    | Psihat.p[s] | Psihat.x    *)
   | CObj of dctx                            (*    | Psi                       *)         
   | MV   of offset                          (*    | u//u | p//p | psi/psi     *)
   | MUndef

 and msub =                                  (* Contextual substitutions       *)
   | MShift of int                           (* theta ::= ^n                   *)
   | MDot   of mfront * msub                 (*       | MFt . theta            *)

 and csub =                                  (* Context substitutions          *)
   | CShift of int                           (* delta ::= ^n                   *)
   | CDot   of dctx * csub                   (*       | cPsi .delta            *)

 and ctx_offset = 
    | CtxShift of ctx_var
    | NoCtxShift
    | NegCtxShift of ctx_var

  and cvar =                                  (* Contextual Variables           *)
    | Offset of offset                        (* Bound Variables                *)
    | Inst   of normal option ref * dctx * typ * cnstr list ref
        (* D ; Psi |- M <= A
           provided constraint *)
    | PInst  of head   option ref * dctx * typ * cnstr list ref
        (* D ; Psi |- H => A
           provided constraint *)

  and mm_var  =                               (* Meta^2 Variables                *)
    | MInst   of normal option ref * mctx * dctx * typ * cnstr list ref
        (* D ; Psi |- M <= A
           provided constraint *)


  and tvar =
    | TInst   of typ option ref * dctx * kind * cnstr list ref

  and typ_free_var = Type of typ | TypVar of tvar

  and constrnt =                             (* Constraint                     *)
    | Queued                                 (* constraint ::= Queued          *)
    | Eqn of mctx * dctx * normal * normal
                                             (*            | Psi |-(M1 == M2)  *)
    | Eqh of mctx * dctx * head * head       (*            | Psi |-(H1 == H2)  *)

  and cnstr = constrnt ref

  and dctx =                                 (* LF Context                     *)
    | Null                                   (* Psi ::= .                      *)
    | CtxVar   of ctx_var                    (* | psi                          *)
    | DDec     of dctx * typ_decl            (* | Psi, x:A   or x:block ...    *)

  and ctx_var = 
    | CtxName   of name
    | CtxOffset of offset
    | CInst  of dctx option ref * cid_schema * mctx * mctx (* delete both mctx
							      contexts *)
        (* D |- Psi : schema   *)

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
  
  
  and typ_rec =    (* Sigma x1:A1 ... xn:An. B *)
    |  SigmaLast of typ                             (* ... . B *)
    |  SigmaElem of name * typ * typ_rec            (* xk : Ak, ... *)

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and mctx = ctyp_decl ctx          (* Modal Context  D: CDec ctx     *)


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

  (* val blockLength : typ_rec -> int *)
  let rec blockLength = function
    | SigmaLast _ -> 1
    | SigmaElem(_x, _tA, recA) -> 1 + blockLength recA

  (* getType traverses the typ_rec from left to right;
     target is relative to the remaining suffix of the type 

     getType head s_recA target j = (tA, s')
     
     if  Psi(head) = Sigma recA'
         and [s]recA is a suffix of recA'
     then
         Psi |- [s']tA  <= type

     CLIENTS: pass 1 for the last argument j

    (* getType head s_recA target 1 *)
    val getType : head -> trec_clo -> int -> int -> tclo
  *)
  let rec getType head s_recA target j = match (s_recA, target) with
    | ((SigmaLast lastA, s), 1) ->
        (lastA, s)
    
    | ((SigmaElem (_x, tA, _recA), s), 1) -> 
        (tA, s)
    
    | ((SigmaElem (_x, _tA, recA), s), target) ->
        let tPj = Proj (head, j) in
          getType head (recA, Dot (Head tPj, s)) (target - 1) (j + 1)
    
    | _ -> raise Not_found
end



(** Internal Computation Syntax *)
module Comp = struct

 type depend =  
   | Implicit   (* Maybe *)
   | Explicit   (* No *)

 type  kind = 
   | Ctype of Loc.t
   | PiKind  of Loc.t option * (LF.ctyp_decl * depend) * kind

 type meta_typ = 
   | MetaTyp of LF.typ * LF.dctx
   | MetaSchema of cid_schema 

 type meta_obj = 
   | MetaCtx of Loc.t option * LF.dctx 
   | MetaObj of Loc.t option * LF.psi_hat * LF.normal
   | MetaObjAnn of Loc.t option * LF.dctx * LF.normal

 type meta_spine = 
   | MetaNil 
   | MetaApp of meta_obj * meta_spine
   (* MetaSClo of meta_spine * msub *)

 type typ =
   | TypBase of Loc.t option * cid_comp_typ * meta_spine
   | TypBox   of Loc.t option * LF.typ  * LF.dctx
   | TypSub   of Loc.t option * LF.dctx * LF.dctx
   | TypArr   of typ * typ
   | TypCross of typ * typ
   | TypCtxPi of (name * cid_schema * depend) * typ
   | TypPiBox of (LF.ctyp_decl * depend) * typ
   | TypClo   of typ *  LF.msub
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
   | Syn    of Loc.t option * exp_syn
   | Rec    of Loc.t option * name * exp_chk
   | Fun    of Loc.t option * name * exp_chk
   | CtxFun of Loc.t option * name * exp_chk
   | MLam   of Loc.t option * name * exp_chk
   | Pair   of Loc.t option * exp_chk * exp_chk     
   | LetPair of Loc.t option * exp_syn * (name * name * exp_chk) 
   | Let    of Loc.t option * exp_syn * (name * exp_chk)
   | Box    of Loc.t option * LF.psi_hat * LF.normal
   | SBox   of Loc.t option * LF.psi_hat * LF.sub
   | Case   of Loc.t option * case_pragma * exp_syn * branch list
   | If     of Loc.t option * exp_syn * exp_chk * exp_chk
   | Value  of value 

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

 and pattern = 
   | PatEmpty  of Loc.t * LF.dctx 
   | PatMetaObj of Loc.t option * meta_obj
   | PatConst of Loc.t * cid_comp_const * pattern_spine
   | PatFVar   of Loc.t * name
   | PatVar   of Loc.t * offset
   | PatPair  of Loc.t * pattern * pattern
   | PatTrue  of Loc.t 
   | PatFalse of Loc.t 
   | PatAnn   of Loc.t * pattern * typ

 and pattern_spine = 
   | PatNil
   | PatApp of Loc.t * pattern * pattern_spine 
  
  and branch =
    | EmptyBranch of Loc.t * LF.ctyp_decl LF.ctx *  LF.ctyp_decl LF.ctx  
        * pattern * (LF.msub * LF.csub)
    | Branch of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx  
        * pattern * (LF.msub * LF.csub) * exp_chk 

    | BranchBox of LF.mctx * LF.mctx
        * (LF.dctx * branch_pattern * LF.msub * LF.csub)

    | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx 
        * (LF.dctx * LF.sub * LF.msub * LF.csub)
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
    | CompTyp  of Loc.t * name * Comp.kind
    | CompConst of Loc.t * name * Comp.typ
    | CompTypAbbrev of Loc.t * name * Comp.kind * Comp.typ
    | Schema of cid_schema * LF.schema
    | Rec    of cid_prog   * Comp.typ * Comp.exp_chk
    | Pragma of LF.prag

  type sgn = decl list

end


