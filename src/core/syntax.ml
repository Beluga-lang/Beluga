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

    and typ_decl =                              (* LF Declarations                *)
      | TypDecl of name * typ                   (* D := x:A                       *)
      | TypDeclOpt of name                      (*   |  x:_                       *)

    and ctyp_decl =                             (* Contextual Declarations        *)
      | MDecl of name * typ  * dctx             (* D ::= u::A[Psi]                *)
      | PDecl of name * typ  * dctx             (*   |   p::A[Psi]                *)
      | SDecl of name * dctx * dctx             (*   |   s::A[Psi]                *)
      | CDecl of name * cid_schema 
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
     | MV   of offset                          (*    | u//u | p//p               *)
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

    and mm_var  =                               (* Meta² Variables                *)
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
      | CInst  of dctx option ref * cid_schema * mctx * mctx
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
      | _ -> raise Not_found
  end


 (** Internal Computation Syntax *)
  module Comp = struct

   type depend =  
     | Implicit
     | Explicit

   type typ =
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
      | Box    of Loc.t option * LF.psi_hat * LF.normal
      | SBox   of Loc.t option * LF.psi_hat * LF.sub
      | Case   of Loc.t option * exp_syn * branch list
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


    and branch =
      | BranchBox  of LF.mctx * LF.mctx
          * (LF.dctx * LF.normal * LF.msub * LF.csub) 
          * exp_chk

      | BranchSBox of LF.mctx * LF.mctx
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
      | SDecl of Loc.t * name * dctx * dctx
      | CDecl of Loc.t * name * name

    and typ =
      | Atom   of Loc.t * name * spine
      | ArrTyp of Loc.t * typ      * typ
      | PiTyp  of Loc.t * typ_decl * typ
      | Sigma of Loc.t * typ_rec
      | Ctx   of Loc.t * dctx 

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

    and typ_rec =
      | SigmaLast of typ
      | SigmaElem of name * typ * typ_rec

    and tuple =
      | Last of normal
      | Cons of normal * tuple

    and dctx =
      | Null
      | CtxVar   of Loc.t * name
      | DDec     of dctx * typ_decl

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of Loc.t * typ_decl ctx * typ_rec

    and schema =
      | Schema of sch_elem list

    and psi_hat  = name list

    and mctx     = ctyp_decl ctx          

    and prag =
      | NamePrag of name * string * string option 
      | NotPrag

  end


  (** External Computation Syntax *)
  module Comp = struct

   type depend =  
     | Implicit
     | Explicit

    type typ =                                     (* Computation-level types *)
      | TypBox   of Loc.t * LF.typ  * LF.dctx      (* tau ::= A[Psi]          *)
      | TypSub   of Loc.t * LF.dctx * LF.dctx      (*    | Phi[Psi]          *)
      | TypArr   of Loc.t * typ * typ              (*     | tau -> tau        *)
      | TypCross of Loc.t * typ * typ              (*     | tau * tau         *)
      | TypCtxPi of Loc.t * (name * name * depend) * typ 
                                                   (*     | Pi psi:(w)*. tau  *)
      | TypPiBox of Loc.t * LF.ctyp_decl * typ     (*     | Pi u::A[Psi].tau  *)
      | TypBool                                    (*     | Bool              *)

    and exp_chk =                            (* Computation-level expressions *)
       | Syn    of Loc.t * exp_syn                (*  e ::= i                 *)
       | Fun    of Loc.t * name * exp_chk         (*    | fn f => e           *)
       | CtxFun of Loc.t * name * exp_chk         (*    | FN f => e           *)
       | MLam   of Loc.t * name * exp_chk         (*    | mlam f => e         *)
       | Pair   of Loc.t * exp_chk * exp_chk      (*    | (e1 , e2)           *)
       | LetPair of Loc.t * exp_syn * (name * name * exp_chk) 
                                                  (*    | let (x,y) = i in e  *)
       | Box    of Loc.t * LF.psi_hat * LF.normal (*    | box (Psi hat. M)    *)
       | SBox   of Loc.t * LF.psi_hat * LF.sub 
       | Case   of Loc.t * exp_syn * branch list  (*    | case i of branches   *)
       | If of Loc.t * exp_syn * exp_chk * exp_chk(*    | if i then e1 else e2 *)   

    and exp_syn =
       | Var    of Loc.t * name                   (*  i ::= x                 *)
       | Apply  of Loc.t * exp_syn * exp_chk      (*    | i e                 *)
       | CtxApp of Loc.t * exp_syn * LF.dctx      (*    | i [Psi]             *)
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal)
                                                  (*    | i [Psi hat. M]      *)
       | MAnnApp   of Loc.t * exp_syn * (LF.dctx * LF.normal) (* i [Psi. M]     *)
       | BoxVal of Loc.t * LF.dctx * LF.normal 
       | Ann    of Loc.t * exp_chk * typ          (*    | e : tau             *)
       | Equal  of Loc.t * exp_syn * exp_syn
       | Boolean of Loc.t * bool


    and branch =
      | BranchBox of Loc.t * LF.mctx 
          * (LF.dctx * LF.normal * (LF.typ * LF.dctx) option)
          * exp_chk

       | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx 
           * (LF.dctx * LF.sub    * LF.dctx option) 
           * exp_chk 

   type rec_fun = RecFun of name * typ * exp_chk

(* Useful for debugging the parser, but there should be a better place for them... *)
   let rec synToString = function
       | Var    (_loc,  _) -> "Var"
       | Apply  (_loc,  syn, chk) -> "Apply(" ^ synToString syn ^ ", " ^ chkToString chk ^ ")"
       | CtxApp (_loc,  syn, _dctx) -> "CtxApp(" ^ synToString syn ^ ", _dctx)"
       | MApp   (_loc,  syn, (_, _)) -> "MApp(" ^ synToString syn ^ ", ...)"
       | BoxVal (_loc, _, _) -> "BoxVal(...)"
       | Ann    (_loc, chk, _) -> "Ann(" ^ chkToString chk ^ ", _)"
       | Equal   (_loc,  syn1, syn2) -> "Equal("  ^ synToString syn1 ^ " == " ^ synToString syn2 ^ ")"
       | Boolean (_loc, _) -> "Boolean(_)"
      
   and chkToString = function
       | Syn     (_loc,  syn) -> "Syn(" ^ synToString syn ^ ")"
       | Fun     (_loc, _, chk) -> "Fun(_, " ^ chkToString chk ^ ")"
       | CtxFun  (_loc, _, chk) ->  "CtxFun(_, " ^ chkToString chk ^ ")"
       | MLam    (_loc, _, chk) ->  "MLam(_, " ^ chkToString chk ^ ")"
       | Pair    (_loc, chk1, chk2) ->  "Fun(_, " ^ chkToString chk1 ^ ", " ^ chkToString chk2 ^ ")"
       | LetPair (_loc, syn, (_, _, chk)) -> "LetPair(" ^ synToString syn ^", (_, _, " ^ chkToString chk ^ "))"
       | Box     (_loc, _, _) -> "Box(...)"
       | Case    (_loc, syn, _) -> "Case(" ^ synToString syn ^ " of ...)"
       | If      (_loc, syn, chk1, chk2) -> "If(" ^ synToString syn ^ " Then " ^  chkToString chk1 ^ " Else " ^ chkToString chk2 ^ ")"

  end


  (** External Signature Syntax *)
  module Sgn = struct

    type decl =
      | Const    of Loc.t * name * LF.typ
      | Typ      of Loc.t * name * LF.kind
      | Schema   of Loc.t * name * LF.schema
      | Pragma   of Loc.t * LF.prag
      | Rec      of Loc.t * Comp.rec_fun list   
      | Val      of Loc.t * name * Comp.typ option * Comp.exp_syn 
       

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
      | MDeclOpt of name
      | SDecl of name * dctx * dctx
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
      | FMVar of name   * sub
      | FPVar of name   * sub

    and spine =
      | Nil
      | App of normal * spine

    and sub =
      | EmptySub
      | Id
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

  end


  (** Approximate Computation Syntax *)
  module Comp = struct

   type depend =  
     | Implicit
     | Explicit

    type typ =
      | TypBox     of Loc.t * LF.typ  * LF.dctx
      | TypSub     of Loc.t * LF.dctx  * LF.dctx
      | TypArr     of typ * typ
      | TypCross   of typ * typ
      | TypCtxPi   of (name * cid_schema * depend) * typ
      | TypPiBox   of LF.ctyp_decl * typ
      | TypBool

    and exp_chk =
       | Syn    of Loc.t * exp_syn
       | Fun    of Loc.t * name * exp_chk         (* fn   f => e         *)
       | CtxFun of Loc.t * name * exp_chk         (* FN   f => e         *)
       | MLam   of Loc.t * name * exp_chk         (* mlam f => e         *)
       | Pair   of Loc.t * exp_chk * exp_chk      (* (e1 , e2)           *)
       | LetPair of Loc.t * exp_syn * (name * name * exp_chk) 
                                                  (* let (x,y) = i in e  *)
       | Box    of Loc.t * LF.psi_hat * LF.normal (* box (Psi hat. M)    *)
       | SBox   of Loc.t * LF.psi_hat * LF.sub    (* box (Psi hat. M)    *)
       | Case   of Loc.t * exp_syn * branch list
       | If      of Loc.t * exp_syn * exp_chk * exp_chk

    and exp_syn =
       | Var    of offset                                     (* x              *)
       | Const  of cid_prog                                   (* c              *)
       | Apply  of Loc.t * exp_syn * exp_chk                  (* i e            *)
       | CtxApp of Loc.t * exp_syn * LF.dctx                  (* i [Psi]        *)
       | MApp   of Loc.t * exp_syn * (LF.psi_hat * LF.normal) (* i [Psi_hat. M] *)
       | MAnnApp   of Loc.t * exp_syn * (LF.dctx * LF.normal) (* i [Psi. M]     *)
       | BoxVal of Loc.t * LF.dctx * LF.normal                (* box (Psi. tR)  *)
       | Ann    of exp_chk * typ                              (* e : tau        *)
       | Equal  of Loc.t  * exp_syn * exp_syn
       | Boolean of Loc.t * bool


    and branch =
      | BranchBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx 
          * (LF.dctx * LF.normal * (LF.typ * LF.dctx) option)
          * exp_chk
      | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx 
          * (LF.dctx * LF.sub * LF.dctx option)
          * exp_chk

  end

end
