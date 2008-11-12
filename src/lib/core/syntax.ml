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
      | App of normal * spine

    type sgn_decl =
      | SgnTyp   of Loc.t * name * kind
      | SgnConst of Loc.t * name * typ

  end

  module Comp = struct
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
      | PDecl of name * typ  * dctx        (*   |  p::A[Psi]                 *)
      | SDecl of name * dctx * dctx        (*   |  s::A[Psi]                 *)
                                           (* Potentially, A is Sigma type ? *)

    and typ =                              (* LF level                       *)
      | Atom  of cid_typ * spine           (* A ::= a M1 ... Mn              *)
      | PiTyp of typ_decl * typ            (*   | Pi x:A.B                   *)
      | TClo  of typ * sub                 (*   | TClo(A,s)                  *)
      | TMClo of typ * msub                (*   | TMClo (A, t)               *)

    and normal =                           (* normal terms                   *)
      | Lam  of name * normal              (* M ::= \x.M                     *)
      | Root of head * spine               (*   | h . S                      *)
      | Clo  of (normal * sub)             (*   | Clo(N,s)                   *)
      | MClo of (normal * msub)            (*   | MClo(M, t)                 *)

    and head =
      | BVar  of offset                    (* H ::= x                        *)
      | Const of cid_term                  (*   | c                          *)
      | MVar  of cvar * sub                (*   | u[s]                       *)
      | PVar  of cvar * sub                (*   | p[s]                       *)
      | AnnH  of head * typ                (*   | (H:A)                      *)
      | Proj  of head * int                (*   | #k(x) | #k(p[s])           *)

    and spine =                            (* spine                          *)
      | Nil                                (* S ::= Nil                      *)
      | App  of normal * spine             (*   | M . S                      *)
      | SClo of spine * sub                (*   | SClo(S,s)                  *)
      | SMClo of spine * msub              (*   | SMClo(S,t)                 *)

    and sub =                              (* Substitutions                  *)
      | Shift of offset                    (* sigma ::= ^n                   *)
      | SVar  of cvar * sub                (*       | s[sigma]               *)
      | Dot   of front * sub               (*       | Ft . s                 *)

    and front =                            (* Fronts:                        *)
      | Head of head                       (* Ft ::= H                       *)
      | Obj  of normal                     (*    | N                         *)
      | Undef                              (*    | _                         *)

    and msub =                             (* Contextual substitutions       *)
      | MShift of offset                   (* theta ::= ^n                   *)
      | MDot   of mfront * msub            (*       | MFt . theta            *) 

    and mfront =                           (* Fronts:                        *)
      | Id   of offset                     (* MFt ::= k                      *)
      | MObj of psi_hat * normal           (*    | Psihat.N                  *)
      | PObj of psi_hat * offset           (*    | Psihat.x                  *)


    and cvar =                             (* Contextual Variables           *)
      | Offset of offset                   (* Bound Variables                *)
      | Inst   of normal option ref * dctx * typ * cnstr list ref  
          (* D ; Psi |- M <= A 
             provided constraint *)
      | PInst  of head   option ref * dctx * typ * cnstr list ref  
          (* D ; Psi |- H => A 
             provided constraint *)
      | CInst  of dctx   option ref * schema
          (* D |- Psi : schema   *)

    and constrnt =                         (* Constraint                     *)
      | Solved                             (* constraint ::= solved          *)
      | Eqn of psi_hat * normal * normal   (*            | Psi |-(M1 == M2)  *)
      | Eqh of psi_hat * head * head       (*            | Psi |-(H1 == H2)  *)

    and cnstr = constrnt ref

    and dctx =                             (* LF Context                     *)
      | Null                               (* Psi ::= .                      *)
      | CtxVar   of cvar                   (* | psi                          *)
      | DDec     of dctx * typ_decl        (* | Psi, x:A                     *)
      | SigmaDec of dctx * sigma_decl      (* | Psi, x:Sigma x1:A1...xn:An.A *)

    and 'a ctx =                           (* Generic context declaration    *)
      | Empty                              (* Context                        *)
      | Dec of 'a ctx * 'a                 (* C ::= Empty                    *)
                                           (* | C, x:'a                      *)

    and sch_elem =                         (* Schema Element                 *)
      | SchElem of typ ctx * sigma_decl    (* Pi    x1:A1 ... xn:An. 
                                              Sigma y1:B1 ... yk:Bk. B       *)
                                           (* Sigma-types not allowed in Ai  *)

    and schema =
      | Schema of sch_elem list

    and psi_hat = cvar option * offset     (* Psihat ::=         *)
                                           (*        | psi       *)
                                           (*        | .         *)
                                           (*        | Psihat, x *)

    and typ_rec = typ list                 (* Sigma x1:A1 ... xk:Ak          *)
                                           (* should not be a list ... -bp   *)

    type sgn_decl =
      | SgnTyp   of cid_typ  * kind
      | SgnConst of cid_term * typ



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
                                                           (* Computational level expressions *)
    type exp =                                             (* Expressions :                   *)
      | Var     of offset                                  (* e := x                          *)
      | Rec     of name       * exp                        (*    | rec f => e                 *)
      | Fun     of name       * exp                        (*    | fn x => e                  *)
      | CtxFun  of name       * exp                        (*    | FN psi => e                *)
      | MLam    of name       * exp                        (*    | mlam u => e                *)
      | Box     of LF.psi_hat * LF.normal                  (*    | box Psihat.M               *)
      | SBox    of LF.psi_hat * LF.sub                     (*    | sbox Psihat.s              *)
      | Pack    of LF.psi_hat * LF.normal * exp            (*    | <Psihat.M , e>             *)
      | Apply   of exp        * exp                        (*    | e e'                       *)
      | CtxApp  of exp        * LF.dctx                    (*    | e <Psi>                    *)
      | MApp    of exp        * (LF.psi_hat * LF.normal)   (*    | e <Psihat.M>               *)
      | Ann     of exp        * typ                        (*    | e : tau                    *)
      | Case    of exp        * branch list                (*    | case e of b1 => e1 ...     *)
      | Let     of exp        * (name * exp)               (*    | let x = e in e'            *)
      | LetPack of exp        * (name * name * exp)        (*    | let pack <u,x> = e in e'   *)

    and branch =                                  (* Branches                        *)
      | BBranch of LF.ctyp_decl LF.ctx            (* b := Pibox D.                   *)
                 * (LF.psi_hat * LF.normal * typ) (*      box(Psihat.M) : A[Psi]     *)
                 * exp                            (*      => e                       *)

      | SBranch of LF.ctyp_decl LF.ctx            (*    | Pibox D.                   *)
                 * (LF.psi_hat * LF.sub    * typ) (*      sbox(Psihat.s) : Phi[Psi]  *)
                 * exp                            (*      => e                       *)
     
     and typ =                                    (* Computational level types       *)          
       | BTyp     of typ  * LF.dctx               (* tau := A[Psi]                   *)
       | STyp     of LF.dctx * LF.dctx            (*     |  Psi[Phi]                 *)
       | Arrow    of typ  * typ                   (*     |  tau -> tau'              *)
       | CtxPi    of (name * LF.schema) * typ     (*     | Pi g::W.tau               *)
       | PiBox    of LF.ctyp_decl * typ           (*     | Pibox  u::A[Psi].tau      *)
       | SigmaBox of LF.ctyp_decl * typ           (*     | Sigmabox u::A[Psi].tau    *)

  end

end
