(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)



open Id



(** External Syntax *)
module Ext = struct

  module Loc = Camlp4.PreCast.Loc

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



(** Internal Syntax *)
module Int = struct

  type kind =
    | Typ
    | PiKind of typ_decl * kind

  and typ_decl =                         (* LF Declarations                *)
    | TypDecl of name * typ              (* D := x:A                       *)

  and sigma_decl =
    | SigmaDecl of name * typ_rec        (* x:Sigma x1:A1 .... xk:Ak       *)

  and ctx_decl =                         (* Contextual Declarations        *)
    | MDecl of name * typ  * dctx        (* D ::= u::A[Psi]                *)
    | PDecl of name * typ  * dctx        (*   |  p::A[Psi]                 *)
    | SDecl of name * dctx * dctx        (*   |  s::A[Psi]                 *)
                                         (* Potentially, A is Sigma type ? *)

  and typ =                              (* LF level                       *)
    | Atom  of cid_typ * spine           (* A ::= a M1 ... Mn              *)
    | PiTyp of typ_decl * typ            (*   | Pi x:A.B                   *)
    | TClo  of typ * sub                 (*   | TClo(A,s)                  *)

  and normal =                           (* normal terms                   *)
    | Lam  of name * normal              (* M ::= \x.M                     *)
    | Root of head * spine               (*   | h . S                      *)
    | Clo  of (normal * sub)             (*   | Clo(N,s)                   *)

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

  and sub =                              (* Substitutions                  *)
    | Shift of offset                    (* sigma ::= ^n                   *)
    | SVar  of cvar * sub                (*       | s[sigma]               *)
    | Dot   of front * sub               (*       | Ft . s                 *)

  and front =                            (* Fronts:                        *)
    | Head of head                       (* Ft ::= H                       *)
    | Obj  of normal                     (*    | N                         *)
    | Undef                              (*    | _                         *)

  and cvar =                                                     (* Contextual Variables                  *)
    | Offset of offset                                           (* Bound Variables                       *)
    | Inst   of normal option ref * dctx * typ * cnstr list ref  (* D ; Psi |- M <= A provided constraint *)
    | PInst  of head   option ref * dctx * typ * cnstr list ref  (* D ; Psi |- H => A                     *)
    | CInst  of dctx   option ref * schema                       (* D       |- Psi : schema               *)

  and constrnt =                         (* Constraint                     *)
    | Solved                             (* constraint ::= solved          *)
    | Eqn of psi_hat * normal * normal   (*            | Psi |-(M1 == M2)  *)
    | Eqh of psi_hat * head * head       (*            | Psi |-(H1 == H2)  *)

  and cnstr = constrnt ref

  and dctx =                             (* LF Context                              *)
    | Null                               (* Psi, Phi ::= Null                       *)
    | CtxVar   of cvar                   (*          | psi                          *)
    | DDec     of dctx * typ_decl        (*          | Psi, x:A                     *)
    | SigmaDec of dctx * sigma_decl      (*          | Psi, x:Sigma x1:A1...xn:An.A *)

  and 'a ctx =                           (* Generic context declaration    *)
    | Empty                              (* Context                        *)
    | Dec of 'a ctx * 'a                 (* C ::= Empty                    *)
                                         (*   | C, x:'a                    *)

  and sch_elem =                         (* Schema Element                               *)
    | SchElem of typ ctx * sigma_decl    (* Pi x1:A1 ... xn:An. Sigma y1:B1 ... yk:Bk. B *)
                                         (* Sigma-types not allowed in Ai                *)

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

  type nclo     = normal  * sub          (* Ns = N[s]                      *)
  type tclo     = typ     * sub          (* As = A[s]                      *)
  type trec_clo = typ_rec * sub          (* Arec[s]                        *)
  type mctx     = ctx_decl ctx           (* Modal Context  D: CDec ctx     *)
                                         (* Comp. Context  G: VDec ctx     *)
                                         (* CtxVar Context O: CtxDec ctx   *)

end
