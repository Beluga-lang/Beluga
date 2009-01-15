(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
*)

open Syntax
open Id

(** Approximate Simple Syntax *)
module Apx : sig

  module LF : sig

    type kind =                     (* kinds                          *)
      | Typ                         (* K ::= type                     *)
      | PiKind of typ_decl * kind   (*   | Pi x:A.K                   *)

    and typ_decl =
      | TypDecl of name * typ

    and ctyp_decl =
      | MDecl of  name * typ  * dctx
      | PDecl of  name * typ  * dctx

    and sigma_decl =
      | SigmaDecl of name * typ_rec

    and typ =                       (* types                          *)
      | Atom  of cid_typ * spine    (* A ::= a M1 ... Mn              *)
      | PiTyp of typ_decl * typ     (*   | Pi x:A.B                   *)

    and typ_rec =
      | SigmaLast of typ
      | SigmaElem of name * typ * typ_rec

    and normal =                    (* normal terms                   *)
      | Lam  of name * normal       (* M ::= \x.M                     *)
      | Root of head * spine        (*   | h . S                      *)

    and head =
      | BVar  of offset             (* H ::= x                        *)
      | Const of cid_term           (*   | c                          *)
      | MVar  of offset * sub       (*   | u[s]                       *)
      | PVar  of offset * sub       (*   | p[s]                       *)
      | FVar  of name               (*   | X                          *)

    and spine =                     (* spine                          *)
      | Nil                         (* S ::= Nil                      *)
      | App of normal * spine       (*   | M . S                      *)

    and sub =                       (* Substitutions                  *)
      | EmptySub                    (* sigma ::= .                    *)
      | Id                          (*       | id                     *) 
      | Dot   of front * sub        (*       | Ft . s                 *)

    and front =                     (* Fronts:                        *)
      | Head of head                (* Ft ::= H                       *)
      | Obj  of normal              (*    | N                         *)


    and dctx =
      | Null
      | CtxVar   of offset 
      | DDec     of dctx * typ_decl

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of typ_decl ctx * sigma_decl

    and schema =
      | Schema of sch_elem list

    and psi_hat = Int.LF.cvar option * offset 
  end

  module Comp : sig

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
          * (LF.psi_hat * LF.normal * (LF.typ * LF.dctx))
          * exp_chk

  end

end

val recSgnDecl : Ext.Sgn.decl -> Int.Sgn.decl
