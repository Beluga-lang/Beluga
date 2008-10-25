(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)



open Id



(** External Syntax *)
module Ext : sig

  module Loc : Camlp4.Sig.Loc

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
module Int : sig

  type kind =
    | Typ
    | PiKind of typ_decl * kind

  and typ_decl =
    | TypDecl of name * typ

  and sigma_decl =
    | SigmaDecl of name * typ_rec

  and ctx_decl =
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

  type nclo     = normal * sub
  type tclo     = typ    * sub
  type trec_clo = typ_rec * sub
  type mctx     = ctx_decl ctx



  (*------------------------------------------------------------------------ *)

  val dctxToHat   : dctx -> psi_hat

  val ctxDec      : dctx -> int -> typ_decl
  val ctxSigmaDec : dctx -> int -> sigma_decl
  val ctxVar      : dctx -> cvar option

  val mctxMDec    : mctx -> int -> typ * dctx
  val mctxPDec    : mctx -> int -> typ * dctx

  val newMVar     : dctx * typ -> cvar
  val newPVar     : dctx * typ -> cvar

end
