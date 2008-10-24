(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
   @author Darin Morrison
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
    | Clo  of normal * sub

  and head =
    | BVar  of offset
    | Const of cid_term
    | MVar  of cvar * sub
    | PVar  of cvar * sub
    | AnnH  of head * typ
    | Proj  of head * int

  and spine =
    | Nil
    | App  of normal * spine
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

  type nclo     = normal  * sub
  type tclo     = typ     * sub
  type trec_clo = typ_rec * sub
  type mctx     = ctx_decl ctx



  (* Should consider moving the following stuff out into it's own
     module, e.g., Subst -dwm *)

  (**************************)
  (* Explicit Substitutions *)
  (**************************)


  (* id = ^0 
     
     Invariant:

        Psi |- id : Psi      id is patsub

     Note: we do not take into account weakening here. 
  *)
  let id = Shift 0


  (* shift = ^1
  
     Invariant:

        Psi, x:A |- ^ : Psi      ^ is patsub

  *)
  let shift = Shift 1


  (* invShift = ^-1 = _.^0

     Invariant:

        G |- ^-1 : G, V      ^-1 is patsub

  *)
  let invShift = Dot (Undef, id)

(*
  let comp s1 s2 = match (s1, s2) with
    | (Shift 0, s) -> s
    (* next line is an optimization *)
    (* roughly 15% on standard suite for Twelf 1.1 *)
    (* Sat Feb 14 10:15:16 1998 -fp *)
    | (s, Shift 0) -> s
    | (SVar(s,tau), s2) -> SVar(s, comp tau s2)
      (* (s1, SVar(s,tau)) => undefined ? -bp *)
    | (Shift (n), Dot (Ft, s)) -> comp (Shift (n-1)) s
    | (Shift (n), Shift (m)) -> Shift (n+m)
    | (Dot (Ft, s), s') -> Dot (frontSub Ft s', comp s s')

    (* comp(s[tau], Shift(k)) = s[tau]
       where s :: Psi[Phi]  and |Psi| = k 

       comp(s[tau], Shift(k)) = Dot(Id(1), ... Dot(Id(k0), s[tau]))
       where s :: Psi[Phi]  and |Psi| = k'
       k = k' + k0  
     *)
*)

  let bvarSub = assert false

  let frontSub = assert false

  let decSub = assert false

  let comp = assert false

  let dot1 = assert false

  let invDot1 = assert false

  let isPatSub = assert false

  (***************************)
  (* Inverting Substitutions *)
  (***************************)

  let invert = assert false

  let strengthen = assert false

  let isId = assert false

  let compInv = assert false

  (*------------------------------------------------------------------------ *)

  let dctxToHat = assert false

  let ctxDec = assert false

  let ctxSigmaDec = assert false

  let ctxVar = assert false

  let mctxMDec = assert false

  let mctxPDec = assert false

  let constType = assert false

  let tconstKind = assert false

  let newMVar = assert false

  let newPVar = assert false

end
