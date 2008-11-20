(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)



open Store
open Store.Cid
open Syntax



let rec internalize_sgn_decl = function
  | Ext.LF.SgnTyp (_, a, k)   ->
      let k' = internalize_kind (BVar.create ()) k in
      let a' = Typ.add (Typ.mk_entry a k') in
        Int.LF.SgnTyp (a', k')

  | Ext.LF.SgnConst (_, c, a) ->
      let a' = internalize_typ (BVar.create ()) a in
      let c' = Term.add (Term.mk_entry c a') in
        Int.LF.SgnConst (c', a')



and internalize_kind ctx = function
  | Ext.LF.Typ _                             -> Int.LF.Typ

  | Ext.LF.ArrKind (_, a, k)                 ->
      let x    = Id.mk_name None
      and a'   = internalize_typ  ctx  a in
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let k'   = internalize_kind ctx' k in
        Int.LF.PiKind (Int.LF.TypDecl (x, a'), k')

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let a'   = internalize_typ  ctx  a
      and ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let k'   = internalize_kind ctx' k in
        Int.LF.PiKind (Int.LF.TypDecl (x, a'), k')



and internalize_typ ctx = function
  | Ext.LF.Atom (_, a, ms)      ->
      let a'  = Typ.index_of_name a
      and ms' = internalize_spine ctx ms in
        Int.LF.Atom (a', ms')

  | Ext.LF.ArrTyp (_, a, b)     ->
      let x    = Id.mk_name None
      and a'   = internalize_typ ctx  a in
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let b'   = internalize_typ ctx' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, a'), b')

  | Ext.LF.PiTyp (_, Ext.LF.TypDecl (x, a), b) ->
      let a'   = internalize_typ ctx  a
      and ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let b'   = internalize_typ ctx' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, a'), b')



and internalize_term ctx = function
  | Ext.LF.Lam (_, x, m)   ->
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let m'   = internalize_term ctx' m in
        Int.LF.Lam (x, m')

  | Ext.LF.Root (_, h, ms) ->
      let h'  = internalize_head  ctx h
      and ms' = internalize_spine ctx ms in
        Int.LF.Root (h', ms')



and internalize_head ctx = function
  | Ext.LF.Name (_, x_or_c) ->
      (* First check to see if a name is a term variable.  If the
         lookup fails, we can assume it must be a constant. *)
      try
        Int.LF.BVar (BVar.index_of_name ctx x_or_c)
      with
        | Not_found ->
            Int.LF.Const (Term.index_of_name x_or_c)



and internalize_spine ctx = function
  | Ext.LF.Nil            -> Int.LF.Nil

  | Ext.LF.App (_, m, ms) ->
      let m'  = internalize_term  ctx m
      and ms' = internalize_spine ctx ms
      in Int.LF.App (m', ms')


(* TYPE RECONSTRUCTION -rgerma *)

(* utility functions *)
let rec type_of_fvar x = function
  | Int.LF.Empty ->
      raise Not_found

  | Int.LF.Dec (ctx, Int.LF.TypDecl (x', a)) ->
      if x = x' then a else type_of_fvar x ctx


(* TODO reorder declaration to avoid mutual recursion if possible *)
exception NotImplemented

(* TODO detail as in check.ml *)
exception Error

(* PHASE 0 : Indexing *)
let rec index_kind ctx = function
  | Ext.LF.Typ _                             -> Apx.LF.Typ

  | Ext.LF.ArrKind (_, a, k)                 ->
      let x    = Id.mk_name None
      and a'   = index_typ ctx a in
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let k'   = index_kind ctx' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let a'   = index_typ ctx a
      and ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let k'   = index_kind ctx' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

and index_typ ctx = function
  | Ext.LF.Atom (_, a, s)      ->
      let a' = Typ.index_of_name a
      and s' = index_spine ctx s in
        Apx.LF.Atom (a', s')

  | Ext.LF.ArrTyp (_, a, b)     ->
      let x    = Id.mk_name None
      and a'   = index_typ ctx a in
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let b'   = index_typ ctx' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

  | Ext.LF.PiTyp (_, Ext.LF.TypDecl (x, a), b) ->
      let a'   = index_typ ctx  a
      and ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let b'   = index_typ ctx' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

and index_term ctx = function
  | Ext.LF.Lam (_, x, m)   ->
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let m'   = index_term ctx' m in
        Apx.LF.Lam (x, m')

  | Ext.LF.Root (_, h, s) ->
      let h' = index_head  ctx h
      and s' = index_spine ctx s in
        Apx.LF.Root (h', s')

and index_head ctx = function
  | Ext.LF.Name (_, n) ->
      try 
        Apx.LF.BVar (BVar.index_of_name ctx n)
      with Not_found -> try
        Apx.LF.Const (Term.index_of_name n)
      with Not_found ->
        Apx.LF.FVar (n)
                  
and index_spine ctx = function
  | Ext.LF.Nil         -> Apx.LF.Nil

  | Ext.LF.App (_, m, s) ->
      let m' = index_term  ctx m
      and s' = index_spine ctx s in
        Apx.LF.App (m', s')

(* PHASE 1 : Elaboration and free variables typing *)
let rec elaborate_kind d1 y1 ps = function
  | Apx.LF.Typ -> 
      (d1, y1, Int.LF.Typ)

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let (d2, y2, a') = elaborate_typ  d1 y1 ps a in
      let ps'          = (Int.LF.DDec (ps, Int.LF.TypDecl (x, a'))) in
      let (d3, y3, k') = elaborate_kind d2 y2 ps' k in
        (d3, y3, Int.LF.PiKind (Int.LF.TypDecl (x, a'), k'))

(* Δ₁ ; Υ₁ ; Ψ ⊢ a ⇐ type / (Δ₂ ; Υ₂ ; A) *)
and elaborate_typ d1 y1 ps = function
  | Apx.LF.Atom (a, s) ->
      let k  = (Typ.get a).Typ.kind in
      let (d2, y2, s') = elaborate_spine_k d1 y1 ps s k in
        (d2, y2, Int.LF.Atom (a, s'))

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let (d2, y2, a') = elaborate_typ d1 y1 ps a in
      let ps'          = (Int.LF.DDec (ps, Int.LF.TypDecl (x, a'))) in
      let (d3, y3, b') = elaborate_typ d2 y2 ps' b in
        (d3, y3, Int.LF.PiTyp (Int.LF.TypDecl (x, a'), b'))

(* Δ₁ ; Υ₁ ; Ψ ⊢ m ⇐ A / (Δ₂ ; Υ₂ ; M) *)
and elaborate_term d1 y1 ps m a = match (m, a) with
  | (Apx.LF.Lam (x, m), Int.LF.PiTyp (Int.LF.TypDecl (_, a), b)) ->
      let ps' = (Int.LF.DDec (ps, Int.LF.TypDecl (x, a))) in
      let (d2, y2, m') = elaborate_term d1 y1 ps' m b in
        (d2, y2, Int.LF.Lam(x, m'))

  | (Apx.LF.Root (Apx.LF.Const c, s), (Int.LF.Atom _ as p)) ->
      let a = (Term.get c).Term.typ in
      let (d2, y2, s') = elaborate_spine d1 y1 ps s a p in
        (d2, y2, Int.LF.Root (Int.LF.Const c, s'))

  | (Apx.LF.Root (Apx.LF.BVar x, s), (Int.LF.Atom _ as p)) ->
      let Int.LF.TypDecl (_, a) = Context.ctxDec ps x in
      let (d2, y2, s') = elaborate_spine d1 y1 ps s a p in
        (d2, y2, Int.LF.Root (Int.LF.BVar x, s'))

(* TODO
  | (Apx.LF.Root (Apx.LF.FVar x, s), (Int.LF.Atom _ as p)) ->
      raise NotImplemented
*)

  | _ ->
      raise Error

(* Δ₁ ; Υ₁ ; Ψ ⊢ s : A ⇐ P / (Δ₂ ; Υ₂ ; S) *)
and elaborate_spine d1 y1 _ s a p = match (s, a, p) with
(* and elaborate_spine d1 y1 ps s a p = match (s, a, p) with *)
  | (Apx.LF.Nil, Int.LF.Atom (a, _), Int.LF.Atom (a', _)) ->
      if a = a' then
        (d1, y1, Int.LF.Nil)
      else
        raise Error

  (* FIXME
  | (Apx.LF.App (m, s), Int.LF.PiTyp (Int.LF.TypDecl (x, a), b), Int.LF.Atom _) ->
      let (d2, y2, m') = elaborate_term  d1 y1 ps m a in
      let (d3, y3, s') = elaborate_spine d2 y2 ps s ([m'/x] b) p in
        (d3, y3, Int.LF.App (m', s'))
  *)

  (* FIXME
  | (s, Int.LF.PiTypImp (Int.LF.TypDecl (x, a), b), Int.LF.Atom _) ->
      let u = mvar[id(ps)] in
      let (d2, y2, s') = elaborate_spine (Dec (d1, Mdecl (u, a, ps))) y1 ps s ([u/x] b) p in
        (d2, y2, Int.LF.App (u, s'))
  *)

  | _ ->
      raise Error

(* Δ₁ ; Υ₁ ; Ψ ⊢ s : K ⇐ type / (Δ₂ ; Υ₂ ; S) *)
and elaborate_spine_k d1 y1 _ s k = match (s, k) with
(* and elaborate_spine_k d1 y1 ps s k = match (s, k) with *)
  | (Apx.LF.Nil, Int.LF.Typ) ->
      (d1, y1, Int.LF.Nil)

  (* FIXME
  | (Apx.LF.App (m, s), Int.LF.PiKind (Int.LF.TypDecl (x, a), k)) ->
      let (d2, y2, m') = elaborate_term    d1 y1 ps m a in
      let (d3, y3, s') = elaborate_spine_k d2 y2 ps ([m'/x] k) in
        (d3, y3, Int.LF.App (m', s'))
  *)

  (* FIXME
  | (s, Int.LF.PiKindImp (Int.LF.TypDecl (x, a), k)) ->
      let u = mvar[id(ps)] in
      let (d2, y2, s') = elaborate_spine_k (Dec (d1, Mdecl (u, a, ps))) y1 ps s ([u/x] k) in
        (d2, y2, Int.LF.App (u, s'))
  *)

  | _ ->
      raise Error


(* PHASE 2 : Reconstruction *)
let rec reconstruct_kind = function
  | _ ->
      raise NotImplemented
        (* FIXME
let rec reconstruct_kind d1 y1 ps = function
  | Int.LF.Typ ->
      (d1, id(d1))

  | Int.LF.PiKind (Int.LF.TypDecl (x, a), k) ->
      let (d2, r2) = reconstruct_typ d1 y1 ps a in
      let (d3, r3) = reconstruct_kind d2 [[r2]](Int.LF.Ddec (ps, Int.LF.TypDecl (x, a))) [[r2]]k in
        (d3, [[r3]]r2)
          *)

and reconstruct_typ = function
  | _ -> raise NotImplemented

(* Δ₁ ; Y₁ ; Ψ ⊢ M ⇐ A / (Δ₂ ; ρ) *)
and reconstruct_term d1 y1 ps m a = match (m, a) with
  | (Int.LF.Lam (x, m), Int.LF.PiTyp (Int.LF.TypDecl (_, a), b)) ->
      let ps' = (Int.LF.DDec (ps, Int.LF.TypDecl (x, a))) in
        reconstruct_term d1 y1 ps' m b

  | (Int.LF.Root (Int.LF.Const c, s), (Int.LF.Atom _ as p)) ->
      let a = (Term.get c).Term.typ in
        reconstruct_spine d1 y1 ps s a p

  | (Int.LF.Root (Int.LF.BVar x, s), (Int.LF.Atom _ as p)) ->
      let Int.LF.TypDecl (_, a) = Context.ctxDec ps x in
        reconstruct_spine d1 y1 ps s a p

  (* FIXME
  | (Int.LF.Root (Int.LF.FVar x, s), (Int.LF.Atom _ as p)) ->
      let a = type_of_fvar x y1 in
        reconstruct_spine d1 y1 ps s a p
  *)

  | _ ->
      raise Error

and reconstruct_spine = function
  | _ -> raise NotImplemented

and reconstruct_spine_k = function
  | _ -> raise NotImplemented


(* PHASE 3 : transform Y to a bunch of implicit Pi's *)
let rec phase3_kind = function
  | _ -> raise NotImplemented
and phase3_typ = function
  | _ -> raise NotImplemented


(* wrapper function *)
let rec reconstruct_sgn_decl = function
  | _ ->
      raise NotImplemented
    (* FIXME
  | Ext.LF.SgnTyp (_, a, k0)   ->
      let k1           = index_kind (BVar.create ()) k0 in
      let (d2, y2, k2) = elaborate_kind Int.LF.Empty Int.LF.Empty Int.LF.Null k1 in
      let (d3, r3)     = reconstruct_kind d2 y2 Int.LF.Null k2 in
      let k4           = phase3_kind d3 [r3]y2 [r3]k2 in
      let a'           = Typ.add (Typ.mk_entry a k4) in
        Int.LF.SgnTyp (a', k4)

  | Ext.LF.SgnConst (_, c, a0) ->
      let a1           = index_typ (BVar.create ()) a0 in
      let (d2, y2, a2) = elaborate_typ Int.LF.Empty Int.LF.Empty Int.LF.Null a1 in
      let (d3, r3)     = reconstruct_typ d2 y2 Int.LF.Null a2 in
      let a4           = phase3_typ d3 [r3]y2 [r3]a2 in
      let c'           = Term.add (Term.mk_entry c a4) in
        Int.LF.SgnConst (c', a4)
    *)
