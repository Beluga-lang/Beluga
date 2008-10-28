(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)



open Store
open Store.Cid
open Syntax



let rec internalize_sgn_decl = function
  | Ext.SgnTyp (_, a, k)   ->
      let k' = internalize_kind (BVar.create ()) k in
      let a' = Typ.add (Typ.mk_entry a k') in
        Int.SgnTyp (a', k')

  | Ext.SgnConst (_, c, a) ->
      let a' = internalize_typ (BVar.create ()) a in
      let c' = Term.add (Term.mk_entry c a') in
        Int.SgnConst (c', a')



and internalize_kind ctx = function
  | Ext.Typ _                             -> Int.Typ

  | Ext.ArrKind (_, a, k)                 ->
      let x    = Id.mk_name None
      and a'   = internalize_typ  ctx  a in
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let k'   = internalize_kind ctx' k in
        Int.PiKind (Int.TypDecl (x, a'), k')

  | Ext.PiKind (_, Ext.TypDecl (x, a), k) ->
      let a'   = internalize_typ  ctx  a
      and ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let k'   = internalize_kind ctx' k in
        Int.PiKind (Int.TypDecl (x, a'), k')



and internalize_typ ctx = function
  | Ext.Atom (_, a, ms)      ->
      let a'  = Typ.index_of_name a
      and ms' = internalize_spine ctx ms in
        Int.Atom (a', ms')

  | Ext.ArrTyp (_, a, b)     ->
      let x    = Id.mk_name None
      and a'   = internalize_typ ctx  a in
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let b'   = internalize_typ ctx' b in
        Int.PiTyp (Int.TypDecl (x, a'), b')

  | Ext.PiTyp (_, Ext.TypDecl (x, a), b) ->
      let a'   = internalize_typ ctx  a
      and ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let b'   = internalize_typ ctx' b in
        Int.PiTyp (Int.TypDecl (x, a'), b')



and internalize_term ctx = function
  | Ext.Lam (_, x, m)   ->
      let ctx' = BVar.extend ctx (BVar.mk_entry x) in
      let m'   = internalize_term ctx' m in
        Int.Lam (x, m')

  | Ext.Root (_, h, ms) ->
      let h'  = internalize_head  ctx h
      and ms' = internalize_spine ctx ms in
        Int.Root (h', ms')



and internalize_head ctx = function
  | Ext.Name (_, x_or_c) ->
      (* First check to see if a name is a term variable.  If the
         lookup fails, we can assume it must be a constant. *)
      try
        Int.BVar (BVar.index_of_name ctx x_or_c)
      with
        | Not_found ->
            Int.Const (Term.index_of_name x_or_c)



and internalize_spine ctx = function
  | Ext.Nil         -> Int.Nil

  | Ext.App (m, ms) ->
      let m'  = internalize_term  ctx m
      and ms' = internalize_spine ctx ms
      in Int.App (m', ms')
