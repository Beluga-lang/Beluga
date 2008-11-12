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
  | Ext.LF.Nil         -> Int.LF.Nil

  | Ext.LF.App (m, ms) ->
      let m'  = internalize_term  ctx m
      and ms' = internalize_spine ctx ms
      in Int.LF.App (m', ms')
