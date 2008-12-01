(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)

open Store
open Store.Cid
open Syntax
open Substitution
open Id

module Apx = struct

  module LF = struct

    type kind =
      | Typ
      | PiKind of typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and typ =
      | Atom  of cid_typ * spine
      | PiTyp of typ_decl * typ

    and normal =
      | Lam  of name * normal
      | Root of head * spine

    and head =
      | BVar  of offset
      | Const of cid_term
      | FVar  of name

    and spine =
      | Nil
      | App of normal * spine

  end

end

module E = Ext.LF
module A = Apx.LF
module I = Int.LF

exception NotImplemented

type error =
  | ExpAppNotFun
  | ExpNilNotAtom
  | KindMisMatch
  | SubIllTyped
  | TypMisMatch of I.dctx * I.tclo * I.tclo
  | IllTyped    of I.dctx * A.normal * I.tclo

exception Error of error

(* PHASE 0 : Indexing

   index_term names ext_m = m

   Translates external syntax into approximate syntax.
*)
let rec index_kind names = function
  | E.Typ _ ->
      A.Typ

  | E.ArrKind (_, a, k) ->
      let x      = Id.mk_name None
      and a'     = index_typ names a in
      let names' = BVar.extend names (BVar.mk_entry x) in
      let k'     = index_kind names' k in
        A.PiKind (A.TypDecl (x, a'), k')

  | E.PiKind (_, E.TypDecl (x, a), k) ->
      let a'     = index_typ names a
      and names' = BVar.extend names (BVar.mk_entry x) in
      let k'     = index_kind names' k in
        A.PiKind (A.TypDecl (x, a'), k')

and index_typ names = function
  | E.Atom (_, a, s) ->
      let a' = Typ.index_of_name a
      and s' = index_spine names s in
        A.Atom (a', s')

  | E.ArrTyp (_, a, b) ->
      let x      = Id.mk_name None
      and a'     = index_typ names a in
      let names' = BVar.extend names (BVar.mk_entry x) in
      let b'     = index_typ names' b in
        A.PiTyp (A.TypDecl (x, a'), b')

  | E.PiTyp (_, E.TypDecl (x, a), b) ->
      let a'     = index_typ names  a
      and names' = BVar.extend names (BVar.mk_entry x) in
      let b'     = index_typ names' b in
        A.PiTyp (A.TypDecl (x, a'), b')

and index_term names = function
  | E.Lam (_, x, m)   ->
      let names' = BVar.extend names (BVar.mk_entry x) in
      let m'     = index_term names' m in
        A.Lam (x, m')

  | E.Root (_, h, s) ->
      let h' = index_head  names h
      and s' = index_spine names s in
        A.Root (h', s')

and index_head names = function
  | E.Name (_, n) ->
      try
        A.BVar (BVar.index_of_name names n)
      with Not_found -> try
        A.Const (Term.index_of_name n)
      with Not_found ->
        A.FVar n

and index_spine names = function
  | E.Nil ->
      A.Nil

  | E.App (_, m, s) ->
      let m' = index_term  names m
      and s' = index_spine names s in
        A.App (m', s')

(* PHASE 1 : Elaboration and free variables typing *)
let rec is_a_pattern_spine seen_vars spine = match spine with
  | A.Nil ->
      true

  | A.App (A.Root (A.BVar x, A.Nil), spine) ->
      not (List.mem x seen_vars) && is_a_pattern_spine (x :: seen_vars) spine

  | _ ->
      false

let rec elaborate_kind cPsi k = match k with
  | A.Typ ->
      I.Typ

  | A.PiKind (A.TypDecl (x, a), k) ->
      let tA    = elaborate_typ cPsi a in
      let cPsi' = (I.DDec (cPsi, I.TypDecl (x, tA))) in
      let tK    = elaborate_kind cPsi' k in
        I.PiKind (I.TypDecl (x, tA), tK)

and elaborate_typ cPsi a = match a with
  | A.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let tS = elaborate_spine_k_i cPsi s i (tK, Substitution.LF.id) in
        I.Atom (a, tS)

  | A.PiTyp (A.TypDecl (x, a), b) ->
      let tA    = elaborate_typ cPsi a in
      let cPsi' = (I.DDec (cPsi, I.TypDecl (x, tA))) in
      let tB    = elaborate_typ cPsi' b in
        I.PiTyp (I.TypDecl (x, tA), tB)

and elaborate_term cPsi m sA = match (m, sA) with
  | (A.Lam (x, m), (I.PiTyp (tA, tB), s)) ->
      let cPsi' = I.DDec (cPsi, LF.decSub tA s) in
      let tM    = elaborate_term cPsi' m (tB, LF.dot1 s) in
        I.Lam(x, tM)

  | (A.Root (A.Const c, spine), ((I.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let tS = elaborate_spine_i cPsi spine i (tA, LF.id) (tP, s) in
        I.Root (I.Const c, tS)

  | (A.Root (A.BVar x, spine), (I.Atom _ as tP, s)) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elaborate_spine cPsi spine (tA, LF.id) (tP, s) in
        I.Root (I.BVar x, tS)

  | (A.Root (A.FVar x, spine), (I.Atom _ as tP, s)) ->
      try
        let tA = FVar.get x in
        let tS = elaborate_spine cPsi spine (tA, LF.id) (tP, s) in
          I.Root (I.FVar x, tS)
      with Not_found ->
        if is_a_pattern_spine [] spine then
          let (tS, tA) = elaborate_spine_infer cPsi spine tP in
          let _        = FVar.add x tA in
            I.Root (I.FVar x, tS)
        else
          raise NotImplemented
          (*
            let placeholder = ref I.Nil in
               (add_delayed
                  let tA = FVar.get x in
                     placeholder := elaborate_spine cPsi spine (tA, LF.id) (tP, s);
                I.Root (I.FVar x, placeholder)
               )
          *)

  | _ ->
      raise (Error (IllTyped (cPsi, m, sA)))

and elaborate_spine_i cPsi spine i sA sP =
  if i = 0 then
    elaborate_spine cPsi spine sA sP
  else
    match sA with
      | (I.PiTyp(I.TypDecl(_, tA), tB), s) ->
          let u  = Context.newMVar (cPsi, I.TClo(tA, s)) in
          let tR = I.Root (I.MVar (u, LF.id), I.Nil) in
            elaborate_spine_i cPsi spine (i - 1) (tB, I.Dot (I.Obj tR, s)) sP

and elaborate_spine cPsi s sA sP = match (s, sA) with
  | (A.Nil, (I.Atom (a, _spine), _s)) ->
      let (I.Atom (a', _spine'), _s') = sP in
        if a = a' then
          I.Nil
        else
          raise (Error (TypMisMatch (cPsi, sA, sP)))

  | (A.Nil, _) ->
      raise (Error ExpNilNotAtom)

  | (A.App (m, spine), (I.PiTyp (I.TypDecl (_, tA), tB), s)) ->
      let tM = elaborate_term  cPsi m (tA, s) in
      let tS = elaborate_spine cPsi spine (tB, I.Dot (I.Obj tM, s)) sP in
        I.App (tM, tS)

  | (A.App _, _) ->
      raise (Error ExpAppNotFun)

and elaborate_spine_k_i cPsi spine i sK =
  if  i = 0 then
    elaborate_spine_k cPsi spine sK
  else
    match sK with
      | (I.PiKind(I.TypDecl(_, tA), tK), s) ->
          let u  = Context.newMVar (cPsi, I.TClo (tA, s)) in
          let tR = I.Root (I.MVar (u, LF.id), I.Nil) in
            elaborate_spine_k_i cPsi spine (i - 1) (tK, I.Dot (I.Obj tR, s))

and elaborate_spine_k cPsi spine sK = match (spine, sK) with
  | (A.Nil, (I.Typ, _s)) ->
      I.Nil

  | (A.Nil, _) ->
      raise (Error KindMisMatch)

  | (A.App (m, spine), (I.PiKind (I.TypDecl (_, tA), tK), s)) ->
      let tM = elaborate_term    cPsi m (tA, s) in
      let tS = elaborate_spine_k cPsi spine (tK, I.Dot(I.Obj (tM), s)) in
        I.App (tM, tS)

  | (A.App _, _) ->
      raise (Error ExpAppNotFun)

and elaborate_spine_infer cPsi spine tP = match spine with
  | A.Nil ->
      (I.Nil, tP)

  | A.App (A.Root (A.BVar x, A.Nil), spine) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (tS, tB) = elaborate_spine_infer cPsi spine tP in

      let rec foo cPsi i j = match cPsi with (* TODO rename *)
        | I.Null ->
            I.Shift 0

        | I.DDec (cPsi, I.TypDecl _) ->
            let x = if i = j then 0 else i in
              I.Dot (I.Head (I.BVar x), foo cPsi (i + 1) j) in

      (* TODO confirm this is correct *)
      let tB' = I.TClo (tB, foo cPsi 0 x) in
        (I.App (I.Root (I.BVar x, I.Nil), tS),
         I.PiTyp (I.TypDecl (Id.mk_name None, tA), tB'))


(* PHASE 2 : Reconstruction *)
let rec reconstruct_kind cPsi tK = match tK with
  | I.Typ ->
      ()

  | I.PiKind (I.TypDecl (x, tA), tK) -> (
      reconstruct_typ cPsi tA;
      reconstruct_kind (I.DDec (cPsi, I.TypDecl (x, tA))) tK
    )


and reconstruct_typ cPsi tA = match tA with
  | I.Atom (a, tS) ->
      let tK = (Typ.get a).Typ.kind in
        reconstruct_spine_k cPsi tS (tK, LF.id)

  | I.PiTyp (I.TypDecl (x, tA), tB) -> (
      reconstruct_typ cPsi tA;
      reconstruct_typ (I.DDec (cPsi, I.TypDecl (x, tA))) tB
    )

and reconstruct_term cPsi tM sA = match (tM, sA) with
  | (I.Lam (_, tM), (I.PiTyp (tA, tB), s)) ->
      let cPsi' = (I.DDec (cPsi, LF.decSub tA s)) in
        reconstruct_term cPsi' tM (tB, LF.dot1 s)

  | (I.Root (I.Const c, tS), ((I.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
        reconstruct_spine cPsi tS (tA, LF.id) (tP, s)

  | (I.Root (I.BVar x, tS), ((I.Atom _ as tP), s)) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
        reconstruct_spine cPsi tS (tA, LF.id) (tP, s)

  | (I.Root (I.MVar (I.Inst (_tM, _cPhi, _tP', _cnstr), _s), _tS), ((I.Atom _ as _tP), _s')) ->
      (*
        if instanciated then
          check as normal term
        else
          reconstruct_sub cPsi s cPhi;
          unifyTyp cPsi (tP, s') (tP', s);
          reconstruct_spine cPsi tS (tP', s) (tP, s') (* redundant since we assume tS to be Nil *)
        )
      *)
      raise NotImplemented

  | (I.Root (I.FVar x, tS), ((I.Atom _ as tP), s)) ->
      let tA = FVar.get x in
        reconstruct_spine cPsi tS (tA, LF.id) (tP, s)

and reconstruct_spine cPsi tS sA sP = match (tS, sA) with
  | (I.Nil, (_tP', _s)) ->
      (* unifyTyp cPsi tP tP' *)
      raise NotImplemented

  | (I.App (tM, tS), (I.PiTyp (I.TypDecl (_, tA), tB), s)) -> (
      reconstruct_term  cPsi tM (tA, s);
      reconstruct_spine cPsi tS (tB, I.Dot (I.Obj(tM), s)) sP
    )

and reconstruct_spine_k cPsi tS sK = match (tS, sK) with
  | (I.Nil, (I.Typ, _s)) ->
      ()

  | (I.App (tM, tS), (I.PiKind (I.TypDecl (_, tA), tK), s)) -> (
      reconstruct_term    cPsi tM (tA, s);
      reconstruct_spine_k cPsi tS (tK, I.Dot (I.Obj(tM), s))
    )

and reconstruct_sub cPsi s cPhi = match (s, cPhi) with
  | (I.Shift 0, I.Null) ->
      ()

  | (I.Dot (I.Head I.BVar x, s), I.DDec (cPhi, I.TypDecl (_, _tA))) ->
      let I.TypDecl (_, _tA') = Context.ctxDec cPsi x in (
          reconstruct_sub  cPsi s cPhi;
          (* unifyTyp cPsi (tA', s) (tA, LF.id) *)
          raise NotImplemented
        )

  | (I.Dot (I.Obj tM, s), I.DDec (cPhi, I.TypDecl (_, tA))) -> (
      reconstruct_sub  cPsi s cPhi;
      reconstruct_term cPsi tM (tA, s)
    )


(* PHASE 3 : transform Y to a bunch of implicit Pi's *)
let rec phase3_kind tK = match tK with
  | _ ->
      (tK, 0) (* TODO implement this *)

and phase3_typ tA = match tA with
  | _ ->
      (tA, 0) (* TODO implement this *)


(* wrapper function *)
let rec reconstruct_sgn_decl d = match d with
  | E.SgnTyp (_, a, k0)   ->
      let k1       = index_kind (BVar.create ()) k0 in
      let k2       = elaborate_kind I.Null k1 in
      let _        = reconstruct_kind I.Null k2 in
      let (k3, i)  = phase3_kind k2 in
      let a'       = Typ.add (Typ.mk_entry a k3 i) in
        I.SgnTyp (a', k3)

  | E.SgnConst (_, c, a0) ->
      let a1       = index_typ (BVar.create ()) a0 in
      let a2       = elaborate_typ I.Null a1 in
      let _        = reconstruct_typ I.Null a2 in
      let (a3, i)  = phase3_typ a2 in
      let c'       = Term.add (Term.mk_entry c a3 i) in
        I.SgnConst (c', a3)

(* TODO
   - add an implicit Delta to the store and work with it
   - add delayed jobs stuff
   - think about phase 3
*)
