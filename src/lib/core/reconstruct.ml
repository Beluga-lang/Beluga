(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)

open Store
open Store.Cid
open Syntax
open Substitution

(* type_of_fvar x cUpsilon = A 

   Invariant: 
   If x:A in cUpsilon then
   
    D ; cUpsilon |- A <= type

 *)
let rec type_of_fvar x = function
  | Int.LF.Empty ->
      raise Not_found

  | Int.LF.Dec (ctx, Int.LF.TypDecl (x', a)) ->
      if x = x' then a else type_of_fvar x ctx


exception NotImplemented
exception Error (* TODO detail error types as in check.ml *)

(* PHASE 0 : Indexing 
  
   index_term names ext_m = m 

   Translates external syntax into approximate syntax.
*)
let rec index_kind names = function
  | Ext.LF.Typ _ -> 
      Apx.LF.Typ

  | Ext.LF.ArrKind (_, a, k) ->
      let x      = Id.mk_name None
      and a'     = index_typ names a in
      let names' = BVar.extend names (BVar.mk_entry x) in
      let k'     = index_kind names' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let a'     = index_typ names a
      and names' = BVar.extend names (BVar.mk_entry x) in
      let k'     = index_kind names' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

and index_typ names = function
  | Ext.LF.Atom (_, a, s) ->
      let a' = Typ.index_of_name a
      and s' = index_spine names s in
        Apx.LF.Atom (a', s')

  | Ext.LF.ArrTyp (_, a, b) ->
      let x      = Id.mk_name None
      and a'     = index_typ names a in
      let names' = BVar.extend names (BVar.mk_entry x) in
      let b'     = index_typ names' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

  | Ext.LF.PiTyp (_, Ext.LF.TypDecl (x, a), b) ->
      let a'     = index_typ names  a
      and names' = BVar.extend names (BVar.mk_entry x) in
      let b'     = index_typ names' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

and index_term names = function
  | Ext.LF.Lam (_, x, m)   ->
      let names' = BVar.extend names (BVar.mk_entry x) in
      let m'     = index_term names' m in
        Apx.LF.Lam (x, m')

  | Ext.LF.Root (_, h, s) ->
      let h' = index_head  names h
      and s' = index_spine names s in
        Apx.LF.Root (h', s')

and index_head names = function
  | Ext.LF.Name (_, n) ->
      try 
        Apx.LF.BVar (BVar.index_of_name names n)
      with Not_found -> try
        Apx.LF.Const (Term.index_of_name n)
      with Not_found ->
        Apx.LF.FVar (n)
                  
and index_spine names = function
  | Ext.LF.Nil -> 
      Apx.LF.Nil

  | Ext.LF.App (_, m, s) ->
      let m' = index_term  names m
      and s' = index_spine names s in
        Apx.LF.App (m', s')

(* PHASE 1 : Elaboration and free variables typing *)
let rec is_a_pattern_spine seen_vars spine = match spine with
  | Apx.LF.Nil ->
      true

  | Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine) ->
      not (List.mem x seen_vars) && is_a_pattern_spine (x :: seen_vars) spine

  | _ ->
      false

let rec elaborate_kind cPsi k = match k with 
  | Apx.LF.Typ -> 
      Int.LF.Typ

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let tA    = elaborate_typ cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elaborate_kind cPsi' k in
        Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK)

and elaborate_typ cPsi a = match a with 
  | Apx.LF.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let tS = elaborate_spine_k_i cPsi s i (tK, Substitution.LF.id) in
        Int.LF.Atom (a, tS)

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let tA    = elaborate_typ cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elaborate_typ cPsi' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB)

and elaborate_term cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
      let tM    = elaborate_term cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam(x, tM)

  | (Apx.LF.Root (Apx.LF.Const c, spine), ((Int.LF.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let tS = elaborate_spine_i cPsi spine i (tA, LF.id) (tP, s) in
        Int.LF.Root (Int.LF.Const c, tS)

  | (Apx.LF.Root (Apx.LF.BVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elaborate_spine cPsi spine (tA, LF.id) (tP, s) in
        Int.LF.Root (Int.LF.BVar x, tS)

  | (Apx.LF.Root (Apx.LF.FVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      try
        let tA = FVar.get x in
        let tS = elaborate_spine cPsi spine (tA, LF.id) (tP, s) in
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        if is_a_pattern_spine [] spine then
          let (tS, tA) = elaborate_spine_infer cPsi spine tP in
          let _        = FVar.add x tA in
            Int.LF.Root (Int.LF.FVar x, tS)
        else
          raise NotImplemented
          (*
            let placeholder = ref Int.LF.Nil in
               (add_delayed
                  let tA = FVar.get x in
                     placeholder := elaborate_spine cPsi spine (tA, LF.id) (tP, s);
                Int.LF.Root (Int.LF.FVar x, placeholder)
               )
          *)

  | _ ->
      raise Error (* Error message *)

and elaborate_spine_i cPsi spine i sA sP = 
  if i = 0 then 
    elaborate_spine cPsi spine sA sP
  else
    match sA with 
      | (Int.LF.PiTyp(Int.LF.TypDecl(_, tA), tB), s) ->
          let u  = Context.newMVar (cPsi, Int.LF.TClo(tA, s)) in
          let tR = Int.LF.Root(Int.LF.MVar(u, LF.id), Int.LF.Nil) in 
          elaborate_spine_i cPsi spine (i - 1) (tB, Int.LF.Dot(Int.LF.Obj(tR), s)) sP

      | _  ->       
          raise Error (* Error message *)

and elaborate_spine cPsi s sA sP = match (s, sA) with
  | (Apx.LF.Nil, (Int.LF.Atom (a, _spine), _s)) -> 
      let (Int.LF.Atom (a', _spine'), _s') = sP in 
        if a = a' then
          Int.LF.Nil
        else
          raise Error (* Error message *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let tM = elaborate_term  cPsi m (tA, s) in 
      let tS = elaborate_spine cPsi spine (tB, Int.LF.Dot(Int.LF.Obj(tM), s)) sP in
        Int.LF.App (tM, tS)

  | _ ->
      raise Error (* Error message *)


and elaborate_spine_k_i cPsi spine i sK = 
  if  i = 0 then 
    elaborate_spine_k cPsi spine sK
  else 
    match sK with 
      | (Int.LF.PiKind(Int.LF.TypDecl(_, tA), tK), s) ->
          let u  = Context.newMVar (cPsi, Int.LF.TClo(tA, s)) in
          let tR = Int.LF.Root(Int.LF.MVar(u, LF.id), Int.LF.Nil) in 
            elaborate_spine_k_i cPsi spine (i - 1) (tK, Int.LF.Dot(Int.LF.Obj(tR), s))

      | _  ->  
          raise Error
     

and elaborate_spine_k cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (Int.LF.Typ, _s)) -> 
      Int.LF.Nil

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let tM = elaborate_term    cPsi m (tA, s) in 
      let tS = elaborate_spine_k cPsi spine (tK, Int.LF.Dot(Int.LF.Obj (tM), s)) in
        Int.LF.App (tM, tS)

and elaborate_spine_infer cPsi spine tP = match spine with
  | Apx.LF.Nil ->
      (Int.LF.Nil, tP)

  | Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (tS, tB) = elaborate_spine_infer cPsi spine tP in

      let rec foo cPsi i j = match cPsi with (* TODO rename *)
        | Int.LF.Null ->
            Int.LF.Shift 0
              
        | Int.LF.DDec (cPsi, Int.LF.TypDecl _) ->
            let x = if i = j then 0 else i in
              Int.LF.Dot (Int.LF.Head (Int.LF.BVar x), foo cPsi (i + 1) j) in

      (* TODO confirm this is correct *)
      let tB' = Int.LF.TClo (tB, foo cPsi 0 x) in
        (Int.LF.App (Int.LF.Root (Int.LF.BVar x, Int.LF.Nil), tS), 
         Int.LF.PiTyp (Int.LF.TypDecl (Id.mk_name None, tA), tB'))

(* PHASE 2 : Reconstruction *)
(* FIXME maybe we'll need to work with explicit substitution for types here too
   will see when spine functions get implemented *)
let rec reconstruct_kind cPsi tK = match tK with
  | Int.LF.Typ ->
      ()

  | Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK) -> (
      reconstruct_typ cPsi tA ;
      reconstruct_kind (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) tK
    )


and reconstruct_typ cPsi tA = match tA with
  | Int.LF.Atom (a, tS) ->
      let tK = (Typ.get a).Typ.kind in
        reconstruct_spine_k cPsi tS tK

  | Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB) -> (
      reconstruct_typ cPsi tA ;
      reconstruct_typ (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) tB
    )

and reconstruct_term cPsi tM tA = match (tM, tA) with
  | (Int.LF.Lam (x, tM), Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB)) ->
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
        reconstruct_term cPsi' tM tB

  | (Int.LF.Root (Int.LF.Const c, tS), (Int.LF.Atom _ as tP)) ->
      let tA = (Term.get c).Term.typ in
        reconstruct_spine cPsi tS tA tP

  | (Int.LF.Root (Int.LF.BVar x, tS), (Int.LF.Atom _ as tP)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        reconstruct_spine cPsi tS tA tP

  | (Int.LF.Root (Int.LF.MVar (_u, _s), _tS), (Int.LF.Atom _ as _tP)) ->
      raise NotImplemented
  (*
  | (Int.LF.Root (Int.LF.FVar x, s), (Int.LF.Atom _ as p)) ->
      let tA = type_of_fvar x in
        reconstruct_spine cPsi s tA p
  *)

  | _ ->
      raise Error (* Error message *)

and reconstruct_spine = function
  | _ -> raise NotImplemented

and reconstruct_spine_k = function
  | _ -> raise NotImplemented


(* PHASE 3 : transform Y to a bunch of implicit Pi's *)
let rec phase3_kind tK = match tK with
  | _ -> 
      (tK, 0) (* TODO implement this *)

and phase3_typ tA = match tA with
  | _ -> 
      (tA, 0) (* TODO implement this *)


(* wrapper function *)
let rec reconstruct_sgn_decl d = match d with
  | Ext.LF.SgnTyp (_, a, k0)   ->
      let k1       = index_kind (BVar.create ()) k0 in
      let k2       = elaborate_kind Int.LF.Null k1 in
      let _        = reconstruct_kind Int.LF.Null k2 in
      let (k3, i)  = phase3_kind k2 in
      let a'       = Typ.add (Typ.mk_entry a k3 i) in
        Int.LF.SgnTyp (a', k3)

  | Ext.LF.SgnConst (_, c, a0) ->
      let a1       = index_typ (BVar.create ()) a0 in
      let a2       = elaborate_typ Int.LF.Null a1 in
      let _        = reconstruct_typ Int.LF.Null a2 in
      let (a3, i)  = phase3_typ a2 in
      let c'       = Term.add (Term.mk_entry c a3 i) in
        Int.LF.SgnConst (c', a3)

