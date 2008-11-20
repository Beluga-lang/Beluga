(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)



open Store
open Store.Cid
open Syntax
open Substitution

(* Translation of external syntax into 
   LF internal syntax 

   Eventually calls to internalize_sgn_decl
   will be replaced reconstruct_sgn_decl. 

*)
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


(* --------------------------------------------------------------------- *)
(* TYPE RECONSTRUCTION *)

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


(* TODO reorder declaration to avoid mutual recursion if possible *)
exception NotImplemented

(* TODO detail as in check.ml *)
exception Error

(* PHASE 0 : Indexing 
  
   index_term names ext_m = m 

   Translates external syntax into approximate syntax.
*)
let rec index_kind names = function
  | Ext.LF.Typ _                             -> Apx.LF.Typ

  | Ext.LF.ArrKind (_, a, k)                 ->
      let x    = Id.mk_name None
      and a'   = index_typ names a in
      let names' = BVar.extend names (BVar.mk_entry x) in
      let k'   = index_kind names' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let a'   = index_typ names a
      and names' = BVar.extend names (BVar.mk_entry x) in
      let k'   = index_kind names' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

and index_typ names = function
  | Ext.LF.Atom (_, a, s)      ->
      let a' = Typ.index_of_name a
      and s' = index_spine names s in
        Apx.LF.Atom (a', s')

  | Ext.LF.ArrTyp (_, a, b)     ->
      let x    = Id.mk_name None
      and a'   = index_typ names a in
      let names' = BVar.extend names (BVar.mk_entry x) in
      let b'   = index_typ names' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

  | Ext.LF.PiTyp (_, Ext.LF.TypDecl (x, a), b) ->
      let a'   = index_typ names  a
      and names' = BVar.extend names (BVar.mk_entry x) in
      let b'   = index_typ names' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

and index_term names = function
  | Ext.LF.Lam (_, x, m)   ->
      let names' = BVar.extend names (BVar.mk_entry x) in
      let m'   = index_term names' m in
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
  | Ext.LF.Nil         -> Apx.LF.Nil

  | Ext.LF.App (_, m, s) ->
      let m' = index_term  names m
      and s' = index_spine names s in
        Apx.LF.App (m', s')

(* PHASE 1 : Elaboration and free variables typing *)

(* y1 -> cUpsilon  or  make it global *)
let rec elaborate_kind y1 cPsi k = match k with 
  | Apx.LF.Typ -> 
      (y1, Int.LF.Typ)

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let (y2, tA) = elaborate_typ y1 cPsi a in
      let cPsi'      = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let (y3, tK) = elaborate_kind y2 cPsi' k in
        (y3, Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK))


and elaborate_typ y1 cPsi a = match a with 
  | Apx.LF.Atom (a, s) ->
      (* (tK, i) = (Typ.get a).Typ.kind *)
      let tK  = (Typ.get a).Typ.kind in
      let (y2, tS) = elaborate_spine_k_i y1 cPsi s 0 (tK, Substitution.LF.id) in
        (y2, Int.LF.Atom (a, tS))

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let (y2, tA) = elaborate_typ y1 cPsi a in
      let cPsi'     = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let (y3, tB) = elaborate_typ y2 cPsi' b in
        (y3, Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB))

and elaborate_term y1 cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
      let (y2, tM) = elaborate_term y1 cPsi' m (tB, LF.dot1 s) in
        (y2, Int.LF.Lam(x, tM))

  | (Apx.LF.Root (Apx.LF.Const c, spine), ((Int.LF.Atom _ as tP), s)) ->
      (* (tA, i) = Term.get c).Term.typ  -bp *)
      let tA = (Term.get c).Term.typ in
      let (y2, tS) = elaborate_spine_i y1 cPsi spine 0 (tA, LF.id) (tP,s) in
        (y2, Int.LF.Root (Int.LF.Const c, tS))

  | (Apx.LF.Root (Apx.LF.BVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (y2, tS) = elaborate_spine y1 cPsi spine (tA, LF.id) (tP,s ) in
        (y2, Int.LF.Root (Int.LF.BVar x, tS))

  | (Apx.LF.Root (Apx.LF.FVar _x, _spine), (Int.LF.Atom _ , _s)) ->
      raise NotImplemented

  | _ ->
      raise Error (* Error message *)


and elaborate_spine_i y1 cPsi spine i sA sP = 
  if i = 0 then 
    elaborate_spine y1 cPsi spine sA sP
  else
    begin match sA with 
      | (Int.LF.PiTyp(Int.LF.TypDecl(_,tA), tB), s)
	-> let u = Context.newMVar (cPsi, Int.LF.TClo(tA, s)) in
	   let tR = Int.LF.Root(Int.LF.MVar(u,LF.id), Int.LF.Nil) in 
             elaborate_spine_i y1 cPsi spine (i-1) (tB, Int.LF.Dot(Int.LF.Obj(tR), s)) sP
	    
      | _  ->	    raise Error
    end 

and elaborate_spine y1 cPsi s sA sP = match (s, sA) with
  | (Apx.LF.Nil, (Int.LF.Atom (a, _spine), _s)) -> 
      let (Int.LF.Atom (a', _spine'), _s') = sP in 
	if a = a' then
          (y1, Int.LF.Nil)
	else
          raise Error

 | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let (y2, tM) = elaborate_term  y1 cPsi m (tA, s) in 
      let (y3, tS) = elaborate_spine y2 cPsi spine (tB, Int.LF.Dot(Int.LF.Obj(tM), s)) sP in
        (y3, Int.LF.App (tM, tS))
  | _ ->
      raise Error


and elaborate_spine_k_i y1 cPsi spine i sK = 
  if  i = 0 then 
    elaborate_spine_k y1 cPsi spine sK
  else 
    begin match sK with 
      | (Int.LF.PiKind(Int.LF.TypDecl(_,tA), tK), s)
	-> let u = Context.newMVar (cPsi, Int.LF.TClo(tA, s)) in
	   let tR = Int.LF.Root(Int.LF.MVar(u, LF.id), Int.LF.Nil) in 
             elaborate_spine_k_i y1 cPsi spine (i-1) (tK, Int.LF.Dot(Int.LF.Obj(tR), s))
	    
      | _  ->	    raise Error
    end 

and elaborate_spine_k y1 cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (Int.LF.Typ, _s)) -> 
      (y1, Int.LF.Nil) 

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let (y2, tM) = elaborate_term    y1 cPsi m (tA,s) in 
      let (y3, tS) = elaborate_spine_k y2 cPsi spine (tK, Int.LF.Dot(Int.LF.Obj(tM), s)) in
        (y3, Int.LF.App (tM, tS))


(*
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

*)
(* wrapper function *)
let rec reconstruct_sgn_decl _ =  raise NotImplemented

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

