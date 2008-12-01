(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

open Store
open Store.Cid
open Syntax
open Substitution


module Unif = Unify.UnifyNoTrail


exception NotImplemented
exception Error (* TODO detail error types as in check.ml *)

(* PHASE 0 : Indexing 
  
   index_term names ext_m = m 

   Translates an object ext_m in external syntax
   into an object m in approximate internal syntax.
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


(* ******************************************************************* *)
(* PHASE 1 : Elaboration and free variables typing                     *)

(* patSpine s = bool 
 
   if cPsi |- s : A <- P  and
      s is a pattern spine (simple approximate), 
   i.e. it consists of distinct bound variables
    
   then
      return true; 
      otherwise false.
     
*)
let patSpine spine = 
  let rec patSpine' seen_vars spine = match spine with
    | Apx.LF.Nil ->
        true
          
    | Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine) ->
        not (List.mem x seen_vars) && patSpine' (x :: seen_vars) spine
          
    | _ ->  false
  in 
    patSpine' [] spine

(* elKind  cPsi (k,s) = K 

 *)

let rec elKind cPsi k = match k with 
  | Apx.LF.Typ -> 
      Int.LF.Typ

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elKind cPsi' k in
        Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK)

(* elTyp cPsi a = A 

   Pre-condition: 
       Upsilon = set of free variables

   if |cPsi| |- a <= type
   then
       cPsi   |- A <- type (pre-dependent)

   Effect: 
       Upsilon' = FV(A)  where Upsilon' is an extension of Upsilon

*)
and elTyp cPsi a = match a with 
  | Apx.LF.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let tS = elKSpineI cPsi s i (tK, Substitution.LF.id) in
        Int.LF.Atom (a, tS)

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp cPsi' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB)

(* elTerm  cPsi m sA = M 
   elTermW cPsi m sA = M  where sA = (A,s) is in whnf

   if |cPsi| |- m <= |[s]A'| 
       cPsi  |- s <= cPsi'
       cPsi' |- A <- type (pre-dependent)       
   then 
       cPsi |- M <- A     (pre-dependent)       

*)
and elTerm cPsi m sA = elTermW cPsi m (Whnf.whnfTyp sA) 

and elTermW cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
      let tM    = elTerm cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam(x, tM)

  | (Apx.LF.Root (Apx.LF.Const c, spine), ((Int.LF.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let tS = elSpineI cPsi spine i (tA, LF.id) (tP, s) in
        Int.LF.Root (Int.LF.Const c, tS)

  | (Apx.LF.Root (Apx.LF.BVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in
        Int.LF.Root (Int.LF.BVar x, tS)

  | (Apx.LF.Root (Apx.LF.FVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      try
        let tA = FVar.get x in
        let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        if patSpine spine then
          let (tS, tA) = elSpineSynth cPsi spine (tP,s) in
          let _        = FVar.add x tA in
            Int.LF.Root (Int.LF.FVar x, tS)
        else
          raise NotImplemented
          (*
            let placeholder = ref Int.LF.Nil in
               (add_delayed
                  let tA = FVar.get x in
                     placeholder := elSpine cPsi spine (tA, LF.id) (tP, s);
                Int.LF.Root (Int.LF.FVar x, placeholder)
               )
          *)

  | _ ->
      raise Error (* Error message *)

(* elSpineI  cPsi spine i sA sP  = S
   elSpineIW cPsi spine i sA sP  = S   

     where sA = (A,s) and sP = (P,s') 
       and sA and sP in whnf
 
   Pre-condition: 
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; cPsi |- spine <- [s]A  (approx)   
   then
      O' ; U' ; cPsi |- S <- [s]A : [s']P (pre-dependent)


   Post-condition:  
     U' = extension of U containing all free variables of S
     O' = extension of O containing i new meta-variables
              for implicit arguments

   Comment: elSpineI will insert new meta-variables (as references)
     for omitted implicit type arguments; their type is pre-dependent. 
*)
and elSpineI cPsi spine i sA sP = 
      elSpineIW cPsi spine i (Whnf.whnfTyp sA) (Whnf.whnfTyp sP)

and elSpineIW cPsi spine i sA sP = 
  if i = 0 then 
    elSpine cPsi spine sA sP
  else
    match sA with 
      | (Int.LF.PiTyp(Int.LF.TypDecl(_, tA), tB), s) ->
          let u = Context.newMVar (cPsi, Int.LF.TClo(tA, s)) in
          let h = Int.LF.MVar(u, LF.id) in 
          elSpineI cPsi spine (i - 1) (tB, Int.LF.Dot(Int.LF.Head(h), s)) sP

      | _  ->       
          raise Error (* Error message *)

(* elSpine  cPsi spine sA sP = S 
   elSpineW cPsi spine sA sP = S
     where sA = (A,s) and sP = (P,s') 
       and sA and sP in whnf

   Pre-condition: 
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; cPsi |- spine <- [s]A  (approx)   
   then
      O' ; U' ; cPsi |- S <- [s]A : [s']P (pre-dependent)


   Post-condition:  
     U' = extension of U containing all free variables of S
     O' = extension of O containing new meta-variables of S

*)
and elSpine cPsi spine sA sP =
   elSpineW cPsi spine (Whnf.whnfTyp sA) (Whnf.whnfTyp sP)

and elSpineW cPsi spine sA sP = match (spine, sA) with
  | (Apx.LF.Nil, (Int.LF.Atom (a, _spine), _s)) -> 
      let (Int.LF.Atom (a', _spine'), _s') = sP in 
        if a = a' then
          Int.LF.Nil
        else
          raise Error (* Error message *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm  cPsi m (tA, s) in 
      let tS = elSpine cPsi spine (tB, Int.LF.Dot(Int.LF.Obj(tM), s)) sP in
        Int.LF.App (tM, tS)

  | _ ->
      raise Error (* Error message *)

(* see invariant for elSpineI *)
and elKSpineI cPsi spine i sK = 
  if  i = 0 then 
    elKSpine cPsi spine sK
  else 
    match sK with 
      | (Int.LF.PiKind(Int.LF.TypDecl(_, tA), tK), s) ->
          let u  = Context.newMVar (cPsi, Int.LF.TClo(tA, s)) in
          let h = Int.LF.MVar(u, LF.id) in 
            elKSpineI cPsi spine (i - 1) (tK, Int.LF.Dot(Int.LF.Head(h), s))

      | _  ->  
          raise Error
     
(* see invariant for elSpine *)
and elKSpine cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (Int.LF.Typ, _s)) -> 
      Int.LF.Nil

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm   cPsi m (tA, s) in 
      let tS = elKSpine cPsi spine (tK, Int.LF.Dot(Int.LF.Obj (tM), s)) in
        Int.LF.App (tM, tS)

(* elSpineSynth cPsi spine sP = (S, P') 

   Pre-condition: 
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; Psi |- spine < [s]P


   Post-condition:  
     U' = extension of U containing all free variables of S
     O' = extension of O containing new meta-variables of S

*)
and elSpineSynth cPsi spine sP = match (spine, sP) with
  | (Apx.LF.Nil, (tP, s))  ->
      (Int.LF.Nil, Int.LF.TClo (tP, s))

  | (Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
   
      let (tS, tB) = elSpineSynth cPsi spine sP in 
     
      let s = Int.LF.Dot(Int.LF.Head (Int.LF.BVar x), LF.id) in 
      (* cPsi       |- s  : cPsi, y:A 
         cPsi, y:A  |- s' : cPsi      where s' = (s)^1

      *)
       let s' = LF.invert s  in
       let tB' = Int.LF.TClo(tB, s') in
       (* cPsi, y:A |- tB' <- type (pre-dependent) *)

         (Int.LF.App (Int.LF.Root (Int.LF.BVar x, Int.LF.Nil), tS), 
          Int.LF.PiTyp (Int.LF.TypDecl (Id.mk_name None, tA), tB'))

(*  DEAD CODE - bp


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
*)

(* ******************************************************************* *)
(* PHASE 2 : Reconstruction *)


(*  recTerm cPsi M sA = ()

    Pre-condition:

    U = FV(M) (FV(A), FV(K) resp.)
    O = meta-variables in M (A, K, resp.)

   Invariant:
    If  O ; U ; cPsi |- M <- [s]A (predependent)
        and there exists a modal substitution r  
        s.t. O' |- r <= O
    then 

       recTerm cPsi M sA succeeds and 

       O' ; [|r|]U ; [|r|]cPsi |- [|r|]M <= [|r|][s]A 
  
   Post-condition: 

     U' = [|r|]U
     O' s.t. O' |- r <= O , and 

   Effect: 
     - all meta-variables in O have been destructively updated. 
     - may raise exception Error, if no modal substitution r exists.

Similar invariants and pre- and post-conditions for:

    recKind cPsi K = K'
    recTyp  cPsi A = A'

*)
let rec recKind cPsi tK = match tK with
  | Int.LF.Typ ->
      ()

  | Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK) -> 
     (recTyp cPsi tA ;
      recKind (Int.LF.DDec (cPsi, Int.LF.TypDecl (x,tA))) tK
     )


and recTyp cPsi tA = match tA with
  | Int.LF.Atom (a, tS) ->
      let tK = (Typ.get a).Typ.kind in
        recKSpine cPsi tS (tK, LF.id)

  | Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB) -> (
      recTyp cPsi tA ;
      recTyp (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) tB
    )

and recTerm cPsi tM sA = 
  recTermW cPsi tM (Whnf.whnfTyp sA)

and recTermW cPsi tM sA = match (tM, sA) with
  | (Int.LF.Lam (_, tM), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
        recTerm cPsi' tM (tB, LF.dot1 s)

  | (Int.LF.Root (Int.LF.Const c, tS), (Int.LF.Atom _ as tP, s)) ->
      let tA = (Term.get c).Term.typ in
        recSpine cPsi tS (tA, LF.id) (tP, s)

  | (Int.LF.Root (Int.LF.BVar x, tS), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        recSpine cPsi tS (tA, LF.id) (tP, s)

  | (Int.LF.Root (Int.LF.MVar (_u, _s), _tS), _sP) ->
     (* would need to be lowered ? – since M is not kept in 
        whnf, may need to do it manually? Maybe automatically lowered
        since u must occur in a type, and it will be lowered there? 
         -bp *)
      raise NotImplemented

  | (Int.LF.Root (Int.LF.FVar x, tS), (Int.LF.Atom _ as tP, s)) ->
      let tA = FVar.get x in 
        recSpine cPsi tS (tA, LF.id) (tP, s)

  | _ ->
      raise Error (* Error message *)

and recSpine cPsi tS sA sP = 
      recSpineW cPsi tS (Whnf.whnfTyp sA) sP 

and recSpineW cPsi tS sA sP = match (tS, sA) with 
  | (Int.LF.Nil, (tP',s'))   -> 
      Unif.unifyTyp (Context.dctxToHat cPsi, sP, (tP', s'))

  | (Int.LF.App(tM, tS), (Int.LF.PiTyp (Int.LF.TypDecl(_,tA), tB), s)) ->
      (recTerm  cPsi tM (tA,s);
       recSpine cPsi tS (tB, Int.LF.Dot(Int.LF.Obj(tM), s)) sP
      )
  (* other case: tS = SClo(tS',s') cannot happen *)        


and recKSpine cPsi tS sK = match (tS, sK) with 
  | (Int.LF.Nil, (Int.LF.Typ, _s))   -> 
      ()

  | (Int.LF.App(tM, tS), (Int.LF.PiKind (Int.LF.TypDecl(_,tA), tK), s)) ->
      (recTerm  cPsi tM (tA,s);
       recKSpine cPsi tS (tK, Int.LF.Dot(Int.LF.Obj(tM), s)) 
      )

  (* other case: tS = SClo(tS',s') cannot happen *)

(* ******************************************************************* *)
(* Abstraction:

   - Abstract over the meta-variables in O
   - Abstract over the free variables in U

   Abstraction only succeeds, if O and U are not cyclic.

   Abstraction should be in a different module. -bp
 *)


let rec abstractKind tK = match tK with
  | _ -> 
      (tK, 0) (* TODO implement this *)

and abstractTyp tA = match tA with
  | _ -> 
      (tA, 0) (* TODO implement this *)


(* wrapper function *)
let rec recSgnDecl d = match d with
  | Ext.LF.SgnTyp (_, a, extK)   ->
      let apxK     = index_kind (BVar.create ()) extK in
      let tK       = elKind Int.LF.Null apxK in
      let _        = recKind Int.LF.Null tK in
      let (tK', i) = abstractKind tK in
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
      (* why does Term.add return a' ? -bp *)
        Int.LF.SgnTyp (a', tK')

  | Ext.LF.SgnConst (_, c, extT) ->
      let apxT     = index_typ (BVar.create ()) extT in
      let tA       = elTyp Int.LF.Null apxT in
      let _        = recTyp Int.LF.Null tA in
      let (tA', i)  = abstractTyp tA in
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
        Int.LF.SgnConst (c', tA')

