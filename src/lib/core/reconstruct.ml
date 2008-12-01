(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
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

module Unif = Unify.UnifyNoTrail
module E    = Ext.LF
module A    = Apx.LF
module I    = Int.LF

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

   Translates an object ext_m in external syntax
   into an object m in approximate internal syntax.
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
    | A.Nil ->
        true
          
    | A.App (A.Root (A.BVar x, A.Nil), spine) ->
        not (List.mem x seen_vars) && patSpine' (x :: seen_vars) spine
          
    | _ ->  false
  in 
    patSpine' [] spine

(* elKind  cPsi (k,s) = K 

*)
let rec elKind cPsi k = match k with 
  | A.Typ -> 
      I.Typ

  | A.PiKind (A.TypDecl (x, a), k) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (I.DDec (cPsi, I.TypDecl (x, tA))) in
      let tK    = elKind cPsi' k in
        I.PiKind (I.TypDecl (x, tA), tK)

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
  | A.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let tS = elKSpineI cPsi s i (tK, Substitution.LF.id) in
        I.Atom (a, tS)

  | A.PiTyp (A.TypDecl (x, a), b) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (I.DDec (cPsi, I.TypDecl (x, tA))) in
      let tB    = elTyp cPsi' b in
        I.PiTyp (I.TypDecl (x, tA), tB)

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
  | (A.Lam (x, m), (I.PiTyp (tA, tB), s)) ->
      let cPsi' = I.DDec (cPsi, LF.decSub tA s) in
      let tM    = elTerm cPsi' m (tB, LF.dot1 s) in
        I.Lam(x, tM)

  | (A.Root (A.Const c, spine), ((I.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let tS = elSpineI cPsi spine i (tA, LF.id) (tP, s) in
        I.Root (I.Const c, tS)

  | (A.Root (A.BVar x, spine), (I.Atom _ as tP, s)) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in
        I.Root (I.BVar x, tS)

  | (A.Root (A.FVar x, spine), (I.Atom _ as tP, s)) ->
      try
        let tA = FVar.get x in
        let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in
          I.Root (I.FVar x, tS)
      with Not_found ->
        if patSpine spine then
          let (tS, tA) = elSpineSynth cPsi spine (tP,s) in
          let _        = FVar.add x tA in
            I.Root (I.FVar x, tS)
        else
          raise NotImplemented
          (*
            let placeholder = ref I.Nil in
               (add_delayed
                  let tA = FVar.get x in
                     placeholder := elSpine cPsi spine (tA, LF.id) (tP, s);
                I.Root (I.FVar x, placeholder)
               )
          *)

  | _ ->
      raise (Error (IllTyped (cPsi, m, sA)))

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
      | (I.PiTyp (I.TypDecl (_, tA), tB), s) ->
          let u = Context.newMVar (cPsi, I.TClo (tA, s)) in
          let h = I.MVar (u, LF.id) in 
            elSpineI cPsi spine (i - 1) (tB, I.Dot (I.Head h, s)) sP

      (* other cases impossible by (soundness?) of abstraction *)

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
  | (A.Nil, (I.Atom (a, _spine), _s)) -> 
      let (I.Atom (a', _spine'), _s') = sP in 
        if a = a' then
          I.Nil
        else
          raise (Error (TypMisMatch (cPsi, sA, sP)))

  | (A.Nil, _) ->
      raise (Error ExpNilNotAtom)

  | (A.App (m, spine), (I.PiTyp (I.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm  cPsi m (tA, s) in 
      let tS = elSpine cPsi spine (tB, I.Dot (I.Obj tM, s)) sP in
        I.App (tM, tS)

  | (A.App _, _) ->
      raise (Error ExpAppNotFun)

(* see invariant for elSpineI *)
and elKSpineI cPsi spine i sK = 
  if  i = 0 then 
    elKSpine cPsi spine sK
  else 
    match sK with 
      | (I.PiKind (I.TypDecl (_, tA), tK), s) ->
          let u = Context.newMVar (cPsi, I.TClo (tA, s)) in
          let h = I.MVar (u, LF.id) in 
            elKSpineI cPsi spine (i - 1) (tK, I.Dot (I.Head h, s))

      (* other cases impossible by (soundness?) of abstraction *)

     
(* see invariant for elSpine *)
and elKSpine cPsi spine sK = match (spine, sK) with
  | (A.Nil, (I.Typ, _s)) -> 
      I.Nil

  | (A.Nil, _) ->
      raise (Error KindMisMatch)

  | (A.App (m, spine), (I.PiKind (I.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm   cPsi m (tA, s) in 
      let tS = elKSpine cPsi spine (tK, I.Dot (I.Obj tM, s)) in
        I.App (tM, tS)

  | (A.App _, _) ->
      raise (Error ExpAppNotFun)

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
  | (A.Nil, (tP, s))  ->
      (I.Nil, I.TClo (tP, s))

  | (A.App (A.Root (A.BVar x, A.Nil), spine), sP) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in   
      let (tS, tB) = elSpineSynth cPsi spine sP in 

      let s = I.Dot (I.Head (I.BVar x), LF.id) in 
      (* cPsi       |- s  : cPsi, y:A 
         cPsi, y:A  |- s' : cPsi      where s' = (s)^1

      *)
       let s' = LF.invert s in
       let tB' = I.TClo (tB, s') in
       (* cPsi, y:A |- tB' <- type (pre-dependent) *)

         (I.App (I.Root (I.BVar x, I.Nil), tS), 
          I.PiTyp (I.TypDecl (Id.mk_name None, tA), tB'))

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
  | I.Typ ->
      ()

  | I.PiKind (I.TypDecl (x, tA), tK) -> (
      recTyp cPsi tA;
      recKind (I.DDec (cPsi, I.TypDecl (x,tA))) tK
    )

and recTyp cPsi tA = match tA with
  | I.Atom (a, tS) ->
      let tK = (Typ.get a).Typ.kind in
        recKSpine cPsi tS (tK, LF.id)

  | I.PiTyp (I.TypDecl (x, tA), tB) -> (
      recTyp cPsi tA;
      recTyp (I.DDec (cPsi, I.TypDecl (x, tA))) tB
    )

and recTerm cPsi tM sA = 
  recTermW cPsi tM (Whnf.whnfTyp sA)

and recTermW cPsi tM sA = match (tM, sA) with
  | (I.Lam (_, tM), (I.PiTyp (tA, tB), s)) ->
      let cPsi' = I.DDec (cPsi, LF.decSub tA s) in
        recTerm cPsi' tM (tB, LF.dot1 s)

  | (I.Root (I.Const c, tS), (I.Atom _ as tP, s)) ->
      let tA = (Term.get c).Term.typ in
        recSpine cPsi tS (tA, LF.id) (tP, s)

  | (I.Root (I.BVar x, tS), (I.Atom _ as tP, s)) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
        recSpine cPsi tS (tA, LF.id) (tP, s)

  | (I.Root (I.MVar (I.Inst (_tM, _cPhi, _tP', _cnstr), _s), _tS), ((I.Atom _ as _tP), _s')) ->
     (* would need to be lowered ? – since M is not kept in 
        whnf, may need to do it manually? Maybe automatically lowered
        since u must occur in a type, and it will be lowered there? 
         -bp *)
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

  | (I.Root (I.FVar x, tS), (I.Atom _ as tP, s)) ->
      let tA = FVar.get x in 
        recSpine cPsi tS (tA, LF.id) (tP, s)

and recSpine cPsi tS sA sP = 
  recSpineW cPsi tS (Whnf.whnfTyp sA) sP 

and recSpineW cPsi tS sA sP = match (tS, sA) with 
  | (I.Nil, (tP', s')) -> 
      Unif.unifyTyp (Context.dctxToHat cPsi, sP, (tP', s'))

  | (I.App (tM, tS), (I.PiTyp (I.TypDecl (_, tA), tB), s)) -> (
      recTerm  cPsi tM (tA,s);
      recSpine cPsi tS (tB, I.Dot(I.Obj(tM), s)) sP
    )

  (* other case: tS = SClo(tS',s') cannot happen *)        

and recKSpine cPsi tS sK = match (tS, sK) with 
  | (I.Nil, (I.Typ, _s)) -> 
      ()

  | (I.App (tM, tS), (I.PiKind (I.TypDecl (_,tA), tK), s)) -> (
      recTerm   cPsi tM (tA,s);
      recKSpine cPsi tS (tK, I.Dot (I.Obj tM, s))
    )

  (* other case: tS = SClo(tS',s') cannot happen *)

(*
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

*)

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
  | E.SgnTyp (_, a, extK)   ->
      let apxK     = index_kind (BVar.create ()) extK in
      let tK       = elKind I.Null apxK in
      let _        = recKind I.Null tK in
      let (tK', i) = abstractKind tK in
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        (* why does Term.add return a' ? -bp *)
        (* because (a : name) and (a' : cid_typ) *)
        I.SgnTyp (a', tK')

  | E.SgnConst (_, c, extT) ->
      let apxT     = index_typ (BVar.create ()) extT in
      let tA       = elTyp I.Null apxT in
      let _        = recTyp I.Null tA in
      let (tA', i)  = abstractTyp tA in
        (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
        I.SgnConst (c', tA')
