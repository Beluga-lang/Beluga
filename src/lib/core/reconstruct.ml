(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

(* TO DO:
  
   - add appropriate case for FV to unify

   - Finish collect

   - Finish recSub

   - Write phase 2 and phase 3 for abstraction

   - Deal with FV which are non-patterns
  
   - Create test cases for type reconstruction

   - Code walk for reconstruction

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


   ASSUMPTION:

      ext_m is in beta-eta normal form
          m is in beta-eta normal form, i.e.
      all occurrences of free variables in m
      are eta-expanded.

   Generalization:
      Allow user to write terms which are not eta-expanded.
      this requires a change in the definition of FVar constructor. 

      FVar of name     

      would need to change to  FVar of name * sub * typ * dctx
      and may also need information about its type and context in 
      which it was created;                      
              
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

   if |cPsi| |- a <= type and 
      a is in beta-eta normal form
   then
       cPsi   |- A <- type (pre-dependent)
   and A is in beta-eta normal form.

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
                                m is in beta-eta normal form.
   if |cPsi| |- m <= |[s]A'| 
       cPsi  |- s <= cPsi'
       cPsi' |- A <- type (pre-dependent)       
   then 
       cPsi |- M <- A     (pre-dependent)       
   and M is in beta-eta normal form, i.e.
     all free variables are eta-expanded.

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
        (* For type reconstruction to succeed, we must have
            . |- tA <= type 
           This will be enforced during abstraction *)
        let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in
          I.Root (I.FVar x, tS)
      with Not_found ->
        if patSpine spine then          
          let (tS, tA) = elSpineSynth cPsi spine (tP,s) in
          (* For type reconstruction to succeed, we must have
            . |- tA <= type  and cPsi |- tS : tA <= [s]tP
            This will be enforced during abstraction. 
        *)
          let _        = FVar.add x tA in
            I.Root (I.FVar x, tS) 
        else
          raise NotImplemented 
          (*
            let v = newMVar (cPsi, TClo(tP, s))  in
               (add_delayed (cPsi |- m = v[id])
                I.Root (I.MVar (v, LF.id), I.Nil)
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
      and spine is a pattern spine


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
      (*  cPsi |- tS : tB <- sP  (pre-dependent) *)
      (*  show there exists: tB'  s.t [x/y,id(cPsi)]tB' = tB 
           tB' = [(x/y, id(cPsi))^-1] tB                                 
      *)
      let s = I.Dot (I.Head (I.BVar x), LF.id) in 
      (* cPsi       |- s  : cPsi, y:A 
         cPsi, y:A  |- s' : cPsi      where s' = (s)^1

      *)
       let s' = LF.invert s in
       let tB' = I.TClo (tB, s') in
       (* cPsi, y:A |- tB' <- type (pre-dependent) *)

         (I.App (I.Root (I.BVar x, I.Nil), tS), 
          I.PiTyp (I.TypDecl (Id.mk_name None, tA), tB'))
   
   (* other cases impossible *)

(* ******************************************************************* *)
(* PHASE 2 : Reconstruction *)

(*  recTerm cPsi sM sA = ()

    Pre-condition:

    U = FV(M) (FV(A), FV(K) resp.)
    O = meta-variables in M (A, K, resp.)

   Invariant:
    If  O ; U ; cPsi |- [s']M <- [s]A (predependent)
        and there exists a modal substitution r  
        s.t. O' |- r <= O
    then 

       recTerm cPsi sM sA succeeds and 

       O' ; [|r|]U ; [|r|]cPsi |- [|r|][s']M <= [|r|][s]A 
  
   Post-condition: 

     U' = [|r|]U
     O' s.t. O' |- r <= O , and 

   Effect: 
     - all meta-variables in O have been destructively updated. 
     - may raise exception Error, if no modal substitution r exists.

Similar invariants and pre- and post-conditions for:

    recKind cPsi (K,s) = K'
    recTyp  cPsi (A,s) = A'

*)
let rec recKind cPsi sK = match sK with
  | (I.Typ, _s) ->
      ()

  | (I.PiKind (I.TypDecl(_x, tA) as adec, tK), s) -> (
      recTyp cPsi (tA, s);
      recKind (I.DDec (cPsi, LF.decSub adec s)) (tK, LF.dot1 s)
    )

and recTyp cPsi sA = recTypW cPsi (Whnf.whnfTyp sA)

and recTypW cPsi sA = match sA with
  | (I.Atom (a, tS) , s) ->
      let tK = (Typ.get a).Typ.kind in
        recKSpine cPsi (tS, s) (tK, LF.id)

  | (I.PiTyp ((I.TypDecl (_x, tA) as adec), tB), s) -> (
      recTyp cPsi (tA, s);
      recTyp (I.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s)
    )

and recTerm cPsi sM sA = 
  recTermW cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW cPsi sM sA = match (sM, sA) with
  | ((I.Lam (_, tM), s'), (I.PiTyp (tA, tB), s)) ->
      let cPsi' = I.DDec (cPsi, LF.decSub tA s) in
        recTerm cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)

  | ((I.Root (I.Const c, tS), s'), (I.Atom _ as tP, s)) ->
      let tA = (Term.get c).Term.typ in
        recSpine cPsi (tS, s') (tA, LF.id) (tP, s)

  | ((I.Root (I.BVar x, tS), s'), (I.Atom _ as tP, s)) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
        recSpine cPsi (tS, s') (tA, LF.id) (tP, s)

  | ((I.Root (I.MVar (I.Inst (_r, cPhi, tP', _cnstr), t), _tS), s'), (I.Atom _ as tP, s)) ->
     (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
     (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in 
        (recSub cPsi s1 cPhi;
         Unif.unifyTyp (Context.dctxToHat cPsi, (tP', s1), (tP, s))
        )               

  | ((I.Root (I.FVar x, tS), s'), (I.Atom _ as tP, s)) ->
      (* x is in eta-expanded form and tA is closed 
         type of FVar x : A[cPsi'] and FVar x should be 
         associated with a substitution, since tA is not always
         closed. 
 
         by invariant of whnf: s' = id 
      *)
      let tA = FVar.get x in 
        recSpine cPsi (tS,s') (tA, LF.id) (tP, s)

and recSpine cPsi sS sA sP = 
  recSpineW cPsi sS (Whnf.whnfTyp sA) sP 

and recSpineW cPsi sS sA sP = match (sS, sA) with 
  | ((I.Nil, _s), (tP', s')) -> 
      Unif.unifyTyp (Context.dctxToHat cPsi, sP, (tP', s'))

  | ((I.App (tM, tS), s'), (I.PiTyp (I.TypDecl (_, tA), tB), s)) -> (
      recTerm  cPsi (tM, s') (tA,s);
      recSpine cPsi (tS, s') (tB, I.Dot (I.Obj tM, s)) sP
    )

  (* other case: tS = SClo(tS',s') to be added -bp *)        

and recKSpine cPsi sS sK = match (sS, sK) with 
  | ((I.Nil, _s), (I.Typ, _s')) -> 
      ()

  | ((I.App (tM, tS), s'), (I.PiKind (I.TypDecl (_,tA), tK), s)) -> (
      recTerm   cPsi (tM, s') (tA,s);
      recKSpine cPsi (tS, s') (tK, I.Dot (I.Obj tM, s))
    )

  (* other case: tS = SClo(tS',s') to be added -bp *)


and recSub cPsi s cPhi = match (s, cPhi) with
  | (I.Shift _n, _cPhi) ->
      ()

  | (I.Dot (I.Head I.BVar x, s), I.DDec (cPhi, I.TypDecl (_, _tA))) ->
      let I.TypDecl (_, _tA') = Context.ctxDec cPsi x in (
          recSub  cPsi s cPhi;
          (* unifyTyp cPsi (tA', s) (tA, LF.id) *)
          raise NotImplemented
        )

  | (I.Dot (I.Obj tM, s), I.DDec (cPhi, I.TypDecl (_, tA))) -> (
      recSub  cPsi s cPhi;
      recTerm cPsi (tM, LF.id) (tA, s)
    )

  (* needs other cases for Head(h) where h = MVar, Const, etc. -bp *)

(* ******************************************************************* *)
(* Abstraction:

   - Abstract over the meta-variables in O
   - Abstract over the free variables in F

   Abstraction only succeeds, if O and F are not cyclic.

   Abstraction should be in a different module. -bp

  We write {{Q}} for the context of Q, where MVars and FVars have
  been translated to declarations and their occurrences to BVars.
  We write {{A}}_Q, {{M}}_Q, {{S}}_Q for the corresponding translation 
  of a type, an expression or spine.

  Just like contexts Psi, any Q is implicitly assumed to be
  well-formed and in dependency order. ** note that Q may contain
  cyclic dependencies, which need to be detected **

  We write  Q ; Psi ||- M  if all MVars and FVars in M and Psi are 
  collected in Q. In particular, . ; Psi ||- M means M and Psi contain 
  no MVars or FVars.  Similarly, for spines . ; Psi ||- S and other 
  syntactic categories.

  Abstraction proceeds in three phases:

   - Collection of all MVars and FVars in M into Q;
  
   - Abstraction over all MVars and FVars (which are listed in Q) 
     and occur in M, will yield a new term M' 

   - 

 Collection and abstraction raise Error if there are unresolved
  constraints after simplification.



*)

  type free_var =
    | MV of I.head          (* Y ::= u[s]   where h = MVar(u, Psi, P, _)
                               and    Psi |- u[s] <= [s]P *)
    | FV of Id.name * I.typ (*     | (F, A)                  . |- F <= A *)


(* exists p cQ = B
   where B iff cQ = cQ1, Y, cQ2  s.t. p(Y)  holds
*)
let exists p cQ =
  let rec exists' cQ = match cQ with 
    | I.Empty        -> false
    | I.Dec(cQ', y)  -> p(y) || exists' cQ'
  in
    exists' cQ


(* eqMoVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let rec eqMVar mV1 mV2 = match (mV1, mV2) with
  | (I.MVar (I.Inst (r1, _, _, _), _s) , MV (I.MVar (I.Inst (r2, _, _, _), _s'))) -> 
       r1 = r2
  | _ -> false

(* eqFVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FV (n2, _)) -> (n1 = n2)
  | _ ->  false


let rec raiseType cPsi tA = match cPsi with
  | I.Null -> tA
  | I.DDec (cPsi', decl) -> 
      raiseType cPsi' (I.PiTyp (decl, tA))


(* collectTerm cQ phat (tM,s) = cQ' 
   
   Invariant:

   If  cPsi' |- tM <= tA'   and 
       cPsi  |- s  <= cPsi' and  (tM, s) is ins whnf
                            and   phat = |cPsi|
       No circularities in [s]tM
       (enforced by extended occurs-check for FVars 
        in Unify (to be done -bp))

   then cQ' = cQ, cQ'' 
        where cQ'' contains all MVars and FVars in tM
            all MVars and FVars in s are already in cQ.


   Improvement: if tM is in normal form, we don't
                need to call whnf.
*)
let rec collectTerm cQ phat sM = collectTermW cQ phat (Whnf.whnf sM)

and collectTermW cQ ((cvar, offset) as phat) sM = match sM with
  | (I.Lam (_x, tM), s) -> 
      collectTerm cQ (cvar, offset + 1) (tM, LF.dot1 s)

  | (I.Root (h, tS), s) -> 
      let cQ' = collectHead cQ phat (h,s) in 
        collectSpine cQ' phat (tS, s)


(* collectSpine cQ phat (S, s) = cQ' 

   Invariant: 
   If    cPsi |- s : cPsi1     cPsi1 |- S : A > P
   then  cQ' = cQ, cQ''
       where cQ'' contains all MVars and FVars in (S, s)

*)
and collectSpine cQ phat sS = match sS with 
  | (I.Nil, _) -> cQ

  | (I.SClo (tS, s'), s) ->
    (* need to collect MVars and FVars from s' first? 
       since invariant of collectTerm says so... *)
      collectSpine cQ phat (tS, LF.comp s' s)

  | (I.App (tM, tS), s) ->
    let cQ' = collectTerm cQ phat (tM, s) in 
      collectSpine cQ' phat (tS, s)


(* collectSub cQ phat s = cQ'

   Invariant: 
   If    cPsi |- s : cPsi1    and phat = |cPsi|
   then  cQ' = cQ, cQ''
   where cQ'' contains all MVars and FVars in s
*)
and collectSub cQ phat s = match s with 
  | (I.Shift _) -> cQ 
  | (I.Dot (I.Head h, s)) -> 
    let cQ' = collectHead cQ phat (h, LF.id) in 
      collectSub cQ' phat s

  | (I.Dot (I.Obj tM, s)) ->
    let cQ' = collectTerm cQ phat (tM, LF.id) in 
      collectSub cQ' phat s

  (*
  | (I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
  *)


and collectHead cQ phat sH = match sH with
  | (I.BVar _x, _s)  -> cQ
  | (I.Const _c, _s) -> cQ
  | (I.FVar name, s) ->
      if exists (eqFVar name) cQ then  
        cQ
      else 
        let  tA  = FVar.get name in 
        (* tA must be closed *)          
        (* Since we only use abstraction on pure LF objects,
           there are no context variables; different abstraction
           is necessary for handling computation-level expressions,
           and LF objects which occur in computations. *)
        let cQ' = collectTyp cQ (None, 0) (tA, LF.id) in  
          collectSub (I.Dec (cQ', FV (name, tA))) phat s

  | (I.MVar (I.Inst(_r, cPsi, tA, _cnstrs), s') as u, s) -> 
      if exists (eqMVar u) cQ then
        collectSub cQ phat (LF.comp s' s)  
      else  
        (*  checkEmpty !cnstrs ? -bp *) 
        let tA' = raiseType cPsi tA  (* tA' = Pi cPsi. tA *) in 
        let cQ' = collectTyp cQ (None,0) (tA', LF.id) in   
          collectSub (I.Dec (cQ', MV u)) phat (LF.comp s' s)



and collectTyp cQ ((cvar, offset) as phat) sA =  match sA with
  | (I.Atom (_a, tS), s) -> collectSpine cQ phat (tS, s)
  | (I.PiTyp (I.TypDecl (_, tA), tB), s) -> 
      let cQ' = collectTyp cQ phat (tA, s) in
        collectTyp cQ' (cvar, offset + 1) (tB, LF.dot1 s)


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
      let _        = FVar.clear ()
      let tK       = elKind I.Null apxK in
      let _        = recKind I.Null (tK, LF.id) in
      let (tK', i) = abstractKind tK in
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        (* why does Term.add return a' ? -bp *)
        (* because (a : name) and (a' : cid_typ) *)
        I.SgnTyp (a', tK')

  | E.SgnConst (_, c, extT) ->
      let apxT     = index_typ (BVar.create ()) extT in
      let _        = FVar.clear ()
      let tA       = elTyp I.Null apxT in
      let _        = recTyp I.Null (tA, LF.id) in
      let (tA', i) = abstractTyp tA in
        (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
        I.SgnConst (c', tA')
