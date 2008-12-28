(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

(* TODO
   - Deal with FV which are non-patterns
   - Cycle detection ?
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

exception Error of string

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

(* Free variable constraints: 

   fvar_cnstr  C := . | Root(FVar X, tS) & C 

   The constraints are generated when encountering
   a free variable X whose type is yet unknown and has a 
   non-pattern spine tS. This means we cannot easily infer
   the type of the free variable X. 
 
*)



let fvar_cnstr : ((A.normal * I.cvar)  list) ref = ref []

let add_fvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fvarCnstr () = (fvar_cnstr := [])

let rec raiseType cPsi tA = match cPsi with
  | I.Null -> tA
  | I.DDec (cPsi', decl) ->
      raiseType cPsi' (I.PiTyp (decl, tA))

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
        (true, 0)

    | A.App (A.Root (A.BVar x, A.Nil), spine) ->
        if not (List.mem x seen_vars) then 
          let (b,l) = patSpine' (x :: seen_vars) spine in 
            (b, l+1)
        else (false, 0)

    | _ ->  (false, 0)
  in
    patSpine' [] spine


(* etaExpandMV cPsi sA s' = tN 

    cPsi'  |- s'   <= cPsi 
    cPsi   |- [s]A <= typ

    cPsi'  |- tN   <= [s'][s]A

*)
let rec etaExpandMV cPsi sA s' = etaExpandMV' cPsi (Whnf.whnfTyp sA)  s'

and etaExpandMV' cPsi sA  s' = match sA with
  | (I.Atom (_a, _tS) as tP, s) -> 
      let u = Whnf.newMVar (cPsi, I.TClo(tP,s)) in        
         I.Root (I.MVar (u, s'), I.Nil)  

  | (I.PiTyp (I.TypDecl (x, _tA) as decl, tB), s) -> 
      I.Lam (x, etaExpandMV (I.DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) (LF.dot1 s'))

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
      let (_, d) = Context.dctxToHat cPsi in  
      (* let tS = elKSpineI cPsi s i (tK, Substitution.LF.id) in *)
      let tS = elKSpineI cPsi s i (tK, I.Shift d) in  
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
  | (A.Lam (x, m), (I.PiTyp (I.TypDecl (_x, _tA) as decl, tB), s)) ->
      let cPsi' = I.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm cPsi' m (tB, LF.dot1 s) in
        I.Lam(x, tM)

  | (A.Root (A.Const c, spine), ((I.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let (_, d) = Context.dctxToHat cPsi in  
      let tS = elSpineI cPsi spine i (tA, I.Shift d) (tP, s) in 
        I.Root (I.Const c, tS)

  | (A.Root (A.BVar x, spine), (I.Atom _ as tP, s)) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in 
        I.Root (I.BVar x, tS) 

  | (A.Root (A.FVar x, spine) as m, (I.Atom _ as tP, s)) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
      (* let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in *)
        let (_, d) = Context.dctxToHat cPsi in 
      let tS = elSpine cPsi spine (tA, I.Shift d) (tP, s) in 
          I.Root (I.FVar x, tS)
      with Not_found ->
        let (patternSpine, _l) = patSpine spine in 
        if patternSpine then
        let (_, d) = Context.dctxToHat cPsi in 
        let (tS, tA) = elSpineSynth cPsi spine (I.Shift d) (tP, s) in
            (* For type reconstruction to succeed, we must have
               . |- tA <= type  and cPsi |- tS : tA <= [s]tP
               This will be enforced during abstraction.
            *)
          let _        = FVar.add x tA in
            I.Root (I.FVar x, tS)
        else
          let v = Whnf.newMVar (cPsi, I.TClo(tP, s)) in
            (add_fvarCnstr (m, v) ;
             I.Root (I.MVar (v, LF.id), I.Nil)
            )

      end

  | _ ->
      raise (Error "Ill-typed " (* (IllTyped (cPsi, m, sA)) *))

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
          (* cPsi' |- tA <= typ
             cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A

             tN = u[s']  and u::A'[.]   

             s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
             and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)
             
          *)
          let (_, d) = Context.dctxToHat cPsi in      
          let tN     = etaExpandMV I.Null (tA, s) (I.Shift d) in 
          let spine' = elSpineI cPsi spine (i - 1) (tB, I.Dot (I.Obj tN, s)) sP in
            I.App (tN, spine')
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
          raise (Error "Type mismatch " (* (TypMisMatch (cPsi, sA, sP)) *))

  | (A.Nil, _) ->
      raise (Error "Expression not of atomic type" ) (* ExpNilNotAtom *)

  | (A.App (m, spine), (I.PiTyp (I.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm  cPsi m (tA, s) in
      let tS = elSpine cPsi spine (tB, I.Dot (I.Obj tM, s)) sP in
        I.App (tM, tS)

  | (A.App _, sA) ->
      raise (Error ("Spine of atomic type " ^ 
                      (Pretty.Int.DefaultPrinter.typToString (I.TClo(sA)))))

(* see invariant for elSpineI *)
and elKSpineI cPsi spine i sK =
  if  i = 0 then
    elKSpine cPsi spine sK
  else
    match sK with
      | (I.PiKind (I.TypDecl (_, tA), tK), s) ->
          let (_, d) = Context.dctxToHat cPsi in 
          let tN     = etaExpandMV I.Null (tA,s) (I.Shift d) in
          let spine' = elKSpineI cPsi spine (i - 1) (tK, I.Dot (I.Obj tN, s)) in
            I.App (tN, spine')

      (* other cases impossible by (soundness?) of abstraction *)


(* see invariant for elSpine *)
and elKSpine cPsi spine sK = match (spine, sK) with
  | (A.Nil, (I.Typ, _s)) ->
      I.Nil

  | (A.Nil, _) ->
      raise (Error "Kind mismatch") (* KindMisMatch *)

  | (A.App (m, spine), (I.PiKind (I.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm   cPsi m (tA, s) in
      let tS = elKSpine cPsi spine (tK, I.Dot (I.Obj tM, s)) in
        I.App (tM, tS)

  | (A.App _, _) ->
      raise (Error "Non-empty spine of atomic type") (* ExpAppNotFun *)

(* elSpineSynth cPsi spine s' sP = (S, A') 

   Pre-condition:
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; Psi |- spine < [s]P
      and spine is a pattern spine
                  
              Psi |- s' <= .      |cPsi| = d  and s' = ^d

                
              Psi |- s   <= Psi'
                . |- ss' <= Psi

   then O ; U ; Psi |- S : [s']A' < [s]P

   Post-condition:
     U = containing all free variables of S (unchanged)
     O = containing new meta-variables of S (unchanged)

*)
and elSpineSynth cPsi spine s' sP = match (spine, sP) with
  | (A.Nil, (tP, s))  ->
      let ss = LF.invert s' in 
        (* ensure that [ss] ([s]tP) exists ! *)
       (I.Nil, I.TClo(tP, LF.comp s ss)) 

  | (A.App (A.Root (A.BVar x, A.Nil), spine), sP) ->
      let I.TypDecl (_, tA) = Context.ctxDec cPsi x in
      (* cPsi |- tA : type 
         cPsi |- s' : cPsi'
       *)
      let ss = LF.invert s' in 
      let tA' = Whnf.normTyp (tA, ss) in 

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth cPsi spine (I.Dot(I.Head(I.BVar x), s')) sP in

      (*  cPsi |- tS : [s', x]tB <- sP  (pre-dependent) *)

      (* cPsi, y:A |- tB' <- type (pre-dependent) *)

         (I.App (I.Root (I.BVar x, I.Nil), tS),
          I.PiTyp (I.TypDecl (Id.mk_name None, tA'), tB))

   (* other cases impossible *)


(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr cnstr = match cnstr with 
  | []  -> ()
  | ((A.Root(A.FVar x, spine) , I.Inst(r, cPsi, I.TClo(tP,s), _)) :: cnstrs) ->
     begin try 
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
        let (_, d) = Context.dctxToHat cPsi in 
          
        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let tS = elSpine cPsi spine (tA, I.Shift d) (tP,s) in 
          (r := Some (I.Root (I.FVar x, tS));
           solve_fvarCnstr cnstrs  
          )
     with Not_found ->
       raise (Error "Type reconstruction: Left-over constraints for free variables \n")
     end


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
        let (_, d) = Context.dctxToHat cPsi in 
      let tA' =  recKSpine cPsi (tS, s) (tK, I.Shift d) in 
        tA'


  | (I.PiTyp ((I.TypDecl (_x, tA) as adec), tB), s) -> (      
      recTyp cPsi (tA, s);
      recTyp (I.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s);
    )

and recTerm cPsi sM sA =
  recTermW cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW cPsi sM sA = match (sM, sA) with
  | ((I.Lam (_, tM), s'), (I.PiTyp (tA, tB), s)) ->
      let cPsi' = I.DDec (cPsi, LF.decSub tA s) in
        recTerm cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)

  | ((I.Root (I.Const c, tS), s'), (I.Atom _ as tP, s)) ->
      let tA = (Term.get c).Term.typ in
      let (_, d) = Context.dctxToHat cPsi in 
        recSpine cPsi (tS, s') (tA, I.Shift d) (tP, s)

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
      let (_, d) = Context.dctxToHat cPsi in  
        recSpine cPsi (tS, s') (tA, I.Shift d) (tP, s)    

and recSpine cPsi sS sA sP = 
  recSpineW cPsi sS (Whnf.whnfTyp sA) sP

and recSpineW cPsi sS sA sP = match (sS, sA) with
  | ((I.Nil, _s), (tP', s')) ->
      Unif.unifyTyp (Context.dctxToHat cPsi, sP, (tP', s'))  
      
  | ((I.App (tM, tS), s'), (I.PiTyp (I.TypDecl (_, tA), tB), s)) -> (
      let _ = recTerm  cPsi (tM, s') (tA, s) in 
      (*   cPsi |-  s <= cPsi1     cPsi1 |- Pi x:tA .tB <= typ
                                   cPsi1 |- tA <= typ   
                                   cPsi1, x:tA |- tB <= typ

           cPsi |-  s'<= cPsi2     cPsi |- [s']tM <= tA'   tA' = [s]tA   
           
           cPsi2 |- tM <= tA2       [s']tA2 = tA' = [s]tA
       
           cPsi |-  [s']tM . s <= cPsi1, x: tA

      *)
      recSpine cPsi (tS, s') (tB, I.Dot (I.Obj (I.Clo (tM,s')), s)) sP 
    )

  | ((I.SClo (tS, s), s'), sA) -> 
      recSpine cPsi (tS, LF.comp s s') sA sP

and recKSpine cPsi sS sK = match (sS, sK) with
  | ((I.Nil, _s), (I.Typ, _s')) ->
      ()

  | ((I.App (tM, tS), s'), (I.PiKind (I.TypDecl (_, tA), tK), s)) -> (
      recTerm   cPsi (tM, s') (tA, s);
      recKSpine cPsi (tS, s') (tK, I.Dot (I.Obj tM, s))
    )

  | ((I.SClo (tS, s),  s'), sK) -> 
      recKSpine cPsi (tS, LF.comp s s') sK

and recSub cPsi s cPhi = match (s, cPhi) with
  | (I.Shift _n, _cPhi) ->
      (* We may need to expand cPhi further if n =/= 0 *)
      ()

  | (I.Dot (I.Head I.BVar x, s), I.DDec (cPhi, I.TypDecl (_, tA))) ->
      let I.TypDecl (_, tA') = Context.ctxDec cPsi x in 
        recSub  cPsi s cPhi;
        Unif.unifyTyp (Context.dctxToHat cPsi, (tA', LF.id), (tA, s))


  | (I.Dot (I.Obj tM, s), I.DDec (cPhi, I.TypDecl (_, tA))) -> (
      recSub  cPsi s cPhi;
      recTerm cPsi (tM, LF.id) (tA, s)
    )

  | (I.Dot (I.Undef, _s), _) ->
      raise (Error "Found Undef")

  (* needs other cases for Head(h) where h = MVar, Const, etc. -bp *)

let recSgnDecl d = match d with
  | E.SgnTyp (_, a, extK)   ->
      let apxK     = index_kind (BVar.create ()) extK in
      let _        = FVar.clear () in
      let tK       = elKind I.Null apxK in
      let _        = solve_fvarCnstr !fvar_cnstr in
      let _        = reset_fvarCnstr () in 
      let _        = recKind I.Null (tK, LF.id) in
      let (tK', i) = Abstract.abstrKind tK in
      (* let _        = Printf.printf "\n Reconstruction (wih abstraction) of constant %s \n %s \n\n" a.string_of_name
        (Pretty.Int.DefaultPrinter.kindToString tK') in *)
      let _        = Check.LF.checkKind I.Empty I.Null tK' in  
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" a.string_of_name  in 
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        (* why does Term.add return a' ? -bp *)
        (* because (a : name) and (a' : cid_typ) *)
        I.SgnTyp (a', tK')

  | E.SgnConst (_, c, extT) ->
      let apxT     = index_typ (BVar.create ()) extT in
      let _        = Printf.printf "\n Reconstruct constant : %s  \n" c.string_of_name  in 
      let _        = FVar.clear () in
      let tA       = elTyp I.Null apxT in
      let _        = solve_fvarCnstr !fvar_cnstr in
      let _        = reset_fvarCnstr () in 
      (* let _        = Printf.printf "\n Elaboration of constant %s \n : %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))) in  *)
      let _        = recTyp I.Null (tA, LF.id) in
      (* let _        = Printf.printf "\n Reconstruction (without abstraction) of constant %s \n %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))) in *)

      let (tA', i) = Abstract.abstrTyp tA in 
      (*let _        = Printf.printf "\n Reconstruction (with abstraction) of constant %s \n %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA', LF.id))) in *)
      let _        = Check.LF.checkTyp I.Empty I.Null (tA', LF.id) in  
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" c.string_of_name  in 
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in 
        I.SgnConst (c', tA')



