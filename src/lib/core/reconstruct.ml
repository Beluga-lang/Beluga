(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

(* TODO

   - add appropriate case for FV to unify
   - Deal with FV which are non-patterns
   - Write cycle detection 
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

module Unify = Unify.StdTrail

exception NotImplemented

type error =
  | ExpAppNotFun
  | ExpNilNotAtom
  | KindMisMatch
  | SubIllTyped
  | TypMisMatch of Int.LF.dctx * Int.LF.tclo * Int.LF.tclo
  | IllTyped    of Int.LF.dctx * Apx.LF.normal * Int.LF.tclo

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
        Apx.LF.FVar n

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

let rec etaExpandMV cPsi sA = etaExpandMV' cPsi (Whnf.whnfTyp sA) 

and etaExpandMV' cPsi sA  = match sA with

  | (Int.LF.Atom (_a, _tS) as tP, s) -> 
    let u      = Context.newMVar (cPsi, Int.LF.TClo (tP, s)) in         
      Int.LF.Root(Int.LF.MVar (u, LF.id), Int.LF.Nil)

  | (Int.LF.PiTyp (Int.LF.TypDecl(x, _tA) as decl, tB), s) -> 
      Int.LF.Lam (x, etaExpandMV (Int.LF.DDec(cPsi, decl)) (tB, LF.dot1 s))

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

   if |cPsi| |- a <= type and
      a is in beta-eta normal form
   then
       cPsi   |- A <- type (pre-dependent)
   and A is in beta-eta normal form.

   Effect:
       Upsilon' = FV(A)  where Upsilon' is an extension of Upsilon

*)
and elTyp cPsi a = match a with
  | Apx.LF.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let _        = Printf.printf "\n Elaborate spine for constant : "; print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_kind tK in
      let tS = elKSpineI cPsi s i (tK, Substitution.LF.id) in
        Int.LF.Atom (a, tS)

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp cPsi' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB)

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
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
        let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        if patSpine spine then
          let (tS, tA) = elSpineSynth cPsi spine (tP, s) in
            (* For type reconstruction to succeed, we must have
               . |- tA <= type  and cPsi |- tS : tA <= [s]tP
               This will be enforced during abstraction.
            *)
          let _        = FVar.add x tA in
            Int.LF.Root (Int.LF.FVar x, tS)
        else
          (Printf.printf "Reconstruction of free variables with non-pattern spines not handled";
           print_newline ();
           raise NotImplemented)
            (*
              let v = newMVar (cPsi, TClo(tP, s)) in
              (add_delayed (cPsi |- m = v[id])
                Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)
              )
            *)
      end

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
      | (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s) ->
          let tN     = etaExpandMV cPsi (tA,s) in
          let spine' = elSpineI cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) sP in
            (* This only works, if tA is atomic -- if tA is not atomic, we
               need to eta-expand h, so we preserve normal forms -bp *)
            Int.LF.App (tN, spine')

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
  | (Apx.LF.Nil, (Int.LF.Atom (a, _spine), _s)) ->
      let (Int.LF.Atom (a', _spine'), _s') = sP in
        if a = a' then
          Int.LF.Nil
        else
          raise (Error (TypMisMatch (cPsi, sA, sP)))

  | (Apx.LF.Nil, _) ->
      raise (Error ExpNilNotAtom)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm  cPsi m (tA, s) in
      let tS = elSpine cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) sP in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      raise (Error ExpAppNotFun)

(* see invariant for elSpineI *)
and elKSpineI cPsi spine i sK =
  if  i = 0 then
    elKSpine cPsi spine sK
  else
    match sK with
      | (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s) ->
          let tN     = etaExpandMV cPsi (tA,s) in
          let spine' = elKSpineI cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

      (* other cases impossible by (soundness?) of abstraction *)


(* see invariant for elSpine *)
and elKSpine cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (Int.LF.Typ, _s)) ->
      Int.LF.Nil

  | (Apx.LF.Nil, _) ->
      raise (Error KindMisMatch)

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm   cPsi m (tA, s) in
      let tS = elKSpine cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      raise (Error ExpAppNotFun)

(* elSpineSynth cPsi spine sP = (S, A')

   Pre-condition:
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; Psi |- spine < [s]P
      and spine is a pattern spine

   then O ; U ; Psi |- S : A' < [s]P

   Post-condition:
     U = containing all free variables of S (unchanged)
     O = containing new meta-variables of S (unchanged)

*)
and elSpineSynth cPsi spine sP = match (spine, sP) with
  | (Apx.LF.Nil, (tP, s))  ->
      (Int.LF.Nil, Int.LF.TClo (tP, s))

  | (Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (tS, tB) = elSpineSynth cPsi spine sP in
      (*  cPsi |- tS : tB <- sP  (pre-dependent) *)
      (*  show there exists: tB'  s.t [x/y,id(cPsi)]tB' = tB
           tB' = [(x/y, id(cPsi))^-1] tB
      *)
      let s = Int.LF.Dot (Int.LF.Head (Int.LF.BVar x), LF.id) in
      (* cPsi       |- s  : cPsi, y:A
         cPsi, y:A  |- s' : cPsi      where s' = (s)^1

      *)
       let s' = LF.invert s in
       let tB' = Int.LF.TClo (tB, s') in
       (* cPsi, y:A |- tB' <- type (pre-dependent) *)

         (Int.LF.App (Int.LF.Root (Int.LF.BVar x, Int.LF.Nil), tS),
          Int.LF.PiTyp (Int.LF.TypDecl (Id.mk_name None, tA), tB'))

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
  | (Int.LF.Typ, _s) ->
      ()

  | (Int.LF.PiKind (Int.LF.TypDecl(_x, tA) as adec, tK), s) -> (
      recTyp cPsi (tA, s);
      recKind (Int.LF.DDec (cPsi, LF.decSub adec s)) (tK, LF.dot1 s)
    )

and recTyp cPsi sA = recTypW cPsi (Whnf.whnfTyp sA)

and recTypW cPsi sA = match sA with
  | (Int.LF.Atom (a, tS) , s) ->
      let tK = (Typ.get a).Typ.kind in
        recKSpine cPsi (tS, s) (tK, LF.id)

  | (Int.LF.PiTyp ((Int.LF.TypDecl (_x, tA) as adec), tB), s) -> (
      recTyp cPsi (tA, s);
      recTyp (Int.LF.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s)
    )

and recTerm cPsi sM sA =
  recTermW cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW cPsi sM sA = match (sM, sA) with
  | ((Int.LF.Lam (_, tM), s'), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
        recTerm cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)

  | ((Int.LF.Root (Int.LF.Const c, tS), s'), (Int.LF.Atom _ as tP, s)) ->
      let tA = (Term.get c).Term.typ in
        recSpine cPsi (tS, s') (tA, LF.id) (tP, s)

  | ((Int.LF.Root (Int.LF.BVar x, tS), s'), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        recSpine cPsi (tS, s') (tA, LF.id) (tP, s)

  | ((Int.LF.Root (Int.LF.MVar (Int.LF.Inst (_r, cPhi, tP', _cnstr), t), _tS), s'), (Int.LF.Atom _ as tP, s)) ->
     (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
     (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in
      let _        = Printf.printf "\n RecTerm: Unify "; print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ (Whnf.normTyp (tP',s1)) in
      let _        = Printf.printf "\n with "; print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ (Whnf.normTyp (tP,s)) in
      let _        = (recSub cPsi s1 cPhi;
                      Unify.unifyTyp (Context.dctxToHat cPsi, (tP', s1), (tP, s))) in 
       Printf.printf "\n done "; print_newline ()

  | ((Int.LF.Root (Int.LF.FVar x, tS), s'), (Int.LF.Atom _ as tP, s)) ->
      (* x is in eta-expanded form and tA is closed
         type of FVar x : A[cPsi'] and FVar x should be
         associated with a substitution, since tA is not always
         closed.

         by invariant of whnf: s' = id
      *)
      let tA = FVar.get x in
        recSpine cPsi (tS, s') (tA, LF.id) (tP, s)

and recSpine cPsi sS sA sP =
  recSpineW cPsi sS (Whnf.whnfTyp sA) sP

and recSpineW cPsi sS sA sP = match (sS, sA) with
  | ((Int.LF.Nil, _s), (tP', s')) ->
      let _        = Printf.printf "\n RecSpine Unify "; print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ (Whnf.normTyp (tP',s')) in
      let _        = Printf.printf "\n with "; print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ (Whnf.normTyp sP) in
      let _        =  Unify.unifyTyp (Context.dctxToHat cPsi, sP, (tP', s')) in 
        Printf.printf "\n done "; print_newline ()

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) -> (
      recTerm  cPsi (tM, s') (tA, s);
      recSpine cPsi (tS, s') (tB, Int.LF.Dot (Int.LF.Obj tM, s)) sP
    )

  | ((Int.LF.SClo (tS, s), s'), sA) -> 
      recSpine cPsi (tS, LF.comp s s') sA sP

and recKSpine cPsi sS sK = match (sS, sK) with
  | ((Int.LF.Nil, _s), (Int.LF.Typ, _s')) ->
      ()

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) -> (
      recTerm   cPsi (tM, s') (tA, s);
      recKSpine cPsi (tS, s') (tK, Int.LF.Dot (Int.LF.Obj tM, s))
    )

  | ((Int.LF.SClo (tS, s),  s'), sK) -> 
      recKSpine cPsi (tS, LF.comp s s') sK

and recSub cPsi s cPhi = match (s, cPhi) with
  | (Int.LF.Shift _n, _cPhi) ->
      ()

  | (Int.LF.Dot (Int.LF.Head Int.LF.BVar x, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) ->
      let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in (
          recSub  cPsi s cPhi;
          Unify.unifyTyp (Context.dctxToHat cPsi, (tA', s), (tA, LF.id))
        )

  | (Int.LF.Dot (Int.LF.Obj tM, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) -> (
      recSub  cPsi s cPhi;
      recTerm cPsi (tM, LF.id) (tA, s)
    )

  (* needs other cases for Head(h) where h = MVar, Const, etc. -bp *)

let recSgnDecl d = match d with
  | Ext.Sgn.Typ (_, a, extK)   ->
      let apxK     = index_kind (BVar.create ()) extK in
      let _        = FVar.clear () in
      let _        = Printf.printf "Reconstruction for constant : %s " a.string_of_name; print_newline () in
      let tK       = elKind Int.LF.Null apxK in
      let _        = recKind Int.LF.Null (tK, LF.id) in
      let (tK', i) = Abstract.abstrKind tK in
      let _        = Printf.printf "\n Reconstruction for constant : %s done -- number of implicit arg: %s " a.string_of_name (string_of_int i); print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_kind tK' in
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        (* why does Term.add return a' ? -bp *)
        (* because (a : name) and (a' : cid_typ) *)
        Int.Sgn.Typ (a', tK')

  | Ext.Sgn.Const (_, c, extT) ->
      let apxT     = index_typ (BVar.create ()) extT in
      let _        = FVar.clear () in
      let _        = Printf.printf "\n Reconstruction for constant : %s " c.string_of_name; print_newline () in
      let tA       = elTyp Int.LF.Null apxT in
      let _        = Printf.printf "\n Elaboration for constant : %s " c.string_of_name; print_newline () in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ (Whnf.normTyp (tA, LF.id)) in
      let _        = recTyp Int.LF.Null (tA, LF.id) in
      let _        = Printf.printf "\n Reconstruction (without abstraction) for : %s \n" c.string_of_name; print_newline () in
      let tAnorm   = Whnf.normTyp (tA, LF.id) in
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ tAnorm in 
      let (tA', i) = Abstract.abstrTyp tAnorm in
      let _        = Printf.printf "\n Reconstruction for constant : %s done -- number of implicit arg: %s " c.string_of_name (string_of_int i); print_newline ()  in 
      let _        = Pretty.Int.DefaultPrinter.ppr_lf_typ tA' in 
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  " c.string_of_name; print_newline ()  in 
      let _        = Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', LF.id) in  
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
        Int.Sgn.Const (c', tA')



