(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)
open Store
open Store.Cid
open Substitution
open Syntax

module I    = Int.LF
module Comp = Int.Comp

exception NotImplemented

(* ******************************************************************* *)
(* Abstraction:

   - Abstract over the meta-variables in O
   - Abstract over the free variables in F

   Abstraction only succeeds, if O and F are not cyclic.

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
                             and    Psi |- u[s] <= [s]P               *)
  | FV of Id.name * I.typ option 
                         (*     | (F, A)                  . |- F <= A *)

(* exists p cQ = B
   where B iff cQ = cQ1, Y, cQ2  s.t. p(Y)  holds
*)
let exists p cQ =
  let rec exists' cQ = match cQ with
    | I.Empty        -> false
    | I.Dec(cQ', y)  -> p y || exists' cQ'
  in
    exists' cQ

(* length cPsi = |cPsi| *)
let length cPsi = 
  let (_, n) = Context.dctxToHat cPsi in
    n

(* eqMVar mV mV' = B
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
  | _ -> false

(* index_of cQ n = i
   where cQ = cQ1, Y, cQ2 s.t. n = Y and length cQ2 = i
*)
let rec index_of cQ n = match (cQ, n) with
  | (I.Empty, _) ->
      raise Not_found (* impossible due to invariant on collect *)

  | (I.Dec (cQ', MV u1), MV u2) ->
      (* TODO investigate the feasibility of having it start at 0*)
      if eqMVar u1 (MV u2) then 1 else (index_of cQ' n) + 1 

  | (I.Dec (cQ', FV (f1, _)), FV (f2, tA)) ->
      if eqFVar f1 (FV (f2, tA)) then 1 else (index_of cQ' n) + 1

  | (I.Dec (cQ', _), _) ->
      (index_of cQ' n) + 1

let rec raiseType cPsi tA = match cPsi with
  | I.Null -> tA
  | I.DDec (cPsi', decl) ->
      raiseType cPsi' (I.PiTyp (decl, tA))

let rec raiseKind cPsi tK = match cPsi with
  | I.Null -> tK
  | I.DDec (cPsi', decl) ->
      raiseKind cPsi' (I.PiKind (decl, tK))

(* If   cQ = cQ1 (MV u) cQ2
   and  u :: A[Psi]
   then (ctxToDctx cQ) = (ctxToDctx cQ1) Pi Psi . A (ctxToDctx cQ2)

   If   cQ = cQ1 (FV (F, A)) cQ2
   then (ctxToDctx cQ) = (ctxToDctx cQ1) A (ctxToDctx cQ2)
*)
let rec ctxToDctx cQ = match cQ with
  | I.Empty ->
      I.Null

  | I.Dec (cQ', MV (I.MVar (I.Inst (_, cPsi, tA, _), _s))) ->
      I.DDec (ctxToDctx cQ', I.TypDecl (Id.mk_name None, raiseType cPsi tA))

  | I.Dec (cQ', FV (_, Some tA)) ->
      I.DDec (ctxToDctx cQ', I.TypDecl (Id.mk_name None, tA))


let rec ctxToMCtx cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', MV (I.MVar (I.Inst (_, cPsi, tA, _), _s))) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (Id.mk_name None, tA, cPsi))

  (* this case should not happen -bp *)
  | I.Dec (cQ', FV (_, Some tA)) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (Id.mk_name None, tA, I.Null))


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
      let cQ' = collectHead cQ phat (h, s) in
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

  (* this case should be impossible :

  | (I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
  *)

(* collectMSub cQ theta = cQ' *) 
and collectMSub cQ theta =  match theta with 
  | Comp.MShiftZero -> cQ 
  | Comp.MDot(Comp.MObj(phat, tM), t) -> 
    let cQ' = collectTerm cQ phat (tM, LF.id) in 
      collectMSub cQ' t

  | Comp.MDot(Comp.PObj(phat, h), t) -> 
     let cQ' = collectHead cQ phat (h, LF.id) in 
       collectMSub cQ' t

and collectHead cQ phat sH = match sH with
  | (I.BVar _x, _s)  -> cQ
  | (I.Const _c, _s) -> cQ
  | (I.FVar name, s) ->
      if exists (eqFVar name) cQ then
        cQ
      else
        let tA  = FVar.get name in
        (* tA must be closed *)
        (* Since we only use abstraction on pure LF objects,
           there are no context variables; different abstraction
           is necessary for handling computation-level expressions,
           and LF objects which occur in computations. *)
        let cQ' = collectTyp cQ (None, 0) (tA, LF.id) in
          collectSub (I.Dec (cQ', FV (name, Some tA))) phat s

  | (I.MVar (I.Inst (_r, cPsi, tA, _cnstrs), s') as u, s) ->
      if exists (eqMVar u) cQ then
        collectSub cQ phat (LF.comp s' s)
      else
        (*  checkEmpty !cnstrs ? -bp *)
        let tA' = raiseType cPsi tA  (* tA' = Pi cPsi. tA *) in
        let cQ' = collectTyp cQ (None, 0) (tA', LF.id) in
          collectSub (I.Dec (cQ', MV u)) phat (LF.comp s' s)

and collectTyp cQ ((cvar, offset) as phat) sA = match sA with
  | (I.Atom (_a, tS), s) ->
      collectSpine cQ phat (tS, s)

  | (I.PiTyp (I.TypDecl (_, tA), tB), s) ->
      let cQ' = collectTyp cQ phat (tA, s) in
        collectTyp cQ' (cvar, offset + 1) (tB, LF.dot1 s)

  | (I.TClo (tA, s'), s) ->
      collectTyp cQ phat (tA, LF.comp s' s)

and collectKind cQ ((cvar, offset) as phat) sK = match sK with
  | (I.Typ, _s) ->
      cQ

  | (I.PiKind (I.TypDecl (_, tA), tK), s) ->
      let cQ' = collectTyp cQ phat (tA, s) in
        collectKind cQ' (cvar, offset + 1) (tK, LF.dot1 s)

(* abstractKind cQ offset tK = tK'

   where tK' is tK with all occurences of FVar and MVar have been replaced by
   BVar and indexed according to their order in cQ and the base offset

   assumes there are no cycles
*)
let rec abstractKind cQ offset tK = match tK with
  | I.Typ -> I.Typ

  | I.PiKind (I.TypDecl (x, tA), tK) ->
      I.PiKind (I.TypDecl (x, abstractTyp cQ offset tA), abstractKind cQ (offset + 1) tK)

and abstractTyp cQ offset tA = match tA with
  | I.Atom (a, tS) ->
      I.Atom (a, abstractSpine cQ offset tS)

  | I.PiTyp (I.TypDecl (x, tA), tB) ->
      I.PiTyp (I.TypDecl (x, abstractTyp cQ offset tA), abstractTyp cQ (offset + 1) tB)

  | I.TClo sA ->
      abstractTyp cQ offset (Whnf.normTyp sA) (* TODO confirm that [1] *)

and abstractTerm cQ offset tM = match tM with
  | I.Lam (x, tM) ->
      I.Lam (x, abstractTerm cQ (offset + 1) tM)

  | I.Root (I.MVar(_u, s) as tH, I.Nil) -> 
      let x = index_of cQ (MV tH) + offset in 
      I.Root (I.BVar x, subToSpine cQ offset s I.Nil)

  | I.Root (tH, tS) ->
      I.Root (abstractHead cQ offset tH, abstractSpine cQ offset tS)

  | I.Clo sM ->
      abstractTerm cQ offset (Whnf.norm sM) (* TODO confirm that [1] *)

and abstractHead cQ offset tH = match tH with
  | I.BVar x ->
      I.BVar x

  | I.Const c ->
      I.Const c

(*  | I.MVar (_u, _s) ->
     
      (*
        I.BVar ((index_of cQ (MV tH)) + offset)
        unroll s as a spine
      *)
      raise NotImplemented
*)
  | I.FVar n ->
      I.BVar ((index_of cQ (FV (n, None))) + offset)

  | I.AnnH (_tH, _tA) ->
      raise NotImplemented

  (* other cases impossible for object level *)


and subToSpine cQ offset s tS = match s with
  | I.Shift k -> 
      if k < offset then 
	subToSpine cQ offset (I.Dot(I.Head(I.BVar (k+1)), I.Shift (k+1))) tS
      else (* k = offet *) tS
  | I.Dot(I.Head(h), s) -> 
      subToSpine cQ offset s (I.App(I.Root(h, I.Nil), tS))
  | I.Dot(I.Obj(tM), s) -> 
      subToSpine cQ offset s (I.App (abstractTerm cQ offset tM, tS))

and abstractSpine cQ offset tS = match tS with
  | I.Nil ->
      I.Nil

  | I.App (tM, tS) ->
      I.App (abstractTerm cQ offset tM, abstractSpine cQ offset tS)

  | I.SClo sS ->
      abstractSpine cQ offset (Whnf.normSpine sS) (* TODO confirm that [1] *)

and abstractCtx cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ, MV (I.MVar (I.Inst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractCtx cQ in
      let cPsi' = abstractDctx cQ cPsi in
(*      let  (_, depth)  = dctxToHat cPsi in  *)
      let tA'   = abstractTyp cQ (length cPsi) tA in
      let s'    = abstractSub cQ (length cPsi) s in
      let u'    = I.MVar (I.Inst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', MV u')

  | I.Dec (cQ, FV (f, Some tA)) ->
      let cQ' = abstractCtx cQ in
      let tA' = abstractTyp cQ' 0 tA in
        I.Dec (cQ', FV (f, Some tA'))

and abstractDctx cQ cPsi = match cPsi with
  | I.Null ->
      I.Null

  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractDctx cQ cPsi in
      let tA'   = abstractTyp cQ (length cPsi) tA in
        I.DDec (cPsi', I.TypDecl (x, tA'))

  (* other cases impossible in LF layer *)

and abstractSub cQ offset s = match s with
  | I.Shift _ ->
      s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractHead cQ offset tH), abstractSub cQ offset s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractTerm cQ offset tM), abstractSub cQ offset s)

  (* what about I.Dot (I.Undef, s) ? *)

  (* SVar impossible in LF layer *)

and abstrMSub cQ t = match t with
  | Comp.MShiftZero -> Comp.MShiftZero
  | Comp.MDot(Comp.MObj(phat, tM), t) -> 
     let tM' = abstractTerm cQ 0 tM in 
       Comp.MDot(Comp.MObj(phat, tM'), abstrMSub cQ t)

  | Comp.MDot(Comp.PObj(phat, h), t) -> 
     let h' = abstractHead cQ 0 h in 
       Comp.MDot(Comp.PObj(phat, h'), abstrMSub cQ t)

and abstractMSub t =  
    let cQ  = collectMSub I.Empty t in
    let t'  = abstrMSub cQ t in
    let cD  = ctxToMCtx cQ in 
     ( t' , cD) 


(* wrapper function *)
let abstrKind tK =
  (* what is the purpose of phat? *)
  let empty_phat = (None, 0) in
  let cQ         = collectKind I.Empty empty_phat (tK, LF.id) in
  let cQ'        = abstractCtx cQ in
  let tK'        = abstractKind cQ' 0 tK in
  let cPsi       = ctxToDctx cQ' in
    (raiseKind cPsi tK', length cPsi)

and abstrTyp tA =
  let empty_phat = (None, 0) in
  let cQ         = collectTyp I.Empty empty_phat (tA, LF.id) in
  let cQ'        = abstractCtx cQ in
  let tA'        = abstractTyp cQ' 0 tA in
  let cPsi       = ctxToDctx cQ' in
    (raiseType cPsi tA', length cPsi)


(* [1] maybe we only call normalisation "once" from the wrapper function, would
   need smaller interface in whnf.mli

   should be written in whnf form, since then normalization is done simultanously
   with abstraction. -bp 

 *)
