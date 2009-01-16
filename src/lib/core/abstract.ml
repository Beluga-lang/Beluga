(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)
open Store
open Store.Cid
open Substitution
open Syntax
open Id

module S    = Substitution.LF
module I    = Int.LF
module Comp = Int.Comp

exception NotImplemented

exception Error of string

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



   Collection will work in a generic way so we can collect 
   - FVar  (named free LF-bound variables),  
   - FMVar (named free meta-variables),  
   - FPVar (named free parameter variables),  

   - MVars (references to meta-variables representing unknowns)

   Abstraction over LF-bound variables and abstraction of named
   meta-variables and parameter variables are however kept separate. 

   Abstraction over LF-bound variables is performed by the functions
   abstractTerm, abstractType, etc.

   Abstraction over meta-variables and parameter variables is
   performed by the functions abstractMVarTerm, abstractMVarType, etc.


   


*)


type free_var =
  (* Free variables (references): unnamed *)

  (* For MV and PV it suffices to store the reference for the
     respective MVar and PVar; the substitution associated with an
     MVar and PVar is irrelevant here *)

  | MV of I.head          (* Y ::= u[s]   where h = MVar(u, Psi, P, _)  
                             and    Psi |- u[s] <= [s]P               *)
  | PV of I.head          (*    |  p[s]   where h = PVar(p, Psi, A, _)
                             and    Psi |- p[s] <= [s]A               *)

  (* Free named variables *)
  | FV of Id.name * I.typ option 
                         (*     | (F, A)                  . |- F <= A *)

  | FMV of Id.name * (I.typ * I.dctx) option 
                         (*     | (F, (A, cPsi))                  cPsi |- F <= A *)

  | FPV of Id.name * (I.typ * I.dctx) option 
                         (*     | (F, (A, cPsi))                  cPsi |- F <= A *)

let freeVarToString x = match x with
  | (MV tH) -> Pretty.Int.DefaultPrinter.headToString tH
  | (PV tH) -> Pretty.Int.DefaultPrinter.headToString tH
  | (FV (n, _tA))  -> "FV " ^ n.string_of_name
  | (FMV (n, _)) -> "FMV " ^ n.string_of_name
  | (FPV (n, _)) -> "FPV " ^ n.string_of_name


let rec raiseType cPsi tA = match cPsi with
  | I.Null -> (None, tA)
  | I.CtxVar psi -> (Some psi, tA)
  | I.DDec (cPsi', decl) ->
      raiseType cPsi' (I.PiTyp (decl, tA))

let rec raiseKind cPsi tK = match cPsi with
  | I.Null -> tK
  | I.DDec (cPsi', decl) ->
      raiseKind cPsi' (I.PiKind (decl, tK))

let ctxVarToString psi = match psi with
  | None -> " "
  | (Some (I.Offset k)) -> "Ctx_Var " ^ string_of_int k

let rec printCollection cQ = match cQ with
  | I.Empty -> Printf.printf " \n end "
  | I.Dec(cQ, MV ((I.MVar (I.Inst(_r, cPsi, tP, _c), _s)) as h)) -> 
      let (ctx_var, tA) = raiseType cPsi tP in        
      (printCollection cQ ; 
       Printf.printf " %s : " 
         (Pretty.Int.DefaultPrinter.normalToString (Whnf.norm (I.Root(h, I.Nil), LF.id))) ;
       Printf.printf " %s . %s \n" 
         (ctxVarToString ctx_var)
         (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA , LF.id)))
      )
  | I.Dec(cQ, PV ((I.PVar (I.PInst(_r, cPsi, tA', _c), _s)) as h)) -> 
      let (ctx_var, tA) = raiseType cPsi tA' in        
      (printCollection cQ ; 
       Printf.printf " %s : " 
         (Pretty.Int.DefaultPrinter.normalToString (Whnf.norm (I.Root(h, I.Nil), LF.id))) ;
       Printf.printf " %s . %s \n" 
         (ctxVarToString ctx_var)
         (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA , LF.id)))
      )

  | I.Dec(cQ, FV (_n, None)) -> (printCollection cQ ; Printf.printf " FV _ . ")

  | I.Dec(cQ, FV (n, Some tA)) -> 
            (printCollection cQ ; 
             Printf.printf " FV %s : %s \n" n.string_of_name 
                     (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))))

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
       r1 == r2
  | _ -> false



(* eqPVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let rec eqPVar mV1 mV2 = match (mV1, mV2) with
  | (I.PVar (I.PInst (r1, _, _, _), _s) , PV (I.PVar (I.PInst (r2, _, _, _), _s'))) -> 
       r1 == r2
  | _ -> false

(* eqFVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FV (n2, _)) -> (n1 = n2)
  | _ -> false


(* eqFMVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFMVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FMV (n2, _)) -> (n1 = n2)
  | _ -> false


(* eqFPVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFPVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FPV (n2, _)) -> (n1 = n2)
  | _ -> false

(* index_of cQ n = i
   where cQ = cQ1, Y, cQ2 s.t. n = Y and length cQ2 = i
*)
let rec index_of cQ n = 
  match (cQ, n) with
  | (I.Empty, _) ->
      raise (Error "index_of for a free variable (FV, FMV, FPV, MV,  does not exist – should be impossible \n")  (* impossible due to invariant on collect *)

  | (I.Dec (cQ', MV u1), MV u2) ->
      (* TODO investigate the feasibility of having it start at 0 *)
      if eqMVar u1 (MV u2) then 1 else (index_of cQ' n) + 1 

  | (I.Dec (cQ', PV p1), PV p2) ->
      (* TODO investigate the feasibility of having it start at 0 *)
      if eqPVar p1 (PV p2) then 1 else (index_of cQ' n) + 1 

  | (I.Dec (cQ', FV (f1, _)), FV (f2, tA)) ->
      if eqFVar f1 (FV (f2, tA)) then 1 else (index_of cQ' n) + 1

  | (I.Dec (cQ', FMV (u1, _)), FMV (u2, tA_cPsi)) ->
      if eqFMVar u1 (FMV (u2, tA_cPsi)) then 1 else (index_of cQ' n) + 1

  | (I.Dec (cQ', FPV (p1, _)), FPV (p2, tA_cPsi)) ->
      if eqFMVar p1 (FPV (p2, tA_cPsi)) then 1 else (index_of cQ' n) + 1


  | (I.Dec (cQ', _), _) ->
      (index_of cQ' n) + 1

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
      begin match raiseType cPsi tA with
        | (None, tA') -> 
            I.DDec (ctxToDctx cQ', I.TypDecl (Id.mk_name None, tA'))
        | (Some _, _ ) -> raise (Error "ctxToDctx generates LF-dctx with context variable: should be impossible!")
      end 
  | I.Dec (cQ', FV (_, Some tA)) ->
      I.DDec (ctxToDctx cQ', I.TypDecl (Id.mk_name None, tA))



let rec ctxToMCtx cQ  = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', MV (I.MVar (I.Inst (_, cPsi, tA, _), _s))) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (Id.mk_name None, tA, cPsi))

  | I.Dec (cQ', PV (I.PVar (I.PInst (_, cPsi, tA, _), _s))) ->
      I.Dec (ctxToMCtx cQ', I.PDecl (Id.mk_name None, tA, cPsi))

  | I.Dec (cQ', FMV (u, Some (tA, cPsi))) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (u, tA, cPsi))

  | I.Dec (cQ', FPV (p, Some (tA, cPsi))) ->
      I.Dec (ctxToMCtx cQ', I.PDecl (p, tA, cPsi))

  (* this case should not happen -bp *)
(* | I.Dec (cQ', FV (_, Some tA)) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (Id.mk_name None, tA, I.Null))
*)


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
      let cQ1 =  collectSub cQ phat s in 
      let cQ2 = collectHead cQ1 phat (h, LF.id) in
        cQ2

  | (I.Dot (I.Obj tM, s)) ->
      let cQ1 =  collectSub cQ phat s in 
      let cQ2 = collectTerm cQ1 phat (tM, LF.id) in
        cQ2

  | (I.Dot (I.Undef, s)) ->
    (let _ = Printf.printf "Collect Sub encountered undef \n" in 
          collectSub cQ phat  s)


(* collectMSub cQ theta = cQ' *) 
and collectMSub cQ theta =  match theta with 
  | Comp.MShift _n -> cQ 
  | Comp.MDot(Comp.MObj(phat, tM), t) -> 
      let cQ1 =  collectMSub cQ t in 
      let cQ2 = collectTerm cQ1 phat (tM, LF.id) in 
        cQ2

  | Comp.MDot(Comp.PObj(phat, h), t) -> 
      let cQ1 =  collectMSub cQ t in 
      let cQ2 = collectHead cQ1 phat (h, LF.id) in 
        cQ2

and collectHead cQ phat sH = match sH with

  | (I.BVar _x, _s)  -> cQ

  | (I.Const _c, _s) -> cQ

  | (I.FVar name, s) ->
      let cQ' = collectSub cQ (None, 0) s in
        if exists (eqFVar name) cQ' then
          cQ'
        else
          let tA  = FVar.get name in
            (* tA must be closed *)
            (* Since we only use abstraction on pure LF objects,
               there are no context variables; different abstraction
               is necessary for handling computation-level expressions,
               and LF objects which occur in computations. *)
            I.Dec (collectTyp cQ' (None, 0) (tA, LF.id), FV (name, Some tA))


  | (I.FMVar (u, s'), s) ->
      let cQ' = collectSub cQ phat (LF.comp s' s) in
        if exists (eqFMVar u) cQ' then
          cQ'
        else
          let (tA, cPhi)  = FMVar.get u in
            (* tA must be closed with respect to cPhi *)
            (* Since we only use abstraction on pure LF objects,
               there are no context variables; different abstraction
               is necessary for handling computation-level expressions,
               and LF objects which occur in computations. *)
            I.Dec (collectTyp cQ' (None, 0) (tA, LF.id), FMV (u, Some (tA, cPhi)))

  | (I.MVar (I.Inst (_r, cPsi, tA, _cnstrs), s') as u, s) ->
      let cQ' = collectSub cQ phat (LF.comp s' s) in
        if exists (eqMVar u) cQ' then
          cQ'
        else
          (*  checkEmpty !cnstrs ? -bp *)
          let (ctx_var, tA') = raiseType cPsi tA  (* tA' = Pi cPsi. tA *) in
            I.Dec (collectTyp cQ' (ctx_var, 0) (tA', LF.id), MV u) 


  | (I.MVar (I.Offset _k, s'), s) ->
       collectSub cQ phat (LF.comp s' s) 
      
  | (I.PVar (I.PInst (_r, cPsi, tA, _cnstrs), s') as p, s) ->
      let cQ' = collectSub cQ phat (LF.comp s' s) in
        if exists (eqPVar p) cQ' then
          cQ'
        else
          (*  checkEmpty !cnstrs ? -bp *)
          let (ctx_var, tA') = raiseType cPsi tA  (* tA' = Pi cPsi. tA *) in

            I.Dec (collectTyp cQ' (ctx_var, 0) (tA', LF.id), PV p) 

  | (I.PVar (I.Offset _k, s'), s) ->
       collectSub cQ phat (LF.comp s' s) 
      

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


let rec collectDctx cQ ((cvar, offset) as _phat) cPsi = match cPsi with 
  | I.Null -> cQ

  | I.CtxVar _ -> cQ

  | I.DDec(cPsi, I.TypDecl(_, tA)) ->
      let cQ' =  collectDctx cQ (cvar, offset - 1) cPsi in 
        collectTyp cQ' (cvar, offset - 1) (tA, LF.id)

let rec collectMctx cQ cD = match cD with
  | I.Empty -> cQ

  | I.Dec(cD, I.MDecl(_u, tA, cPsi)) -> 
      let cQ'  = collectMctx cQ cD in 
      let phat = Context.dctxToHat cPsi in 
      let cQ'' = collectDctx cQ' phat cPsi in 
        collectTyp cQ'' phat  (tA, LF.id)

  | I.Dec(cD, I.PDecl(_p, tA, cPsi)) -> 
      let cQ'  = collectMctx cQ cD in 
      let phat = Context.dctxToHat cPsi in 
      let cQ'' = collectDctx cQ' phat cPsi in 
        collectTyp cQ'' phat (tA, LF.id)



let rec collectPattern cQ cD cPsi (phat, tM) tA = 
  let cQ1 = collectMctx cQ cD in 
  let cQ2 = collectTerm cQ1 phat (tM, LF.id) in 
  let cQ3 = collectDctx cQ2 phat cPsi in 
    collectTyp cQ3 phat (tA, LF.id)



(* ****************************************************************** *)
(* Abstraction over LF-bound variables                                *)
(* ****************************************************************** *)

(* abstractKind cQ offset tK = tK'

   where tK' is tK with all occurences of FVar and MVar have been replaced by
   BVar and indexed according to their order in cQ and the base offset

   assumes there are no cycles
*)

let rec abstractKind cQ offset sK = match sK with
  | (I.Typ, _s) -> I.Typ

  | (I.PiKind (I.TypDecl (x, tA), tK), s) ->
      I.PiKind (I.TypDecl (x, abstractTyp cQ offset (tA,s)), abstractKind cQ (offset + 1) (tK, LF.dot1 s))

and abstractTyp cQ offset sA = abstractTypW cQ offset (Whnf.whnfTyp sA) 

and abstractTypW cQ offset sA = match sA with
  | (I.Atom (a, tS), s (* id *)) ->
      I.Atom (a, abstractSpine cQ offset (tS, s))

  | (I.PiTyp (I.TypDecl (x, tA), tB), s) ->
      I.PiTyp (I.TypDecl (x, abstractTyp cQ offset (tA, s)), abstractTyp cQ (offset + 1) (tB, LF.dot1 s))

and abstractTerm cQ offset sM = abstractTermW cQ offset (Whnf.whnf sM)

and abstractTermW cQ offset sM = match sM with
  | (I.Lam (x, tM), s) ->
      I.Lam (x, abstractTerm cQ (offset + 1) (tM, LF.dot1 s))

  | (I.Root (I.MVar (I.Inst(_r, cPsi, _tP , _cnstr), s) as tH, _tS (* Nil *)), _s (* LF.id *)) -> 
    (* Since sM is in whnf, _u is MVar (Inst (ref None, tP, _, _)) *)
      let x = index_of cQ (MV tH) + offset in 
        I.Root (I.BVar x, subToSpine cQ offset (s,cPsi) I.Nil)     

  | (I.Root (tH, tS), s (* LF.id *)) ->
      I.Root (abstractHead cQ offset tH, abstractSpine cQ offset (tS,s))


and abstractHead cQ offset tH = match tH with
  | I.BVar x ->
      I.BVar x   

  | I.Const c ->
      I.Const c

  | I.FVar n ->
      I.BVar ((index_of cQ (FV (n, None))) + offset)

  | I.AnnH (_tH, _tA) ->
      raise NotImplemented

  (* other cases impossible for object level *)


and subToSpine cQ offset (s,cPsi) tS = match (s, cPsi) with
  | (I.Shift _k, I.Null) ->  tS

  | (I.Shift k , I.DDec(_cPsi', _dec)) ->
       subToSpine cQ offset ((I.Dot (I.Head (I.BVar (k + 1)), I.Shift (k + 1))), cPsi) tS

  | (I.Dot (I.Head (I.BVar k), s), I.DDec(cPsi', _dec)) -> 
      subToSpine cQ offset  (s,cPsi') (I.App (I.Root (I.BVar k, I.Nil), tS))

  | (I.Dot (I.Head (I.MVar (_u, _r)), _s) , I.DDec(_cPsi', _dec)) -> 
      (Printf.printf "SubToSpine encountered MVar as head \n";
      raise NotImplemented)
      (* subToSpine cQ offset s (I.App (I.Root (I.BVar k, I.Nil), tS)) *)

  | (I.Dot (I.Obj tM, s), I.DDec(cPsi', _dec)) -> 
      subToSpine cQ offset (s, cPsi') (I.App (abstractTerm cQ offset (tM, LF.id), tS))

and abstractSpine cQ offset sS = match sS with
  | (I.Nil, _s) ->
      I.Nil

  | (I.App (tM, tS), s) ->
      I.App (abstractTerm cQ offset (tM,s),  abstractSpine cQ offset (tS, s))

  | (I.SClo (tS, s'), s)  ->
      abstractSpine cQ offset (tS, LF.comp s' s)

and abstractCtx cQ =  match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ, MV (I.MVar (I.Inst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractCtx cQ in
      let cPsi' = abstractDctx cQ cPsi in 
      (* let  (_, depth)  = dctxToHat cPsi in   *)
      (* let tA'   = abstractTyp cQ 0 (tA, LF.id) in *)
      let tA'   = abstractTyp cQ (length cPsi) (tA, LF.id) in 
      let s'    = abstractSub cQ (length cPsi) s in
      let u'    = I.MVar (I.Inst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', MV u')

  | I.Dec (cQ, PV (I.PVar (I.PInst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractCtx cQ in
      let cPsi' = abstractDctx cQ cPsi in 
      (* let  (_, depth)  = dctxToHat cPsi in   *)
      (* let tA'   = abstractTyp cQ 0 (tA, LF.id) in *)
      let tA'   = abstractTyp cQ (length cPsi) (tA, LF.id) in 
      let s'    = abstractSub cQ (length cPsi) s in
      let p'    = I.PVar (I.PInst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', PV p')

  | I.Dec (cQ, FV (f, Some tA)) ->
      let tA' = abstractTyp cQ 0 (tA, LF.id) in
      let cQ' = abstractCtx cQ in
        I.Dec (cQ', FV (f, Some tA'))



and abstractDctx cQ cPsi = match cPsi with
  | I.Null ->
      I.Null
  | I.CtxVar psi -> I.CtxVar psi

  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractDctx cQ cPsi in
      let tA'   = abstractTyp cQ (length cPsi) (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

  (* other cases impossible in LF layer *)

and abstractSub cQ offset s = match s with
  | I.Shift _ ->
      s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractHead cQ offset tH), abstractSub cQ offset s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractTerm cQ offset (tM, LF.id)), abstractSub cQ offset s)

  (* what about I.Dot (I.Undef, s) ? *)

  (* SVar impossible in LF layer *)

(* ****************************************************************** *)
(* Abstraction over meta-variables and parameter variables            *)
(* ****************************************************************** *)

(* Abstracting over free meta-variables (MVars with references), 
   named free meta-variables, and named free parameter variables to
   create a context cD.


   This is needed in type checking and type reconstruction for computations.

*)

let rec abstractMVarTyp cQ offset sA = abstractMVarTypW cQ offset (Whnf.whnfTyp sA) 

and abstractMVarTypW cQ offset sA = match sA with
  | (I.Atom (a, tS), s (* id *)) ->
      I.Atom (a, abstractMVarSpine cQ offset (tS, s))

  | (I.PiTyp (I.TypDecl (x, tA), tB), s) ->
      I.PiTyp (I.TypDecl (x, abstractMVarTyp cQ offset (tA, s)), 
               abstractMVarTyp cQ offset (tB, LF.dot1 s))

and abstractMVarTerm cQ offset sM = abstractMVarTermW cQ offset (Whnf.whnf sM)

and abstractMVarTermW cQ offset sM = match sM with
  | (I.Lam (x, tM), s) ->
      I.Lam (x, abstractMVarTerm cQ offset (tM, LF.dot1 s))
  | (I.Root (tH, tS), s (* LF.id *)) ->
      I.Root (abstractMVarHead cQ offset tH, abstractMVarSpine cQ offset (tS,s))


and abstractMVarHead cQ offset tH = match tH with
  | I.BVar x ->
      I.BVar x

  | I.PVar (I.PInst(_r, _cPsi, _tA , _cnstr), s) -> 
      let x = index_of cQ (PV tH) + offset in 
        I.PVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.FPVar (p, s) -> 
      let x = index_of cQ (FPV (p, None)) + offset in 
        I.PVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MVar (I.Inst(_r, _cPsi, _tP , _cnstr), s) -> 
      let x = index_of cQ (MV tH) + offset in 
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MVar (I.Offset x , s) -> 
      I.MVar (I.Offset x, abstractMVarSub cQ offset s) 

  |  I.FMVar (u, s) ->  -> 
      let x = index_of cQ (FMV (u, None)) + offset in 
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.Const c ->
      I.Const c

  | I.FVar n ->
      I.BVar ((index_of cQ (FV (n, None))) + offset)

  | I.AnnH (_tH, _tA) ->
      raise NotImplemented

  | I.PVar (I.Offset _ , _s) -> raise (Error "Encountered bound parameter variable")


  (* other cases impossible for object level *)
and abstractMVarSpine cQ offset sS = match sS with
  | (I.Nil, _s) ->
      I.Nil

  | (I.App (tM, tS), s) ->
      I.App (abstractMVarTerm cQ offset (tM,s),  abstractMVarSpine cQ offset (tS, s))

  | (I.SClo (tS, s'), s)  ->
      abstractMVarSpine cQ offset (tS, LF.comp s' s)


and abstractMVarSub cQ offset s = match s with
  | I.Shift _ ->
      s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractMVarHead cQ offset tH), abstractMVarSub cQ offset s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractMVarTerm cQ offset (tM, LF.id)), abstractMVarSub cQ offset s)


and abstractMVarDctx cQ offset cPsi = match cPsi with
  | I.Null ->
      I.Null
  | I.CtxVar psi -> I.CtxVar psi

  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

and abstractMVarMctx cQ cD = match cD with
  | I.Empty -> I.Empty

  | I.Dec(cD, I.MDecl(u, tA, cPsi)) -> 
      let cD' = abstractMVarMctx cQ cD in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in
        I.Dec(cD', I.MDecl (u, tA', cPsi'))

  | I.Dec(cD, I.PDecl(u, tA, cPsi)) -> 
      let cD' = abstractMVarMctx cQ cD in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in
        I.Dec(cD', I.PDecl (u, tA', cPsi'))


and abstractMVarCtx cQ =  match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ, MV (I.MVar (I.Inst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractMVarCtx cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in 
      let s'    = abstractMVarSub cQ 0 s in
        (* Do we need to consider the substitution s here ? -bp *)  
      let u'    = I.MVar (I.Inst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', MV u')

  | I.Dec (cQ, PV (I.PVar (I.PInst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractMVarCtx cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0  (tA, LF.id) in 
      let s'    = abstractMVarSub cQ 0 s in
        (* Do we need to consider the substitution s here ? -bp *)  
      let p'    = I.PVar (I.PInst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', PV p')

  | I.Dec (cQ, FMV (u, Some (tA, cPsi))) ->
      let cQ'   = abstractMVarCtx cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in

        I.Dec (cQ', FMV (u, Some (tA', cPsi')))


  | I.Dec (cQ, FPV (u, Some (tA, cPsi))) ->
      let cQ'   = abstractMVarCtx cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in

        I.Dec (cQ', FPV (u, Some (tA', cPsi')))



(* Casess for: FMV, FPV *)


let rec abstrMSub cQ t = match t with
  | Comp.MShift n -> Comp.MShift n
  | Comp.MDot(Comp.MObj(phat, tM), t) -> 
      let s'  = abstrMSub cQ t in 
      let tM' = abstractMVarTerm cQ 0 (tM, LF.id) in 
        Comp.MDot(Comp.MObj(phat, tM'), s') 

  | Comp.MDot(Comp.PObj(phat, h), t) ->
      let s' = abstrMSub cQ t in 
      let h' = abstractMVarHead cQ 0 h in 
        Comp.MDot(Comp.PObj(phat, h'), s')


and abstractMSub t =  
  let cQ  = collectMSub I.Empty t in
  let cQ' = abstractMVarCtx cQ in
  let t'  = abstrMSub cQ' t in
  let cD'  = ctxToMCtx cQ' in  
    (t' , cD')  


(* wrapper function *)
let abstrKind tK =
  (* what is the purpose of phat? *)
  let empty_phat = (None, 0) in
  let cQ         = collectKind I.Empty empty_phat (tK, LF.id) in
  let cQ'        = abstractCtx cQ in
  let tK'        = abstractKind cQ' 0 (tK, LF.id) in
  let cPsi       = ctxToDctx cQ' in
    (raiseKind cPsi tK', length cPsi)

and abstrTyp tA =
  let empty_phat = (None, 0) in
  let cQ         = collectTyp I.Empty empty_phat (tA, LF.id) in
  let cQ'        = abstractCtx cQ in
  let tA'        = abstractTyp cQ' 0 (tA, LF.id) in
  let cPsi       = ctxToDctx cQ' in
    begin match raiseType cPsi tA' with 
      | (None, tA'') -> (tA'', length cPsi)
      | _            -> raise (Error "Abstraction not valid LF-type because of left-over context variable")
    end 

(*  
   1) Collect FMVar and FPVars  in cD1, Psi1, tM and tA
   2) Abstract FMVar and FPVars in cD1, Psi1, tM and tA
 
*)
  and abstrPattern cD1 cPsi1 (phat, tM) tA =  
  let cQ      = collectPattern I.Empty cD1 cPsi1 (phat,tM) tA in 
  let cQ'     = abstractMVarCtx cQ in 
  let cD1'    = abstractMVarMctx cQ' cD1 in 
  let offset  = Context.length cD1' in 
  let tM'     = abstractMVarTerm cQ' offset (tM, LF.id) in 
  let cPsi1'  = abstractMVarDctx cQ' offset cPsi1 in 
  let tA'     = abstractMVarTyp  cQ' offset (tA, LF.id) in 
  let cD'     = ctxToMCtx cQ' in 
  let cD      = Context.append cD' cD1' in 
    (cD, cPsi1', (phat, tM'), tA')
    




