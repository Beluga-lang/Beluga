(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)

open Context
open Store.Cid
open Substitution
open Syntax.Int


type error =
  | CtxVarMisMatch of cvar * cvar
  | SigmaIllTyped of mctx * dctx * 
                     trec_clo (* inferred *) * trec_clo (* expected *)
  | ExpAppNotFun  
  | KindMisMatch 
  | SubIllTyped      
  | TypIllTyped of mctx * dctx * 
                   tclo (* inferred *) * tclo (* expected *) 
  | TypMisMatch  of mctx * dctx * tclo * tclo
  | IllTyped of mctx * dctx * nclo * tclo

exception Error of error

(* check cD cPsi (tM, s1) (tA, s2) = ()

   Invariant: 

     If   cD ; cPsi |- s1 <= cPsi1   
     and  cD ; cPsi |- s2 <= cPsi2    cPsi2 |- tA <= type
     returns () 
     if there exists an tA' s.t.    
          cD ; cPsi1 |- tM      <= tA' 
     and  cD ; cPsi  |- tA'[s1]  = tA [s2] : type
     and  cD ; cPsi  |- tM [s1] <= tA'[s1]
     otherwise exception Error is raised
*)
let rec checkW cD cPsi sM1 sA2 = match (sM1, sA2) with
  | ((Lam (_, tM), s1), (PiTyp ((TypDecl (_x, _tA) as tX), tB), s2))
    -> check cD
             (DDec (cPsi, decSub tX s2))
             (tM, dot1 s1)
             (tB, dot1 s2)

  | ((Root (h, tS), s), (((Atom _), _s') as sP))
    -> (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
       let sA = Whnf.whnfTyp (inferHead cD cPsi h, id) in
         checkSpine cD cPsi (tS, s) sA sP

  | _
    -> raise (Error (IllTyped (cD, cPsi, sM1, sA2)))

and check cD cPsi sM1 sA2 = checkW cD cPsi (Whnf.whnf sM1) (Whnf.whnfTyp sA2)



(* checkSpine cD cPsi (tS, s1) (tA, s2) sP = ()

   Invariant: 
     If   cD ; cPsi  |- s1 <= cPsi1  
     and  cD ; cPsi  |- s2 <= cPsi2
     and  cD ; cPsi2 |- tA <= type      (tA, s2) in whnf  
     then succeeds if there exists tA', tP' such that
               cD ; cPsi1 |- tS : tA' > tP'
          and  cD ; cPsi  |- s' : cPsi'
          and  cD ; cPsi' |- tA' <= type
          and  cD ; cPsi  |- tA'[s'] = tA [s2] <= type
          and  cD ; cPsi  |- tP'[s'] = sP      <= type
*)
and checkSpine cD cPsi sS1 sA2 (sP : tclo) = match (sS1, sA2) with
  | ((Nil, _), sP') ->
      if Whnf.convTyp sP' sP
      then
        ()
      else
        raise (Error (TypMisMatch (cD, cPsi, sP', sP)))

  | ((SClo (tS, s'), s), sA) ->
      checkSpine cD cPsi (tS, comp s' s) sA sP

  | ((App (tM, tS), s1), (PiTyp (TypDecl (_, tA1), tB2), s2)) ->
        check cD cPsi (tM, s1) (tA1, s2)
      ; (*     cD ; cPsi1        |- tM  <= tA1'
           and cD ; cPsi         |- s1  <= cPsi1
           and cD ; cPsi2, x:tA1 |- tB2 <= type
           and [s1]tA1' = [s2]tA1
        *)
        let tB2 = Whnf.whnfTyp (tB2, Dot (Obj (Clo (tM, s1)), s2)) in
          checkSpine cD cPsi (tS, s1) tB2 sP

  | ((App (_tM, _tS), _), (_tA, _s)) ->
      (* tA <> (Pi x:tA1. tA2, s) *)
      raise (Error ExpAppNotFun)



(* inferHead cD cPsi h = tA

   Invariant:

     returns tA if
           cD ; cPsi |- h -> tA
     where cD ; cPsi |- tA <= type
     else exception Error is raised. 
*)
and inferHead cD cPsi head = match head with
  | BVar k'                 ->
      let (_, _l) = dctxToHat cPsi in
      let TypDecl (_, tA) = ctxDec cPsi k' in
        tA

  | Proj (BVar k',  target) ->
      let SigmaDecl (_, recA) = ctxSigmaDec cPsi k' in
        (* getType traverses the type from left to right;
           target is relative to the remaining suffix of the type *)
      let rec getType s_recA target j = match (s_recA, target) with
        | (( tA :: _recA, s), 1)      -> TClo(tA, s)

        | ((_tA ::  recA, s), target) ->
            let tPj = Root (Proj (BVar k', j), Nil) in
              getType (recA, Dot (Obj tPj, s)) (target - 1) (j + 1)

      in
        getType (recA, id) target 1

  (* Missing cases?  Tue Sep 30 22:09:27 2008 -bp 

     Proj (PVar(p,s), i) 
     Proj (MVar(p,s), i) 

     These cases are impossible at the moment.
  *)
  | Const c                 -> 
      (Term.get c).Term.typ

  | MVar (Offset u, s)      ->
      (* cD ; cPsi' |- tA <= type *)
      let (tA, cPsi') = mctxMDec cD u in
          checkSub cD cPsi s cPsi'
        ; TClo (tA, s)

  | PVar(Offset u,s)        ->
      (* cD ; cPsi' |- tA <= type *)
      let (tA, cPsi') = mctxPDec cD u in
          checkSub cD cPsi s cPsi'
        ; TClo (tA, s)



(* checkSub cD cPsi s cPsi' = ()

   Invariant:

     succeeds iff cD ; cPsi |- s : cPsi'
*)
and checkSub cD cPsi s cPsi' = match (cPsi, s, cPsi') with
  | (Null, Shift 0, Null)               -> ()

  | (CtxVar psi, Shift 0, CtxVar psi')  ->
      if psi = psi'
      then ()
      else raise (Error (CtxVarMisMatch (psi, psi')))

  (* SVar case to be added - bp *)

  | (DDec (cPsi, _tX), Shift k, Null)   ->
      if k > 0
      then checkSub cD cPsi (Shift (k - 1)) Null
      else raise (Error (SubIllTyped))

  | (cPsi', Shift k, cPsi)              ->
      checkSub cD cPsi' (Dot (Head (BVar (k + 1)), Shift (k + 1))) cPsi

  | (cPsi', Dot (Head h, s'), DDec (cPsi, (TypDecl (_, tA2)))) ->
      (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
      let _   = checkSub cD cPsi' s' cPsi
      (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
      and tA1 = inferHead cD cPsi' h
      in
        if Whnf.convTyp (tA1, id) (tA2, s')
        then ()
        else raise (Error (TypIllTyped (cD, cPsi', (tA1, id), (tA2, s'))))

  | (cPsi', Dot (Head (BVar w), t), SigmaDec (cPsi, (SigmaDecl (_, arec)))) ->
      (* other heads of type Sigma disallowed -bp *)
      let _ = checkSub cD cPsi' t cPsi
      (* ensures that t is well-typed before comparing types BRec = [t]ARec *)
      and SigmaDecl (_, brec) = ctxSigmaDec cPsi' w
      in
        if Whnf.convTypRec (brec, id) (arec, t)
        then ()
        else raise (Error (SigmaIllTyped (cD, cPsi', (brec, id), (arec, t))))

  | (cPsi', Dot (Obj tM, s'), DDec (cPsi, (TypDecl (_, tA2)))) ->
      (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
      let _ = checkSub cD cPsi' s' cPsi
      (* ensures that s' is well-typed and [s']tA2 is well-defined *)
      in
        check cD cPsi' (tM, id) (tA2, s')



(*****************)
(* Kind Checking *)
(*****************)

(* kind checking is only applied to type constants declared in
   the signature; 

   All constants declared in the signature do not contain any
   contextual variables, hence Delta = . 
*)



(* checkSpineK cD cPsi (tS, s1) (K, s2)

  Invariant:

    succeeds iff cD ; cPsi |- [s1]tS <= [s2]K
*)
and checkSpineK cD cPsi sS1 sK = match (sS1, sK) with
  | ((Nil, _), (Typ, _s))             -> ()

  | ((Nil, _), _)                     ->  
      raise (Error (KindMisMatch))

  | ((SClo (tS, s'), s), sK)          ->
      checkSpineK cD cPsi (tS, comp s' s) sK

  | ((App (tM, tS), s1), (PiKind (TypDecl (_, tA1), kK), s2)) ->
        check cD cPsi (tM, s1) (tA1, s2)
      ; checkSpineK cD cPsi (tS, s1) (kK, Dot (Obj (Clo (tM, s1)), s2))

  | ((App (_tM , _tS), _), (_kK, _s)) ->
      raise  (Error ExpAppNotFun)



(* checkTyp (cD, cPsi, (tA,s))

   Invariant:

     succeeds iff cD ; cPsi |- [s]tA <= type
*)
let rec checkTyp' (cD, cPsi, (tA, s)) = match (tA, s) with
  | (Atom (a, tS), s)                ->
      checkSpineK cD cPsi (tS, s) ((Typ.get a).Typ.kind, id)

  | (PiTyp (TypDecl (x, tA), tB), s) ->
        checkTyp cD cPsi (tA, s) 
      ; checkTyp cD (DDec (cPsi, TypDecl(x, TClo (tA, s)))) (tB, dot1 s)

and checkTyp cD cPsi sA = checkTyp' (cD, cPsi, Whnf.whnfTyp sA)



(* checkTypRec cD cPsi (recA, s)

   Invariant:

     succeeds iff cD ; cPsi |- [s]recA <= type
*)
let rec checkTypRec cD cPsi (recA, s) = match recA with
  | []         -> ()
  | tA :: recA ->
        checkTyp    cD cPsi (tA, s)
      ; checkTypRec cD
                    (DDec (cPsi, decSub (TypDecl (Id.mk_name None, tA)) s))
                    (recA, dot1 s)



(* checkKind cD cPsi K

   Invariant:

     succeeds iff cD ; cPsi |- K kind
*)
let rec checkKind cD cPsi kind = match kind with
  | Typ                            -> ()
  | PiKind (TypDecl (x, tA), kind) ->
        checkTyp  cD cPsi (tA, id)
      ; checkKind cD (DDec (cPsi, TypDecl (x, tA))) kind



(* checkDec cD cPsi (x:tA, s)

   Invariant:

     succeeds iff cD ; cPsi |- [s]tA <= type
*)
and checkDec cD cPsi (decl, s) = match decl with
  | TypDecl (_, tA) -> checkTyp cD cPsi (tA, s)



(* checkSigmaDec cD cPsi (x:recA, s)

   Invariant:

     succeeds iff cD ; cPsi |- [s]recA <= type
*)
and checkSigmaDec cD cPsi (sigma_decl, s) = match sigma_decl with
  | SigmaDecl (_, arec) -> checkTypRec cD cPsi (arec, s)



(* checkCtx cD cPsi

   Invariant:

     succeeds iff cD |- cPsi ctx
*)
and checkCtx cD cPsi = match cPsi with Null ->  ()
  | DDec (cPsi, tX)     ->
        checkCtx cD cPsi
      ; checkDec cD cPsi (tX, id)

  | SigmaDec (cPsi, tX) ->
        checkCtx      cD cPsi
      ; checkSigmaDec cD cPsi (tX, id)

  | CtxVar _psi         -> ()
  (* need to check if psi is in Omega (or cD, if context vars live there) -bp *)



let rec check_sgn_decls = function
  | []                       -> ()

  | SgnTyp   (_a, k) :: decls ->
      let cD   = Empty
      and cPsi = Null
      in
          checkKind cD cPsi k
        ; check_sgn_decls decls

  | SgnConst (_c, a) :: decls ->
      let cD   = Empty
      and cPsi = Null
      in
          checkTyp cD cPsi (a, id)
        ; check_sgn_decls decls
