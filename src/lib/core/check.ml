(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [1])


module LF = struct 
  open Context
  open Store.Cid
  open Substitution
  open Syntax.Int.LF

  module Print = Pretty.Int.DefaultPrinter
  
  exception Error of string

  (* check cO cD cPsi (tM, s1) (tA, s2) = ()

     Invariant: 

     If   cO ; cD ; cPsi |- s1 <= cPsi1   
     and  cO ; cD ; cPsi |- s2 <= cPsi2    cPsi2 |- tA <= type
     returns () 
     if there exists an tA' s.t.    
     cO ; cD ; cPsi1 |- tM      <= tA' 
     and  cO ; cD ; cPsi  |- tA'[s1]  = tA [s2] : type
     and  cO ; cD ; cPsi  |- tM [s1] <= tA'[s1]
     otherwise exception Error is raised
  *)
  let rec checkW cO cD cPsi sM1 sA2 = match (sM1, sA2) with
    | ((Lam (_, tM), s1), (PiTyp ((TypDecl (_x, _tA) as tX), tB), s2))
      -> 
        check cO cD
        (DDec (cPsi, LF.decSub tX s2))
          (tM, LF.dot1 s1)
          (tB, LF.dot1 s2)

    | ((Root (h, tS), s (* id *)), (((Atom _), _s') as sP))
      -> (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
        let sA = Whnf.whnfTyp (inferHead cO cD cPsi h, LF.id) in
          checkSpine cO cD cPsi (tS, s) sA sP

    | _
      -> raise (Error "LF Term is ill-typed")
               (* IllTyped (cD, cPsi, sM1, sA2) *)

  and check cO cD cPsi sM1 sA2 = checkW cO cD cPsi (Whnf.whnf sM1) (Whnf.whnfTyp sA2)



  (* checkSpine cO cD cPsi (tS, s1) (tA, s2) sP = ()

     Invariant: 
     If   cO ;  cD ; cPsi  |- s1 <= cPsi1  
     and  cO ;  cD ; cPsi  |- s2 <= cPsi2
     and  cO ;  cD ; cPsi2 |- tA <= type      (tA, s2) in whnf  
     then succeeds if there exists tA', tP' such that
          cO ; cD ; cPsi1 |- tS : tA' > tP'
     and  cO ; cD ; cPsi  |- s' : cPsi'
     and  cO ; cD ; cPsi' |- tA' <= type
     and  cO ; cD ; cPsi  |- tA'[s'] = tA [s2] <= type
     and  cO ; cD ; cPsi  |- tP'[s'] = sP      <= type
  *)
  and checkSpine cO cD cPsi sS1 sA2 (sP : tclo) = match (sS1, sA2) with
    | ((Nil, _), sP') ->
        if Whnf.convTyp sP' sP then
          ()
        else
          let _ = Printf.printf "checkSpine: Expected type : %s \n Inferred type: %s\n\n"
            (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp sP))
            (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp sP')) in 
          raise (Error "Spine Type Mismatch")
            (* (TypMisMatch (cD, cPsi, sP', sP)) *)

    | ((SClo (tS, s'), s), sA) ->
        checkSpine cO cD cPsi (tS, LF.comp s' s) sA sP

    | ((App (tM, tS), s1), (PiTyp (TypDecl (_, tA1), tB2), s2)) ->
        check cO cD cPsi (tM, s1) (tA1, s2)
        ; (*     cD ; cPsi1        |- tM  <= tA1'
                 and cD ; cPsi         |- s1  <= cPsi1
                 and cD ; cPsi2, x:tA1 |- tB2 <= type
                 and [s1]tA1' = [s2]tA1
          *)
        let tB2 = Whnf.whnfTyp (tB2, Dot (Obj (Clo (tM, s1)), s2)) in
          checkSpine cO cD cPsi (tS, s1) tB2 sP

    | ((App (_tM, _tS), _), (_tA, _s)) ->
        (* tA <> (Pi x:tA1. tA2, s) *)
        raise (Error "Expression not a function")
                 (* ExpAppNotFun *)



  (* inferHead cO cD cPsi h = tA

     Invariant:

     returns tA if
     cO cD ; cPsi |- h -> tA
     where cO cD ; cPsi |- tA <= type
     else exception Error is raised. 
  *)
  and inferHead cO cD cPsi head = match head with
    | BVar k'                 ->
        let (_, _l) = dctxToHat cPsi in
        let TypDecl (_, tA) = ctxDec cPsi k' in
          tA

    | Proj (BVar k',  target) ->
        let SigmaDecl (_, recA) = ctxSigmaDec cPsi k' in
          (* getType traverses the type from left to right;
             target is relative to the remaining suffix of the type *)
        let rec getType s_recA target j = match (s_recA, target) with
          | ( (SigmaLast lastA, s), 1 )      -> TClo(lastA, s)

          | ( (SigmaElem(_x, tA, _recA), s), 1 )   -> TClo(tA, s)

          | ( (SigmaElem(_x, _tA, recA), s), target ) ->
              let tPj = Root (Proj (BVar k', j), Nil) in
                getType (recA, Dot (Obj tPj, s)) (target - 1) (j + 1)

        in
          getType (recA, LF.id) target 1

    (* Missing cases?  Tue Sep 30 22:09:27 2008 -bp 

       Proj (PVar(p,s), i) 
       Proj (MVar(p,s), i) 

       These cases are impossible at the moment.
    *)
    | Const c                 -> 
        (Term.get c).Term.typ

    | MVar (Offset u, s)      ->
        (* cD ; cPsi' |- tA <= type *)
        let (tA, cPsi') = Cwhnf.mctxMDec cD u in
        let _ = checkSub cO cD cPsi s cPsi'  in  
           TClo (tA, s)  

    | PVar(Offset p,s)        ->
        (* cD ; cPsi' |- tA <= type *)
        let (tA, cPsi') = Cwhnf.mctxPDec cD p in
          checkSub cO cD cPsi s cPsi'
          ; TClo (tA, s)

    | FVar _ -> 
        raise (Error "Encountered free variable\n")


  (* checkSub cO cD cPsi s cPsi' = ()

     Invariant:

     succeeds iff cO cD ; cPsi |- s : cPsi'
  *)
  and checkSub cO cD cPsi s cPsi' = match (cPsi, s, cPsi') with
    | (Null, Shift (NoCtxShift, 0), Null)               -> ()

    | (CtxVar psi, Shift (NoCtxShift, 0), CtxVar psi')  ->
        if psi = psi' then 
          ()
        else raise (Error "Context variable mismatch")
                      (* (CtxVarMisMatch (psi, psi')) *)

    | (CtxVar psi, Shift (CtxShift (psi'), 0), Null)  ->  
        if psi = psi' then 
          () 
        else 
          raise (Error "Substitution ill-typed" )


    | (Null , Shift (NegCtxShift (psi'), 0), CtxVar psi)  ->  
        if psi = psi' then 
          () 
        else 
          raise (Error "Substitution ill-typed" )

    (* SVar case to be added - bp *)

    | (DDec (cPsi, _tX), Shift (psi, k), Null)   ->
        if k > 0
        then checkSub cO cD cPsi (Shift (psi, k - 1)) Null
        else raise (Error "Substitution illtyped")
                      (* (SubIllTyped) *)

    | (DDec (cPsi, _tX), Shift (phi, k), CtxVar psi)   ->
        if k > 0
        then checkSub cO cD cPsi (Shift (phi, k - 1)) (CtxVar psi) 
        else raise (Error ("Substitution illtyped: k = %s" ^ (string_of_int k)))
                      (* (SubIllTyped) *)

    | (cPsi', Shift (psi, k), cPsi)              ->
        checkSub cO cD cPsi' (Dot (Head (BVar (k + 1)), Shift (psi, k + 1))) cPsi

    | (cPsi', Dot (Head h, s'), DDec (cPsi, (TypDecl (_, tA2)))) ->
        (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
        let _   = checkSub cO cD cPsi' s' cPsi
          (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
        and tA1 = inferHead cO cD cPsi' h
        in
          if Whnf.convTyp (tA1, LF.id) (tA2, s')
          then ()
          else 
            let _ = Printf.printf " Inferred type: %s \n Expected type: %s \n\n"
                    (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA1, LF.id)))
                    (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA2, s'))) in
          raise (Error "Substitution ill-typed")
          (* (TypIllTyped (cD, cPsi', (tA1, LF.id), (tA2, s'))) *)

    | (cPsi', Dot (Head (BVar w), t), SigmaDec (cPsi, (SigmaDecl (_, arec)))) ->
        (* other heads of type Sigma disallowed -bp *)
        let _ = checkSub cO cD cPsi' t cPsi
          (* ensures that t is well-typed before comparing types BRec = [t]ARec *)
        and SigmaDecl (_, brec) = ctxSigmaDec cPsi' w
        in
          if Whnf.convTypRec (brec, LF.id) (arec, t)
          then ()
          else raise (Error "Sigma-type illtyped")
                        (* (SigmaIllTyped (cD, cPsi', (brec, LF.id), (arec, t))) *)

    (* Add other cases for different heads -bp Fri Jan  9 22:53:45 2009 -bp *)


    | (cPsi', Dot (Obj tM, s'), DDec (cPsi, (TypDecl (_, tA2)))) ->
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let _ = checkSub cO cD cPsi' s' cPsi
          (* ensures that s' is well-typed and [s']tA2 is well-defined *)
        in
          check cO cD cPsi' (tM, LF.id) (tA2, s')

    | (cPsi1, s, cPsi2) -> 
        let _ = Printf.printf "\n Check substitution: %s   |-    %s    <= %s  \n\n"
          (Pretty.Int.DefaultPrinter.dctxToString (Whnf.normDCtx cPsi1))
          (Pretty.Int.DefaultPrinter.subToString (Whnf.normSub s)) 
          (Pretty.Int.DefaultPrinter.dctxToString (Whnf.normDCtx cPsi2)) in
          raise (Error "Substitution is ill-typed; This case should be impossible.\n")



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
  and checkSpineK cO cD cPsi sS1 sK = match (sS1, sK) with
    | ((Nil, _), (Typ, _s))             -> ()

    | ((Nil, _), _)                     ->  
        raise (Error "Kind mismatch")
                 (* (KindMisMatch) *)

    | ((SClo (tS, s'), s), sK)          ->
        checkSpineK cO cD cPsi (tS, LF.comp s' s) sK

    | ((App (tM, tS), s1), (PiKind (TypDecl (_, tA1), kK), s2)) ->
        check cO cD cPsi (tM, s1) (tA1, s2)
        ; checkSpineK cO cD cPsi (tS, s1) (kK, Dot (Obj (Clo (tM, s1)), s2))

    | ((App (_tM , _tS), _), (_kK, _s)) ->
        raise  (Error "LF term not well-typed")
                  (* ExpAppNotFun *)



  (* checkTyp (cD, cPsi, (tA,s))

     Invariant:

     succeeds iff cD ; cPsi |- [s]tA <= type
  *)
  let rec checkTyp' cO cD cPsi (tA, s) = match (tA, s) with
    | (Atom (a, tS), s)                ->
        checkSpineK cO cD cPsi (tS, s) ((Typ.get a).Typ.kind, LF.id)

    | (PiTyp (TypDecl (x, tA), tB), s) ->
        checkTyp cO cD cPsi (tA, s) 
        ; checkTyp cO cD (DDec (cPsi, TypDecl(x, TClo (tA, s)))) (tB, LF.dot1 s)

  and checkTyp cO cD cPsi sA = checkTyp' cO cD cPsi (Whnf.whnfTyp sA)



  (* checkTypRec cO cD cPsi (recA, s)

     Invariant:

     succeeds iff cO cD ; cPsi |- [s]recA <= type
  *)
  let rec checkTypRec cO cD cPsi (typRec, s) = match typRec with
    | SigmaLast lastA         -> checkTyp cO cD cPsi (lastA, s)
    | SigmaElem(_x, tA, recA) ->
        checkTyp  cO  cD cPsi (tA, s)
        ; checkTypRec cO cD
          (DDec (cPsi, LF.decSub (TypDecl (Id.mk_name None, tA)) s))
          (recA, LF.dot1 s)



  (* checkKind cO cD cPsi K

     Invariant:

     succeeds iff cO cD ; cPsi |- K kind
  *)
  let rec checkKind cO cD cPsi kind = match kind with
    | Typ                            -> ()
    | PiKind (TypDecl (x, tA), kind) ->
        checkTyp cO cD cPsi (tA, LF.id)
        ; checkKind cO cD (DDec (cPsi, TypDecl (x, tA))) kind



  (* checkDec cO cD cPsi (x:tA, s)

     Invariant:

     succeeds iff cO ; cD ; cPsi |- [s]tA <= type
  *)
  and checkDec cO cD cPsi (decl, s) = match decl with
    | TypDecl (_, tA) -> checkTyp cO cD cPsi (tA, s)



  (* checkSigmaDec cO cD cPsi (x:recA, s)

     Invariant:

     succeeds iff cO ; cD ; cPsi |- [s]recA <= type
  *)
  and checkSigmaDec cO cD cPsi (sigma_decl, s) = match sigma_decl with
    | SigmaDecl (_, arec) -> checkTypRec cO cD cPsi (arec, s)



  (* checkDCtx cO cD cPsi

     Invariant:

     succeeds iff cO ; cD |- cPsi ctx
  *)
  and checkDCtx cO  cD cPsi = match cPsi with 
    | Null ->  ()
    | DDec (cPsi, tX)     ->
        checkDCtx cO cD cPsi
        ; checkDec cO cD cPsi (tX, LF.id)

    | SigmaDec (cPsi, tX) ->
        checkDCtx cO cD cPsi
        ; checkSigmaDec cO cD cPsi (tX, LF.id)

    | CtxVar (CtxOffset psi_offset)  -> 
        if psi_offset <= (Context.length cO) then ()
        else 
          raise (Error "Context variable out of scope")

    (* other cases should be impossible -bp *)

end (* struct LF *)

module Comp = struct

  module E = Error

  module Unify = Unify.EmptyTrail
(* NOTES on handling context variables: -bp 

  - We should maybe put context variables into a context Omega (not Delta)
    It makes it difficult to deal with branches.

    Recall: Case(e, branches)  where branch 1 = Pi Delta1. box(psihat. tM1) : A1[Psi1] -> e1

    Note that any context variable occurring in Delta, psihat, A and Psi is bound OUTSIDE. 
    So if 
 
    D ; G |- Case (e, branches)  and ctxvar psi in D the branch 1 is actually well formed iff

    D, D1 ; Psi1 |- tM1 <= tA1  (where only psi declared in D is relevant to the rest.)

    Also, ctx variables are not subject to instantiations during unification / matching
    which is used in type checking and type reconstruction. 

    This has wider implications; 

   * revise indexing structure; the offset of ctxvar is with respect to 
   a context Omega

   * Applying substitution for context variables; does it make sense to
   deal with it lazily? – It seems complicated to handle lazy context substitutions
   AND lazy msubs. 

    If we keep them in Delta, we need to rewrite mctxToMSub for example; 

  

*)

  open Context
  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF 
  module C = Cwhnf

  module Print = Pretty.Int.DefaultPrinter

(*  module Unif = Unify.UnifyNoTrail *)

(*  type error = 
    | CaseScrutineeMismatch
    | FunMismatch
    | CtxAbsMismatch
    | MLamMismatch
    | TypMismatch

  exception Error of error
*)

  exception Error of string
  exception Err of E.error
  let raiseErr x = raise (Err x)
  
  let rec length cD = match cD with
    | I.Empty -> 0
    | I.Dec(cD, _) -> 1 + length cD

  let rec lookup cG k = match (cG, k) with 
    | (I.Dec(_cG', (_,  tau)), 1) ->  tau
    | (I.Dec( cG', (_,  _tau)), k) ->  
        lookup cG' (k-1)

  let rec split tc d = match (tc, d) with
    | (tc, 0) -> tc
    | (MDot(_ft, t), d) -> split t (d-1)

  let rec mctxToMSub cD = match cD with
    | I.Empty -> C.id
    | I.Dec(cD', I.MDecl(_, tA, cPsi)) -> 
      let t = mctxToMSub cD' in 
      let cPsi' = Cwhnf.cnormDCtx (cPsi,t) in 
      let tA' = Cwhnf.cnormTyp (tA, t) in 
      let u = Whnf.newMVar (cPsi' , tA') in 
      let phat = Context.dctxToHat cPsi in 
        MDot(MObj(phat, I.Root(I.MVar(u, S.LF.id), I.Nil)) , t) 
    | I.Dec(cD', I.PDecl(_, tA, cPsi)) -> 
      let t = mctxToMSub cD' in  
      let p = Whnf.newPVar (Cwhnf.cnormDCtx (cPsi,t),  Cwhnf.cnormTyp (tA, t)) in
      let phat = Context.dctxToHat cPsi in  
        MDot(PObj(phat, I.PVar(p, S.LF.id)) , t)

(* ctxToSub cPsi:

  generates, based on cPsi, a substitution suitable for unification

 Currently broken: assumes all types in cPsi are atomic
*)
  let rec ctxToSub cPsi = match cPsi with
    | I.Null -> S.LF.id
    | I.DDec(cPsi', I.TypDecl(_, tA)) -> 
      let s = ((ctxToSub cPsi') : I.sub) in 
(* For the moment, assume tA atomic. *)
(* lower tA? *)
(* A = A_1 -> ... -> A_n -> P

 create cPhi = A_1, ..., A_n
    \x_1. ... \x_n. u[id]
    u::P[cPhi]

already done in reconstruct.ml
          let (_, d) = Context.dctxToHat cPsi in
          let tN     = etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift d) in
in elSpineIW
*)
      let (_, phat') = Context.dctxToHat cPsi' in
      let u     = Whnf.etaExpandMV I.Null (tA, s) (I.Shift (I.NoCtxShift, phat')) in
(*      let u = Whnf.newMVar (I.Null ,  I.TClo( tA, s)) in  *)
      let front = (I.Obj(    (*I.Root(I.MVar(u, S.LF.id), I.Nil) *)    u ) : I.front) in
      in
        I.Dot(front, s)




  (* extend t1 t2 = t
    
     Invariant: 
     If    . |- t1 <= cD1
       and . |- t2 <= cD2
       and FMV(cD1) intersect FMV(cD2) = {} 
       (i.e. no modal variable occurring in type declarations in cD1
        also occurs in a type declaration of cD2)
     then
           . |- t1,t2 <= cD1, cD2   and t = t1,t2
  *)
  let extend t1 t2 = 
    let rec ext t2 = match t2 with
    | MShift 0 -> t1
    (* other cases should be impossible *)
    | MDot(ft, t) -> MDot(ft, ext t)
    in ext t2


  let rec checkTyp cO cD tau = match tau with 
    | TypBox (tA, cPsi) -> 
        (LF.checkDCtx cO cD cPsi ; 
         LF.checkTyp  cO cD cPsi (tA, S.LF.id))

    | TypArr (tau1, tau2) -> 
        (checkTyp cO cD tau1 ;
         checkTyp cO cD tau2)

    | TypCtxPi ((psi_name, schema_cid), tau) -> 
        checkTyp (I.Dec(cO, I.CDecl(psi_name, schema_cid))) cD tau

    | TypPiBox ((cdecl, _ ), tau) -> 
        checkTyp cO (I.Dec(cD, cdecl)) tau        


  (* check cO cD cG e (tau, theta) = ()

     Invariant:

     If  cO ; cD ; cG |- e wf-exp
     and cO ; cD |- theta <= cD' 
     and cO ; cD'|- tau <= c_typ
     returns ()
     if  cO ; cD ; cG |- e <= [|t|]tau

     otherwise exception Error is raised
  *)

  let rec checkW cO cD cG e ttau = match (e , ttau) with 
    | (Rec(f, e), (tau, t)) ->  
        check cO cD (I.Dec (cG, (f, TypClo(tau,t)))) e ttau

    | (Fun(x, e), (TypArr(tau1, tau2), t)) -> 
        check cO cD (I.Dec (cG, (x, TypClo(tau1, t)))) e (tau2, t)

    | (CtxFun(psi, e) , (TypCtxPi ((_psi, schema), tau), t)) -> 
        check (I.Dec(cO, I.CDecl(psi, schema))) cD cG e (tau, t)

    | (MLam(u, e), (TypPiBox((I.MDecl(_u, tA, cPsi), _ ), tau), t)) -> 
        check cO (I.Dec(cD, I.MDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
              cG   e (tau, C.mvar_dot1 t)

    | (Box(_phat, tM), (TypBox (tA, cPsi), t)) -> 
      begin try 
        let cPsi' = C.cnormDCtx (cPsi, t) in 
        let tA'   = C.cnormTyp (tA, t) in 
          LF.check cO cD  cPsi' (tM, S.LF.id) (tA', S.LF.id)
      with Cwhnf.FreeMVar (I.FMVar(u, _ )) -> 
        raise (Error ("Free meta-variable " ^ (R.render_name u)))
      end 

        (* LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) *)


    | (Case (e, branches), (tau, t)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypBox(tA, cPsi),  t') -> 
              checkBranches cO cD cG branches (C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) (tau,t)
          | _ -> raise (Error "Case scrutinee not of boxed type")
        end

    | (Syn e, (tau, t)) -> 
        if C.convCTyp (tau,t) (syn cO cD cG e) then ()
        else raise (Error "Type mismatch")

  and check cO cD cG e (tau, t) = 
   let _ = dprint (fun () -> "check cO = " ^ Print.mctxToString cO) in
    checkW cO cD cG e (C.cwhnfCTyp (tau, t))

  and syn cO cD cG e = match e with 
    | Var x  -> (lookup cG x, C.id) 
          (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD !!! *)

    | Const prog  -> ((Comp.get prog).Comp.typ, C.id) 

    | Apply (e1, e2) -> 
        begin match C.cwhnfCTyp (syn cO cD cG e1) with 
          | (TypArr (tau2, tau), t) -> 
              (check cO cD cG e2 (tau2, t);
               (tau, t))
          | _ -> raise (Error "Function mismatch")
        end
    | CtxApp (e, cPsi) -> 
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypCtxPi ((_psi, w) , tau), t) ->
              let _ = Printf.printf "\n Schema checking omitted \n" in 
              (* REVISIT: Sun Jan 11 17:48:52 2009 -bp *)
              (* let tau' =  Cwhnf.csub_ctyp cPsi 1 tau in 
                 let t'   = Cwhnf.csub_msub cPsi 1 t in   *)

              let tau1 = Cwhnf.csub_ctyp cPsi 1 (Cwhnf.cnormCTyp (tau,t)) in  

              (checkSchema cO cD cPsi (Schema.get_schema w)
               (* (tau', t') *)
             ; (tau1, Cwhnf.id)
              )
          | _ -> raise (Error "Context abstraction mismatch")
        end 
    | MApp (e, (phat, tM)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypPiBox ((I.MDecl(_, tA, cPsi), _ ), tau), t) -> 
                (LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id);
                 (tau, MDot(MObj (phat, tM), t))
                )
          | _ -> raise (Error "MLam mismatch")
        end

    | (Ann (e, tau)) -> 
        (check cO cD cG e (tau, C.id) ; 
         (tau, C.id))

  and checkBranches cO cD cG branches tAbox ttau = match branches with
    | [] -> ()
    | (branch::branches) -> 
        let _ = checkBranch cO cD cG branch tAbox ttau in 
          checkBranches cO cD cG branches tAbox ttau

  and checkBranch cO cD cG branch (tA, cPsi) (tau, t) = 
   match branch with
   | BranchBox (cD1, (_phat, tM1, (tA1, cPsi1)), e1) ->  

      let _ = LF.check cO cD1 cPsi1 (tM1, S.LF.id) (tA1, S.LF.id) in 

      let d1 = length cD1 in 
      let _d  = length cD in 
      let t1 = mctxToMSub cD1 in   (* {cD1} |- t1 <= cD1 *)
      let t' = mctxToMSub cD in    (* {cD}  |- t' <= cD *)
      let tc = extend t' t1 in     (* {cD1, cD} |- t', t1 <= cD, cD1 *) 
      let phat = dctxToHat cPsi in 

      let _    = Unify.unifyDCtx (I.Empty) 
                                 (C.cnormDCtx (cPsi, t')) (C.cnormDCtx (cPsi1, tc)) in 
      let _    = Unify.unifyTyp (I.Empty) 
                                (phat, (C.cnormTyp (tA, t'), S.LF.id), (C.cnormTyp (tA1, tc), S.LF.id))  in 

      let (tc', cD1'') = Abstract.abstractMSub tc in  (* cD1' |- tc' <= cD, cD1 *)


      let t'' = split tc' d1 in (* cD1' |- t'' <= cD  suffix *)


     (* let  _   = Printf.printf "Type of scrutinee: %s   |-    %s \n\n Type of Pattern in branch: %s   |-  %s \n\n"
         (Pretty.Int.DefaultPrinter.dctxToString (Cwhnf.cnormDCtx (cPsi, t'')))
         (Pretty.Int.DefaultPrinter.typToString (Cwhnf.cnormTyp (tA, t'')))
         (Pretty.Int.DefaultPrinter.dctxToString (Cwhnf.cnormDCtx (cPsi1, tc')))
         (Pretty.Int.DefaultPrinter.typToString (Cwhnf.cnormTyp (tA1, tc'))) in 
     *)
      let e1' = begin try Cwhnf.cnormExp (e1, tc')  
                 with Cwhnf.FreeMVar (I.FMVar(u, _ )) -> 
                   raise (Error ("Encountered free meta-variable " ^ (R.render_name u)))
                end  in

      let cG1 = C.cwhnfCtx (cG, t'') in   

      let tau' = (tau, C.mcomp t'' t)  in 

         check cO cD1'' cG1 e1' tau' 
          

  (* checkTypeAgainstSchema cO cD cPsi tA (elements : sch_elem list)
  *)
  and checkTypeAgainstSchema cO cD cPsi tA =

    let rec projectCtxIntoDctx = function
         |  I.Empty -> I.Null
         |  I.Dec (rest, last) -> I.DDec (projectCtxIntoDctx rest, last)

    and checkAgainstElement (I.SchElem (some_part, block_part)) =
      match (some_part, block_part) with
        (cSomeCtx, I.SigmaDecl(_name, I.SigmaLast elem1)) ->
          let dctx = projectCtxIntoDctx cSomeCtx in 
          let dctxSub = ctxToSub dctx in
          let _ = dprint (fun () -> "checkAgainstElement  " ^ Print.subToString dctxSub) in
      let subD = mctxToMSub cD in   (* {cD} |- subD <= cD *)
          let normedA = Cwhnf.cnormTyp (tA, subD)
          and normedElem1 = Cwhnf.cnormTyp (elem1, subD) in
          
      let phat = dctxToHat cPsi in
            dprint (fun () -> "normedElem1 " ^ Print.typToString normedElem1 ^ ";\n" ^ "normedA " ^ Print.typToString normedA)
;
            dprint (fun () -> "***Unify.unifyTyp ("
                        ^ "\n   dctx = " ^ Print.dctxToString dctx
                        ^ "\n   " ^ Print.typToString normedA ^ " [ " ^ Print.subToString dctxSub ^ " ] "
                        ^ "\n== " ^ Print.typToString normedElem1 ^ " [ " ^Print.subToString dctxSub ^ " ] "
                        )
          ; try Unify.unifyTyp cD (phat, (normedA, S.LF.id), (normedElem1, dctxSub))
            with exn ->  (print_string ("Type " ^ Print.typToString tA ^ " doesn't unify with " ^ Print.typToString elem1 ^ "\n") ; flush_all()
                         ; raise exn)
    in
      function
        [] -> raise (Error ("Type " ^ Print.typToString tA ^ " doesn't check against schema"))
      | element :: elements ->
          try
            checkAgainstElement element
          with
            _ -> checkTypeAgainstSchema cO cD cPsi tA elements

(* The rule for checking a context against a schema is

    psi::W \in \Omega
    -----------------
     ... |- psi <= W

so checking a context element against a context element is just equality. *)
  and checkElementAgainstElement _cO _cD (I.SchElem(cSome1, block1)) (I.SchElem(cSome2, block2)) =
    (cSome1 = cSome2) && (block1 = block2)
    

  (* checkElementAgainstSchema cO cD sch_elem (elements : sch_elem list)
  *)
  and checkElementAgainstSchema cO cD sch_elem elements =
    List.exists (checkElementAgainstElement cO cD sch_elem) elements

  and checkSchema cO cD cPsi (I.Schema elements as schema) = 
     dprint (fun () -> "checkSchema " ^ Print.mctxToString cO ^ " ... " ^ Print.dctxToString cPsi ^ " against " ^ Print.schemaToString schema);
     print_string "\n WARNING: Schema checking not fully implemented\n" 
   ; match cPsi with
     | I.Null -> ()
     | I.CtxVar phi ->
         let rec lookupCtxVar = function
           | I.Empty -> raise (Error ("Context variable not found"))
           | I.Dec(cO, I.CDecl(psi, schemaName)) -> function
               | I.CtxName phi  when  psi = phi  ->  (psi, schemaName)
               |  (I.CtxName _phi) as ctx_var  ->  lookupCtxVar cO ctx_var
               |  I.CtxOffset 1  ->  (psi, schemaName)
               |  I.CtxOffset n  ->  lookupCtxVar cO (I.CtxOffset (n-1))
         in
         let lookupCtxVarSchema cO phi = snd (lookupCtxVar cO phi) in
         let I.Schema phiSchemaElements = Schema.get_schema (lookupCtxVarSchema cO phi) in
           if List.for_all (fun phiElem -> checkElementAgainstSchema cO cD phiElem elements) phiSchemaElements
           then ()
           else raiseErr (E.CtxVarMismatch (phi, schema))

     | I.DDec (cPsi', decl) ->
         begin
           checkSchema cO cD cPsi' schema
         ; match decl with
           | I.TypDecl (_x, tA) -> checkTypeAgainstSchema cO cD cPsi' tA elements
         end
  
end

module Sgn = struct


  let rec check_sgn_decls = function
    | []                       -> ()

    | Syntax.Int.Sgn.Typ   (_a, tK) :: decls ->
        let cD   = Syntax.Int.LF.Empty 
        and cO   = Syntax.Int.LF.Empty
        and cPsi = Syntax.Int.LF.Null
        in
            LF.checkKind cO cD cPsi tK
          ; check_sgn_decls decls

    | Syntax.Int.Sgn.Const (_c, tA) :: decls ->
        let cD   = Syntax.Int.LF.Empty
        and cO   = Syntax.Int.LF.Empty
        and cPsi = Syntax.Int.LF.Null
        in
            LF.checkTyp cO cD cPsi (tA, Substitution.LF.id)
          ; check_sgn_decls decls

    | Syntax.Int.Sgn.Schema (_w, schema) :: decls -> 
        let cD   = Syntax.Int.LF.Empty
        and cO   = Syntax.Int.LF.Empty
        and cPsi = Syntax.Int.LF.Null
        in 
          Comp.checkSchema cO cD cPsi schema
          ; check_sgn_decls decls

    | Syntax.Int.Sgn.Rec (_f, tau, e) :: decls ->
        let cD = Syntax.Int.LF.Empty  
        and cO   = Syntax.Int.LF.Empty
        and cG = Syntax.Int.LF.Empty in 
          Comp.checkTyp cO cD tau
          ; Comp.check cO cD cG e (tau, Cwhnf.id)
          ; check_sgn_decls decls


end
