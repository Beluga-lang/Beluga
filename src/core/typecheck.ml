(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
   @author Darin Morrison
*)

  exception Error of string

  module I = Syntax.Int

    (* check cD cPsi (tM, s1) (tA, s2) = ()

       Invariant: 
       If   cD ; cPsi |- s1 <= Psi1   
       and  cD ; cPsi |- s2 <= Psi2    Psi2 |- tA <= type
       returns () 
       if there exists an tA' s.t.    
            cD ; Psi1 |- tM <= tA' 
       and  cD ; cPsi  |- tA'[s1] = tA[s2] : type
       and  cD ; cPsi  |- tM[s1] <= tA'[s1]
       otherwise exception Error is raised
    *)
    let rec checkW cD cPsi sM1 sA2 = match (sM1, sA2) with
      | ((I.Lam(_,tM), s1), (I.PiTyp(I.TypDecl(x,tA) as tX, tB), s2)) ->
          check cD  (I.DDec(cPsi, I.decSub tX s2))
                 (tM, I.dot1 s1) (tB, I.dot1 s2)
      | ((I.Root (h, tS), s), (I.Atom _,s') as sP) ->
        let
          (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
          sA = Whnf.whnfTyp (inferHead cD cPsi h, I.id)
        in
(*XXX 
          checkSpine cD cPsi (tS, s) sA sP
*) ()
 
    and check cD cPsi sM1 sA2 = checkW cD cPsi (Whnf.whnf sM1) (Whnf.whnfTyp sA2)


    (* checkSpine (cD, cPsi, (tS, s1), (tA, s2), sP) = ()

       Invariant: 
       If   cD ; cPsi |- s1 <= Psi1  
       and  cD ; cPsi |- s2 <= Psi2  and  cD ; Psi2 |- tA <= type ,   (tA, s2) in whnf  
       then succeeds if there exists tA', tP' such that cD ; Psi1 |- tS : tA' > tP'
            and  cD ; cPsi |- s' : cPsi'    and  cD ; cPsi' |- tA' <= type
            and  cD ; cPsi |- tA'[s'] = tA [s2] <= type
            and  cD ; cPsi |- tP'[s'] = sP     <= type
    *)
    and checkSpine cD cPsi sS1 sA2 sP = match (sS1, sA2) with
        ((I.Nil, _), sP') ->
            if Whnf.convTyp sP' sP then ()
            else raise (Error "Type mismatch")

      | ((I.SClo (tS, s'), s), sA) ->
          checkSpine cD cPsi (tS, I.comp s' s) sA sP

      | ((I.App (tM, tS), s1), (I.PiTyp (I.TypDecl (_, tA1), tB2), s2)) ->
         (check cD cPsi (tM, s1) (tA1, s2);
           let
             (* cD ; Psi1 |- tM <= tA1',  cD ; cPsi |- s1 <= Psi1
                cD ; Psi2, x:tA1 |- tB2 <= type  and [s1]tA1' = [s2]tA1 *)
             tB2 = Whnf.whnfTyp (tB2, I.Dot (I.Obj (I.Clo(tM,s1)), s2))
           in 
             checkSpine cD cPsi (tS, s1) tB2 sP
          )

      | ((I.App (tM , tS), _),  (tA, s)) -> (* tA <> (Pi x:tA1. tA2, s) *)
          raise  (Error "Expression is applied, but not a function")

    (* inferHead cD cPsi h = tA

       Invariant: returns tA if
              cD ; cPsi |- h -> tA
       where  cD ; cPsi |- tA <= type
       else exception Error is raised. 
    *)
    and inferHead cD cPsi head = match head with
         I.BVar k' ->
           let I.TypDecl (_, tA) = I.ctxDec cPsi k'
           in tA
      | I.Proj (I.BVar(k'),  target) ->
        let I.SigmaDecl(_, recA) = I.ctxSigmaDec cPsi k'
          (* getType traverses the type from left to right;
             target is relative to the remaining suffix of the type
          *)
        in let rec getType s_recA target j = match (s_recA, target) with
            | ((tA::recA, s), 1) -> I.TClo(tA, s)
            | ((tA::recA, s), target) ->
                    let tPj = I.Root(I.Proj(I.BVar k', j), I.Nil) 
                    in 
                      getType (recA, I.Dot(I.Obj(tPj), s)) (target-1) (j+1)
        in 
          getType (recA, I.id) target 1
   
      (* Missing cases?  Tue Sep 30 22:09:27 2008 -bp 

         Proj (I.PVar(p,s), i) 
         Proj (I.MVar(p,s), i) 

         These cases are impossible at the moment.
       *)
      | I.Const c -> I.constType c

      | I.MVar(I.Offset u, s) ->
        let
          (* cD ; cPsi' |- tA <= type *)
          (tA, cPsi') = I.mctxMDec cD u
        in 
          (checkSub cD cPsi s cPsi';
           I.TClo(tA, s))

      | I.PVar(I.Offset u,s) ->
        let
          (* cD ; cPsi' |- tA <= type *)
          (tA, cPsi') = I.mctxPDec cD u
        in 
          (   checkSub cD cPsi s cPsi';
              I.TClo(tA, s)   )

    (* checkSub cD cPsi s cPsi' = ()

       Invariant:
       This function succeeds iff cD ; cPsi |- s : cPsi'
    *)
    and checkSub cD cPsi s cPsi' = match (cPsi, s, cPsi') with
         (I.Null, I.Shift 0, I.Null) -> ()
      | (I.CtxVar(psi), I.Shift 0, I.CtxVar(psi')) ->
           if psi = psi' then () else raise (Error "ctx variable mismatch")
      (* SVar case to be added - bp *)
      | (I.DDec (cPsi, tX), I.Shift k, I.Null) ->
           if k>0 then checkSub cD cPsi (I.Shift (k-1)) I.Null
           else raise (Error "Substitution not well-typed")

      | (cPsi', I.Shift k, cPsi) ->
          checkSub cD cPsi' (I.Dot (I.Head(I.BVar (k+1)), I.Shift (k+1))) cPsi

      | (cPsi', I.Dot (I.Head h, s'), 
                           I.DDec (cPsi, (I.TypDecl (_, tA2)))) ->
        (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
        let 
           _ = checkSub cD cPsi' s' cPsi
          (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
          and tA1 = inferHead cD cPsi' h
        in
          if Whnf.convTyp (tA1, I.id) (tA2, s') then ()
          else raise (Error ("Substitution not well-typed \n  found: " 
                            (* Print.expToString (cD, cPsi', tA1) ^ "\n  expected: " ^
                            Print.expToString (cD, cPsi', I.Clo (tA2, s'))*)))

      | (cPsi', I.Dot (I.Head(I.BVar w), t), 
                           I.SigmaDec (cPsi, (I.SigmaDecl (_, arec)))) ->
        (* other heads of type Sigma disallowed -bp *)
        let
          _ = checkSub cD cPsi' t cPsi
          (* ensures that t is well-typed before comparing types BRec =[t]ARec *)
        and I.SigmaDecl (_, brec) = I.ctxSigmaDec cPsi' w
        in
          if Whnf.convTypRec (brec, I.id) (arec, t)  then ()
          else raise (Error "Declaration not well-typed")

      | (cPsi', I.Dot (I.Obj tM, s'), I.DDec (cPsi, (I.TypDecl (_, tA2)))) ->
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let 
          _ = checkSub cD cPsi' s' cPsi
          (* ensures that s' is well-typed and [s']tA2 is well-defined *)
        in
          check cD cPsi' (tM, I.id) (tA2, s')


    (* ---------------------------------------------------------- *)
    (* kind checking *)
    (* kind checking is only applied to type constants declared in
       the signature; 
       All constants declared in the signature do not contain any
       contextual variables, hence Delta = . 
     *)
   
    (* checkSpineK cD cPsi (tS, s1) (K, s2) succeeds 
       iff  cD ; cPsi |- [s1]tS <= [s2]K
     *)
    and checkSpineK cD cPsi sS1 sA = match (sS1, sA) with
      | ((I.Nil, _), (I.Typ,s)) -> ()
      | ((I.Nil, _), _) ->  raise (Error "kind mismatch")
      | ((I.SClo (tS, s'), s), sA) ->
          checkSpineK cD cPsi (tS, I.comp s' s) sA
      | ((I.App (tM, tS), s1), (I.PiKind (I.TypDecl (_, tA1), kind), s2)) ->
          (   check cD cPsi (tM, s1) (tA1, s2);
              checkSpineK cD cPsi (tS, s1) (kind, I.Dot (I.Obj (I.Clo (tM, s1)), s2))   )
      | ((I.App (tM , tS), _), (tA, s)) ->
          raise  (Error "Expression is applied, but not a function")

    (* checkTyp (cD, cPsi, (tA,s)) succeeds iff cD ; cPsi |- [s]tA <= type *)
    let rec checkTyp' (cD, cPsi, (tA,s)) = match (tA, s) with
         (I.Atom(a, tS),s) ->
            checkSpineK cD cPsi (tS,s) (I.tconstKind(a), I.id)
      | (I.PiTyp(I.TypDecl(x, tA), tB), s)  ->
        (   checkTyp cD cPsi (tA,s); 
            checkTyp cD (I.DDec(cPsi, I.TypDecl(x, I.TClo(tA,s)))) (tB, I.dot1 s)   )

    and checkTyp cD cPsi sA = checkTyp' (cD, cPsi, Whnf.whnfTyp sA)

    (* checkTypRec cD cPsi (recA, s) succeeds iff cD ; cPsi |- [s]recA <= type *)
    let rec checkTypRec cD cPsi (recA, s) = match recA with
         [] -> ()
      | tA::recA ->
        (checkTyp cD cPsi (tA, s);
         checkTypRec cD (I.DDec(cPsi, I.decSub (I.TypDecl(Id.mk_name None, tA)) s))
                     (recA, I.dot1 s))

    (* checkKind cD cPsi K succeeds iff cD ; cPsi |- K kind *)
    let rec checkKind cD cPsi kind = match kind with
          I.Typ -> ()
      | I.PiKind(I.TypDecl(x, tA), kind) ->
         (checkTyp cD cPsi (tA, I.id); 
          checkKind cD (I.DDec(cPsi, I.TypDecl(x, tA))) kind)


    (* checkDec cD cPsi (x:tA, s) succeeds iff cD ; cPsi |- [s]tA <= type *)
    and checkDec cD cPsi (decl, s) = match decl with
        I.TypDecl (_, tA) -> checkTyp cD cPsi (tA, s)

    (* checkSigmaDec cD cPsi (x:recA, s) succeeds iff cD ; cPsi |- [s]recA <= type *)
    and checkSigmaDec cD cPsi (sigma_decl, s) = match sigma_decl with
        I.SigmaDecl (_, arec) ->
            checkTypRec cD cPsi (arec, s)

    (* checkCtx (cD, cPsi) succeeds iff cD |- cPsi ctx *)
    and checkCtx cD cPsi = match cPsi with I.Null ->  ()
      | I.DDec (cPsi, tX) ->
          (checkCtx cD cPsi; checkDec cD cPsi (tX, I.id))
      | I.SigmaDec (cPsi, tX) ->
          (checkCtx cD cPsi; checkSigmaDec cD cPsi (tX, I.id))
      | I.CtxVar psi -> () 
        (* need to check if psi is in Omega (or cD, if context vars live there) -bp *) 
