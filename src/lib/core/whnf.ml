(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**

   @author Brigitte Pientka
   modified:  Joshua Dunfield

*)

(* Weak Head Normalization,
   Normalization, and alpha-conversion *)

open Context
open Substitution
open Syntax.Int.LF
open Error 

exception Error of error

let rec raiseType cPsi tA = match cPsi with
  | Null -> tA
  | DDec (cPsi', decl) ->
      raiseType cPsi' (PiTyp (decl, tA))

let rec emptySpine tS = match tS with
  | Nil -> true
  | SClo(tS, _s) -> emptySpine tS



(*************************************)
(* Creating new contextual variables *)
(*************************************)

(* newPVar (cPsi, tA) = p

   Invariant:

         tA =   Atom (a, S)
     or  tA =   Pi (x:tB, tB')
     but tA =/= TClo (_, _)
*)
let newPVar (cPsi, tA) = PInst (ref None, cPsi, tA, ref [])


(* newMVar (cPsi, tA) = newMVarCnstr (cPsi, tA, [])

   Invariant:

         tA =   Atom (a, S)
     or  tA =   Pi (x:tB, tB')
     but tA =/= TClo (_, _)
*)
let newMVar (cPsi, tA) = 
Inst (ref None, cPsi, tA, ref [])



(******************************)
(* Lowering of Meta-Variables *)
(******************************)

(* lowerMVar' cPsi tA[s] = (u, tM), see lowerMVar *)
let rec lowerMVar' cPsi sA' = match sA' with
  | (PiTyp (cD', tA'), s')
    -> let (u', tM) = lowerMVar' (DDec (cPsi, LF.decSub cD' s')) (tA', LF.dot1 s') in
         (u', Lam (Id.mk_name None, tM))

  | (TClo (tA, s), s')
    -> lowerMVar' cPsi (tA, LF.comp s s')

  | (Atom (a, tS), s')
    -> let u' = newMVar (cPsi, Atom (a, SClo (tS, s'))) in
         (u', Root (MVar (u', LF.id), Nil)) (* cvar * normal *)



(* lowerMVar1 (u, tA[s]), tA[s] in whnf, see lowerMVar *)
and lowerMVar1 u sA = match (u, sA) with
  | (Inst (r, cPsi, _, _), (PiTyp _, _))
    -> let (u', tM) = lowerMVar' cPsi sA in
           r := Some tM   (* [| tM / u |] *)
         ; u'             (* this is the new lowered meta-variable of atomic type *)

  | (_, (TClo (tA, s), s'))
    -> lowerMVar1 u (tA, LF.comp s s')

  | (_, (Atom _, _s))
    -> u



(* lowerMVar (u:cvar) = u':cvar

   Invariant:

     If    cD = D1, u::tA[cPsi], D2
     where tA = PiTyp x1:B1 ... xn:tBn. tP
     and   u not subject to any constraints

     then cD' = D1, u'::tP[cPsi, x1:B1, ... xn:tBn], [|t|]D2 
     where  [| lam x1 ... xn. u'[id(cPsi), x1 ... xn] / u |] = t

     Effect: u is instantiated to lam x1 ... xn.u'[id(cPsi), x1 ... xn]
             if n = 0, u = u' and no effect occurs.

   FIXME MVar spine is not elaborated consistently with lowering
     –- Tue Dec 16 00:19:06 EST 2008
*)
and lowerMVar = function
  | Inst (_r, _cPsi, tA, { contents = [] }) as u
    -> lowerMVar1 u (tA, LF.id)

  | _
   (* It is not clear if it can happen that cnstr =/= nil *)
    -> raise (Error ConstraintsLeft)

(* ------------------------------------------------------------ *)
(* Normalization = applying simultaneous hereditary substitution

   Applying the substitution ss to an LF term tM yields again
   a normal term. This corresponds to normalizing the term [s]tM. 

   We assume that the LF term tM does not contain any closures 
   MClo (tN,t), TMClo(tA, t), SMClo(tS, t); this means we must
   first call contextual normalization and then call ordinary
   normalization.

*)
  (* 
     norm (tM,s) = [s]tM 

     Invariant:
     if cD ; cPsi  |- tM <= tA
        cD ; cPsi' |- s <= cPsi
     then
        cD ; cPsi' |- [s]tM <= [s]tA

    Similar invariants for norm, normSpine.
    *)
  let rec norm (tM, sigma) = match tM with
      | Lam (y, tN)       -> Lam (y, norm (tN, LF.dot1 sigma))

      | Clo (tN, s)       -> norm (tN, LF.comp s sigma)

      | Root (BVar i, tS) ->          
          begin match LF.bvarSub i sigma with
            | Obj tM        -> reduce (tM, LF.id) (normSpine (tS, sigma))
            | Head (BVar k) -> Root (BVar k, normSpine (tS, sigma))
            | Head head     -> norm (Root (head, normSpine (tS, sigma)), LF.id)
            (* Undef should not happen ! *)
          end

      (* Meta-variables *)

      | Root (MVar (Offset _ as u, r), tS)
        -> Root (MVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

      | Root (MVar (Inst ({ contents = Some tM}, _, _, _), r) as _u, tS)
        (* constraints associated with u must be in solved form *)
        -> reduce (tM, LF.comp r sigma) (normSpine (tS, sigma))

      | Root (MVar (Inst ({ contents = None }, _, Atom _, _) as u, r), tS)
          (* meta-variable is of atomic type; tS = Nil *)
        -> Root (MVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

      | Root (MVar (Inst ({ contents = None } as r, cPsi, TClo (tA, s'), cnstr) as _u, s), tS)
        -> norm (Root (MVar (Inst (r, cPsi, normTyp (tA, s'), cnstr), s), tS), sigma)

      | Root (MVar (Inst ({ contents = None }, _, _tA, _) as u, _r), _tS)
      (* Meta-variable is not atomic and tA = Pi x:B1.B2 
         lower u, and normalize the lowered meta-variable *)
        ->  let _ = lowerMVar u in  norm (tM, sigma)


      (* Parameter variables *)
      | Root (FMVar (u, r), tS)
        -> Root (FMVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

      (* Parameter variables *)
      | Root (PVar (Offset _ as p, r), tS)
        -> Root (PVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))


      (* Parameter variables *)
      | Root (FPVar (p, r), tS)
        -> Root (FPVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

      | Root (PVar (PInst ({ contents = Some (BVar i) }, _, _, _) as _p, r), tS)
        -> begin match LF.bvarSub i r with
             | Obj tM    -> reduce (tM, LF.id) (normSpine (tS, sigma))
             | Head (BVar x) -> Root (BVar x, normSpine (tS, sigma))
             | Head (head) -> norm (Root (head, normSpine (tS, sigma)), LF.id)
           end

      | Root (PVar (PInst ({ contents = Some (PVar (q, r')) }, _, _, _) as _p, r), tS)
        -> norm (Root (PVar (q, LF.comp r' r), tS), sigma)
       (* where p::tA[cPsi]
          and  cD; cPsi' |- r : cPsi 
          and  cD; cPsi' |- p[r]      -> [r]tA
          and  cD; cPsi  |- q[r']     ->    tA
          and  cD; cPsi' |- q[r' o r] -> [r]tA
         *)
      | Root (PVar (PInst ({ contents = None}, _, _, _) as p, r), tS)
        -> Root (PVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

      (* Constants *)
      | Root (Const c, tS)
        -> Root (Const c, normSpine (tS, sigma))

      (* Projections *)
      | Root (Proj (BVar i, k), tS)
        -> begin match LF.bvarSub i sigma with
             | Head (BVar j)      -> Root (Proj (BVar j, k), normSpine (tS, sigma))
             | Head (PVar (p, s)) -> Root (PVar (p, s)     , normSpine (tS, sigma))
            (* other cases are impossible -- at least for now -bp *)
           end

      | Root (Proj (PVar (Offset _i as q, s), k), tS)
        -> Root (Proj (PVar (q, LF.comp s sigma), k), normSpine (tS, sigma))

      | Root (Proj (PVar (PInst ({ contents = Some (PVar (q, r')) }, _, _, _), s), k), tS)
        -> norm (Root (Proj (PVar (q, LF.comp r' s), k), tS), sigma)

      | Root (Proj (PVar (PInst ({ contents = None}, _, _, _) as q, s), k), tS)
        -> Root (Proj (PVar (q, normSub (LF.comp s sigma)), k), normSpine (tS, sigma))

      | Root (FVar x, tS)
        -> Root(FVar x, normSpine (tS, sigma))
                             

  and normSpine (tS, sigma) = match tS with
    | Nil           -> Nil
    | App  (tN, tS) -> App (norm (tN, sigma), normSpine (tS, sigma))
    | SClo (tS, s)  -> normSpine (tS, LF.comp s sigma)

  (*  reduce(sM, tS) = M'

      cPsi | tS > tA' <= tP
      cPsi |  s  : cPsi''      cPsi'' |- tM <= tA''       [s]tA'' = tA'
   *)

  and reduce sM spine = match (sM, spine) with
    | ((Root (_, _) as root, s), Nil)    -> norm (root, s)
    | ((Lam (_y, tM'), s), App (tM, tS)) -> reduce (tM', Dot (Obj tM, s)) tS
    | ((Clo (tM, s'), s), tS)            -> reduce (tM , LF.comp s' s) tS
    (* other cases are impossible *)


  and normSub s = match s with 
    | Shift _ -> s
    | Dot(ft, s') -> Dot(normFt ft, normSub s')

  and normFt ft = match ft with
    | Obj tM -> 
        begin match norm (tM, LF.id) with
          | Root(BVar k, Nil) -> Head (BVar k)
          | tN                -> Obj (tN) 
        end 
    | Head (BVar _k)  -> ft
    | Head (FVar _k)  -> ft
    | Head (MVar (u, s'))  -> Head(MVar (u, normSub s'))
    | Head (FMVar (u, s')) -> Head(FMVar (u, normSub s'))
    | Head (PVar (p, s'))  -> Head(PVar (p, normSub s'))
    | Head (FPVar (p, s')) -> Head(FPVar (p, normSub s'))
    | Head (Proj(PVar (p,s'), k)) -> Head(Proj(PVar (p, normSub s'), k))
    | Head h            -> Head h
    | Undef             -> Undef  (* -bp Tue Dec 23 2008 : DOUBLE CHECK *)

  (* normType (tA, sigma) = tA'

     If cD ; G |- tA <= type
        cD ; G' |- sigma <= G
     then
        tA' = [sigma]tA
        cD ; G' |- tA' <= type   and tA' is in normal form
  *)
  and normTyp (tA, sigma) = match tA with
    |  Atom (a, tS)
      -> Atom (a, normSpine (tS, sigma))

    |  PiTyp (TypDecl (_x, _tA) as decl, tB)
      -> PiTyp (normDecl (decl, sigma), normTyp (tB, LF.dot1 sigma))

    |  TClo (tA, s)
      -> normTyp (tA, LF.comp s sigma)

  and normTypRec (recA, sigma) = match recA with
    | SigmaLast lastA -> SigmaLast (normTyp(lastA, sigma))
    | SigmaElem (x, tA, recA') ->
       let tA = normTyp (tA, sigma)
       in
         SigmaElem(x, tA, normTypRec (recA', LF.dot1 sigma))

  and normDecl (decl, sigma) = match decl with
     TypDecl (x, tA) -> TypDecl (x, normTyp (tA, sigma))


  let rec normKind tK = match tK with
    | Typ  -> Typ
    | PiKind (decl, tK) -> PiKind(normDecl (decl, LF.id), normKind tK)


  let rec normDCtx cPsi = match cPsi with
    | Null -> Null
    | CtxVar psi -> CtxVar psi 
    | DDec (cPsi1, decl) -> DDec(normDCtx cPsi1, normDecl (decl, LF.id))
    | SigmaDec (cPsi1, SigmaDecl(x, typrec)) ->
        SigmaDec(normDCtx cPsi1, SigmaDecl (x, normTypRec (typrec, LF.id)))


(* ---------------------------------------------------------- *)
(* Weak head normalization = applying simultaneous hereditary 
   substitution lazily                                                 

   Instead of fully applying the substitution sigma to an 
   LF term tM, we apply it incrementally, and delay its application
   where appropriate using Clo, SClo.

   We assume that the LF term tM does not contain any closures 
   MClo (tN,t), TMClo(tA, t), SMClo(tS, t); this means we must
   first call contextual normalization (or whnf) and then call 
   ordinary normalization, if these two substitutions interact.   
*)
  (* 
    whnf(tM,s) = (tN,s')

    Invariant:
    if cD ; cPsi'  |- tM <= tA
       cD ; cPsi   |- s <= cPsi'
    then
       cD ; cPsi  |- s' <= cPsi''
       cD ; cPsi''  |- tN  <= tB

       cD ; cPsi |- [s]tM = tN[s'] <= tA''
       cD ; cPsi |- [s]tA = [s']tB = tA'' <= type 

     Similar invariants for whnf, whnfTyp.

  *)
  let rec whnf sM = match sM with
    | (Lam _, _s)                -> sM

    | (Clo (tN, s), s')          -> whnf (tN, LF.comp s s')

    | (Root (BVar i, tS), sigma) ->       
        begin match LF.bvarSub i sigma with
          | Obj tM    -> whnfRedex ((tM, LF.id), (tS,sigma))
          | Head (BVar k) -> (Root(BVar k, SClo(tS,sigma)), LF.id)
          | Head head     ->  whnf (Root(head, SClo(tS,sigma)), LF.id)
          (* Undef should not happen! *)
        end

    (* Meta-variable *)
    | (Root (MVar (Offset _k as u, r), tS), sigma) ->
        (Root (MVar (u, LF.comp r sigma), SClo (tS, sigma)), LF.id)


    | (Root (FMVar (u, r), tS), sigma) ->
        (Root (FMVar (u, LF.comp r sigma), SClo (tS, sigma)), LF.id)

  
  | (Root (MVar (Inst ({contents = Some tM}, _cPsi, _tA, _) as _u, r), tS), sigma) ->
        (* constraints associated with u must be in solved form *)
      ((*let _ = Printf.printf "Whnf Instantiated MVar %s \n"
                 (Pretty.Int.DefaultPrinter.normalToString (Clo sM)) in 
       let _  = Printf.printf "Typ of Instantiated MVar %s \n"
                 (Pretty.Int.DefaultPrinter.typToString (raiseType cPsi tA)) in *)
       let sR =  whnfRedex ((tM, LF.comp r sigma), (tS, sigma)) in 
(*       let _ = Printf.printf "Whnf Instantiated MVar REDUCED %s \n\n"
                 (Pretty.Int.DefaultPrinter.normalToString (norm sR)) in *)
         sR)


    | (Root (MVar (Inst ({contents = None} as uref, cPsi, tA, cnstr) as u, r), tS) as tM, sigma) ->
      (* note: we could split this case based on tA; 
              this would avoid possibly building closures with id *)
        begin match whnfTyp (tA, LF.id) with
          | (Atom (a, tS'), _s (* id *)) ->
              (* meta-variable is of atomic type; tS = Nil  *)
              let u' = Inst (uref, cPsi, Atom(a, tS'), cnstr) in  
                (Root (MVar (u', LF.comp r sigma), SClo (tS, sigma)), LF.id)
          | (PiTyp _ , _s)->
              (* Meta-variable is not atomic and tA = Pi x:B1.B2 
                 lower u, and normalize the lowered meta-variable
                 note: we may expose and compose substitutions twice. *)
              let _ = lowerMVar u in                  
                whnf (tM, sigma)
        end

    (* Parameter variable *)
    | (Root (PVar (Offset _k as p, r), tS), sigma) ->
        (Root (PVar (p, LF.comp r sigma), SClo (tS, sigma)), LF.id)

    | (Root (FPVar (p, r), tS), sigma) ->
        (Root (FPVar (p, LF.comp r sigma), SClo (tS, sigma)), LF.id)

    | (Root (PVar (PInst ({ contents = Some (BVar i)} as _p, _, _, _) , r), tS), sigma) ->
        begin match LF.bvarSub i r with
          | Obj tM    -> whnfRedex ((tM, LF.id), (tS, sigma))
          | Head head -> (Root (head, SClo (tS, sigma)), LF.id)
        end

    | (Root (PVar (PInst ({contents = Some (PVar (q, r'))}, _, _, _) as _p, r), tS), sigma) ->
        whnf (Root (PVar (q, LF.comp r' r), tS), sigma)

    (* Constant *)
    | (Root (Const c, tS), sigma) ->
        (Root (Const c, SClo (tS, sigma)), LF.id)

    (* Projections *)
    | (Root (Proj (BVar i, k), tS), sigma) ->
        begin match LF.bvarSub i sigma with
          | Head (BVar j)      -> (Root (Proj (BVar j, k)     , SClo (tS, sigma)), LF.id)
          | Head (PVar (q, s)) -> (Root (Proj (PVar (q, s), k), SClo (tS, sigma)), LF.id)
          (* other cases are impossible -- at least for now -bp *)
        end

    | (Root (Proj (PVar (Offset _ as q, s), k), tS), sigma) ->
        (Root (Proj (PVar (q, LF.comp s sigma), k), SClo (tS, sigma)), LF.id)

    | (Root (Proj (PVar (PInst ({contents = Some (PVar (q', r'))}, _, _, _) as _q, s), k), tS), sigma) ->
        whnf (Root (Proj (PVar (q', LF.comp r' s), k), tS), sigma)

    (* Free variables *)
    | (Root (FVar x, tS), sigma) ->
        (Root (FVar x, SClo (tS, sigma)), LF.id)


  (* whnfRedex((tM,s1), (tS, s2)) = (R,s')
 
     If cD ; Psi1 |- tM <= tA       and cD ; cPsi |- s1 <= Psi1
        cD ; Psi2 |- tS > tA <= tP  and cD ; cPsi |- s2 <= Psi2
     then
        cD ; cPsi |- s' : cPsi'    and cD ; cPsi' |- R' -> tP'   

        [s']tP' = [s2]tP and [s']R' = tM[s1] @ tS[s2] 

  *)
  and whnfRedex (sM, sS) = match (sM, sS) with
    | ((Root (_, _) as root, s1), (Nil, _s2)) ->
        whnf (root, s1) 
       
    | ((Lam (_x, tM), s1), (App (tN, tS), s2)) ->
        let tN' = Clo (    tN , s2) in  (* cD ; cPsi |- tN'      <= tA' *)
        let s1' = Dot (Obj tN', s1) in  (* cD ; cPsi |- tN' . s1 <= Psi1, x:tA''
                                           tA'' = [s1]tA' *)
          whnfRedex ((tM, s1'), (tS, s2))

    | (sM, (SClo (tS, s2'), s2)) ->
        whnfRedex (sM, (tS, LF.comp s2' s2))

    | ((Clo (tM, s), s1), sS) ->
        whnfRedex ((tM, LF.comp s s1), sS)


    (* whnfTyp (tA, sigma) = tA'

       If cD ; cPsi  |- tA <= type
          cD ; cPsi' |- sigma <= cPsi
       then
          tA' = [sigma]tA
          cD ; cPsi' |- tA' <= type   and tA' is in weak head normal form

     *)
  and whnfTyp (tA, sigma) = match tA with
    | Atom (a, tS)     -> (Atom (a, SClo (tS, sigma)), LF.id)
    | PiTyp (_cD, _tB) -> (tA, sigma)
    | TClo (tA, s)     -> whnfTyp (tA, LF.comp s sigma)




  (* ----------------------------------------------------------- *)
    (* makePatSub s = Some(s') if s is convertible to a patSub
                      None otherwise

       Invariant:
       If    cPsi |- s : cPsi' 
       and   s = n1 .. nm ^k
       then  tB iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
    let rec mkPatSub s = match s with
      | Shift (NoCtxShift, _k)            -> s
      | Shift (CtxShift(_psi), _k)        -> s
      | Shift (NegCtxShift _ ,  _k)        -> 
          raise (Error NotPatSub)

      | Dot (Head (BVar n), s) ->
            let s' = mkPatSub s in
            let rec checkBVar s = match s with
              | Shift (_ , k)            -> n <= k
              | Dot (Head (BVar n'), s') -> n <> n' && checkBVar s'
              | Dot (Undef, s')          ->            checkBVar s' in
            let _ = checkBVar s'
            in
              Dot (Head (BVar n), s')
      | Dot (Undef, s)         -> Dot (Undef, mkPatSub s)

      | Dot (Obj (tM), s)      ->
          begin match whnf (tM, LF.id) with
            | (Root (BVar k, Nil), _id) -> Dot (Head (BVar k), mkPatSub s)
            | _                         -> raise (Error NotPatSub)
          end

      | _                      -> raise (Error NotPatSub)

    let rec makePatSub s = try Some (mkPatSub s) with Error _ -> None

  (* ----------------------------------------------------------- *)

  (* Conversion :  Convertibility modulo alpha 

   *)
    (* convTyp (tA,s1) (tB,s2) = true iff [s1]tA = [s2]tB
       conv (tM,s1) (tN,s2) = true    iff [s1]tM = [s2]tN
       convSpine (S1,s1) (S2,s2) = true iff [s1]S1 = [s2]S2

       convSub s s' = true iff s = s'

       This is on normal forms -- needs to be on whnf.
     *)

    let rec conv sM1 sN2 = conv' (whnf sM1) (whnf sN2)

    and conv' sM sN = match (sM, sN) with
      | ((Lam (_, tM1), s1),  (Lam (_, tM2), s2))
        -> conv (tM1, LF.dot1 s1) (tM2, LF.dot1 s2)

      | ((Root (head1, spine1), s1), (Root (head2, spine2), s2))
        -> let hConv = match (head1, head2) with
             | (BVar k1, BVar k2)
               -> k1 = k2

             | (Const c1, Const c2)
               -> c1 = c2

              | (PVar (p, s'), PVar (q, s''))
                -> p = q && convSub (LF.comp s' s1) (LF.comp s'' s2)

              | (FPVar (p, s'), FPVar (q, s''))
                -> p = q && convSub (LF.comp s' s1) (LF.comp s'' s2)

              | (MVar (u, s'), MVar (w, s''))
                -> u = w && convSub (LF.comp s' s1) (LF.comp s'' s2)

              | (FMVar (u, s'), FMVar (w, s''))
                -> u = w && convSub (LF.comp s' s1) (LF.comp s'' s2)

              | (AnnH (head, _tA), _)
                -> conv' (Root (head, spine1), s1) sN

              | (_ , AnnH (head, _tA))
                -> conv' sM (Root (head, spine2), s2)

              | (Proj (BVar k1, i), Proj (BVar k2, j))
                -> k1 = k2 && i = j

              | (Proj (PVar (p, s'), i), Proj (PVar (q, s''), j))
                ->    p = q
                   && i = j
                   && convSub (LF.comp s' s1) (LF.comp s'' s2)
                   (* additional case: p[x] = x ? -bp*)

              | (FVar x , FVar y)
                ->  x = y 

              | (_, _)
                -> false
            in
                 hConv
              && convSpine (spine1, s1) (spine2, s2)

      | _ -> false



     and convSpine spine1 spine2 = match (spine1, spine2) with
       | ((Nil, _s1), (Nil, _s2))
         -> true

       | ((App (tM1, spine1), s1), (App (tM2, spine2), s2))
         ->   conv      (tM1   , s1) (tM2   , s2)
           && convSpine (spine1, s1) (spine2, s2)

       | (spine1, (SClo (tS, s), s'))
         -> convSpine spine1 (tS, LF.comp s s')

       | ((SClo (tS, s), s'), spine2)
         -> convSpine (tS, LF.comp s s') spine2



    and convSub subst1 subst2 = match (subst1, subst2) with
      | (Shift (psi,n), Shift (psi', k)) -> 
          n = k && psi = psi'

      | (SVar(Offset s1, sigma1), SVar(Offset s2, sigma2))
        -> s1 = s2 && convSub sigma1 sigma2

      | (Dot (f, s), Dot (f', s'))
        -> convFront f f' && convSub s s'
      
      | (Shift (psi, n), Dot(Head BVar _k, _s')) 
          -> convSub (Dot (Head (BVar (n+1)), Shift (psi, n+1))) subst2

      | (Dot(Head BVar _k, _s'), Shift (psi, n)) 
          -> convSub subst1 (Dot (Head (BVar (n+1)), Shift (psi, n+1)))
          
      |  _
        -> false



    and convFront front1 front2 = match (front1, front2) with
      | (Head (BVar i), Head (BVar k))
        -> i = k

      | (Head (Const i), Head (Const k))
        -> i = k

      | (Head (PVar (q, s)), Head (PVar (p, s')))
        ->    p = q
           && convSub s s'


      | (Head (FPVar (q, s)), Head (FPVar (p, s')))
        ->    p = q
           && convSub s s'

      | (Head (MVar (u, s)), Head (MVar (v, s')))
        ->  u = v
           && convSub s s'

      | (Head (FMVar (u, s)), Head (FMVar (v, s')))
        ->    u = v
           && convSub s s'

      | (Head (Proj (head, k)), Head (Proj (head', k')))
        ->    k = k'
           && convFront (Head head) (Head head')

      | (Head (FVar x), Head (FVar y))
        -> x = y

      | (Obj tM, Obj tN)
        -> conv (tM, LF.id) (tN, LF.id)

      | (Head head, Obj tN)
        -> conv (Root (head, Nil), LF.id) (tN, LF.id)

      | (Obj tN, Head head)
        -> conv (tN, LF.id) (Root (head, Nil), LF.id)

      | (Undef, Undef)
        -> true

      | (_, _)
        -> false



    let rec convTyp' sA sB = match (sA, sB) with
      | ((Atom (a1, spine1), s1), (Atom (a2, spine2), s2))
        ->    a1 = a2
           && convSpine (spine1, s1) (spine2, s2)

      | ((PiTyp (TypDecl (_, tA1), tB1), s1), (PiTyp (TypDecl (_, tA2), tB2),s2))
            (* G |- A1[s1] = A2[s2] by typing invariant *)
        ->   convTyp (tA1,      s1) (tA2,      s2)
          && convTyp (tB1, LF.dot1 s1) (tB2, LF.dot1 s2)

      | _
        -> false



    and convTyp sA sB = convTyp' (whnfTyp sA) (whnfTyp sB)



    (* convTypRec((recA,s), (recB,s'))

       Given: cD ; Psi1 |- recA <= type   and cD ; Psi2 |- recB  <= type
              cD ; cPsi  |- s <= cPsi       and cD ; cPsi  |- s' <= Psi2

       returns true iff recA and recB are convertible where 
          cD ; cPsi |- [s]recA = [s']recB <= type
     *)
    let rec convTypRec sArec sBrec = match (sArec, sBrec) with
      | (  (SigmaLast lastA,  s),     (SigmaLast lastB,  s')  )
        -> convTyp (lastA, s) (lastB, s')

      | (  (SigmaElem(_xA, tA, recA),  s),     (SigmaElem(_xB, tB, recB),  s')  )
        ->   convTyp (tA, s) (tB, s')
          && convTypRec (recA, LF.dot1 s) (recB, LF.dot1 s')



    (* convDCtx cPsi cPsi' = true iff
       cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx       
     *)
    let rec convDCtx cPsi cPsi' = match (cPsi, cPsi') with
      | (Null, Null)
        -> true

      | (CtxVar c1, CtxVar c2)
        -> c1 = c2

      | (DDec (cPsi1, TypDecl (_, tA)), DDec (cPsi2, TypDecl (_, tB)))
        ->   convTyp (tA, LF.id) (tB, LF.id)
          && convDCtx cPsi1 cPsi2

      | (SigmaDec (cPsi , SigmaDecl(_, typrec )),
         SigmaDec (cPsi', SigmaDecl(_, typrec')))
        ->   convDCtx cPsi cPsi'
          && convTypRec (typrec, LF.id) (typrec', LF.id)

      | (_, _)
        -> false


    (* convCtx cPsi cPsi' = true iff
       cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx       
     *)
    let rec convCtx cPsi cPsi' = match (cPsi, cPsi') with
      | (Empty, Empty)
        -> true

      | (Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB)))
        ->   convTyp (tA, LF.id) (tB, LF.id)
          && convCtx cPsi1 cPsi2


    (* convHatCtx((psiOpt, l), cPsi) = true iff |cPsi| = |Psihat|

       where psiOpt is a context variable, l = |Psihat|
             cPsi is a object-level context.
    *)
    let convHatCtx ((cvar, l), cPsi) =
      let (cvar', l') = dctxToHat cPsi in
             l'   = l
          && cvar = cvar'



(* etaExpandMV cPsi sA s' = tN
 *
 *  cPsi'  |- s'   <= cPsi
 *  cPsi   |- [s]A <= typ
 *
 *  cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMV cPsi sA s' = etaExpandMV' cPsi (whnfTyp sA)  s'

and etaExpandMV' cPsi sA  s' = match sA with
  | (Atom (_a, _tS) as tP, s) ->
      let u = newMVar (cPsi, TClo(tP,s)) in
        Root (MVar (u, s'), Nil)

  | (PiTyp (TypDecl (x, _tA) as decl, tB), s) ->
      Lam (x, etaExpandMV (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) (LF.dot1 s'))
