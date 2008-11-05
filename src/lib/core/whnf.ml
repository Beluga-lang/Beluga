(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**

   @author Brigitte Pientka
   modified:  Joshua Dunfield

*)

(* Weak Head Normalization,
   Normalization, and alpha-conversion *)

open Context
open Substitution
open Syntax.Int



type error =
  | ConstraintsLeft
  | NotPatSub

exception Error of error

(******************************)
(* Lowering of Meta-Variables *)
(******************************)

(* lowerMVar' cPsi tA[s] = (u, tM), see lowerMVar *)
let rec lowerMVar' cPsi sA' = match sA' with
  | (PiTyp (cD', tA'), s')
    -> let (u', tM) = lowerMVar' (DDec (cPsi, decSub cD' s')) (tA', dot1 s') in
         (u', Lam (Id.mk_name None, tM))

  | (TClo (tA, s), s')
    -> lowerMVar' cPsi (tA, comp s s')

  | (Atom (a, tS), s')
    -> let u' = newMVar (cPsi, Atom (a, SClo (tS, s'))) in
         (u', Root (MVar (u', id), Nil)) (* cvar * normal *)



(* lowerMVar1 (u, tA[s]), tA[s] in whnf, see lowerMVar *)
and lowerMVar1 u sA = match (u, sA) with
  | (Inst (r, cPsi, _, _), (PiTyp _, _))
    -> let (u', tM) = lowerMVar' cPsi sA in
           r := Some tM   (* [| tM / u |] *)
         ; u'             (* this is the new lowered meta-variable of atomic type *)

  | (_, (TClo (tA, s), s'))
    -> lowerMVar1 u (tA, comp s s')

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
*)
    and lowerMVar = function
      | Inst (_r, _cPsi, tA, { contents = [] }) as u
        -> lowerMVar1 u (tA, id)

      | _
        (* It is not clear if it can happen that cnstr =/= nil *)
        -> raise (Error ConstraintsLeft)



    (* ------------------------------------------------------------ *)
    (* Normalization = applying simultaneous hereditary 
       substitution                                                 

       Applying the substitution sigma to an LF term tM yields again
       a normal term. This corresponds to normalizing the term [s]tM. 

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
      | Lam (y, tN)       -> Lam (y, norm (tN, dot1 sigma))

      | Clo (tN, s)       -> norm (tN, comp s sigma)

      | Root (BVar i, tS) ->
          begin match bvarSub i sigma with
            | Obj tM    -> reduce (tM, id) (normSpine (tS, sigma))
            | Head head -> Root (head, normSpine (tS, sigma))
            (* Undef should not happen ! *)
          end



      (* Meta-variables *)

      | Root (MVar (Offset _ as u, r), tS)
        -> Root (MVar (u, comp sigma r), normSpine (tS, sigma))

      | Root (MVar (Inst ({ contents = Some tM}, _, _, _), r) as _u, tS)
        (* constraints associated with u must be in solved form *)
        -> reduce (tM, r) (normSpine (tS, sigma))

      | Root (MVar (Inst ({ contents = None }, _, Atom _, _) as u, r), tS)
          (* meta-variable is of atomic type; tS = Nil *)
        -> Root (MVar (u, comp r sigma), normSpine (tS, sigma))

      | Root (MVar (Inst ({ contents = None } as r, cPsi, TClo (tA, s'), cnstr) as _u, s), tS)
        -> norm (Root (MVar (Inst (r, cPsi, normTyp (tA, s'), cnstr), s), tS), sigma)

      | Root (MVar (Inst ({ contents = None }, _, _tA, _) as u, _r), _tS)
      (* Meta-variable is not atomic and tA = Pi x:B1.B2 
         lower u, and normalize the lowered meta-variable *)
        -> let _ = lowerMVar u in norm (tM, sigma)



      (* Parameter variables *)
      | Root (PVar (Offset _ as p, r), tS)
        -> Root (PVar (p, comp sigma r), normSpine (tS, sigma))

      | Root (PVar (PInst ({ contents = Some (BVar i) }, _, _, _) as _p, r), tS)
        -> begin match bvarSub i r with
             | Obj tM    -> reduce (tM, id) (normSpine (tS, sigma))
             | Head head -> Root (head, normSpine (tS, sigma))
           end

      | Root (PVar (PInst ({ contents = Some (PVar (q, r')) }, _, _, _) as _p, r), tS)
        -> norm (Root (PVar (q, comp r' r), tS), sigma)
       (* where p::tA[cPsi]
          and  cD; cPsi' |- r : cPsi 
          and  cD; cPsi' |- p[r]      -> [r]tA
          and  cD; cPsi  |- q[r']     ->    tA
          and  cD; cPsi' |- q[r' o r] -> [r]tA
         *)
      | Root (PVar (PInst ({ contents = None}, _, _, _) as p, r), tS)
        -> Root (PVar (p, comp r sigma), normSpine (tS, sigma))

      (* Constants *)
      | Root (Const c, tS)
        -> Root (Const c, normSpine (tS, sigma))

      (* Projections *)
      | Root (Proj (BVar i, k), tS)
        -> begin match bvarSub i sigma with
             | Head (BVar j)      -> Root (Proj (BVar j, k), normSpine (tS, sigma))
             | Head (PVar (p, s)) -> Root (PVar (p, s)     , normSpine (tS, sigma))
            (* other cases are impossible -- at least for now -bp *)
           end

      | Root (Proj (PVar (Offset _i as q, s), k), tS)
        -> Root (Proj (PVar (q, comp s sigma), k), normSpine (tS, sigma))

      | Root (Proj (PVar (PInst ({ contents = Some (PVar (q, r')) }, _, _, _), s), k), tS)
        -> norm (Root (Proj (PVar (q, comp r' s), k), tS), sigma)

      | Root (Proj (PVar (PInst ({ contents = None}, _, _, _) as q, s), k), tS)
        -> Root (Proj (PVar (q, comp s sigma), k), normSpine (tS, sigma))



    and normSpine (tS, sigma) = match tS with
      | Nil           -> Nil
      | App  (tN, tS) -> App (norm (tN, sigma), normSpine (tS, sigma))
      | SClo (tS, s)  -> normSpine (tS, comp s sigma)

    (*   cPsi |- s' : cPsi'       cPsi'  | tS > tA' <= tP
         cPsi |  s  : cPsi''      cPsi'' |- tM <= tA''       [s']tA' = [s'']tA''
     *)

    and reduce sM spine = match (sM, spine) with
      | ((Root (_, _) as root, s), Nil)    -> norm (root, s)
      | ((Lam (_y, tM'), s), App (tM, tS)) -> reduce (tM', Dot (Obj tM, s)) tS
      | ((Clo (tM, s'), s), tS)            -> reduce (tM , comp s' s)       tS
      (* other cases are impossible *)



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
        -> PiTyp (normDecl (decl, sigma),  normTyp (tB, dot1 sigma))

      |  TClo (tA, s)
        -> normTyp (tA, comp s sigma)

    and normTypRec (recA, sigma) = match recA with
      | []          -> []
      | tA :: recA' -> normTyp (tA, sigma) :: normTypRec (recA', dot1 sigma)

    and normDecl (decl, sigma) = match decl with
       TypDecl (x, tA) -> TypDecl (x, normTyp (tA, sigma))



    (* ---------------------------------------------------------- *)
    (* Weak head normalization = applying simultaneous hereditary 
       substitution lazily                                                 

       Instead of fully applying the substitution sigma to an 
       LF term tM, we apply it incrementally, and delay its application
       where appropriate using Clo, SClo.
         
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

      | (Clo (tN, s), s')          -> whnf (tN, comp s s')

      | (Root (BVar i, tS), sigma) ->
          begin match bvarSub i sigma with
            | Obj tM    -> whnfRedex (whnf(tM,id), (tS,sigma))
            | Head head -> (Root(head, SClo(tS,sigma)), id)
            (* Undef should not happen! *)
          end


      (* Meta-variable *)
      |  (Root (MVar (Offset _k as u, r), tS), sigma)
        -> (Root (MVar (u, comp sigma r), SClo (tS, sigma)), id)

      | (Root (MVar (Inst ({ contents = Some tM }, _    , _ , _     ) as _u, r), tS)      , sigma)
         (* constraints associated with u must be in solved form *)
        -> whnfRedex (whnf (tM, r), (tS, sigma))

      | (Root (MVar (Inst ({ contents = None    }, _cPsi, tA, _cnstr) as u , r), tS) as tM, sigma)
            (* note: we could split this case based on tA; 
                     this would avoid possibly building closures with id *)
        -> let rec expose (tA, s) = match tA with
             | Atom (a, tS)                ->
                 Atom (a, SClo (tS, s))

             | PiTyp (TypDecl (x, tA), tB) ->
                 PiTyp (TypDecl (x, TClo (tA, s)), TClo (tB, dot1 s))

             | TClo (tA, s')               ->
                 expose (tA, comp s' s)
           in
             begin match expose (tA, id) with
               | Atom _       ->
                 (* meta-variable is of atomic type; tS = Nil *)
                   (Root (MVar (u, comp r sigma), SClo (tS, sigma)), id)

               | PiTyp (_, _) ->
                  (* Meta-variable is not atomic and tA = Pi x:B1.B2 
                     lower u, and normalize the lowered meta-variable
                     note: we may expose and compose substitutions twice. *)
                   let _ = lowerMVar u in
                     whnf (tM, sigma)
             end


      (* Parameter variable *)
      | (Root (PVar (Offset _k as p, r), tS), sigma)
        -> (Root (PVar (p, comp sigma r), SClo (tS, sigma)), id)

      | (Root (PVar (PInst ({ contents = Some (BVar i)} as _p, _, _, _) , r), tS), sigma)
        ->
          begin match bvarSub i r with
            | Obj tM    -> whnfRedex (whnf (tM, id), (tS, sigma))
            | Head head -> (Root (head, SClo (tS, sigma)), id)
          end

      | (Root (PVar (PInst ({ contents = Some (PVar (q, r')) }, _, _, _) as _p, r), tS), sigma)
        -> whnf (Root (PVar (q, comp r' r), tS), sigma)


      (* Constant *)
      | (Root (Const c, tS), sigma)
        -> (Root (Const c, SClo (tS, sigma)), id)


      (* Projections *)
      | (Root (Proj (BVar i, k), tS), sigma)
        -> begin match bvarSub i sigma with
             | Head (BVar j)      -> (Root (Proj (BVar j, k)     , SClo (tS, sigma)), id)
             | Head (PVar (q, s)) -> (Root (Proj (PVar (q, s), k), SClo (tS, sigma)), id)
            (* other cases are impossible -- at least for now -bp *)
           end


      | (Root (Proj (PVar (Offset _ as q, s), k), tS), sigma)
        -> (Root (Proj (PVar (q, comp s sigma), k), SClo (tS, sigma)), id)

      | (Root (Proj (PVar (PInst ({ contents = Some (PVar (q', r'))}, _, _, _) as _q, s), k), tS), sigma)
        -> whnf (Root (Proj (PVar (q', comp r' s), k), tS), sigma)



    (* whnfRedex((tM,s1), (tS, s2)) = (R,s')
 
       If cD ; Psi1 |- tM <= tA      and cD ; cPsi |- s1 <= Psi1
          cD ; Psi2 |- tS > tA <= tP  and cD ; cPsi |- s2 <= Psi2
      then
          cD ; cPsi |- s' : cPsi'    and cD ; cPsi' |- R' -> tP'   

          [s']tP' = [s2]tP and [s']R' = tM[s1] @ tS[s2] 

     *)
    and whnfRedex (sM, sS) = match (sM, sS) with
      | ((Root (_, _) as root, s1), (Nil, _s2))
        -> whnf (root, s1)

      | ((Lam (_x, tM), s1), (App (tN, tS), s2))
        ->  let tN' = Clo (    tN , s2) in    (* cD ; cPsi |- tN'      <= tA' *)
            let s1' = Dot (Obj tN', s1)       (* cD ; cPsi |- tN' . s1 <= Psi1, x:tA''
                                                 tA'' = [s1]tA' *)
            in
              whnfRedex ((tM, s1'), (tS, s2))

      | (sM, (SClo (tS, s2'), s2))
        -> whnfRedex (sM, (tS, comp s2' s2))

      | ((Clo (tM, s), s1), sS)
        -> whnfRedex ((tM, comp s s1), sS)



    (* whnfTyp (tA, sigma) = tA'

       If cD ; cPsi  |- tA <= type
          cD ; cPsi' |- sigma <= cPsi
       then
          tA' = [sigma]tA
          cD ; cPsi' |- tA' <= type   and tA' is in weak head normal form

     *)
    and whnfTyp (tA, sigma) = match tA with
      | Atom (a, tS)     -> (Atom (a, SClo (tS, sigma)), id)
      | PiTyp (_cD, _tB) -> (tA, sigma)
      | TClo (tA, s)     -> whnfTyp (tA, comp s sigma)



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
      | Shift _k               -> s

      | Dot (Head (BVar n), s) ->
            let s' = mkPatSub s in
            let rec checkBVar s = match s with
              | Shift k                  -> n <= k
              | Dot (Head (BVar n'), s') -> n <> n' && checkBVar s'
              | Dot (Undef, s')          ->            checkBVar s' in
            let _ = checkBVar s'
            in
              Dot (Head (BVar n), s')
      | Dot (Undef, s)         -> Dot (Undef, mkPatSub s)

      | Dot (Obj (tM), s)      ->
          begin match whnf (tM, id) with
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
        -> conv (tM1, dot1 s1) (tM2, dot1 s2)

      | ((Root (head1, spine1), s1), (Root (head2, spine2), s2))
        -> let hConv = match (head1, head2) with
             | (BVar k1, BVar k2)
               -> k1 = k2

             | (Const c1, Const c2)
               -> c1 = c2

              | (PVar (p, s'), PVar (q, s''))
                -> p = q && convSub (comp s' s1) (comp s'' s2)

              | (MVar (u, s'), MVar (w, s''))
                -> u = w && convSub (comp s' s1) (comp s'' s2)

              | (AnnH (head, _tA), _)
                -> conv' (Root (head, spine1), s1) sN

              | (_ , AnnH (head, _tA))
                -> conv' sM (Root (head, spine2), s2)

              | (Proj (BVar k1, i), Proj (BVar k2, j))
                -> k1 = k2 && i = j

              | (Proj (PVar (p, s'), i), Proj (PVar (q, s''), j))
                ->    p = q
                   && i = j
                   && convSub (comp s' s1) (comp s'' s2)
                   (* additional case: p[x] = x ? -bp*)
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
         -> convSpine spine1 (tS, comp s s')

       | ((SClo (tS, s), s'), spine2)
         -> convSpine (tS, comp s s') spine2



    and convSub subst1 subst2 = match (subst1, subst2) with
      | (Shift n, Shift k)
        -> k  = n

      | (SVar(Offset s1, sigma1), SVar(Offset s2, sigma2))
        -> s1 = s2 && convSub sigma1 sigma2

      | (Dot (f, s), Dot (f', s'))
        -> convFront f f' && convSub s s'

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

      | (Head (MVar (q, s)), Head (MVar (p, s')))
        ->    p = q
           && convSub s s'

      | (Head (Proj (head, k)), Head (Proj (head', k')))
        ->    k = k'
           && convFront (Head head) (Head head')

      | (Obj tM, Obj tN)
        -> conv (tM, id) (tN, id)

      | (Head head, Obj tN)
        -> conv (Root (head, Nil), id) (tN, id)

      | (Obj tN, Head head)
        -> conv (tN, id) (Root (head, Nil), id)

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
          && convTyp (tB1, dot1 s1) (tB2, dot1 s2)

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
      | (([]        , _s), ([]        , _s'))
        -> true

      | ((tA :: recA,  s), (tB :: recB,  s'))
        ->   convTyp    (tA  ,      s) (tB  ,      s')
          && convTypRec (recA, dot1 s) (recB, dot1 s')



    (* convCtx cPsi cPsi' = true iff
       cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx       
     *)
    let rec convDCtx cPsi cPsi' = match (cPsi, cPsi') with
      | (Null, Null)
        -> true

      | (CtxVar c1, CtxVar c2)
        -> c1 = c2

      | (DDec (cPsi1, TypDecl (_, tA)), DDec (cPsi2, TypDecl (_, tB)))
        ->   convTyp (tA, id) (tB, id)
          && convDCtx cPsi1 cPsi2

      | (SigmaDec (cPsi , SigmaDecl(_, typrec )),
         SigmaDec (cPsi', SigmaDecl(_, typrec')))
        ->   convDCtx cPsi cPsi'
          && convTypRec (typrec, id) (typrec', id)

      | (_, _)
        -> false


    (* convHatCtx((psiOpt, l), cPsi) = true iff |cPsi| = |Psihat|

       where psiOpt is a context variable, l = |Psihat|
             cPsi is a object-level context.
    *)
    let convHatCtx ((cvar, l), cPsi) =
      let (cvar', l') = dctxToHat cPsi in
             l'   = l
          && cvar = cvar'
