(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**

   @author Brigitte Pientka

*)

(* Contextual Weak Head Normalization,
   Contextual Normalization, and alpha-conversion 
   for contextual substitutions *)

open Context
open Syntax.Int.LF
open Syntax.Int.Comp

module S = Substitution.LF



(*************************************)
(* Contextual Explicit Substitutions *)

(* Eagerly composes substitution     

   - All meta-variables must be of atomic type P[Psi]
   - Parameter variables may be of type A[Psi]

   - We decided against a constructor MShift n;
     contextual substitutions provide a mapping for different
     kinds of contextual variables and MShift n does not encode
     this information. Hence, it is not clear how to deal with the case 
     comp (MShift n) t   (where t =/= MShift m). 


   - We decided to not provide a constructor Id in msub
     (for similar reasons)

*)
(*************************************)
(* shift t n = t' 

   Invariant: 

   If D |- t <= D' 
   then  D, ... |- t' <= D', ...   where ... has length n
                                   and t' = t^n
*)
let rec shift t n = match t with
  | MShiftZero     -> t
  | MDot(ft, t') -> MDot(shiftMFt ft n, shift t' n)


and shiftMFt ft n = match ft with 
  | MObj(phat, tM) -> 
      MObj(phat, shiftTerm tM n)   

  | PObj(phat, PVar(Offset k, s)) -> 
     PObj(phat, PVar(Offset (k+n), s))

  | PObj(_phat, BVar _k) -> ft

and shiftTerm tM n = match tM with
  | Lam(x, tN)  -> Lam(x, shiftTerm tN n)
  | Root(h, tS) -> Root(shiftHead h n, shiftSpine tS n)
  | Clo(tM, s)  -> Clo(shiftTerm tM n, shiftSub s n)

and shiftHead h n = match h with
  | MVar(Offset k, s) -> MVar(Offset (k+n), shiftSub s n)
  | PVar(Offset k, s) -> PVar(Offset (k+n), shiftSub s n)
  | Proj(PVar(Offset k, s), j) -> Proj(PVar(Offset (k+n), shiftSub s n), j)
  | AnnH(h, tA) -> AnnH(shiftHead h n, shiftTyp tA n)
  | _ -> h

and shiftSpine tS n = match tS with 
  | Nil -> Nil
  | App(tM, tS) -> App(shiftTerm tM n, shiftSpine tS n)
  | SClo(tS, s) -> SClo(shiftSpine tS n, shiftSub s n)

and shiftTyp tA n = match tA with
  | Atom (a, tS) -> Atom(a, shiftSpine tS n)
  | PiTyp(TypDecl(x, tA), tB) -> PiTyp(TypDecl(x, shiftTyp tA n), shiftTyp tB n)
  | TClo(tA, s) -> TClo(shiftTyp tA n, shiftSub s n)

and shiftSub s n = match s with
  | Shift _k -> s
  | SVar(Offset k, s) -> SVar(Offset (k+n), shiftSub s n)
  | Dot(ft, s) -> Dot (shiftFt ft n, shiftSub s n)

and shiftFt ft n = match ft with
  | Head h -> Head (shiftHead h n)
  | Obj tM -> Obj (shiftTerm tM n)
  | Undef  -> Undef
  
(* mvar_dot1 psihat t = t'
   Invariant:

   If   D |- t : D'

   then t' = u[id]. (shiftOne t)  where phat = |Psi|
       and  for all A s.t.  D' ; Psi |- A : type

     D, u::[|t|](P[Psi]) |- t' : D', P[Psi]

  NOTE: This in fact only works, if the type of u is atomic!

 *)
  and mvar_dot1 phat t = MDot (MObj(phat , Root(MVar(Offset 1, S.id), Nil)), shift t 1)


  and pvar_dot1 phat t = MDot (PObj(phat , PVar(Offset 1, S.id)), shift t 1)


  and ctxvar_dot1 t = MDot (CObj(CtxVar(Offset 1)), shift t 1)

(* mcomp (t1, t2) = t'

   Invariant:

   If   D'  |- t1 : D 
   and  D'' |- t2 : D'
   then t'  =  t1 o t2
   and  D'' |- t1 o t2 : D

   Note: Eagerly composes the contextual substitutions t1 and t2.

*)

let rec comp t1 t2 = match (t1, t2) with
  | (MShiftZero, t)         -> t
  | (t, MShiftZero)         -> t
  | (MDot (mft, t), t')     -> MDot (mfrontMSub mft t', comp t t')


(* mfrontMSub Ft t = Ft'

   Invariant:

   If   D |- t : D'     D' ; Psi |- Ft <= A
   then Ft' =  [|t|] Ft
   and  D ; [|t|]Psi |- Ft' : [|t|]A
*)
and mfrontMSub ft t = match ft with
  | MObj (phat, tM)     -> 
	MObj (phat, cnorm(tM, t))
  | PObj (_phat, PVar (Offset k, s))  -> 
      begin match applyMSub k t with
        | PObj(phat, BVar k') ->  
	    begin match S.bvarSub k' s with 
	      | Head(BVar j) -> PObj(phat, BVar j)
	      | Head(PVar (q, s')) -> PObj(phat, PVar(q, s'))
	      (* no case for S.Head(MVar(u, s')) since u not guaranteed
	         to be of atomic type. *)
	      | Obj tM      -> MObj(phat, tM)
	    end 
	| PObj(phat, PVar (q, s')) -> PObj(phat, PVar(q, S.comp s' s))
          (* other cases impossible *)
      end
  | PObj (_phat, BVar _k)  -> ft


(* applyMSub n t = MFt'
     
   Invariant: 

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ft_n      if  t = Ft_1 .. Ft_n .. ^0
     and D ; [|t|]Psi |- Ft' <= [|t|]A
  *)

and applyMSub n t = match (n, t) with
  | (1, MDot (ft, _t)) -> ft
  | (n, MDot (_ft, t)) -> applyMSub (n - 1) t
    

(* ------------------------------------------------------------ *)
(* Normalization = applying simultaneous contextual substitution   

     Applying the contextual substitution t to an normal LF term tM 
     yields again a normal term. This corresponds to normalizing the 
     term [|t|]tM.  

*)
  (* 
     cnorm (tM,t) = [|t|]tM 

     Invariant:
     if cD ; cPsi  |- tM <= tA
     cD'  |- t <= cD
     then
     [|t|] cPsi = cPsi' , [|t|]tA = tA', [|t|]tM = tM'
     cD' ; cPsi' |- tM' <= tA'

     Similar invariants for cnorm, cnormSpine.

     If tM is in normal form, then [|t|]tM is also in normal form. 

  *)
  and cnorm (tM, t) = match tM with
    | Lam (y, tN)       -> Lam (y, cnorm (tN, t))

    | Clo (tN, s)       -> Clo(cnorm (tN, t), cnormSub(s, t))  

    | Root (BVar i, tS) -> Root(BVar i, cnormSpine (tS, t))

    (* Meta-variables *)

    | Root (MVar (Offset k, r), tS)
      -> begin match applyMSub k t with
        | MObj (_phat,tM)   -> Clo(Whnf.whnfRedex ((tM, r), (cnormSpine (tS, t), S.id)))
        (* other cases impossible *)
       end

    (* Ignore other cases for destructive (free) meta-variables -- at least for now *)

    (* Parameter variables *)
    | Root (PVar (Offset k, r), tS)
        (* cD' ; cPsi' |- r <= cPsi1 
           cD          |- t <= cD'
 
           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r

         *)
      -> begin match applyMSub k t with
        | PObj (_phat, BVar i) -> 
	    begin match S.bvarSub i (cnormSub (r,t)) with
	      | Head h  -> Root(h, cnormSpine (tS, t))
	      | Obj tM  -> Clo (Whnf.whnfRedex ((tM, S.id), (cnormSpine (tS, t), S.id)))
	    end
        | PObj (_phat, PVar(Offset i, r')) -> 
	    Root (PVar(Offset i, S.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
            (* Other case MObj _ should not happen -- ill-typed *)
      end

    (* Ignore other cases for destructive (free) parameter variables *)

    (* Constants *)
    | Root (Const c, tS)
      -> Root (Const c, cnormSpine (tS, t))

    (* Projections *)
    | Root (Proj (BVar i, k), tS)
      -> Root (Proj (BVar i, k), cnormSpine (tS, t))

    | Root (Proj (PVar (Offset j, s), k), tS)
        (* cD' ; cPsi' |- s <= cPsi1 *)
        (* cD          |- t <= cD'   *)         
      -> begin match applyMSub j t with
        | PObj (_phat, BVar i)   -> 
            (*  i <= phat *) 
            begin match S.bvarSub i (cnormSub (s,t)) with
              | Head (BVar j)     -> 
                  Root(Proj (BVar j, k), cnormSpine (tS, t))
              | Head (PVar (p,r'))-> 
                  Root(Proj (PVar (p, r'), k), 
                       cnormSpine (tS, t))
                    (* other cases should not happen; 
                       term would be ill-typed *)
            end
        | PObj(_phat, Proj (PVar (Offset i, s'), k)) -> 
	    Root (Proj (PVar (Offset i, S.comp s' (cnormSub (s,t))), k), 
		  cnormSpine (tS, t))
      end

  (* Ignore other cases for destructive (free) parameter-variables *)

  and cnormSpine (tS, t) = match tS with
    | Nil            -> Nil
    | App  (tN, tS)  -> App (cnorm (tN, t), cnormSpine (tS, t))
    | SClo (tS, s)   -> SClo(cnormSpine (tS, t), cnormSub (s, t))


  and cnormSub (s, t) = match s with 
    | Shift _         -> s
    | Dot (ft, s')     -> Dot (cnormFront (ft, t), cnormSub (s', t))
     (* substitution variables ignored for how -bp *)


  and cnormFront (ft, t) = match ft with
    | Head (BVar _ )            -> ft
    | Head (Const _ )           -> ft
    | Head (PVar (Offset i, r)) ->
        begin match applyMSub i t with
          | PObj(_phat, PVar(Offset n, s')) -> 
             Head(PVar(Offset n, S.comp s' (cnormSub (r,t))))
          | PObj (_phat, BVar j)    ->  S.bvarSub j (cnormSub (r,t))
  	      (* other case MObj _ cannot happen *)
        end

    | Head (MVar (Offset i, r)) -> 
        begin match applyMSub i t with
          | MObj (_phat, tM)    -> Obj(Clo (tM, cnormSub (r,t)))
        end

    | Head (Proj (BVar _, _))    -> ft
    | Head (Proj (PVar (Offset i, r), k)) -> 
        let r' = cnormSub (r,t) in 
        begin match applyMSub i t with
          | PObj (_phat, BVar j)  -> 
	      begin match S.bvarSub j r' with
		| Head(BVar j') -> Head(Proj (BVar j', k))
		| Head(PVar (Offset j, s')) -> Head (Proj (PVar (Offset j, s'), k))
                (* other cases impossible for projections *)
	      end
	  | PObj (_phat, PVar(Offset j, s'))   ->  
	      Head(Proj (PVar(Offset j, S.comp s' r'), k))
          (* other case MObj _ cannot happen *)
        end
          
  (* cnormType (tA, t) = tA'

     If cD' ; cPsi  |- tA <= type
     cD |- t <= cD'
     then
     tA' = [|t|]tA  and cPsi' = [|t|]cPsi
     cD' ; cPsi' |- tA' <= type   
  *)
  and cnormTyp (tA, t) = match tA with
    |  Atom (a, tS)
      -> Atom (a, cnormSpine (tS, t))

    |  PiTyp (TypDecl (_x, _tA) as decl, tB)
      -> PiTyp (cnormDecl (decl, t),  cnormTyp (tB, t))

    |  TClo (tA, s)
      -> TClo(cnormTyp (tA,t), cnormSub (s,t))

  and cnormTypRec (recA, t) = match recA with
    | []          -> []
    | tA :: recA' -> cnormTyp (tA, t) :: cnormTypRec (recA', t)

  and cnormDecl (decl, t) = match decl with
      TypDecl (x, tA) -> TypDecl (x, cnormTyp (tA, t))

  and cnormDCtx tcPsi = match tcPsi with
    | (Null, _)       ->  Null 

    | (CtxVar (Offset psi), t) -> 
	begin match applyMSub psi t with
	  | CObj cPsi -> cPsi
	  (* other cases ill-typed *)
	end 

    | (DDec(cPsi, decl), t) ->  
	DDec(cnormDCtx(cPsi, t), cnormDecl(decl, t))

    | (SigmaDec (cPsi, SigmaDecl(x, recA)), t) -> 
	SigmaDec(cnormDCtx (cPsi, t), SigmaDecl(x, cnormTypRec (recA, t)))


  (* ***************************************** *)
  (* Contextual weak head normal form for 
     computation-level types                   *)
  (* ***************************************** *)


  (* cwhnfCTyp (tT1, t1) = (tT2, t2)
     
     Invariant:
     If  cD1 ; cG1 |- tT1 ctype 
     cD        |- t1 <= cD1
     then
     cD2 ; cG2 |- tT2 ctype
     cD        |- t2 <= cD2

     cD        |- [|t2|]cG2 = [|t1|]cG1 = cG'
     cD ; cG'  |- [|t2|]tT2 = [|t1|]tT2 = tT 
     
  *)


  let rec cwhnfCTyp thetaT = match thetaT with 
    | (TypBox (tA, cPsi), t)     
      -> (TypBox(cnormTyp(tA, t), cnormDCtx(cPsi, t)), MShiftZero) 

    | (TypSBox (cPsi, cPsi'), t) 
      -> (TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), MShiftZero)

    | (TypArr (_tT1, _tT2), _t)   -> thetaT

    | (TypCtxPi _, _)             -> thetaT

    | (TypPiBox (_, _) , _)       -> thetaT

    | (TypClo (tT, t'), t)        -> (tT, comp t' t)



  (* ----------------------------------------------------------- *)
  (* Conversion: Convertibility modulo alpha for 
     computation-level types
  *)


  (* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)

  let rec convCTyp thetaT1 thetaT2 = convCTyp' (cwhnfCTyp thetaT1) (cwhnfCTyp thetaT2)

  and convCTyp' thetaT1 thetaT2 = match (thetaT1, thetaT2) with 
    | ((TypBox (tA1, cPsi1), _t1), (TypBox (tA2, cPsi2), _t2)) (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi2
	&&
	  Whnf.convTyp (tA1, S.id) (tA2, S.id)

    | ((TypSBox (cPsi1, cPsi2), _t), (TypSBox (cPsi1', cPsi2'), _t'))  (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi1'
	&&
	  Whnf.convDCtx cPsi2 cPsi2'

    | ((TypArr (tT1, tT2), t), (TypArr (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
	&&
	  convCTyp (tT2, t) (tT2', t')

    | ((TypCtxPi ((_psi, schema), tT1), t) , (TypCtxPi ((_psi', schema'), tT1'), t'))
      -> convSchema schema schema'
	&& 
	  convCTyp (tT1, ctxvar_dot1 t) (tT1', ctxvar_dot1 t')

    | ((TypPiBox (MDecl(_, tA, cPsi), tT), t), (TypPiBox (MDecl(_, tA', cPsi'), tT'), t'))
      -> let psihat = dctxToHat cPsi in 
	Whnf.convTyp (cnormTyp (tA, t), S.id) (cnormTyp (tA', t'), S.id)
	&&
	  Whnf.convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
	&& 
	  convCTyp (tT, mvar_dot1 psihat  t) (tT', mvar_dot1 psihat t') 

(* For now we omit PDecl, SDecl - bp *)

and convSchema (Schema fs) (Schema fs') =  List.for_all2 convSchElem fs fs' 

and convSchElem (SchElem (cPsi, SigmaDecl (_, trec))) (SchElem (cPsi', SigmaDecl (_, trec'))) = 
    Whnf.convCtx cPsi cPsi'
    &&
      Whnf.convTypRec (trec, S.id) (trec', S.id)
