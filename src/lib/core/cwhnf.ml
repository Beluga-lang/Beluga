(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**

   @author Brigitte Pientka

*)

(* Contextual Weak Head Normalization,
   Contextual Normalization, and alpha-conversion 
   for contextual substitutions *)

open Context
open Substitution
open Syntax.Int.LF
open Syntax.Int.Comp


  (*************************************)
  (* Contextual Explicit Substitutions *)
  (* Eagerly composes substitution     *)
  (*************************************)


  (* id = ^0 
     
     Invariant:

     cD |- id : cD      

     Note: we do not take into account weakening here. 
  *)
  let id = MShift 0

  (* shift = ^1
     
     Invariant:

     cD, u:tA[cPsi] |- ^ : cD     
  *)
  let shift = MShift 1


  (* mvarMSub n t = MFt'
     
     Invariant: 

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ftn       if  s = Ft1 .. Ftn .. ^k
     or  Ft' = ^(n + k)    if  s = Ft1 .. Ftm ^k   and m < n
     and Psi |- Ft' <= [|t|]A
  *)

  let rec mvarMSub n t = match (n, t) with
    | (1, MDot (ft, _t)) -> ft
    | (n, MDot (_ft, t)) -> mvarMSub (n - 1) t
    | (n, MShift k)      -> Id (n + k)

  (* comp (t1, t2) = t'

     Invariant:

     If   D'  |- t1 : D 
     and  D'' |- t2 : D'
     then s'  =  t1 o t2
     and  D'' |- t1 o t2 : D

     Note: Eagerly composes the contextual substitutions t1 and t2.

  *)
  let rec comp t1 t2 = match (t1, t2) with
    | (MShift 0, t)             -> t
    | (t, MShift 0)             -> t
    | (MShift n, MDot (_ft, t))  -> comp (MShift (n - 1)) t
    | (MShift n, MShift m)       -> MShift (n + m)
    | (MDot (mft, t), t')        -> MDot (mfrontMSub mft t', comp t t')

  (* mfrontMSub Ft t = Ft'

     Invariant:

     If   D |- t : D'     D' ; Psi |- Ft <= A
     then Ft' =  [|t|] Ft
     and  D ; [|t|]Psi |- Ft' : [|t|]A
  *)
  and mfrontMSub ft t = match ft with
    | Id n                -> mvarMSub n t
    | MObj (phat, tM)     -> 
	MObj (phat, cnorm(tM, t))

  (* dot1 (t) = t'

     Invariant:

     If   D |- t : D'
     then t' = 1. (t o ^)
     and  for all A s.t.  D' ; Psi |- A : type
     D, u::[|t|](A[Psi] |- t' : D', A[Psi]
  *)
  and dot1 t = match t with
    | MShift 0 -> t
    | t        -> MDot (Id 1, comp t shift)


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
      -> begin match mvarMSub k t with
        | MObj (_phat,tM)   -> Whnf.reduce (tM, r) (cnormSpine (tS, t))
        | Id i -> Root (MVar(Offset i, cnormSub (r,t)), cnormSpine (tS, t))
      end

    (* Ignore other cases for destructive (free) meta-variables *)

    (* Parameter variables *)
    | Root (PVar (Offset k, r), tS)
        (* cD' ; cPsi' |- r <= cPsi1 
           cD          |- t <= cD'
 
           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r

         *)
      -> begin match mvarMSub k t with
        | PObj (_phat, i) -> 
	    begin match LF.bvarSub i (cnormSub (r,t)) with
	      | Head (h)  -> Root(h, cnormSpine (tS, t))
	      | Obj (tM)   -> 
		  Whnf.reduce (tM, LF.id) (cnormSpine (tS, t))
	    end
        | Id i -> Root (PVar(Offset i, cnormSub (r,t)), cnormSpine (tS, t))
            (* Other case MObj _ should not happen -- ill-typed *)
      end

    (* Ignore other cases for destructive (free) parameter-variables *)

    (* Constants *)
    | Root (Const c, tS)
      -> Root (Const c, cnormSpine (tS, t))

    (* Projections *)
    | Root (Proj (BVar i, k), tS)
      -> Root (Proj (BVar i, k), cnormSpine (tS, t))

    | Root (Proj (PVar (Offset j, s), k), tS)
        (* cD' ; cPsi' |- s <= cPsi1 *)
        (* cD          |- t <= cD'   *)         
      -> begin match mvarMSub j t with
        | PObj (_phat, i)   -> 
            (*  i <= phat *) 
            begin match LF.bvarSub i (cnormSub (s,t)) with
              | Head (BVar j)     -> 
                  Root(Proj (BVar j, k), cnormSpine (tS, t))
              | Head (PVar (p,r'))-> 
                  Root(Proj (PVar (p, r'), k), 
                       cnormSpine (tS, t))
                    (* other cases should not happen ; 
                       term would be ill-typed *)
            end
        | Id i  -> Root (Proj (PVar (Offset i, cnormSub (s,t)), k), cnormSpine (tS, t))
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
        begin match mvarMSub i t with
          | Id n                -> Head(PVar(Offset n, cnormSub (r,t)))
          | PObj (_phat, j)    ->  LF.bvarSub j (cnormSub (r,t))
  	      (* other case MObj _ cannot happen *)
        end

    | Head (MVar (Offset i, r)) -> 
        begin match mvarMSub i t with
          | Id n                -> Head (MVar (Offset n, cnormSub (r,t)))
          | MObj (_phat, tM)    -> Obj(Whnf.norm (tM, cnormSub (r,t)))
        end

    | Head (Proj (BVar _, _))    -> ft
    | Head (Proj (PVar (Offset i, r), k)) -> 
        begin match mvarMSub i t with
          | Id n                -> Head(Proj(PVar (Offset n, cnormSub (r,t)), k))
          | PObj (_phat, j)   ->  LF.bvarSub j (cnormSub(r,t))
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
	begin match mvarMSub psi t with 
	  | Id phi    -> CtxVar (Offset phi)
	  | CObj cPsi -> cPsi
	  (* other cases ill-typed *)
	end 

    | (DDec(cPsi, decl), t) ->  
	DDec(cnormDCtx(cPsi, t), cnormDecl(decl, t))

    | (SigmaDec (cPsi, SigmaDecl(x, recA)), t) -> 
	SigmaDec(cnormDCtx (cPsi, t), SigmaDecl(x, cnormTypRec (recA, t)))


  (* ***************************************** *)
  (* Contextual Weak Head Normalform for 
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


  let rec cwhnfCTyp ttT = match ttT with 
    | (TypBox (tA, cPsi), t)     
      -> (TypBox(cnormTyp(tA, t), cnormDCtx(cPsi, t)), id) 

    | (TypSBox (cPsi, cPsi'), t) 
      -> (TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), id)

    | (TypArr (_tT1, _tT2), _t)   -> ttT

    | (TypCtxPi _, _)             -> ttT

    | (TypPiBox (_, _) , _)       -> ttT

    | (TypClo (tT, t'), t)        -> (tT, comp t' t)



  (* ----------------------------------------------------------- *)
  (* Converstion: Convertibility modulo alpha for 
     computation-level types
  *)


  (* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)

  let rec convCTyp ttT1 ttT2 = convCTyp' (cwhnfCTyp ttT1) (cwhnfCTyp ttT2)

  and convCTyp' ttT1 ttT2 = match (ttT1, ttT2) with 
    | ((TypBox (tA1, cPsi1), _t1), (TypBox (tA2, cPsi2), _t2)) (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi2
	&&
	  Whnf.convTyp (tA1, LF.id) (tA2, LF.id)

    | ((TypSBox (cPsi1, cPsi2), _t), (TypSBox (cPsi1', cPsi2'), _t'))  (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi1'
	&&
	  Whnf.convDCtx cPsi2 cPsi2'

    | ((TypArr (tT1, tT2), t), (TypArr (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
	&&
	  convCTyp (tT2, t) (tT2', t')

    | ((TypCtxPi ((_psi, _W), tT1), t) , (TypCtxPi ((_psi', _W'), tT1'), t'))
      -> (* convSchema (W, W')   ? *)
	convCTyp (tT1, dot1 t) (tT1', dot1 t')

    | ((TypPiBox (MDecl(_, tA, cPsi), tT), t), (TypPiBox (MDecl(_, tA', cPsi'), tT'), t'))
      -> Whnf.convTyp (cnormTyp (tA, t), LF.id) (cnormTyp (tA', t'), LF.id)
	&&
	  Whnf.convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
	&& 
	  convCTyp (tT, dot1 t) (tT', dot1 t') 

(* For now we omit PDecl, SDecl - bp *)

