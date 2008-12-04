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
(* Eagerly composes substitution     *)
(*************************************)
(* shiftOne t = t' 

   Invariant: 

   If D |- t <= D' 
   then  D, _ |- t' <= D', _
*)
let rec shiftOne t = match t with
  | MShiftZero     -> t
  | MDot(ft, t') -> MDot(shiftOneFt ft, shiftOne t')


and shiftOneFt ft = match ft with 
  | MObj(phat, Root(MVar(Offset k, s), Nil)) -> 
     MObj(phat, Root(MVar(Offset (k+1), s), Nil))

  | PObj(phat, PVar(Offset k, s)) -> 
     PObj(phat, PVar(Offset (k+1), s))

  | PObj(_phat, BVar _k) -> ft


(* mvar_dot1 psihat t = t'
   Invariant:

   If   D |- t : D'
   then t' = u[id]. (shiftOne t)  where phat = |Psi|
       and  for all A s.t.  D' ; Psi |- A : type

     D, u::[|t|](P[Psi]) |- t' : D', P[Psi]

  NOTE: This in fact only works, if the type of u is atomic!

 *)
  and mvar_dot1 phat t = match t with
    | MShiftZero -> t
    | t        -> MDot (MObj(phat , Root(MVar(Offset 1, S.id), Nil)), shiftOne t)


 and pvar_dot1 phat t = match t with
    | MShiftZero -> t
    | t        -> MDot (PObj(phat , PVar(Offset 1, S.id)), shiftOne t)



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
	      (* no case for S.Head(MVar(_, s')) *)
	      | Obj(tM)      -> MObj(phat, tM)
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
        | MObj (_phat,tM)   -> Whnf.reduce (tM, r) (cnormSpine (tS, t))
        (* other cases impossible *)
       end

    (* Ignore other cases for destructive (free) meta-variables *)

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
	      | Head (h)  -> Root(h, cnormSpine (tS, t))
	      | Obj (tM)   -> 
		  Whnf.reduce (tM, S.id) (cnormSpine (tS, t))
	    end
        | PObj (_phat, PVar(Offset i, r')) -> 
	    Root (PVar(Offset i, S.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
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
      -> begin match applyMSub j t with
        | PObj (_phat, BVar i)   -> 
            (*  i <= phat *) 
            begin match S.bvarSub i (cnormSub (s,t)) with
              | Head (BVar j)     -> 
                  Root(Proj (BVar j, k), cnormSpine (tS, t))
              | Head (PVar (p,r'))-> 
                  Root(Proj (PVar (p, r'), k), 
                       cnormSpine (tS, t))
                    (* other cases should not happen ; 
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
          | MObj (_phat, tM)    -> Obj(Whnf.norm (tM, cnormSub (r,t)))
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
(* 	  | Id phi    -> CtxVar (Offset phi)*)
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
      -> (TypBox(cnormTyp(tA, t), cnormDCtx(cPsi, t)), MShiftZero) 

    | (TypSBox (cPsi, cPsi'), t) 
      -> (TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), MShiftZero)

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
	  Whnf.convTyp (tA1, S.id) (tA2, S.id)

    | ((TypSBox (cPsi1, cPsi2), _t), (TypSBox (cPsi1', cPsi2'), _t'))  (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi1'
	&&
	  Whnf.convDCtx cPsi2 cPsi2'

    | ((TypArr (tT1, tT2), t), (TypArr (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
	&&
	  convCTyp (tT2, t) (tT2', t')

(*    | ((TypCtxPi ((_psi, _W), tT1), t) , (TypCtxPi ((_psi', _W'), tT1'), t'))
      -> (* convSchema (W, W')   ? *)
	convCTyp (tT1, dot1 t) (tT1', dot1 t')
*)
    | ((TypPiBox (MDecl(_, tA, cPsi), tT), t), (TypPiBox (MDecl(_, tA', cPsi'), tT'), t'))
      -> let psihat = dctxToHat cPsi in 
	Whnf.convTyp (cnormTyp (tA, t), S.id) (cnormTyp (tA', t'), S.id)
	&&
	  Whnf.convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
	&& 
	  convCTyp (tT, mvar_dot1 psihat  t) (tT', mvar_dot1 psihat t') 

(* For now we omit PDecl, SDecl - bp *)

