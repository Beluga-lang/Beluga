(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contextual normal form

   @author Brigitte Pientka

*)

(* Contextual Weak Head Normalization,
   Contextual Normalization, and alpha-conversion 
   for contextual substitutions *)

open Context
open Syntax.Int

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

let id = Comp.MShiftZero

(* shift t n = t' 

   Invariant: 

   If D |- t <= D' 
   then  D, ... |- t' <= D', ...   where ... has length n
                                   and t' = t^n
*)
let rec shift t n = match t with
  | Comp.MShiftZero     -> t
  | Comp.MDot(ft, t') -> Comp.MDot(shiftMFt ft n, shift t' n)


and shiftMFt ft n = match ft with 
  | Comp.MObj(phat, tM) -> 
      Comp.MObj(phat, shiftTerm tM n)   

  | Comp.PObj(phat, LF.PVar(LF.Offset k, s)) -> 
     Comp.PObj(phat, LF.PVar(LF.Offset (k+n), s))

  | Comp.PObj(_phat, LF.BVar _k) -> ft

and shiftTerm tM n = match tM with
  | LF.Lam(x, tN)  -> LF.Lam(x, shiftTerm tN n)
  | LF.Root(h, tS) -> LF.Root(shiftHead h n, shiftSpine tS n)
  | LF.Clo(tM, s)  -> LF.Clo(shiftTerm tM n, shiftSub s n)

and shiftHead h n = match h with
  | LF.MVar(LF.Offset k, s) -> LF.MVar(LF.Offset (k+n), shiftSub s n)
  | LF.PVar(LF.Offset k, s) -> LF.PVar(LF.Offset (k+n), shiftSub s n)
  | LF.Proj(LF.PVar(LF.Offset k, s), j) -> LF.Proj(LF.PVar(LF.Offset (k+n), shiftSub s n), j)
  | LF.AnnH(h, tA) -> LF.AnnH(shiftHead h n, shiftTyp tA n)
  | _ -> h

and shiftSpine tS n = match tS with 
  | LF.Nil -> LF.Nil
  | LF.App(tM, tS) -> LF.App(shiftTerm tM n, shiftSpine tS n)
  | LF.SClo(tS, s) -> LF.SClo(shiftSpine tS n, shiftSub s n)

and shiftTyp tA n = match tA with
  | LF.Atom (a, tS) -> LF.Atom(a, shiftSpine tS n)
  | LF.PiTyp(LF.TypDecl(x, tA), tB) -> LF.PiTyp(LF.TypDecl(x, shiftTyp tA n), shiftTyp tB n)
  | LF.TClo(tA, s) -> LF.TClo(shiftTyp tA n, shiftSub s n)

and shiftSub s n = match s with
  | LF.Shift _k -> s
  | LF.SVar(LF.Offset k, s) -> LF.SVar(LF.Offset (k+n), shiftSub s n)
  | LF.Dot(ft, s) -> LF.Dot (shiftFt ft n, shiftSub s n)

and shiftFt ft n = match ft with
  | LF.Head h -> LF.Head (shiftHead h n)
  | LF.Obj tM -> LF.Obj (shiftTerm tM n)
  | LF.Undef  -> LF.Undef
  
(* mvar_dot1 psihat t = t'
   Invariant:

   If   D |- t : D'

   then t' = u[id]. (shiftOne t)  where phat = |Psi|
       and  for all A s.t.  D' ; Psi |- A : type

     D, u::[|t|](P[Psi]) |- t' : D', P[Psi]

  NOTE: This in fact only works, if the type of u is atomic!

 *)
  and mvar_dot1 phat t = 
    Comp.MDot (Comp.MObj(phat , LF.Root(LF.MVar(LF.Offset 1, S.id), LF.Nil)), 
               shift t 1)


  and pvar_dot1 phat t = 
    Comp.MDot (Comp.PObj(phat , LF.PVar(LF.Offset 1, S.id)), shift t 1)


  and ctxvar_dot1 t = 
    Comp.MDot (Comp.CObj(LF.CtxVar(LF.Offset 1)), shift t 1)

(* comp (t1, t2) = t'

   Invariant:

   If   D'  |- t1 : D 
   and  D'' |- t2 : D'
   then t'  =  t1 o t2
   and  D'' |- t1 o t2 : D

   Note: Eagerly composes the contextual substitutions t1 and t2.

*)

let rec comp t1 t2 = match (t1, t2) with
  | (Comp.MShiftZero, t)         -> t
  | (t, Comp.MShiftZero)         -> t
  | (Comp.MDot (mft, t), t')     -> Comp.MDot (mfrontMSub mft t', comp t t')


(* mfrontMSub Ft t = Ft'

   Invariant:

   If   D |- t : D'     D' ; Psi |- Ft <= A
   then Ft' =  [|t|] Ft
   and  D ; [|t|]Psi |- Ft' : [|t|]A
*)
and mfrontMSub ft t = match ft with
  | Comp.MObj (phat, tM)     -> 
	Comp.MObj (phat, cnorm(tM, t))
  | Comp.PObj (_phat, LF.PVar (LF.Offset k, s))  -> 
      begin match applyMSub k t with
        | Comp.PObj(phat, LF.BVar k') ->  
	    begin match S.bvarSub k' s with 
	      | LF.Head(LF.BVar j) -> Comp.PObj(phat, LF.BVar j)
	      | LF.Head(LF.PVar (q, s')) -> Comp.PObj(phat, LF.PVar(q, s'))
	      (* no case for S.Head(MVar(u, s')) since u not guaranteed
	         to be of atomic type. *)
	      | LF.Obj tM      -> Comp.MObj(phat, tM)
	    end 
	| Comp.PObj(phat, LF.PVar (q, s')) -> Comp.PObj(phat, LF.PVar(q, S.comp s' s))
          (* other cases impossible *)
      end
  | Comp.PObj (_phat, LF.BVar _k)  -> ft


(* applyMSub n t = MFt'
     
   Invariant: 

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ft_n      if  t = Ft_1 .. Ft_n .. ^0
     and D ; [|t|]Psi |- Ft' <= [|t|]A
  *)

and applyMSub n t = match (n, t) with
  | (1, Comp.MDot (ft, _t)) -> ft
  | (n, Comp.MDot (_ft, t)) -> applyMSub (n - 1) t
    

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
    | LF.Lam (y, tN)       -> LF.Lam (y, cnorm (tN, t))

    | LF.Clo (tN, s)       -> LF.Clo(cnorm (tN, t), cnormSub(s, t))  

    | LF.Root (LF.BVar i, tS) -> LF.Root(LF.BVar i, cnormSpine (tS, t))

    (* Meta-variables *)

    | LF.Root (LF.MVar (LF.Offset k, r), tS)
      -> begin match applyMSub k t with
        | Comp.MObj (_phat,tM)   -> 
            LF.Clo(Whnf.whnfRedex ((tM, r), (cnormSpine (tS, t), S.id)))
        (* other cases impossible *)
       end

    (* Ignore other cases for destructive (free) meta-variables -- at least for now *)

    (* Parameter variables *)
    | LF.Root (LF.PVar (LF.Offset k, r), tS)
        (* cD' ; cPsi' |- r <= cPsi1 
           cD          |- t <= cD'
 
           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r

         *)
      -> begin match applyMSub k t with
        | Comp.PObj (_phat, LF.BVar i) -> 
	    begin match S.bvarSub i (cnormSub (r,t)) with
	      | LF.Head h  -> LF.Root(h, cnormSpine (tS, t))
	      | LF.Obj tM  -> LF.Clo (Whnf.whnfRedex ((tM, S.id), (cnormSpine (tS, t), S.id)))
	    end
        | Comp.PObj (_phat, LF.PVar(LF.Offset i, r')) -> 
	    LF.Root (LF.PVar(LF.Offset i, S.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
            (* Other case MObj _ should not happen -- ill-typed *)
      end

    (* Ignore other cases for destructive (free) parameter variables *)

    (* Constants *)
    | LF.Root (LF.Const c, tS)
      -> LF.Root (LF.Const c, cnormSpine (tS, t))

    (* Projections *)
    | LF.Root (LF.Proj (LF.BVar i, k), tS)
      -> LF.Root (LF.Proj (LF.BVar i, k), cnormSpine (tS, t))

    | LF.Root (LF.Proj (LF.PVar (LF.Offset j, s), k), tS)
        (* cD' ; cPsi' |- s <= cPsi1 *)
        (* cD          |- t <= cD'   *)         
      -> begin match applyMSub j t with
        | Comp.PObj (_phat, LF.BVar i)   -> 
            (*  i <= phat *) 
            begin match S.bvarSub i (cnormSub (s,t)) with
              | LF.Head (LF.BVar j)     -> 
                  LF.Root(LF.Proj (LF.BVar j, k), cnormSpine (tS, t))
              | LF.Head (LF.PVar (p,r'))-> 
                  LF.Root(LF.Proj (LF.PVar (p, r'), k), 
                       cnormSpine (tS, t))
                    (* other cases should not happen; 
                       term would be ill-typed *)
            end
        | Comp.PObj(_phat, LF.Proj (LF.PVar (LF.Offset i, s'), k)) -> 
	    LF.Root (LF.Proj (LF.PVar (LF.Offset i, S.comp s' (cnormSub (s,t))), k), 
		  cnormSpine (tS, t))
      end

  (* Ignore other cases for destructive (free) parameter-variables *)

  and cnormSpine (tS, t) = match tS with
    | LF.Nil            -> LF.Nil
    | LF.App  (tN, tS)  -> LF.App (cnorm (tN, t), cnormSpine (tS, t))
    | LF.SClo (tS, s)   -> LF.SClo(cnormSpine (tS, t), cnormSub (s, t))


  and cnormSub (s, t) = match s with 
    | LF.Shift _         -> s
    | LF.Dot (ft, s')    -> LF.Dot (cnormFront (ft, t), cnormSub (s', t))
     (* substitution variables ignored for how -bp *)


  and cnormFront (ft, t) = match ft with
    | LF.Head (LF.BVar _ )            -> ft
    | LF.Head (LF.Const _ )           -> ft
    | LF.Head (LF.PVar (LF.Offset i, r)) ->
        begin match applyMSub i t with
          | Comp.PObj(_phat, LF.PVar(LF.Offset n, s')) -> 
             LF.Head(LF.PVar(LF.Offset n, S.comp s' (cnormSub (r,t))))
          | Comp.PObj (_phat, LF.BVar j)    ->  S.bvarSub j (cnormSub (r,t))
  	      (* other case MObj _ cannot happen *)
        end

    | LF.Head (LF.MVar (LF.Offset i, r)) -> 
        begin match applyMSub i t with
          | Comp.MObj (_phat, tM)    -> LF.Obj(LF.Clo (tM, cnormSub (r,t)))
        end

    | LF.Head (LF.Proj (LF.BVar _, _))    -> ft
    | LF.Head (LF.Proj (LF.PVar (LF.Offset i, r), k)) -> 
        let r' = cnormSub (r,t) in 
        begin match applyMSub i t with
          | Comp.PObj (_phat, LF.BVar j)  -> 
	      begin match S.bvarSub j r' with
		| LF.Head(LF.BVar j') -> LF.Head(LF.Proj (LF.BVar j', k))
		| LF.Head(LF.PVar (LF.Offset j, s')) -> LF.Head (LF.Proj (LF.PVar (LF.Offset j, s'), k))
                (* other cases impossible for projections *)
	      end
	  | Comp.PObj (_phat, LF.PVar(LF.Offset j, s'))   ->  
	      LF.Head(LF.Proj (LF.PVar(LF.Offset j, S.comp s' r'), k))
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
    |  LF.Atom (a, tS)
      -> LF.Atom (a, cnormSpine (tS, t))

    |  LF.PiTyp (LF.TypDecl (_x, _tA) as decl, tB)
      -> LF.PiTyp (cnormDecl (decl, t),  cnormTyp (tB, t))

    |  LF.TClo (tA, s)
      -> LF.TClo(cnormTyp (tA,t), cnormSub (s,t))

  and cnormTypRec (recA, t) = match recA with
    | []          -> []
    | tA :: recA' -> cnormTyp (tA, t) :: cnormTypRec (recA', t)

  and cnormDecl (decl, t) = match decl with
      LF.TypDecl (x, tA) -> LF.TypDecl (x, cnormTyp (tA, t))

  and cnormDCtx tcPsi = match tcPsi with
    | (LF.Null, _)       ->  LF.Null 

    | (LF.CtxVar (LF.Offset psi), t) -> 
	begin match applyMSub psi t with
	  | Comp.CObj cPsi -> cPsi
	  (* other cases ill-typed *)
	end 

    | (LF.DDec(cPsi, decl), t) ->  
	LF.DDec(cnormDCtx(cPsi, t), cnormDecl(decl, t))

    | (LF.SigmaDec (cPsi, LF.SigmaDecl(x, recA)), t) -> 
	LF.SigmaDec(cnormDCtx (cPsi, t), LF.SigmaDecl(x, cnormTypRec (recA, t)))


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
    | (Comp.TypBox (tA, cPsi), t)     
      -> (Comp.TypBox(cnormTyp(tA, t), cnormDCtx(cPsi, t)), id) 

    | (Comp.TypSBox (cPsi, cPsi'), t) 
      -> (Comp.TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), id)

    | (Comp.TypArr (_tT1, _tT2), _t)   -> thetaT

    | (Comp.TypCtxPi _, _)             -> thetaT

    | (Comp.TypPiBox (_, _) , _)       -> thetaT

    | (Comp.TypClo (tT, t'), t)        -> (tT, comp t' t)



  (* ----------------------------------------------------------- *)
  (* Conversion: Convertibility modulo alpha for 
     computation-level types
  *)


  (* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)

  let rec convCTyp thetaT1 thetaT2 = convCTyp' (cwhnfCTyp thetaT1) (cwhnfCTyp thetaT2)

  and convCTyp' thetaT1 thetaT2 = match (thetaT1, thetaT2) with 
    | ((Comp.TypBox (tA1, cPsi1), _t1), (Comp.TypBox (tA2, cPsi2), _t2)) (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi2
	&&
	  Whnf.convTyp (tA1, S.id) (tA2, S.id)

    | ((Comp.TypSBox (cPsi1, cPsi2), _t), (Comp.TypSBox (cPsi1', cPsi2'), _t'))  (* t1 = t2 = id *)
      -> Whnf.convDCtx cPsi1 cPsi1'
	&&
	  Whnf.convDCtx cPsi2 cPsi2'

    | ((Comp.TypArr (tT1, tT2), t), (Comp.TypArr (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
	&&
	  convCTyp (tT2, t) (tT2', t')

    | ((Comp.TypCtxPi ((_psi, schema), tT1), t) , (Comp.TypCtxPi ((_psi', schema'), tT1'), t'))
      -> convSchema schema schema'
	&& 
	  convCTyp (tT1, ctxvar_dot1 t) (tT1', ctxvar_dot1 t')

    | ((Comp.TypPiBox (LF.MDecl(_, tA, cPsi), tT), t), (Comp.TypPiBox (LF.MDecl(_, tA', cPsi'), tT'), t'))
      -> let psihat = dctxToHat cPsi in 
	Whnf.convTyp (cnormTyp (tA, t), S.id) (cnormTyp (tA', t'), S.id)
	&&
	  Whnf.convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
	&& 
	  convCTyp (tT, mvar_dot1 psihat  t) (tT', mvar_dot1 psihat t') 

(* For now we omit PDecl, SDecl - bp *)

and convSchema (LF.Schema fs) (LF.Schema fs') =  List.for_all2 convSchElem fs fs' 

and convSchElem (LF.SchElem (cPsi, LF.SigmaDecl (_, trec))) (LF.SchElem (cPsi', LF.SigmaDecl (_, trec'))) = 
    Whnf.convCtx cPsi cPsi'
    &&
      Whnf.convTypRec (trec, S.id) (trec', S.id)
