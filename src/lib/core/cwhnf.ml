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


  (* ------------------------------------------------------------ *)
  (* Normalization = applying simultaneous contextual substitution   

     Applying the contextual substitution t to an normal LF term tM 
     yields again a normal term. This corresponds to normalizing the 
     term [|t|]tM.  

   *)
  (* 
    cnorm (tM,t) = [|t|]tM 

    Invariant:
    if cD' ; cPsi  |- tM <= tA
       cD  |- t <= cD'
    then
       [|t|] cPsi = cPsi' , [|t|]tA = tA', [|t|]tM = tM'
       cD' ; cPsi' |- tM' <= tA'

    Similar invariants for cnorm, cnormSpine.

    If tM is in normal form, then [|t|]tM is also in normal form. 

     *)
  let rec cnorm (tM, t) = match tM with
      | Lam (y, tN)       -> Lam (y, cnorm (tN, t))

      | Clo (tN, s)       -> Clo(cnorm (tN, t), cnormSub(s, t))  
      | MClo (tN, t')     -> cnorm (tN, Ctx.comp t' t)

      | Root (BVar i, tS) -> Root(BVar i, cnormSpine (tS, t))

      (* Meta-variables *)

      | Root (MVar (Offset k, r), tS)
        -> begin match Ctx.mvarMSub k t with
            | MObj (_phat,tM)   -> Whnf.reduce (tM, r) (cnormSpine (tS, t))
            | Id i -> Root (MVar(Offset i, cnormSub (r,t)), cnormSpine (tS, t))
          end

      (* Ignore other cases for destructive (free) meta-variables *)

      (* Parameter variables *)
      | Root (PVar (Offset k, r), tS)
        -> begin match Ctx.mvarMSub k t with
            | PObj (_phat, i) -> 
		begin match LF.bvarSub i r with
		  | Head (h)  -> Root(h, cnormSpine (tS, t))
		  | Obj (tM)   -> 
		      Whnf.reduce (tM, LF.id) (cnormSpine (tS, t))
		end
            | Id i -> Root (PVar(Offset i, r), cnormSpine (tS, t))
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
        -> begin match Ctx.mvarMSub j t with
            | PObj (_phat, i)   -> 
              (*  i <= phat *) 
                begin match LF.bvarSub i s with
                  | Head (BVar j)     -> 
                      Root(Proj (BVar j, k), cnormSpine (tS, t))
                  | Head (PVar (p,r'))-> 
                      Root(Proj (PVar (p, LF.comp (cnormSub (r',t)) s), k), 
                           cnormSpine (tS, t))
                  (* other cases should not happen ; 
                     term would be ill-typed *)
                end
            | Id i  -> Root (Proj (PVar (Offset i, s), k), cnormSpine (tS, t))
           end

      (* Ignore other cases for destructive (free) parameter-variables *)

    and cnormSpine (tS, t) = match tS with
      | Nil            -> Nil
      | App  (tN, tS)  -> App (cnorm (tN, t), cnormSpine (tS, t))
      | SClo (tS, s)   -> SClo(cnormSpine (tS, t), cnormSub (s, t))
      | SMClo (tS, t') -> cnormSpine (tS, Ctx.comp t t')


    and cnormSub (s, t) = match s with 
      | Shift _         -> s
      | Dot (ft, s')     -> Dot (cnormFront (ft, t), cnormSub (s', t))
      (* substitution variables ignored for how -bp *)


    and cnormFront (ft, t) = match ft with
      | Head (BVar _ )            -> ft
      | Head (Const _ )           -> ft
      | Head (PVar (Offset i, r)) ->
          begin match Ctx.mvarMSub i t with
            | Id n                -> Head(PVar(Offset n, cnormSub (r,t)))
            | PObj (_phat, j)    ->  LF.bvarSub j (cnormSub (r,t))
  	    (* other case MObj _ cannot happen *)
          end

      | Head (MVar (Offset i, r)) -> 
          begin match Ctx.mvarMSub i t with
            | Id n                -> Head (BVar n)
            | MObj (_phat, tM)    -> Obj(Whnf.norm (tM, cnormSub (r,t)))
          end

      | Head (Proj (BVar _, _))    -> ft
      | Head (Proj (PVar (Offset i, r), k)) -> 
          begin match Ctx.mvarMSub i t with
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

      | TMClo (tA, t') 
        -> cnormTyp (tA, Ctx.comp t' t)

    and cnormTypRec (recA, t) = match recA with
      | []          -> []
      | tA :: recA' -> cnormTyp (tA, t) :: cnormTypRec (recA', t)

    and cnormDecl (decl, t) = match decl with
       TypDecl (x, tA) -> TypDecl (x, cnormTyp (tA, t))

    and cnormDCtx = assert false
(* (Null, t) = Null 
      (* | cnormDCtx (CtxVar psi, t) = 
          lookup in t *)
       | cnormDCtx (DDec(cPsi, decl), t) 
         DDec(cnormDctx(cPsi, t), cnormDecl(decl, t))
*)
(*       | cnormDCtx (SigmaDec (cPsi, sdecl), t) = *)

(*
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


let rec cwhnfCTyp ttT = match (tT, t) with 
  | (TypBox (tA, cPsi), t)     
    -> (TypBox(cnorm(tA, t), cnormDCtx(cPsi, t)), Ctx.id) 

  | (TypSBox (cPsi, cPsi'), t) 
    -> (TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), Ctx.id)

  | (TypArr (tT1, tT2), t)      -> ttT

  | (TypCtxPi ((psi,W), tT), t) -> ttT

  | (TypPiBox (_, _) , t)       -> ttT

  | (TypClo (tT, t'), t)        -> (tT, Ctx.comp t' t)



(* ----------------------------------------------------------- *)
(* Converstion: Convertibility modulo alpha for 
   computation-level types
*)


(* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)

let rec convCTyp ttT1 ttT2 = convCTyp' (cwhnfTyp ttT1) (cwhnfTyp ttT2)

and convCTyp' ttT1 ttT2 = match (ttT1, ttT2) with 
  | ((TypBox (tA1, cPsi1), t1), (TypBox (tA2, cPsi2), t2)) (* t1 = t2 = mid *)
    -> Whnf.convDCtx cPsi1 cPsi2
      &&
	Whnf.conv (tA1, LF.id) (tA2, LF.id)

  | ((TypSBox (cPsi1, cPsi2), t), (TypSBox (cPsi1', cPs2'), t'))  (* t1 = t2 = mid *)
    -> Whnf.convDCtx cPsi1 cPsi1'
      &&
	Whnf.convDCtx cPsi2 cPsi2'

  | ((TypArr (tT1, tT2), t), (TypArr (tT1', tT2'), t')) 
    -> convCTyp (tT1, t) (tT1', t') 
      &&
	convCTyp (tT2, t) (tT2', t')

  | ((TypCtxPi ((psi, W), tT1), t) , (TypCtxPi ((psi', W'), tT1'), t'))
    -> (* convSchema (W, W')   ? *)
      convCTyp (tT1, Ctx.dot1 t) (tT1', Ctx.dot1 t')

  | ((TypPiBox (MDecl(_, tA, cPsi), tT), t), (TypPiBox (MDecl(_, tA', cPsi'), tT'), t'))
    -> Whnf.conv (cnorm (tA, t), LF.id) (cnorm (tA', t'), LF.id)
      &&
       Whnf.convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
      && 
	ConvCTyp (tT, Ctx.dot1 t) (tT', Ctx.dot1 t')

  (* For now we omit PDecl, SDecl - bp *)
*)
