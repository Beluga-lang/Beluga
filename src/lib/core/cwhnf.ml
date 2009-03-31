(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)
(**
   @author Brigitte Pientka
*)

(* Contextual Weak Head Normalization,
   Contextual Normalization, and alpha-conversion 
   for contextual substitutions *)

open Context
open Syntax.Int

module S = Substitution.LF

exception Error of string 

exception Fmvar_not_found
exception FreeMVar of LF.head
exception FreeCtxVar of Id.name
exception NonInvertible 

let rec constraints_solved cnstr = match cnstr with
  | [] -> true
  | ({contents = LF.Queued} :: cnstrs) -> 
      constraints_solved cnstrs 
  | ({contents = LF.Eqn (_cD, _phat, tM, tN)} :: cnstrs) -> 
      if Whnf.conv (tM, S.id) (tN, S.id) then 
        constraints_solved cnstrs
      else         
         false 
 | ({contents = LF.Eqh (_cD, _phat, h1, h2)} :: cnstrs) -> 
      if Whnf.convHead (h1, S.id) (h2, S.id) then 
        constraints_solved cnstrs
      else false 


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

let id = Comp.MShift 0

(* mshift t n = t' 

   Invariant: 

   If cD |- t <= cD' 
   then  cD, ... |- t' <= cD', ...   where ... has length n
                                     and t' = t^n
*)
let rec mshift t n = match t with
  | Comp.MShift k   ->  Comp.MShift (k+n)

  | Comp.MDot(ft, t') -> Comp.MDot(mshiftMFt ft n, mshift t' n)


and mshiftMFt ft n = match ft with 
  | Comp.MObj(phat, tM) -> 
      Comp.MObj(phat, mshiftTerm tM n)   

  | Comp.PObj(phat, LF.PVar(LF.Offset k, s)) -> 
     Comp.PObj(phat, LF.PVar(LF.Offset (k+n), s))

  | Comp.PObj(_phat, LF.BVar _k) -> ft

  | Comp.MV (u_offset) -> Comp.MV (u_offset + n)


and mshiftTerm tM n = match tM with
  | LF.Lam(loc, x, tN)  -> LF.Lam(loc, x, mshiftTerm tN n)
  | LF.Tuple(loc, tuple)  -> LF.Tuple(loc, mshiftTuple tuple n)
  | LF.Root(loc, h, tS) -> LF.Root(loc, mshiftHead h n, mshiftSpine tS n)
  | LF.Clo(tM, s)  -> LF.Clo(mshiftTerm tM n, mshiftSub s n)

and mshiftTuple tuple n = match tuple with
  | LF.Last tM -> LF.Last (mshiftTerm tM n)
  | LF.Cons (tM, rest) ->
      let tMshifted = mshiftTerm tM n in
      let restShifted = mshiftTuple rest n in
        LF.Cons (tMshifted, restShifted)

and mshiftHead h n = match h with
  | LF.MVar(LF.Offset k, s) -> LF.MVar(LF.Offset (k+n), mshiftSub s n)
  | LF.PVar(LF.Offset k, s) -> LF.PVar(LF.Offset (k+n), mshiftSub s n)
  | LF.Proj(LF.PVar(LF.Offset k, s), j) -> LF.Proj(LF.PVar(LF.Offset (k+n), mshiftSub s n), j)
  | LF.AnnH(h, tA) -> LF.AnnH(mshiftHead h n, mshiftTyp tA n)
  | _ -> h

and mshiftSpine tS n = match tS with 
  | LF.Nil -> LF.Nil
  | LF.App(tM, tS) -> LF.App(mshiftTerm tM n, mshiftSpine tS n)
  | LF.SClo(tS, s) -> LF.SClo(mshiftSpine tS n, mshiftSub s n)

and mshiftTyp tA n = match tA with
  | LF.Atom (loc, a, tS) -> LF.Atom (loc, a, mshiftSpine tS n)
  | LF.PiTyp((LF.TypDecl(x, tA), dep), tB) -> LF.PiTyp((LF.TypDecl(x, mshiftTyp tA n), dep), mshiftTyp tB n)
  | LF.TClo(tA, s) -> LF.TClo(mshiftTyp tA n, mshiftSub s n)
  | LF.Sigma typRec -> LF.Sigma (mshiftTypRec typRec n)

and mshiftTypRec typRec n = match typRec with
  | LF.SigmaLast tA -> LF.SigmaLast (mshiftTyp tA n)
  | LF.SigmaElem (x, tA, rest) ->
      let tA = mshiftTyp tA n in
      let rest = mshiftTypRec rest n in
        LF.SigmaElem (x, tA, rest)

and mshiftSub s n = match s with
  | LF.Shift (_,_k) -> s
  | LF.SVar(LF.Offset k, s) -> LF.SVar(LF.Offset (k+n), mshiftSub s n)
  | LF.Dot(ft, s) -> LF.Dot (mshiftFt ft n, mshiftSub s n)

and mshiftFt ft n = match ft with
  | LF.Head h -> LF.Head (mshiftHead h n)
  | LF.Obj tM -> LF.Obj (mshiftTerm tM n)
  | LF.Undef  -> LF.Undef
  
and mshiftDCtx cPsi k = match cPsi with
  | LF.Null -> LF.Null
  | LF.CtxVar _ -> cPsi
  | LF.DDec(cPsi', LF.TypDecl(x, tA)) -> 
      LF.DDec(mshiftDCtx cPsi' k, LF.TypDecl(x, mshiftTyp tA k))



(* mvar_dot1 psihat t = t'
   Invariant:

   If  cO ;  cD |- t : D'

   then t' = u. (mshift t 1)  
       and  for all A s.t.  D' ; Psi |- A : type

     D, u::[|t|](A[Psi]) |- t' : D', A[Psi]


 *)
  and mvar_dot1 t = 
    Comp.MDot (Comp.MV 1, mshift t 1)

  and pvar_dot1 t = 
    Comp.MDot (Comp.MV 1, mshift t 1)



  and mvar_dot t cD = match cD with
    | LF.Empty -> t
    | LF.Dec(cD', _ ) -> 
        mvar_dot (mvar_dot1 t) cD'


(* comp t1 t2 = t'

   Invariant:

   If   D'  |- t1 : D 
   and  D'' |- t2 : D'
   then t'  =  t1 o t2
   and  D'' |- t1 o t2 : D

   Note: Eagerly composes the modal substitutions t1 and t2.

*)

let rec mcomp t1 t2 = match (t1, t2) with
  | (Comp.MShift 0, t)         -> t
  | (t, Comp.MShift 0)         -> t
  | (Comp.MShift n, Comp.MShift k) -> (Comp.MShift (n+k))
  |  (Comp.MShift n, Comp.MDot (_mft, t))  -> 
      mcomp (Comp.MShift (n-1)) t
  | (Comp.MDot (mft, t), t') -> 
      Comp.MDot (mfrontMSub mft t', mcomp t t')


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

        | Comp.MV k'  -> Comp.PObj (_phat, LF.PVar (LF.Offset k', s))
          (* other cases impossible *)
      end
  | Comp.PObj (_phat, LF.BVar _k)  -> ft

  | Comp.MV k -> 
      begin match applyMSub k t with  (* DOUBLE CHECK - bp Wed Jan  7 13:47:43 2009 -bp *)
        | Comp.PObj(phat, p) ->  Comp.PObj(phat, p)          
        | Comp.MObj(phat, tM) ->  Comp.MObj(phat, tM)          
        | Comp.MV k'         -> Comp.MV k'
        (* other cases impossible *)
      end

(*  | Comp.MV u -> 
      begin match applyMSub u t with
        | Comp.MObj(phat, tM) ->  Comp.MObj(phat, tM)          
        | Comp.MV u'          ->  Comp.MV u'
        (* other cases impossible *)
      end
*)

(* applyMSub n t = MFt'
     
   Invariant: 

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ft_n      if  t = Ft_1 .. Ft_n .. ^0
     and D ; [|t|]Psi |- Ft' <= [|t|]A
  *)

and applyMSub n t = 
    begin match (n, t) with
  | (1, Comp.MDot (ft, _t)) -> ft
  | (n, Comp.MDot (_ft, t)) -> applyMSub (n - 1) t
  | (n, Comp.MShift k)       -> Comp.MV (k + n)
    end 



(* invert t = t'

   Invariant:

   If   D  |- t  <= D'    (and s !!!patsub!!!)
   then D' |- t' <= D
   s.t. t o t' = id    (mcomp t' t = id)
*)
and invert s =
  let rec lookup n s p = match s with
    | Comp.MShift _                 -> None
    | Comp.MDot (Comp.Undef, t')    -> lookup (n + 1) t' p

    | Comp.MDot (Comp.MV k, t') ->
        if k = p then Some n
        else lookup (n + 1) t' p 

    | Comp.MDot (Comp.MObj(_phat, LF.Root(_, LF.MVar (LF.Offset k, LF.Shift (_,0)), LF.Nil)), t') -> 
        if k = p then
          Some n
        else lookup (n + 1) t' p 

    | Comp.MDot (Comp.PObj (_phat, LF.PVar (LF.Offset k, LF.Shift (_, 0))), t') -> 
        if k = p then
          Some n
        else lookup (n + 1) t' p 
         
          
  in

  let rec invert'' p ti = match p with
      | 0 -> ti
      | p ->
          let front = match lookup 1 s p with
            | Some k -> Comp.MV k (* or Comp.MObj (phat, Root(MVar(Offset k), id), Nil)  *)
            | None   -> Comp.Undef
          in
            invert'' (p - 1) (Comp.MDot (front, ti)) in

    let rec invert' n t = match t with
      | Comp.MShift p     -> invert'' p (Comp.MShift n)
      | Comp.MDot (_, t') -> invert' (n + 1) t'

    in
      invert' 0 s



(* ------------------------------------------------------------ *)
(* Normalization = applying simultaneous modal substitution   

     Applying the modal substitution t to an normal LF term tM 
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

     If tM is in cnormal form, then [|t|]tM is also in cnormal form. 

  *)
and what_head = function
  | LF.BVar _ -> "BVar"
  | LF.Const _ -> "Const"
  | LF.MVar _ -> "MVar"
  | LF.PVar _ -> "PVar"
  | LF.AnnH _ -> "AnnH"
  | LF.Proj (head, k) -> "Proj " ^ what_head head ^ "." ^ string_of_int k
  | LF.FVar _ -> "FVar"
  | LF.FMVar _ -> "FMVar"
  | LF.FPVar _ -> "FPVar"

and cnorm (tM, t) = match tM with
    | LF.Lam (loc, y, tN)   -> LF.Lam (loc, y, cnorm (tN, t))

    | LF.Tuple (loc, tuple) -> LF.Tuple (loc, cnormTuple (tuple, t))

    | LF.Clo (tN, s)        -> LF.Clo(cnorm (tN, t), cnormSub(s, t))  

    | LF.Root (loc, head, tS) ->

        begin match head with
          | LF.BVar i -> LF.Root(loc, LF.BVar i, cnormSpine (tS, t))

          (* Meta-variables *)

          | LF.MVar (LF.Offset k, r) -> 
              begin match applyMSub k t with
                | Comp.MV  k'            -> 
                    LF.Root (loc, LF.MVar (LF.Offset k', cnormSub (r, t)), cnormSpine (tS, t)) 
                      
                | Comp.MObj (_phat,tM)   -> 
                    LF.Clo(Whnf.whnfRedex ((tM, cnormSub (r, t)), (cnormSpine (tS, t), S.id)))  
                      
              (* other cases impossible *)
              end 

          | LF.FMVar (u, r) ->
              raise (FreeMVar (LF.FMVar (u,cnormSub (r, t))))

          | LF.MVar (LF.Inst ({contents = Some _tM}, _cPsi, _tA, _cnstr), _r) -> 
              (* We could normalize [r]tM *)
              let tM' = Whnf.norm (tM, S.id) in 
                cnorm (tM', t)
                  
          (*        LF.Root (LF.MVar(LF.Inst ({contents = Some (cnorm (tM, t))}, cPsi, tA, cnstr), 
                    cnormSub (r, t)), cnormSpine (tS, t)) 
                    
          *)
          (* CHECK HERE IF THERE ARE ANY LEFT OVER CONSTRAINTS! *)
          | LF.MVar (LF.Inst ({contents = None}, _cPsi, _tA, cnstr) as u , r) ->
              if constraints_solved (!cnstr) then 
                (* raise (Error "Encountered Un-Instantiated MVar with reference ?\n") *)
                LF.Root (loc, LF.MVar(u, cnormSub (r, t)), cnormSpine (tS, t)) 
              else 
                raise (Error "uninstiated meta-variables with unresolved constraints")
                  
                  
          | LF.PVar (LF.PInst ({contents = None}, _cPsi, _tA, _ ) as p, r) -> 
              LF.Root (loc, LF.PVar(p, cnormSub (r, t)), cnormSpine (tS, t)) 

          | LF.PVar (LF.PInst ({contents = Some (LF.BVar x)}, _cPsi, _tA, _ ) , r) ->
              begin match S.bvarSub x (cnormSub (r,t)) with
                | LF.Head h  ->
                    LF.Root (loc, h, cnormSpine (tS, t))
                | LF.Obj tM  -> LF.Clo (Whnf.whnfRedex ((tM, S.id), (cnormSpine (tS, t), S.id)))
              end


          | LF.PVar (LF.PInst ({contents = Some (LF.PVar (q,s))}, _cPsi, _tA, _ ) , r) ->
              LF.Root (loc, LF.PVar (q, (S.comp s (cnormSub (r,t)))), cnormSpine (tS, t))           

        (* Parameter variables *)
          | LF.PVar (LF.Offset k, r)

        (* cD' ; cPsi' |- r <= cPsi1 
           cD          |- t <= cD'
 
           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r

         *)
            -> begin match applyMSub k t with
              | Comp.MV  k'            -> LF.Root (loc, LF.PVar (LF.Offset k', cnormSub (r, t)), cnormSpine (tS, t))
              | Comp.PObj (_phat, LF.BVar i) -> 
                  begin match S.bvarSub i (cnormSub (r,t)) with
                    | LF.Head h  -> LF.Root(loc, h, cnormSpine (tS, t))
                    | LF.Obj tM  -> LF.Clo (Whnf.whnfRedex ((tM, S.id), (cnormSpine (tS, t), S.id)))
                  end
              | Comp.PObj (_phat, LF.PVar(LF.Offset i, r')) -> 
                  LF.Root (loc, LF.PVar(LF.Offset i, S.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
                    
              | Comp.PObj (_phat, LF.PVar(LF.PInst ({contents = None}, _, _, _ ) as p, r')) -> 
                  LF.Root (loc, LF.PVar(p, S.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
                    
                    
              | Comp.PObj (_phat, LF.PVar(LF.PInst ({contents = Some (LF.PVar (x, rx))}, _, _, _ ), r')) -> 
                  LF.Root (loc, LF.PVar (x, S.comp rx (S.comp r' (cnormSub (r,t)))), cnormSpine (tS, t))
                    
              | Comp.PObj (_phat, LF.PVar(LF.PInst ({contents = Some (LF.BVar x)}, _, _, _ ), r')) -> 
                  begin match S.bvarSub x (cnormSub (r',t)) with
                    | LF.Head (LF.BVar i)  ->  
                        begin match S.bvarSub i (cnormSub (r,t)) with
                          | LF.Head h  -> LF.Root(loc, h, cnormSpine (tS, t))
                          | LF.Obj tM  -> LF.Clo (Whnf.whnfRedex ((tM, S.id), (cnormSpine (tS, t), S.id)))
                        end
                    | LF.Head (LF.PVar(q, s)) -> LF.Root(loc, LF.PVar(q,  S.comp s (cnormSub (r,t))), cnormSpine (tS, t))
                        (* Other case MObj _ should not happen -- ill-typed *)
                  end
                    
            end

          | LF.FPVar (p, r) ->
              raise (FreeMVar (LF.FPVar (p, cnormSub (r, t))))

          | LF.Proj (LF.FPVar (_p, _r), _tupleIndex) as head ->
              LF.Root (loc, head, cnormSpine(tS, t))
(*              raise (FreeMVar (LF.FPVar (p, cnormSub (r, t)))) *)

          (* Ignore other cases for destructive (free) parameter variables *)
                
          (* Constants *)
          | LF.Const c
            -> LF.Root (loc, LF.Const c, cnormSpine (tS, t))
              
          (* Free Variables *)
          | LF.FVar x
            -> (Printf.printf "Encountered a free variable!?\n" ; 
                LF.Root (loc, LF.FVar x, cnormSpine (tS, t)))

          (* Projections *)
          | LF.Proj (LF.BVar i, k)
            -> LF.Root (loc, LF.Proj (LF.BVar i, k), cnormSpine (tS, t))

          | LF.Proj (LF.PVar (LF.Offset j, s), tupleIndex)
              (* cD' ; cPsi' |- s <= cPsi1 *)
              (* cD          |- t <= cD'   *)         
            -> begin
              let wrap head = LF.Proj (head, tupleIndex) in
              let newHead =
                match applyMSub j t with
                  | Comp.PObj (_phat, LF.BVar i)   -> 
                      (*  i <= phat *) 
                      begin match S.bvarSub i (cnormSub (s,t)) with
                        | LF.Head (LF.BVar j)      ->  LF.BVar j
                        | LF.Head (LF.PVar (p,r')) ->  LF.PVar (p, r')
                            (* other cases should not happen; 
                               term would be ill-typed *)
                      end
                  | Comp.PObj(_phat, LF.Proj (LF.PVar (LF.Offset i, s'),  otherTupleIndex)) -> 
                      LF.Proj (LF.PVar (LF.Offset i, S.comp s' (cnormSub (s,t))),  otherTupleIndex)
                        
                  | Comp.PObj(_phat, LF.PVar (LF.Offset i, s')) ->
                      wrap (LF.PVar (LF.Offset i, S.comp s' (cnormSub (s,t))))
                        
                  | Comp.PObj (_phat, LF.PVar(LF.PInst ({contents= None}, _, _, _) as p, r')) -> 
                      wrap (LF.PVar (p, S.comp r' (cnormSub (s,t))))
                        
                  | Comp.PObj(_phat, LF.PVar (LF.PInst _, _s')) ->
                      (print_string "cnorm ...PVar PInst {contents= Some ...}\n"; exit 2)
                  | Comp.PObj(_phat, LF.PVar (_, _s')) ->
                      (print_string "cnorm ...PVar ???\n"; exit 2)

                  | Comp.MV  k'            -> wrap (LF.PVar (LF.Offset k', cnormSub (s, t)))
                      
                  | Comp.MObj _ ->             (print_string "mobj\n"; exit 2)
                  | Comp.PObj(_phat, LF.Proj (LF.FPVar (_, _s'), _k)) ->  (print_string "PObj FPVar\n"; exit 2)
                  | Comp.PObj(_phat, LF.Proj (LF.PVar (_, _S'), _k)) ->   (print_string "PObj PVar\n"; exit 2)
                  | Comp.PObj(_phat, LF.Proj _) ->   (print_string "PObj other proj\n"; exit 2)
                  | Comp.PObj(_phat, head) -> 
                        (print_string ("QQQQ " ^ what_head head ^  "\n"); exit 2)
                  | Comp.Undef  ->             (print_string "Undef\n"; exit 2)
              in
                LF.Root (loc, newHead, cnormSpine (tS, t))
            end
          | head -> (print_string ("cnorm fallthru " ^ what_head head ^  "\n"); exit 2)
        end
      (* Ignore other cases for destructive (free) parameter-variables *)
          
  and cnormSpine (tS, t) = match tS with
    | LF.Nil            -> LF.Nil
    | LF.App  (tN, tS)  -> LF.App (cnorm (tN, t), cnormSpine (tS, t))
    | LF.SClo (tS, s)   -> LF.SClo(cnormSpine (tS, t), cnormSub (s, t))

  and cnormTuple (tuple, t) = match tuple with
    | LF.Last tM -> LF.Last (cnorm (tM, t))
    | LF.Cons (tM, rest) ->
        let tM' = cnorm (tM, t) in
        let rest' = cnormTuple (rest, t) in
          LF.Cons (tM', rest')

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
          | Comp.MV k -> LF.Head(LF.PVar (LF.Offset k, cnormSub (r,t)))
              (* other case MObj _ cannot happen *)
        end

    | LF.Head (LF.MVar (LF.Offset i, r)) -> 
        begin match applyMSub i t with
          | Comp.MObj (_phat, tM)    -> LF.Obj(LF.Clo (tM, cnormSub (r,t)))
          | Comp.MV k -> LF.Head(LF.MVar (LF.Offset k, cnormSub (r,t))) 
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

    | LF.Obj (tM) -> LF.Obj(cnorm (tM, t))
          
  (* cnormType (tA, t) = tA'

     If cD' ; cPsi  |- tA <= type
     cD |- t <= cD'
     then
     tA' = [|t|]tA  and cPsi' = [|t|]cPsi
     cD' ; cPsi' |- tA' <= type   
  *)
  and cnormTyp (tA, t) = match tA with
    | LF.Atom (loc, a, tS) ->
        LF.Atom (loc, a, cnormSpine (tS, t))

    | LF.PiTyp ((LF.TypDecl (_x, _tA) as decl, dep), tB)
      -> LF.PiTyp ((cnormDecl (decl, t), dep), cnormTyp (tB, t))

    | LF.TClo (tA, s)
      -> LF.TClo(cnormTyp (tA,t), cnormSub (s,t))

    | LF.Sigma recA
      -> LF.Sigma(cnormTypRec (recA, t))

  and cnormTypRec (typRec, t) = match typRec with
    |  LF.SigmaLast lastA -> LF.SigmaLast(cnormTyp (lastA, t))
    |  LF.SigmaElem (x, tA, recA') ->
         let tA = cnormTyp (tA, t) in
           LF.SigmaElem (x, tA, cnormTypRec (recA', t))

  and cnormDecl (decl, t) = match decl with
      LF.TypDecl (x, tA) -> 
          LF.TypDecl (x, cnormTyp (tA, t))



let rec cnormMSub t = match t with
  | Comp.MShift _n -> t
  | Comp.MDot (Comp.MObj(phat, tM), t) -> 
      Comp.MDot (Comp.MObj (phat, Whnf.norm (tM, S.id)), cnormMSub t) 

  | Comp.MDot (Comp.PObj(phat, LF.PVar(LF.Offset k, s)), t) -> 
      Comp.MDot (Comp.PObj(phat, LF.PVar(LF.Offset k, s)), cnormMSub t)


  | Comp.MDot (Comp.PObj(phat, LF.BVar k), t) -> 
      Comp.MDot (Comp.PObj(phat, LF.BVar k), cnormMSub t)

  | Comp.MDot (Comp.PObj(phat, LF.PVar(LF.PInst ({contents = None}, _cPsi, _tA, _ ) as p,  s)), t) -> 
      Comp.MDot (Comp.PObj(phat, LF.PVar(p, s)), cnormMSub t)

  | Comp.MDot(Comp.PObj(phat, LF.PVar (LF.PInst ({contents = Some (LF.BVar x)}, _cPsi, _tA, _ ) , r)), t) -> 
        let t' = cnormMSub t in 
        begin match S.bvarSub x r with
	  | LF.Head h  ->  
             Comp.MDot (Comp.PObj(phat, h), t')
	  | LF.Obj tM  -> 
              Comp.MDot (Comp.MObj(phat,  Whnf.norm (tM, S.id)), t')
	end

  | Comp.MDot(Comp.PObj(phat, LF.PVar (LF.PInst ({contents = Some (LF.PVar (q,s))}, _cPsi, _tA, _ ) , r)), t) -> 
      cnormMSub (Comp.MDot (Comp.PObj (phat, LF.PVar(q, S.comp s r)), t))

  | Comp.MDot (Comp.MV u, t) -> Comp.MDot (Comp.MV u, cnormMSub t)


  
(* ************************************************* *)
(* cnormDCtx (cPsi, t) = cPsi 

   If cO ; cD  |- cPsi lf-dctx
      cO ; cD' |-  t_d <= cO ; cD
   then 
      cO  ; cD' |- [|t|]cPsi 

*)
let rec cnormDCtx (cPsi, t) = match cPsi with
    | LF.Null       ->  LF.Null 

    | LF.CtxVar (LF.CtxOffset psi) -> 
        LF.CtxVar (LF.CtxOffset psi) 

    | LF.CtxVar (LF.CtxName psi) -> 
        raise (FreeCtxVar psi)

    | LF.DDec(cPsi, decl) ->  
        LF.DDec(cnormDCtx(cPsi, t), cnormDecl(decl, t))



(* ************************************************* *)
(* Context substitutions                             *)
(* ************************************************* *)

let rec csub_typ cPsi k tA = match tA with 
  | LF.Atom (loc, a, tS) -> 
      LF.Atom (loc, a, csub_spine cPsi k tS)

  | LF.PiTyp ((LF.TypDecl (x, tA), dep), tB) -> 
      LF.PiTyp ((LF.TypDecl (x, csub_typ cPsi k tA), dep),
                csub_typ cPsi k tB)

  | LF.TClo (tA, s) -> 
     LF.TClo (csub_typ cPsi k tA, csub_sub cPsi k s)

and csub_norm cPsi k tM = match tM with
  | LF.Lam (loc, x, tN)  -> LF.Lam (loc, x, csub_norm cPsi k tN)

  | LF.Root (loc, h, tS) ->
      LF.Root (loc, csub_head cPsi k h, csub_spine cPsi k tS)

  | LF.Clo (tN, s) -> 
      LF.Clo (csub_norm cPsi k tN, csub_sub cPsi k s)

and csub_head cPsi k h = match h with
  | LF.MVar (u, s) -> LF.MVar(u, csub_sub cPsi k s)
  | LF.PVar (p, s) -> LF.PVar(p, csub_sub cPsi k s)
  | _              -> h

and csub_spine cPsi k tS = match tS with
  | LF.Nil -> LF.Nil
  | LF.App(tM, tS) -> 
      LF.App (csub_norm cPsi k tM, csub_spine cPsi k tS)
  | LF.SClo (tS, s) -> 
      LF.SClo (csub_spine cPsi k tS, csub_sub cPsi k s)

(* csub_sub cPsi phi s = s' 

*)
and csub_sub cPsi phi (* k *) s = match s with
  | LF.Shift (LF.NoCtxShift, _k) -> s

  | LF.Shift (LF.CtxShift (LF.CtxOffset psi), k) -> 
      if psi = phi then 
        begin match Context.dctxToHat cPsi with
          | (Some ctx_v, d) -> 
              LF.Shift (LF.CtxShift ctx_v, k + d)

          | (None, d) ->
              LF.Shift (LF.NoCtxShift, k + d)
        end

      else 
        LF.Shift (LF.CtxShift (LF.CtxOffset psi), k)

  | LF.Shift (LF.NegCtxShift (LF.CtxOffset psi), k) -> 
      if psi = phi then 
        let rec undef_sub d s = 
          if d = 0 then s 
          else undef_sub (d-1) (LF.Dot(LF.Undef, s)) 
        in 
          begin match Context.dctxToHat cPsi with
          | (Some ctx_v, d) -> 
          (* Psi |- s : psi  and psi not in Psi and |Psi| = k 
           * Psi |- Shift(negCtxShift(phi), k) . Undef ....  : phi, Phi 
           *)                      
              undef_sub d (LF.Shift (LF.NegCtxShift ctx_v, k))

          | (None, d) -> undef_sub d (LF.Shift (LF.NoCtxShift, k))

          end
              
      else 

        LF.Shift(LF.NegCtxShift (LF.CtxOffset psi), k)

  | LF.Dot (ft, s) -> 
      LF.Dot (csub_front cPsi phi ft, csub_sub cPsi phi s)

and csub_front cPsi k ft = match ft with
  | LF.Head h -> LF.Head (csub_head cPsi k h)
  | LF.Obj tN -> LF.Obj (csub_norm cPsi k tN)
  | LF.Undef  -> LF.Undef
 
let rec csub_ctyp cPsi k tau = match tau with
  | Comp.TypBox (tA, cPhi) -> 
      Comp.TypBox (csub_typ cPsi k tA, csub_dctx cPsi k cPhi)

  | Comp.TypArr (tau1, tau2) -> 
      Comp.TypArr (csub_ctyp cPsi k tau1, csub_ctyp cPsi k tau2)

  | Comp.TypCross (tau1, tau2) -> 
      Comp.TypCross (csub_ctyp cPsi k tau1, csub_ctyp cPsi k tau2)

  | Comp.TypCtxPi (psi_decl, tau) -> 
      Comp.TypCtxPi (psi_decl, csub_ctyp cPsi (k + 1) tau)

  | Comp.TypPiBox ((LF.MDecl (u, tA, cPhi), dep), tau) -> 
      Comp.TypPiBox ((LF.MDecl (u, tA, csub_dctx cPsi k cPhi), dep),
                     csub_ctyp (cnormDCtx (cPsi, Comp.MShift 1)) k tau)

  | Comp.TypClo (tau, theta) -> 
      Comp.TypClo (csub_ctyp cPsi k tau, csub_msub cPsi k theta)

and csub_psihat cPsi k (ctxvar, offset) = match ctxvar with 
  | None -> (None, offset)
  | Some (LF.CtxOffset psi) -> 
      if k = psi then 
        let (psivar, psi_offset) = dctxToHat cPsi in 
          (psivar, (psi_offset + offset))
       else (ctxvar, offset)



and csub_dctx cPsi k cPhi = 
  let rec csub_dctx' cPhi = match cPhi with 
    | LF.Null -> (LF.Null, false)
    | LF.CtxVar (LF.CtxOffset offset) -> if k = offset then 
        (cPsi, true) else (cPhi, false)

    | LF.DDec (cPhi, LF.TypDecl (x, tA)) ->   
        let (cPhi', b) = csub_dctx' cPhi in 
        if b then       
          (* cPhi |- tA type     phi', cPhi' |- s : phi, cPhi *)
          let tA' = csub_typ cPsi k tA in 
          (LF.DDec (cPhi', LF.TypDecl(x, tA')), b)
        else 
          (LF.DDec(cPhi', LF.TypDecl (x, tA)), b)
  in 
  let(cPhi', _ ) = csub_dctx' cPhi in 
    cPhi'

and csub_msub cPsi k theta = match theta with 
  | Comp.MShift n -> Comp.MShift n
  | Comp.MDot (Comp.MObj (phihat , tM), theta) -> 
      Comp.MDot (Comp.MObj (csub_psihat cPsi k phihat , tM), 
                 csub_msub cPsi k theta)

  | Comp.MDot (Comp.PObj (phihat , h), theta) -> 
      Comp.MDot (Comp.PObj (csub_psihat cPsi k phihat , h), 
                 csub_msub cPsi k theta)

  | Comp.MDot (ft, theta) -> 
      Comp.MDot (ft, csub_msub cPsi k theta)
      

(* ************************************************* *)

(*
*)
let rec mctxMDec cD' k = 
  let rec lookup cD k' = match (cD, k') with
    | (LF.Dec (_cD, LF.MDecl(_u, tA, cPsi)), 1)
      -> (mshiftTyp tA k, mshiftDCtx cPsi k)
        
    | (LF.Dec (_cD, LF.PDecl _), 1)
      -> raise (Error "Expected meta-variable; Found parameter variable")
      
    | (LF.Dec (cD, _), k')
      -> lookup cD (k' - 1)

    | (_ , _ ) -> raise (Error ("Meta-variable out of bounds – looking for " ^ (string_of_int k) ^ "in context n"))
  in 
    lookup cD' k


(*
*)
let rec mctxPDec cD k = 
  let rec lookup cD k' = match (cD, k') with
    | (LF.Dec (_cD, LF.PDecl (_u, tA, cPsi)),  1)
      -> (mshiftTyp tA k, mshiftDCtx cPsi k)
        
    | (LF.Dec (_cD, LF.MDecl _),  1)
      -> raise (Error "Expected parameter variable, but found meta-variable")

    | (LF.Dec (cD, _),  k')
      -> lookup cD (k' - 1)

    | (_ , _ ) -> raise (Error "Parameter variable out of bounds")
  in 
    lookup cD k



let rec mctxMVarPos cD u = 
  let rec lookup cD k = match cD  with
    | LF.Dec (cD, LF.MDecl(v, tA, cPsi))    -> 
        if v = u then 
          (k, (mshiftTyp tA k, mshiftDCtx cPsi k))
        else 
          lookup cD (k+1)
              
    | LF.Dec (cD, _) -> lookup cD (k+1)

    | LF.Empty  -> raise Fmvar_not_found
  in 
    lookup cD 1



let rec mctxPVarPos cD p = 
  let rec lookup cD k = match cD  with
    | LF.Dec (cD, LF.PDecl(q, tA, cPsi))    -> 
        if p = q then 
          (k, (mshiftTyp tA k, mshiftDCtx cPsi k))
        else 
          lookup cD (k+1)
              
    | LF.Dec (cD, _) -> lookup cD (k+1)

    | LF.Empty  -> raise Fmvar_not_found
  in 
    lookup cD 1


  (* ***************************************** *)
  (* Contextual weak head normal form for 
     computation-level types                   *)
  (* ***************************************** *)

  let rec normCTyp tau = match tau with 
    | (Comp.TypBox (tA, cPsi))     
      -> Comp.TypBox(Whnf.normTyp(tA, S.id), Whnf.normDCtx cPsi)

    | (Comp.TypSBox (cPsi, cPsi')) 
      -> Comp.TypSBox(Whnf.normDCtx cPsi, Whnf.normDCtx cPsi')

    | (Comp.TypArr (tT1, tT2))   -> 
        Comp.TypArr (normCTyp tT1, normCTyp tT2)

    | (Comp.TypCross (tT1, tT2))   -> 
        Comp.TypCross (normCTyp tT1, normCTyp tT2)

    | (Comp.TypCtxPi (ctx_dec , tau))      -> 
         Comp.TypCtxPi (ctx_dec, normCTyp tau)

    | (Comp.TypPiBox ((LF.MDecl(u, tA, cPsi) , dep), tau))    -> 
        Comp.TypPiBox ((LF.MDecl (u, Whnf.normTyp (tA, S.id), Whnf.normDCtx cPsi), dep),
                       normCTyp tau)



  let rec cnormCTyp thetaT = 
    begin match thetaT with 
        | (Comp.TypBox (tA, cPsi), t) -> 
            let tA'   = Whnf.normTyp (cnormTyp(tA, t), S.id) in 
            let cPsi' = Whnf.normDCtx (cnormDCtx(cPsi, t)) in 
              Comp.TypBox(tA', cPsi')

        | (Comp.TypSBox (cPsi, cPsi'), t) -> 
            Comp.TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t))

        | (Comp.TypArr (tT1, tT2), t)   -> 
            Comp.TypArr (cnormCTyp (tT1, t), cnormCTyp (tT2, t))

        | (Comp.TypCross (tT1, tT2), t)   -> 
            Comp.TypCross (cnormCTyp (tT1, t), cnormCTyp (tT2, t))


        | (Comp.TypCtxPi (ctx_dec , tau), t)      -> 
              Comp.TypCtxPi (ctx_dec, cnormCTyp (tau, t))

        | (Comp.TypPiBox ((LF.MDecl(u, tA, cPsi) , dep), tau), t)    -> 
              Comp.TypPiBox ((LF.MDecl (u, cnormTyp (tA, t), cnormDCtx (cPsi, t)), dep), 
                             cnormCTyp (tau, mvar_dot1 t))

        | (Comp.TypClo (tT, t'), t)        -> 
              cnormCTyp (tT, mcomp t' t)
      end 


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
      -> 
        let tA' = Whnf.normTyp (cnormTyp(tA, t), S.id) in 
        let cPsi' = Whnf.normDCtx (cnormDCtx(cPsi, t)) in 

          (Comp.TypBox(tA', cPsi') , id)

          (* (Comp.TypBox(cnormTyp(tA, t), cnormDCtx(cPsi, t)), id)  *)

    | (Comp.TypSBox (cPsi, cPsi'), t)  
      -> (Comp.TypSBox(cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), id)

    | (Comp.TypArr (_tT1, _tT2), _t)   -> thetaT

    | (Comp.TypCross (_tT1, _tT2), _t)   -> thetaT

    | (Comp.TypCtxPi _, _)             -> thetaT

    | (Comp.TypPiBox (_, _) , _)       -> thetaT

    | (Comp.TypClo (tT, t'), t)        -> cwhnfCTyp (tT, mcomp t' t)


  (* WHNF and Normalization for computation-level terms to be added -bp *)

  (* cnormExp (e, t) = e' 
   
     If cO ; cD  ; cG   |- e <= tau
        cO ; cD' ; cG'  |- [|t|]e <= tau'  where [|t|]cG = cG' and [|t|]tau = tau'
        cO ; cD'        |- t <= cD
    
     then e' = [|t|]e and cO ; cD' ; cG' |- e' <= tau'

  *)

  let rec cnormExp (e, t) = match (e,t) with
    | (Comp.Syn (i), t) -> Comp.Syn (cnormExp' (i, t))

    | (Comp.Rec (f, e), t) -> Comp.Rec (f, cnormExp (e,t))

    | (Comp.Fun (x, e), t) -> Comp.Fun (x, cnormExp (e,t))

    | (Comp.CtxFun (psi, e) , t ) ->  Comp.CtxFun (psi, cnormExp (e, t))

    | (Comp.MLam (u, e), t) -> Comp.MLam (u, cnormExp (e, mvar_dot1  t))

    | (Comp.Pair (e1, e2), t) -> Comp.Pair (cnormExp (e1, t), cnormExp (e2, t))

    | (Comp.LetPair (i, (x, y, e)), t) -> 
        Comp.LetPair (cnormExp' (i, t), (x, y, cnormExp (e, t)))

    | (Comp.Box (psihat, tM), t) -> Comp.Box (psihat, Whnf.norm (cnorm (tM, t), S.id))

    | (Comp.Case (i, branches), t) -> 
        Comp.Case (cnormExp' (i,t), 
                   List.map (function b -> cnormBranch (b, t)) branches)
    
 
  and cnormExp' (i, t) = match (i,t) with
    | (Comp.Var _, _ ) -> i 

    | (Comp.Const _, _ ) -> i 

    | (Comp.Apply (i, e), t) -> Comp.Apply (cnormExp' (i, t), cnormExp (e,t))
        
    | (Comp.CtxApp (i, cPsi), t) -> Comp.CtxApp (cnormExp' (i, t), Whnf.normDCtx (cnormDCtx (cPsi, t)))

    | (Comp.MApp (i, (psihat, tM)), t) -> 
        Comp.MApp (cnormExp' (i, t), (psihat, Whnf.norm (cnorm (tM, t), S.id)))

    | (Comp.Ann (e, tau), t') -> Comp.Ann (cnormExp (e, t), Comp.TypClo (tau, mcomp t' t))



  (* cnormBranch (BranchBox (cD, (psihat, tM, (tA, cPsi)), e), theta) = 

     If  cD1 ; cG |- BranchBox (cD, (psihat, tM, (tA, cPsi)), e) <= [|theta|]tau

              cD ; cPsi |- tM <= tA 

         cD1            |- theta <= cD1' 

         cD1' ; cG' |- BranchBox (cD, (psihat, tM, (tA, cPsi)), e') <= tau'

         cD1', cD ; cG    |- e' <= tau'

         cG = [|theta|]cG'   and    e  = [|theta|]e'

         |cD| = k  
         
         cD1, cD        |- 1 .... k , (theta o ^k) <= cD1', cD

         cD1, cD        |- (theta o ^k) <= cD1 

      then

         cD1, cD ; cG   |- [1...k, (theta o ^k)|]e'  <= [|theta o ^k |]tau 



  *)
  and cnormBranch (Comp.BranchBox (cD, (psihat, tM, (tA, cPsi)), e) , theta) = 
    (* let l      = Context.length cD in  *)
    (* let theta' = mshift theta l in  *)
    let theta' = mvar_dot theta cD  in
      Comp.BranchBox (cD, (psihat, Whnf.norm (tM, S.id), (Whnf.normTyp (tA, S.id), Whnf.normDCtx cPsi)), 
                      cnormExp (e, theta'))
    

  let rec cwhnfCtx (cG, t) = match cG with 
    | LF.Empty  -> LF.Empty
    | LF.Dec(cG, Comp.CTypDecl (x, tau)) -> LF.Dec (cwhnfCtx (cG,t), Comp.CTypDecl (x, Comp.TypClo (tau, t)))


  let rec cnormCtx (cG, t) = match cG with
    | LF.Empty -> LF.Empty
    | LF.Dec(cG, Comp.CTypDecl(x, tau)) -> 
        LF.Dec (cnormCtx (cG, t), Comp.CTypDecl (x, cnormCTyp (tau, t)))

  let rec normCtx cG = match cG with
    | LF.Empty -> LF.Empty
    | LF.Dec(cG, Comp.CTypDecl (x, tau)) -> LF.Dec (normCtx cG, Comp.CTypDecl(x, normCTyp (cnormCTyp (tau, id))))

  let rec normMCtx cD = match cD with
    | LF.Empty -> LF.Empty
    | LF.Dec(cD, LF.MDecl(u, tA, cPsi)) -> 
        LF.Dec (normMCtx cD, LF.MDecl (u, Whnf.normTyp (tA, S.id), Whnf.normDCtx cPsi))

    | LF.Dec(cD, LF.PDecl(p, tA, cPsi)) -> 
        LF.Dec (normMCtx cD, LF.PDecl (p, Whnf.normTyp (tA, S.id), Whnf.normDCtx cPsi))



  (* ----------------------------------------------------------- *)
  (* Compute the inverted expression 
   *
   * If D ; G |- e <= tau    and D |- t <= D' 
   * then we return an expresion e' for some context G' and some type tau'
   *
   *        s.t. D' ; G' |- e' <= tau' 
   * 
   *  [|t|]G' = G and [|t|]tau' = tau and [|t|]e' = e
   * 
   *  and D ; [|t|]G' |- [|t|]e' <= [|t|]tau'
   * 
   * 
   * In general if t is not a pattern substitution (i.e. maps variables to variables), 
   * the inverse of t will not exist. So, instead we compute one possible expresssion e'
   * (keeping in mind that there may be many such e')
   * 
   *)
 
  let rec lookDom k t1 d =  
    let rec look t p = begin match t with
      | Comp.MDot (Comp.MV k', t) -> 
          if k > d then 
            if k' = (k-d) then Some (p +d)
            else look t (p+1)
          else 
            Some k
      | Comp.MDot (Comp.MObj (_phat, LF.Root(_, LF.MVar (LF.Offset k', LF.Shift (_,0)), _ (* Nil *))), t) -> 
          if k > d then 
            if k' = (k-d) then Some (p+d)
            else look t (p+1)
          else Some k

      | Comp.MDot (Comp.MObj (_phat, LF.Root(_, _, _)), t) -> 
          look t (p+1)


    | Comp.MDot (Comp.PObj (_phat, LF.PVar (LF.Offset k', LF.Shift (_, 0))), t') -> 
        if k > d then 
          if (k-d) = k' then
            Some (p+d)
          else look t' (p+1)
        else Some k

    | Comp.MDot (Comp.Undef, t') -> look t' (p+1)

      | _ -> None
(*          (Printf.printf "InvExp: Looking up %s \n in substitution %s \n depth d = %s \n\n" 
             (string_of_int k) (P.msubToString t1) (string_of_int d);
          raise NonInvertible)*)
      end 
    in
      look t1 1
      


  (* invTerm (tM, t) = tM' s.t. [|t|]tM' = tM *)
  let rec invTerm (tM, t) d = match tM with
    | LF.Lam (loc, y, tN)  -> LF.Lam (loc, y, invTerm (tN, t) d) 

    | LF.Tuple (loc, tuple)  -> LF.Tuple (loc, invTuple (tuple, t) d)

    | LF.Clo (tN, s)       -> LF.Clo(invTerm (tN, t) d , invSub(s, t) d)  

    | LF.Root (loc, LF.BVar i, tS) -> LF.Root(loc, LF.BVar i, invSpine (tS, t) d)

    (* Meta-variables *)

    | LF.Root (loc, LF.MVar (LF.Offset k, r), tS)
      -> 
        let k' =  begin match lookDom k t d with 
                    | None ->  k 
                    | Some k' ->  k' 
                  end 
        in 
          LF.Root (loc, LF.MVar (LF.Offset k', invSub (r, t) d), invSpine (tS, t) d) 

    | LF.Root (_, LF.FMVar (u, r), _tS) ->
        raise  (FreeMVar (LF.FMVar (u,invSub (r, t) d)))

    | LF.Root (_, LF.MVar (LF.Inst ({contents = Some _tM}, _cPsi, _tA, _cnstr), _r), _tS) -> 
        (* We could normalize [r]tM *)
        let tM' = Whnf.norm (tM, S.id) in 
          invTerm (tM', t) d
          
    | LF.Root (_, LF.MVar (LF.Inst ({contents = None}, _cPsi, _tA, _) , _r), _tS) -> 
        raise (Error "Encountered uninstantiated MVar with reference ...\n") 
        (* LF.Root (LF.MVar(u, invSub (r, t)), invSpine (tS, t))  *)

    (* Parameter variables *)
    | LF.Root (loc, LF.PVar (LF.Offset k, r), tS)
        (* cD' ; cPsi' |- r <= cPsi1 
           cD          |- t <= cD'
 
           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r

         *)
      ->  
        let k' =  begin match lookDom k t d with 
                      | None ->  k 
                      | Some k' ->  k' 
                    end 
        in 
          LF.Root (loc, LF.PVar (LF.Offset k', invSub (r, t) d), invSpine (tS, t) d)

    | LF.Root (_, LF.FPVar (p, r), _tS)  ->  raise (FreeMVar 
                                                      (LF.FPVar (p, invSub (r, t) d)))

    | LF.Root (_, LF.Proj(LF.FPVar (p, r), _tupleIndex), _tS)  ->  raise (FreeMVar 
                                                                            (LF.FPVar (p, invSub (r, t) d)))

    (* Ignore other cases for destructive (free) parameter variables *)

    (* Constants *)
    | LF.Root (loc, LF.Const c, tS)
      -> LF.Root (loc, LF.Const c, invSpine (tS, t) d)

    (* Free Variables *)
    | LF.Root (loc, LF.FVar x, tS)        
      -> (Printf.printf "Encountered a free variable!?\n" ; 
          LF.Root (loc, LF.FVar x, invSpine (tS, t) d))

    (* Projections *)
    | LF.Root (loc, LF.Proj (LF.BVar i, k), tS)
      -> LF.Root (loc, LF.Proj (LF.BVar i, k), invSpine (tS, t) d)

    | LF.Root (loc, LF.Proj (LF.PVar (LF.Offset j, s), k), tS)
        (* cD' ; cPsi' |- s <= cPsi1 *)
        (* cD          |- t <= cD'   *)         
      -> 
        let k' =  begin match lookDom j t d with 
                      | None ->  j 
                      | Some k' ->  k' 
                    end 
        in 
          LF.Root(loc, LF.Proj (LF.PVar (LF.Offset k', invSub (s,t) d), k), invSpine (tS, t) d)

  (* Ignore other cases for destructive (free) parameter variables *)

  and invTuple (tuple, t) d = match tuple with
    | LF.Last tM ->
        let invertedM = invTerm (tM, t) d in 
          LF.Last invertedM
    | LF.Cons (tM, tuple) ->
        let invertedM = invTerm (tM, t) d in 
        let invertedTuple = invTuple (tuple, t) d in
          LF.Cons (invertedM, invertedTuple)

  and invSpine (tS, t) d = match tS with
    | LF.Nil            -> LF.Nil
    | LF.App  (tN, tS)  -> LF.App (invTerm (tN, t) d, invSpine (tS, t) d)
    | LF.SClo (tS, s)   -> LF.SClo(invSpine (tS, t) d, invSub (s, t) d)


  and invSub (s, t) d = match s with 
    | LF.Shift (LF.NegCtxShift _, _)         -> raise NonInvertible
    | LF.Shift _                       -> s
    | LF.Dot (ft, s')    -> LF.Dot (invFront (ft, t) d, invSub (s', t) d)
     (* substitution variables ignored for how -bp *)


  and invFront (ft, t) d = match ft with
    | LF.Head (LF.BVar _ )            -> ft
    | LF.Head (LF.Const _ )           -> ft
    | LF.Head (LF.PVar (LF.Offset i, r)) ->
        let k' =  begin match lookDom i t d with 
                      | None ->  i 
                      | Some k' ->  k' 
                    end 
        in 
        LF.Head(LF.PVar (LF.Offset k', invSub (r,t) d))
  	      (* other case MObj _ cannot happen *)

    | LF.Head (LF.MVar (LF.Offset i, r)) -> 
        let k' =  begin match lookDom i t d with 
                      | None ->  i 
                      | Some k' ->  k' 
                    end 
        in 
          LF.Head(LF.MVar (LF.Offset k', invSub (r,t) d)) 

    | LF.Head (LF.Proj (LF.BVar _, _))    -> ft

    | LF.Head (LF.Proj (LF.PVar (LF.Offset i, r), k)) -> 
        let r' = invSub (r,t) d in 
        let k' =  begin match lookDom i t d with 
                      | None ->  i 
                      | Some k' ->  k' 
                    end 
        in 
          LF.Head (LF.Proj (LF.PVar (LF.Offset k', r'), k))

    | LF.Obj (tM) -> LF.Obj(invTerm (tM, t) d)
    | _ ->  raise NonInvertible 
          
  (* invType (tA, t) = tA'

     If cD' ; cPsi  |- tA <= type
     cD |- t <= cD'
     then
     tA' = [|t|]tA  and cPsi' = [|t|]cPsi
     cD' ; cPsi' |- tA' <= type   
  *)
  and invTyp (tA, t) d = match tA with
    |  LF.Atom (loc, a, tS) ->
         LF.Atom (loc, a, invSpine (tS, t) d)

    |  LF.PiTyp ((LF.TypDecl (_x, _tA) as decl, dep), tB)
      -> LF.PiTyp ((invDecl (decl, t) d, dep), invTyp (tB, t) d)

    |  LF.TClo (tA, s)
      -> LF.TClo(invTyp (tA,t) d, invSub (s,t) d)

    | LF.Sigma recA -> 
        LF.Sigma (invTypRec (recA, t) d)


  and invTypRec (typRec, t) d = match typRec with
    |  LF.SigmaLast lastA -> LF.SigmaLast(invTyp (lastA, t) d)
    |  LF.SigmaElem (x, tA, recA') ->
         let tA = invTyp (tA, t) d in
           LF.SigmaElem (x, tA, invTypRec (recA', t) d)

  and invDecl (decl, t) d = match decl with
      LF.TypDecl (x, tA) -> LF.TypDecl (x, invTyp (tA, t) d)


let rec invDCtx (cPsi, t)  d = match cPsi with
    | LF.Null       ->  LF.Null 

    | LF.CtxVar (LF.CtxOffset psi) -> 
        LF.CtxVar (LF.CtxOffset psi) 

    | LF.CtxVar (LF.CtxName psi) -> 
        raise (FreeCtxVar psi)

    | LF.DDec(cPsi, decl) ->  
        LF.DDec(invDCtx(cPsi, t) d, invDecl(decl, t) d) 


  (* invExp (e, t) = e' 
   
     If cO ; cD  ; cG   |- e <= tau
        cO ; cD' ; cG'  |- [|t|]e <= tau'  where [|t|]cG = cG' and [|t|]tau = tau'
        cO ; cD'        |- t <= cD
    
     then e' = [|t|]e and cO ; cD' ; cG' |- e' <= tau'

  *)

  let rec invExp (e, t) d = match (e,t) with
    | (Comp.Syn (i), t) -> Comp.Syn (invExp' (i, t) d)

    | (Comp.Rec (f, e), t) -> Comp.Rec (f, invExp (e,t) d)

    | (Comp.Fun (x, e), t) -> Comp.Fun (x, invExp (e,t) d)

    | (Comp.CtxFun (psi, e) , t ) ->  Comp.CtxFun (psi, invExp (e, t) d)

    | (Comp.MLam (u, e), t) -> Comp.MLam (u, invExp (e, t) (d+1))

    | (Comp.Pair(e1, e2), t) -> Comp.Pair (invExp (e1, t) d, invExp (e2, t) d)

    | (Comp.LetPair (i, (x, y, e)), t) -> Comp.LetPair(invExp' (i,t) d, (x, y, invExp (e, t) d))

    | (Comp.Box (psihat, tM), t) -> Comp.Box (psihat, Whnf.norm (invTerm (tM, t) d, S.id))

    | (Comp.Case (i, branches), t) -> 
        Comp.Case (invExp' (i,t) d, 
                   List.map (function b -> invBranch (b, t) d) branches)
    
 
  and invExp' (i, t) d = match (i,t) with
    | (Comp.Var _, _ ) -> i 

    | (Comp.Const _, _ ) -> i 

    | (Comp.Apply (i, e), t) -> Comp.Apply (invExp' (i, t) d, invExp (e,t) d)
        
    | (Comp.CtxApp (i, cPsi), t) -> Comp.CtxApp (invExp' (i, t) d, Whnf.normDCtx (invDCtx (cPsi, t) d))

    | (Comp.MApp (i, (psihat, tM)), t) -> 
        Comp.MApp (invExp' (i, t) d, (psihat, Whnf.norm (invTerm (tM, t) d, S.id)))

    | (Comp.Ann (e, tau), t') -> Comp.Ann (invExp (e, t) d, Comp.TypClo (tau, mcomp t' t)) 
                                                           (* invCTyp (tau , t') d *)



  (* invBranch (b as BranchBox (cD, (psihat, tM, (tA, cPsi)), e), theta) = b'

  *)
  and invBranch (Comp.BranchBox (cD, (psihat, tM, (tA, cPsi)), e) , theta) d = 
    (* let l      = Context.length cD in  *)
    (* let theta' = mshift theta l in  *)
    let d' = Context.length cD  in
      Comp.BranchBox (cD, (psihat, Whnf.norm (tM, S.id), (Whnf.normTyp (tA, S.id), Whnf.normDCtx cPsi)), 
                      invExp (e, theta) (d+d'))
    

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

    | ((Comp.TypCross (tT1, tT2), t), (Comp.TypCross (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
	&&
	  convCTyp (tT2, t) (tT2', t')


    | ((Comp.TypCtxPi ((_psi, cid_schema), tT1), t) , (Comp.TypCtxPi ((_psi', cid_schema'), tT1'), t'))
      -> cid_schema = cid_schema'
	&& 
	  convCTyp (tT1, t) (tT1', t')

    | ((Comp.TypPiBox ((LF.MDecl(_, tA, cPsi), dep), tT), t), (Comp.TypPiBox ((LF.MDecl(_, tA', cPsi'), dep'), tT'), t'))
      -> dep = dep' 
        &&
          Whnf.convTyp (cnormTyp (tA, t), S.id) (cnormTyp (tA', t'), S.id)
	&&
	  Whnf.convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
	&& 
	  convCTyp (tT, mvar_dot1 t) (tT', mvar_dot1 t') 

(* For now we omit PDecl, SDecl - bp *)

and convSchema (LF.Schema fs) (LF.Schema fs') =  List.for_all2 convSchElem fs fs' 

and convSchElem (LF.SchElem (cPsi, trec)) (LF.SchElem (cPsi', trec')) = 
    Whnf.convCtx cPsi cPsi'
  &&
    Whnf.convTypRec (trec, S.id) (trec', S.id)
