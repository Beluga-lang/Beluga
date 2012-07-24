(**

   @author Brigitte Pientka
   modified:  Joshua Dunfield

*)

(* Weak Head Normalization,
 * Normalization, and alpha-conversion
 *)


let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [17])

open Context
open Syntax.Int.LF
open Syntax.Int
open Substitution


type error =
    CompFreeMVar of Id.name
  | NotPatSub

exception Error of Syntax.Loc.t * error

module R = Store.Cid.DefaultRenderer
module T = Store.Cid.Typ

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | CompFreeMVar u ->
          Format.fprintf ppf "Encountered free meta-variables %s\n"
            (Store.Cid.DefaultRenderer.render_name u)

      | NotPatSub ->
          Format.fprintf ppf "Not a pattern substitution" (* TODO *) ))


exception Fmvar_not_found
exception FreeMVar of head
exception NonInvertible 

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [18])

let rec raiseType cPsi tA = match cPsi with
  | Null -> tA
  | DDec (cPsi', decl) ->
      raiseType cPsi' (PiTyp ((decl, Maybe), tA))

let rec emptySpine tS = match tS with
  | Nil -> true
  | SClo(tS, _s) -> emptySpine tS


  (* isPatSub s = B

     Invariant:

     If    Psi |- s : Psi' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  let rec isPatSub s = 
    (* let s = (Whnf.normSub s) in  *)
    begin match s with
    | Shift (_,_k)              -> true
    | Dot (Head(BVar n), s) ->
        let rec checkBVar s' = match s' with
          | Shift (_ , k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s 
          | Dot (Undef, s)          -> checkBVar s
          | _                       -> false
        in
          checkBVar s && isPatSub s

    | Dot (Undef, s)        -> isPatSub s

    | _                     -> false
    end 

  (* isPatMSub t = B

     Invariant:

     If    cD |- t : cD' 
     and   t = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  let rec isPatMSub t = 
    begin match t with
    | MShift _k             -> true
    | MDot (MV n, t) ->
        let rec checkMVar s' = match s' with
          | MShift  k               -> n <= k
          | MDot (MV n', s)         -> n <> n' && checkMVar s
          | _                       -> false
        in
          checkMVar t && isPatMSub t
(*    | Dot (Obj tM , s)      -> 
        begin match tM with
          | Root(BVar n, tS) -> 
              let rec checkBVar s' = match s' with
                | Shift k                 -> n <= k
                | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
                | Dot (Undef, s)          -> checkBVar s
                | _                       -> false
              in
                emptySpine tS && checkBVar s && isPatSub s
          | _ -> false
        end 
*)    
    | MDot (MUndef, s)       -> isPatMSub s
    | _                     -> false
    end 

(* Eta-contract elements in substitutions *)
let rec etaContract tM = begin match tM with 
  | Root (_, BVar k, Nil) -> Head (BVar k) 
  | Lam  _ as tMn -> 
      let rec etaUnroll k tM = begin match tM with
        | Lam (_ , _, tN) -> 
            let _ = dprint (fun () -> "etaUnroll k ="  ^ string_of_int k ^ "\n") in 
              etaUnroll (k+1) tN
        |  _ ->  let _ = dprint (fun () -> "etaUnroll k ="  ^ string_of_int k ^ "\n") in  (k, tM) 
      end in
      let rec etaSpine k tS = begin match (k, tS) with
        | (0, Nil) -> true
        | (k', App(Root(_ , BVar x, Nil), tS')) -> 
            if k' = x then etaSpine (k'-1)  tS'
            else false
        | _ -> (dprint (fun () -> "[etaSpine] _ ") ; raise (Error.Violation ("etaSpine undefined\n")))
      end in 
        begin match etaUnroll 0 tMn with 
          | (k, Root( _ , BVar x, tS)) -> 
              (let _ = dprint (fun () -> "check etaSpine k ="  ^ string_of_int k ^ "\n") in 
                 (if etaSpine k tS && x > k then 
                    Head(BVar (x-k))
                  else 
                    Obj tMn))
          | _ ->  Obj tMn    
        end 
  | _  -> Obj tM
 end




(*************************************)
(* Creating new contextual variables *)
(*************************************)
(* newCVar n sW = psi
 *
 *)
let newCVar n (sW) = match n with
  | None -> CInst (Id.mk_name Id.NoName, ref None, sW, Empty, Empty)
  | Some name -> CInst (name, ref None, sW, Empty, Empty)


(* newPVar n (cPsi, tA) = p
 *
 * Invariant:
 *
 *       tA =   Atom (a, S)
 *   or  tA =   Pi (x:tB, tB')
 *   but tA =/= TClo (_, _)
 *)
 let newPVar n (cPsi, tA) = match n with
  | None -> PInst (Id.mk_name (Id.BVarName (T.gen_var_name tA)), ref None, cPsi, tA, ref [])
  | Some name -> PInst (name, ref None, cPsi, tA, ref [])


(* newMVar n (cPsi, tA) = newMVarCnstr (cPsi, tA, [])
 *
 * Invariant:
 *
 *       tA =   Atom (a, S)
 *   or  tA =   Pi (x:tB, tB')
 *   but tA =/= TClo (_, _)
 *)


let newMVar n (cPsi, tA) = match n with
  | None -> Inst (Id.mk_name (Id.MVarName (T.gen_var_name tA)), ref None, cPsi, tA, ref [])
  | Some name -> Inst (name, ref None, cPsi, tA, ref [])


(* newMMVar n (cPsi, tA) = newMVarCnstr (cPsi, tA, [])
 *
 * Invariant:
 *
 *       tA =   Atom (a, S)
 *   or  tA =   Pi (x:tB, tB')
 *   but tA =/= TClo (_, _)
 *)
let newMMVar n (cD, cPsi, tA) = match n with
  (* flatten blocks in cPsi, and create appropriate indices in tA 
     together with an appropriate substitution which moves us between 
     the flattened cPsi_f and cPsi. 

     this will allow to later prune MMVars. 
     Tue Dec  1 09:49:06 2009 -bp 
   *)
  | None -> MInst (Id.mk_name (Id.MVarName (T.gen_var_name tA)), ref None, cD, cPsi, tA, ref [])
  | Some name -> MInst (name, ref None, cD, cPsi, tA, ref [])



let newMPVar n (cD, cPsi, tA) = match n with
  | None -> MPInst (Id.mk_name (Id.PVarName (T.gen_var_name tA)), ref None, cD, cPsi, tA, ref []) 
  | Some name -> MPInst (name, ref None, cD, cPsi, tA, ref [])



(******************************)
(* Lowering of Meta-Variables *)
(******************************)

(* lowerMVar' cPsi tA[s] = (u, tM), see lowerMVar *)
let rec lowerMVar' cPsi sA' = match sA' with
  | (PiTyp ((decl,_ ), tA'), s') ->
      let (u', tM) = lowerMVar' (DDec (cPsi, LF.decSub decl s')) (tA', LF.dot1 s') in
        (u', Lam (Syntax.Loc.ghost, Id.mk_name Id.NoName, tM))

  | (TClo (tA, s), s') ->
      lowerMVar' cPsi (tA, LF.comp s s')

  | (Atom (loc, a, tS), s') ->
      let u' = newMVar None (cPsi, Atom (loc, a, SClo (tS, s'))) in
        (u', Root (Syntax.Loc.ghost, MVar (u', LF.id), Nil)) (* cvar * normal *)


(* lowerMVar1 (u, tA[s]), tA[s] in whnf, see lowerMVar *)
and lowerMVar1 u sA = match (u, sA) with
  | (Inst (_n, r, cPsi, _, _), (PiTyp _, _)) ->
      let (u', tM) = lowerMVar' cPsi sA in
        r := Some tM; (* [| tM / u |] *)
        u'            (* this is the new lowered meta-variable of atomic type *)

  | (_, (TClo (tA, s), s')) ->
      lowerMVar1 u (tA, LF.comp s s')

  | (_, (Atom _, _s)) ->
      u


(* lowerMVar (u:cvar) = u':cvar
 *
 * Invariant:
 *
 *   If    cD = D1, u::tA[cPsi], D2
 *   where tA = PiTyp x1:B1 ... xn:tBn. tP
 *   and   u not subject to any constraints
 *
 *   then cD' = D1, u'::tP[cPsi, x1:B1, ... xn:tBn], [|t|]D2
 *   where  [| lam x1 ... xn. u'[id(cPsi), x1 ... xn] / u |] = t
 *
 *   Effect: u is instantiated to lam x1 ... xn.u'[id(cPsi), x1 ... xn]
 *           if n = 0, u = u' and no effect occurs.
 *
 * FIXME MVar spine is not elaborated consistently with lowering
 *   -- Tue Dec 16 00:19:06 EST 2008
 *)
and lowerMVar = function
  | Inst (_n, _r, _cPsi, tA, { contents = [] }) as u ->
      lowerMVar1 u (tA, LF.id)

  | _ ->
      (* It is not clear if it can happen that cnstr =/= nil *)
      (* 2011/01/14: Changed this to a violation for now, to avoid a cyclic dependency on Reconstruct. -mb *)
      raise (Error.Violation "Constraints left")


(*************************************)

let m_id = MShift 0

(* mvar_dot1 psihat t = t'
   Invariant:

   If  cO ;  cD |- t : D'       

   then t' = u. (mshift t 1)  
       and  for all A s.t.  D' ; Psi |- A : type

              D, u::[|t|](A[Psi]) |- t' : D', A[Psi]
 *)
let rec mvar_dot1 t = 
(*    MDot (MV 1, mshift t 1) *)
  MDot (MV 1, mcomp t (MShift 1))

  and pvar_dot1 t = 
    MDot (MV 1, mcomp t (MShift 1))


  (* mvar_dot t cD = t' 

     if cD1 |- t <= cD2 
     then cD1, cD |- t <= cD2, cD
  *)
  and mvar_dot t cD = match cD with
    | Empty -> t
    | Dec(cD', _ ) -> 
        mvar_dot (mvar_dot1 t) cD'



(* mcomp t1 t2 = t'

   Invariant:

   If   D'  |- t1 : D 
   and  D'' |- t2 : D'
   then t'  =  t1 o t2
   and  D'' |- t1 o t2 : D

   Note: Eagerly composes the modal substitutions t1 and t2.

*)

and mcomp t1 t2 = match (t1, t2) with
  | (MShift 0, t)         -> t
  | (t, MShift 0)         -> t
  | (MShift n, MShift k) -> (MShift (n+k))
  |  (MShift n, MDot (_mft, t))  -> 
      mcomp (MShift (n-1)) t
  | (MDot (mft, t), t') -> 
      MDot (mfrontMSub mft t', mcomp t t')


(* mfrontMSub Ft t = Ft'

   Invariant:

   If   D |- t : D'     D' ; Psi |- Ft <= A
   then Ft' =  [|t|] Ft
   and  D ; [|t|]Psi |- Ft' : [|t|]A
*)
and mfrontMSub ft t = match ft with
  | MObj (phat, tM)     -> 
        (* apply cnorm_psihat (phat, t) -bp ? *)
      let phat = cnorm_psihat phat t in 
        MObj (phat, cnorm(tM, t))

  | PObj (phat, PVar (Offset k, s))  -> 
      let phat = cnorm_psihat phat t in 
      begin match LF.applyMSub k t with
        | PObj(phat', BVar k') ->  
            begin match LF.bvarSub k' s with 
              | Head(BVar j) -> PObj(phat', BVar j)
              | Head(PVar (q, s')) -> PObj(phat', PVar(q, s'))
              (* no case for LF.Head(MVar(u, s')) since u not guaranteed
                 to be of atomic type. *)
              | Obj tM      -> MObj(phat', tM)
            end 
        | PObj(phat', PVar (q, s')) -> PObj(phat', PVar(q, LF.comp s' s))

        | MV k'  -> PObj (phat, PVar (Offset k', s))
          (* other cases impossible *)
      end
  | PObj (phat, BVar _k)  -> 
      let phat = cnorm_psihat phat t in 
        PObj (phat, BVar _k) 

  | PObj (phat, PVar (PInst (_n, {contents = Some (BVar x)}, _cPsi, _tA, _ ) , r)) -> 
      let phat = cnorm_psihat phat t in  
        begin match LF.bvarSub x (cnormSub (r,t)) with
          | Head (BVar k)  ->  PObj (phat, BVar k)
          | Head (PVar (q,s))  ->  PObj (phat, PVar (q,s))
          | Obj tM  -> MObj (phat, tM)
        end 

  | PObj (phat, (PVar (PInst (_n, {contents = None}, _cPsi, _tA, _ ), r) as p)) -> 
      let phat = cnorm_psihat phat t in 
        PObj (phat, p)


  | CObj (cPsi) -> CObj (cnormDCtx (cPsi, t))
      
  | MV k -> 
      begin match LF.applyMSub k t with  (* DOUBLE CHECK - bp Wed Jan  7 13:47:43 2009 -bp *)
        | PObj(phat, p) ->  PObj(phat, p)          
        | MObj(phat, tM) ->  MObj(phat, tM)          
        | CObj(cPsi) -> CObj (cPsi)
        | MV k'         -> MV k'
        (* other cases impossible *)
      end

(*  | MV u -> 
      begin match LF.applyMSub u t with
        | MObj(phat, tM) ->  MObj(phat, tM)          
        | MV u'          ->  MV u'
        (* other cases impossible *)
      end
*)



(* m_invert t = t'

   Invariant:

   If   D  |- t  <= D'    (and s !!!patsub!!!)
   then D' |- t' <= D
   s.t. t o t' = id    (mcomp t' t = id)
*)
and m_invert s =
  let rec lookup n s p = match s with
    | MShift _                 -> None
    | MDot (MUndef, t')    -> lookup (n + 1) t' p

    | MDot (MV k, t') ->
        if k = p then Some n
        else lookup (n + 1) t' p 

    | MDot (CObj(CtxVar (CtxOffset k)), t') -> 
        if k = p then
          Some n
        else lookup (n + 1) t' p 

    | MDot (MObj(_phat, Root(_, MVar (Offset k, Shift (_,0)), Nil)), t') -> 
        if k = p then
          Some n
        else lookup (n + 1) t' p 

    | MDot (PObj (_phat, PVar (Offset k, Shift (_, 0))), t') -> 
        if k = p then
          Some n
        else lookup (n + 1) t' p 
         
          
  in

  let rec invert'' p ti = match p with
      | 0 -> ti
      | p ->
          let front = match lookup 1 s p with
            | Some k -> MV k (* or MObj (phat, Root(MVar(Offset k), id), Nil)  *)
            | None   -> MUndef
          in
            invert'' (p - 1) (MDot (front, ti)) in

    let rec invert' n t = match t with
      | MShift p     -> invert'' p (MShift n)
      | MDot (_, t') -> invert' (n + 1) t'

    in
      invert' 0 s


(* Normalization = applying simultaneous hereditary substitution
 *
 * Applying the substitution ss to an LF term tM yields again
 * a normal term. This corresponds to normalizing the term [s]tM.
 *
 * We assume that the LF term tM does not contain any closures
 * MClo (tN,t), TMClo(tA, t), SMClo(tS, t); this means we must
 * first call contextual normalization and then call ordinary
 * normalization.
 *)
(*
 * norm (tM,s) = [s]tM
 *
 * Invariant:
 * if cD ; cPsi  |- tM <= tA
 *    cD ; cPsi' |- s <= cPsi
 * then
 *    cD ; cPsi' |- [s]tM <= [s]tA
 *
 * Similar invariants for norm, normSpine.
 *)
and norm (tM, sigma) = match tM with
  | Lam (loc, y, tN) ->
      Lam (loc, y, norm (tN, LF.dot1 sigma))

  | Tuple (loc, tuple) ->
      Tuple (loc, normTuple (tuple, sigma))

  | Clo (tN, s) ->
      norm (tN, LF.comp s sigma)

  | Root (loc, BVar i, tS) ->
      begin match LF.bvarSub i sigma with
        | Obj tM        -> reduce (tM, LF.id) (normSpine (tS, sigma)) 
        | Head (BVar k) ->  Root (loc, BVar k, normSpine (tS, sigma))
        | Head head     ->  norm (Root (loc, head, normSpine (tS, sigma)), LF.id)
        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
            (* Undef should not happen ! *)
      end

  | Root (_, MMVar (MInst (_, { contents = Some tM}, _, _, _, _),(t, r)), tS) ->
      (* constraints associated with u must be in solved form *)
      let tM' = cnorm (tM, t) in 
      let tM'' = norm (tM', r) in 
      reduce (tM'', sigma) (normSpine (tS, sigma))

  | Root (loc, MMVar (MInst (_, {contents = None}, _, _, Atom _, _) as u, (t, r)), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)
      Root (loc, MMVar (u, (t, normSub (LF.comp r sigma))), normSpine (tS, sigma))

  | Root (loc, MMVar (MInst (n, ({contents = None} as r), cD, cPsi, TClo (tA, s'), cnstr), (t, s)), tS) ->
      norm (Root (loc, MMVar (MInst (n, r, cD, cPsi, normTyp (tA, s'), cnstr), (t, s)), tS), sigma)

  (* Meta-variables *)

  | Root (loc, MVar (Offset _ as u, r), tS) ->
      Root (loc, MVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  | Root (_, MVar (Inst (_, { contents = Some tM}, _, _, _), r), tS) ->
      (* constraints associated with u must be in solved form *)      
        reduce (norm (tM, r),  sigma) (normSpine (tS, sigma))  
      (* reduce (norm (tM, LF.id), LF.comp r sigma) (normSpine (tS, sigma))   *)

  | Root (loc, MVar (Inst (_, {contents = None}, _, Atom _, _) as u, r), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)  
      let s' =  normSub (LF.comp r sigma) in 
      Root (loc, MVar (u, s'), normSpine (tS, sigma))

  | Root (loc, MVar (Inst (n, ({contents = None} as r), cPsi, TClo (tA, s'), cnstr), s), tS) ->
      let tAn = normTyp (tA, s') in 
        norm (Root (loc, MVar (Inst (n, r, cPsi, tAn, cnstr), s), tS), sigma)

  | Root (_, MVar (Inst (_, {contents = None}, _, _tA, _) as u, _r), _tS) ->
      (* Meta-variable is not atomic and tA = Pi x:B1.B2
       * lower u, and normalize the lowered meta-variable
       *)
      let _ = lowerMVar u in
        norm (tM, sigma)

  (* Parameter variables *)
  | Root (loc, FMVar (u, r), tS) ->
      Root (loc, FMVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  (* Parameter variables *)
  | Root (loc, PVar (Offset _ as p, r), tS) ->
      Root (loc, PVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  (* Parameter variables *)
  | Root (loc, FPVar (p, r), tS) ->
      Root (loc, FPVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  | Root (loc, PVar (PInst (_, { contents = Some (BVar i)}, _, _, _), r), tS) ->
      begin match LF.bvarSub i r with
        | Obj tM        ->  reduce (tM, LF.id) (normSpine (tS, sigma))
        | Head (BVar x) ->  Root (loc, BVar x, normSpine (tS, sigma))
        | Head head     ->  norm (Root (loc, head, normSpine (tS, sigma)), LF.id)
      end

  | Root (loc, PVar (PInst (_, { contents = Some (PVar (q, r')) }, _, _, _) as _p, r), tS) ->
      norm (Root (loc, PVar (q, LF.comp r' r), tS), sigma)
      (* where p::tA[cPsi]
       * and  cD; cPsi' |- r : cPsi
       * and  cD; cPsi' |- p[r]      -> [r]tA
       * and  cD; cPsi  |- q[r']     ->    tA
       * and  cD; cPsi' |- q[r' o r] -> [r]tA
       *)
  | Root (loc, PVar (PInst (_, { contents = None}, _, _, _) as p, r), tS) ->
      Root (loc, PVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  | Root (loc, MPVar (MPInst (_, { contents = Some h}, _, _, _, _),(t, r)), tS) ->
      (* constraints associated with u must be in solved form *)
      let h' = cnormHead (h, t) in 
        begin match h' with 
          | BVar i -> begin match LF.bvarSub i (LF.comp r sigma) with
                        | Obj tM -> reduce (tM, LF.id) (normSpine (tS, sigma))
                        | Head (BVar k) -> Root (loc, BVar k , normSpine (tS, sigma))
                        | Head h        -> norm (Root (loc, h, normSpine (tS, sigma)), LF.id)
                        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                            (* Undef should not happen ! *)
                      end 
          | PVar (p, s) -> Root (loc, PVar (p, LF.comp (LF.comp s r) sigma), normSpine (tS, sigma))
          | MPVar (q, (t', r')) -> norm (Root (loc, MPVar (q, (t', LF.comp r' r)), normSpine (tS, sigma)), LF.id)
          (* anything else not allowed *)
        end 

  | Root (loc, MPVar (MPInst (_, {contents = None}, _, _, _, _) as p, (t, r)), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)
      Root (loc, MPVar (p, (t, normSub (LF.comp r sigma))), normSpine (tS, sigma))


  (* Constants *)
  | Root (loc, Const c, tS) ->
      Root (loc, Const c, normSpine (tS, sigma))

  (* Projections *)
  | Root (loc, Proj (BVar i, k), tS) ->
      begin match LF.bvarSub i sigma with
        | Head (BVar j)      -> Root (loc, Proj (BVar j, k), normSpine (tS, sigma))
        | Head (PVar (p, s)) ->  norm (Root (loc, Proj (PVar (p, s), k), SClo (tS, sigma)), LF.id)
                (* Root (loc, Proj (PVar (p, s), k), normSpine (tS, sigma)) *)
      end

  | Root (loc, Proj (FPVar(p,r), k),  tS) ->
      Root (loc, Proj (FPVar (p, normSub (LF.comp r sigma)), k), normSpine (tS, sigma))

  | Root (loc, Proj (PVar (Offset _i as q, s), k), tS) ->
      Root (loc, Proj (PVar (q, LF.comp s sigma), k), normSpine (tS, sigma))

  | Root (loc, Proj (PVar (PInst (_, {contents = Some (PVar (q, r'))}, _, _, _), s), k), tS) ->
      norm (Root (loc, Proj (PVar (q, LF.comp r' s), k), tS), sigma)

  | Root (loc, Proj (PVar (PInst (_, {contents = Some (FPVar (q, r'))}, _, _, _), s), k), tS) ->
      norm (Root (loc, Proj (FPVar (q, LF.comp r' s), k), tS), sigma)

  | Root (loc, Proj (PVar (PInst (_, {contents = Some (BVar i)}, _, _, _), s), k), tS) ->
      begin match LF.bvarSub i s with
        (* | Obj tM     ->  impossible *)
        | Head (BVar x) ->  Root (loc, Proj(BVar x, k), normSpine (tS, sigma))
        | Head (PVar (q,r'))  ->  norm (Root (loc, Proj(PVar (q, LF.comp r' s), k), tS) , sigma)
      end


  | Root (loc, Proj (PVar (PInst (_, {contents = None}, _, _, _) as q, s), k), tS) ->
      Root (loc, Proj (PVar (q, normSub (LF.comp s sigma)), k), normSpine (tS, sigma))

  | Root (loc, FVar x, tS) ->
      Root (loc, FVar x, normSpine (tS, sigma))




and normTuple (tuple, t) = match tuple with
  | Last tM -> Last (norm (tM, t))
  | Cons (tM, rest) ->
      let tM' = norm (tM, t) in
      let rest' = normTuple (rest, t) in
        Cons (tM', rest')

and normSpine (tS, sigma) = 
   begin match tS with
     | Nil           -> Nil
     | App  (tN, tS) -> 
         let tN' =  norm (tN, sigma) in
         App (tN', normSpine (tS, sigma))
     | SClo (tS, s)  -> normSpine (tS, LF.comp s sigma)
   end

(*  reduce(sM, tS) = M'
 *
 *  cPsi | tS > tA' <= tP
 *  cPsi |  s  : cPsi''      cPsi'' |- tM <= tA''       [s]tA'' = tA'
 *)
and reduce sM spine = match (sM, spine) with
  | ((Root (_, _, _) as root, s), Nil)    -> norm (root, s)
  | ((Lam (_, _y, tM'), s), App (tM, tS)) -> reduce (tM', Dot (Obj tM, s)) tS
  | ((Clo (tM, s'), s), tS)               -> reduce (tM , LF.comp s' s) tS
      (* other cases are impossible *)


and normSub s = match s with
  | Shift (CtxShift (CInst (_n, {contents = Some cPhi }, _schema, _octx, _mctx)), k) -> 
      begin match Context.dctxToHat cPhi with
        | (Some ctx_v, d) -> 
            normSub (Shift (CtxShift ctx_v, k + d))
        | (None, d) ->
            Shift (NoCtxShift, k + d)
      end

    | Shift (NegCtxShift (CInst (_n, {contents = Some cPhi }, _schema, _octx, _mctx)), k) -> 
        let rec undef_sub d s = 
          if d = 0 then s 
          else undef_sub (d-1) (Dot(Undef, s)) 
        in 
          begin match Context.dctxToHat cPhi with
          | (Some ctx_v, d) -> 
          (* Phi |- s : psi  and psi not in Psi and |Psi| = k 
           * Psi |- Shift(negCtxShift(phi), k) . Undef ....  : phi, Phi 
           *)                      
              normSub (undef_sub d (Shift (NegCtxShift ctx_v, k)))

          | (None, d) -> undef_sub d (Shift (NoCtxShift, k))

          end

  | Shift _      -> s
  | Dot (ft, s') -> Dot(normFt ft, normSub s')
  | SVar (Offset offset, s') -> SVar (Offset offset, normSub s')

and normFt ft = match ft with
  | Obj tM ->
      etaContract(norm (tM, LF.id))
  | Head (BVar _k)                -> ft
  | Head (FVar _k)                -> ft
  | Head (MPVar (MPInst (_n, { contents = Some h}, _, _, _, _), (t, r))) -> 
      let h' = cnormHead (h,t) in 
        begin match h' with
          | BVar i -> LF.bvarSub i r
          | PVar (p, s) -> Head (PVar (p, LF.comp r s))
          | MPVar (q, (t',r')) -> Head (MPVar (q, (t', LF.comp r r')))
        end 
  | Head (MPVar (MPInst (_n, { contents = None}, _, _, _, _), (_t, _r))) -> 
      ft
  | Head (MPVar (p, (t, s')))     -> Head (MPVar (p, (cnormMSub t, normSub s')))
  | Head (MMVar (MInst (_n, { contents = Some tN}, _, _, _, _), (t, s'))) -> 
     Obj (norm (cnorm (tN, t), s'))
  | Head (MMVar (u, (t, s')))     -> Head (MMVar (u, (cnormMSub t, normSub s')))
  | Head (MVar (Inst (_, { contents = Some tM}, _, _, _), s)) -> 
      Obj(norm (tM, s)) 
  | Head (MVar (u, s'))           -> Head (MVar (u, normSub s'))
  | Head (FMVar (u, s'))          -> Head (FMVar (u, normSub s'))
  | Head (PVar (p, s'))           -> Head (PVar (p, normSub s'))
  | Head (FPVar (p, s'))          -> Head (FPVar (p, normSub s'))
  | Head (Proj (PVar (p, s'), k)) -> Head (Proj (PVar (p, normSub s'), k)) 
  | Head h                        -> Head h 
  | Undef                         -> Undef  (* -bp Tue Dec 23 2008 : DOUBLE CHECK *)



(* normType (tA, sigma) = tA'
 *
 * If cD ; G |- tA <= type
 *    cD ; G' |- sigma <= G
 * then
 *    tA' = [sigma]tA
 *    cD ; G' |- tA' <= type   and tA' is in normal form
 *)
and normTyp (tA, sigma) =  match tA with
  | Atom (loc, a, tS) ->
      Atom (loc, a, normSpine (tS, sigma))

  | PiTyp ((TypDecl (_x, _tA) as decl, dep ), tB) ->
      PiTyp ((normDecl (decl, sigma), dep), normTyp (tB, LF.dot1 sigma))

  | TClo (tA, s) ->
      normTyp (tA, LF.comp s sigma)
 
  | Sigma recA ->
      Sigma (normTypRec (recA, sigma))

and normTypRec (recA, sigma) = match recA with
  | SigmaLast lastA ->
      let tA = normTyp (lastA, sigma) in 
      SigmaLast tA

  | SigmaElem (x, tA, recA') ->
      let tA = normTyp (tA, sigma) in
        SigmaElem(x, tA, normTypRec (recA', LF.dot1 sigma))

and normDecl (decl, sigma) = match decl with
  | TypDecl (x, tA) ->
      TypDecl (x, normTyp (tA, sigma))

  | _ -> decl



and norm_psihat (phat: psi_hat) = match phat with
  | (None , _ ) -> phat
  | (Some (CInst (_n, {contents = Some cPsi}, _schema, _cO, _cD)),  k) -> 
      begin match Context.dctxToHat cPsi with
        | (None, i) -> (None, k+i)
        | (Some cvar', i) -> (Some cvar', i+k)
      end
  |  _ -> phat




(* ********************************************************************* *)
(* Normalization = applying simultaneous modal substitution   

     Applying the modal substitution t to a normal LF term tM 
     yields a normal term. This corresponds to normalizing the term [|t|]tM.
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
  | BVar _ -> "BVar"
  | Const _ -> "Const"
  | MMVar _ -> "M^2Var"
  | MPVar _ -> "M^2PVar"
  | MVar _ -> "MVar"
  | PVar _ -> "PVar"
  | AnnH _ -> "AnnH"
  | Proj (head, k) -> "Proj " ^ what_head head ^ "." ^ string_of_int k
  | FVar _ -> "FVar"
  | FMVar _ -> "FMVar"
  | FPVar _ -> "FPVar"



and cnorm_psihat (phat: psi_hat) t = match phat with
  | (None , _ ) -> phat
  | (Some (CInst (_n, {contents = Some cPsi}, _schema, _cO, _cD)),  k) -> 
      begin match Context.dctxToHat cPsi with
        | (None, i) -> (None, k+i)
        | (Some cvar', i) -> (Some cvar', i+k)
      end
  | (Some (CtxOffset offset), k) -> 
      ((* dprint (fun () -> "[cnorm_psihat] CtxOffset = " ^ string_of_int offset ^ "\n");*)
      begin match LF.applyMSub offset t with 
        | CObj(cPsi) -> 
            begin match Context.dctxToHat (cPsi) with
              | (None, i) -> (None, k+i)
              | (Some cvar', i) -> (Some cvar', i+k)
            end
        | MV offset' -> (Some (CtxOffset offset'), k)
      end )
  |  _ -> phat




and cnorm (tM, t) = match tM with
    | Lam (loc, y, tN)   -> Lam (loc, y, cnorm (tN, t))

    | Tuple (loc, tuple) -> Tuple (loc, cnormTuple (tuple, t))

    | Clo (tN, s)        -> Clo(cnorm (tN, t), cnormSub(s, t))  

    | Root (loc, head, tS) ->
        begin match head with
          | BVar i -> Root(loc, BVar i, cnormSpine (tS, t))

          | MMVar (MInst (_n, {contents = Some tN}, _D, _cPsi, _tA, _cnstr), (t',s')) -> 
              (* Assumes tS = Nil because _n is of atomic type *)
              (*   cD, cPsi |- tM <= tA   and   r = (t,s) 
               *   cD'      |- t <= cD   and cD' ; cPsi' |- s <= |[t]|cPsi 
               *   cD ; |[t]|cPsi |- |[t]|tM <= |[t]|tA
               *   cD' ; cPsi' |- [s]|[t] tM <= [s]|[t]|tA
               *)
              let tN'  = cnorm (tN, t') in 
              let tN'' = norm (tN', s') in 
                cnorm (tN'', t)

          | MMVar (MInst (_n, {contents = None}, _cD , _cPsi, _tA, _cnstr) as u , (t', r)) ->
              (* if constraints_solved (!cnstr) then  *)
                (* raise (Error "Encountered Un-Instantiated MVar with reference ?\n") *)
                let r'  = cnormSub (r, t) in 
                let t'' = cnormMSub (mcomp t' t) in 
                Root (loc, MMVar(u, (t'', r')), cnormSpine (tS, t)) 
              (* else 
                raise (Error.Violation "uninstantiated meta-variables with unresolved constraints") *)

          | MPVar (MPInst (_n, {contents = Some h}, _D, _cPsi, _tA, _cnstr), (t',s')) -> 
              (*   cD, cPsi |- tM <= tA   and   r = (t,s) 
               *   cD'      |- t <= cD   and cD' ; cPsi' |- s <= |[t]|cPsi 
               *   cD ; |[t]|cPsi |- |[t]|tM <= |[t]|tA
               *   cD' ; cPsi' |- [s]|[t] tM <= [s]|[t]|tA
               *)
              let h'  = cnormHead (h, t') in 
                begin match h' with 
                  | BVar i -> begin match LF.bvarSub i s' with
                              | Obj tM -> reduce (cnorm (tM, t),LF.id) (cnormSpine (tS, t))
                              | Head (BVar k) -> Root (loc, BVar k , cnormSpine (tS, t))
                              | Head h        -> cnorm (Root (loc, h, tS), t)
                              | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                               (* Undef should not happen ! *)
                              end
                  | PVar (p, s) -> norm (Root (loc, PVar (p, LF.comp s s'), cnormSpine (tS, t)), LF.id)
                  | MPVar (q, (t', r')) -> cnorm (Root (loc, MPVar (q, (mcomp t' t, s')), cnormSpine (tS, t)), m_id)
                      (* anything else not allowed *)
                end 

          | MPVar (MPInst (_n, {contents = None}, _cD , _cPsi, _tA, _cnstr) as p , (t', r)) ->
              (* if constraints_solved (!cnstr) then  *)
                (* raise (Error "Encountered Un-Instantiated MVar with reference ?\n") *)
                let r'  = cnormSub (r, t) in 
                let t'' = cnormMSub (mcomp t' t) in 
                Root (loc, MPVar(p, (t'', r')), cnormSpine (tS, t)) 

          (* Meta-variables *)

          | MVar (Offset k, r) -> 
              begin match LF.applyMSub k t with
                | MV  k'            -> 
                    Root (loc, MVar (Offset k', cnormSub (r, t)), cnormSpine (tS, t)) 
                      
                | MObj (_phat,tM)   ->                     
                    reduce (tM, cnormSub (r, t)) (cnormSpine (tS, t)) 
                    (* Clo(whnfRedex ((tM, cnormSub (r, t)), (cnormSpine (tS, t), LF.id)))  *) 
                | PObj (_phat, h) -> 
                    let tS' = cnormSpine (tS, t) in 
                      begin match h with 
                        | BVar i -> (match LF.bvarSub i (cnormSub (r,t)) with 
                            | Obj tM        -> reduce (tM, LF.id) tS'
                            | Head (BVar k) ->  Root (loc, BVar k, tS')
                            | Head head     ->  Root (loc, head, tS')
                            | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n")))
                        | PVar (p, r') -> Root (loc, PVar (p, r') , tS')
                      end
              (* other cases impossible *)
              end 

          | FMVar (u, r) -> Root (loc, FMVar (u, cnormSub (r,t)),  cnormSpine (tS, t))
              (* raise (Error (loc, CompFreeMVar u)) *)


          | MVar (Inst (_n, {contents = Some tM}, _cPsi, _tA, _cnstr), r) ->  
              (* We could normalize [r]tM *)
              let tM' = norm (tM, r) in 
                cnorm (tM', t)
                  
          (*        Root (MVar(Inst (_n, {contents = Some (cnorm (tM, t))}, cPsi, tA, cnstr), 
                    cnormSub (r, t)), cnormSpine (tS, t)) 
                    
          *)
          (* CHECK HERE IF THERE ARE ANY LEFTOVER CONSTRAINTS! *)
          | MVar (Inst (_n, {contents = None}, _cPsi, _tA, cnstr) as u , r) ->
              (* if constraints_solved (!cnstr) then *)
                (* raise (Error "Encountered Uninstantiated MVar with reference ?\n") *)
                Root (loc, MVar(u, cnormSub (r, t)), cnormSpine (tS, t)) 
(*              else 
                raise (Error.Violation "uninstantiated meta-variables with unresolved constraints")*)
                  
                  
          | PVar (PInst (_, {contents = None}, _cPsi, _tA, _ ) as p, r) -> 
              Root (loc, PVar(p, cnormSub (r, t)), cnormSpine (tS, t)) 

          | PVar (PInst (_, {contents = Some (BVar x)}, _cPsi, _tA, _ ) , r) ->
              (dprint (fun () -> "[cnorm] PVar Some BVar ");
              begin match LF.bvarSub x (cnormSub (r,t)) with
                | Head h  ->
                    Root (loc, h, cnormSpine (tS, t))
                | Obj tM  -> Clo (whnfRedex ((tM, LF.id), (cnormSpine (tS, t), LF.id)))
              end
              )

          | PVar (PInst (_, {contents = Some (PVar (q,s))}, _cPsi, _tA, _ ) , r) ->
              Root (loc, PVar (q, (LF.comp s (cnormSub (r,t)))), cnormSpine (tS, t))           

        (* Parameter variables *)
          | PVar (Offset k, r)

        (* cD' ; cPsi' |- r <= cPsi1 
           cD          |- t <= cD'
 
           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r

         *)
            -> begin match LF.applyMSub k t with
              | MV  k'            -> Root (loc, PVar (Offset k', cnormSub (r, t)), cnormSpine (tS, t))
              | PObj (_phat, BVar i) -> 
                  begin match LF.bvarSub i (cnormSub (r,t)) with
                    | Head h  -> Root(loc, h, cnormSpine (tS, t))
                    | Obj tM  -> Clo (whnfRedex ((tM, LF.id), (cnormSpine (tS, t), LF.id)))
                  end
              | PObj (_phat, PVar(Offset i, r')) -> 
                  Root (loc, PVar(Offset i, LF.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
                    
              | PObj (_phat, PVar(PInst (_, {contents = None}, _, _, _ ) as p, r')) -> 
                  Root (loc, PVar(p, LF.comp r' (cnormSub (r,t))), cnormSpine (tS, t))
                    
                    
              | PObj (_phat, PVar(PInst (_, {contents = Some (PVar (x, rx))}, _, _, _ ), r')) -> 
                  Root (loc, PVar (x, LF.comp rx (LF.comp r' (cnormSub (r,t)))), cnormSpine (tS, t))
                    
              | PObj (_phat, PVar(PInst (_, {contents = Some (BVar x)}, _, _, _ ), r')) -> 
                  begin match LF.bvarSub x (cnormSub (r',t)) with
                    | Head (BVar i)  ->  
                        begin match LF.bvarSub i (cnormSub (r,t)) with
                          | Head h  -> Root(loc, h, cnormSpine (tS, t))
                          | Obj tM  -> Clo (whnfRedex ((tM, LF.id), (cnormSpine (tS, t), LF.id)))
                        end
                    | Head (PVar(q, s)) -> Root(loc, PVar(q,  LF.comp s (cnormSub (r,t))), cnormSpine (tS, t))
                        (* Other case MObj _ should not happen -- ill-typed *)
                  end

              | PObj (_phat, MPVar (MPInst (_, {contents = Some h}, _cD, _cPsi, _tA, _), (mr, r))) -> 
                   norm (Root (loc, h, cnormSpine (tS, t)), LF.id)

              | PObj (_phat, MPVar (MPInst (_, {contents = None}, _cD, _cPsi, _tA, _) as q, (mr, r))) -> 
                   Root (loc, MPVar(q, (mr,r)), cnormSpine (tS, t))

              | PObj (_phat, FPVar (p,r)) -> Root (loc, FPVar (p,r), cnormSpine (tS, t))

              | PObj (_phat, _) -> (print_string "whnf PObj 827 crash\n"; exit 189)
              | MObj (_phat, Root(_, MVar _, _)) -> (print_string "whnf MObj 827 crash -- MVar\n"; exit 190)
            end

          | FPVar (p, r) -> Root(loc, FPVar (p, cnormSub (r,t)), cnormSpine (tS, t)) 
              (* raise (Error (loc, CompFreeMVar p)) *)

          | Proj (FPVar (_p, _r), _tupleIndex) as head -> 
              Root (loc, head, cnormSpine(tS, t)) 
                (*              raise (FreeMVar (FPVar (p, cnormSub (r, t)))) *)

          (* Ignore other cases for destructive (free) parameter variables *)
                
          (* Constants *)
          | Const c
            -> Root (loc, Const c, cnormSpine (tS, t))
              
          (* Free Variables *)
          | FVar x ->
              raise (Error.Violation "Encountered a free variable during normalization.")

          (* Projections *)
          | Proj (PVar (PInst (_, {contents = None}, _cPsi, _tA, _ ) as p, r), k) -> 
              Root (loc, Proj( PVar(p, cnormSub (r, t)), k), cnormSpine (tS, t))

          | Proj (PVar (PInst (_, {contents = Some (BVar x)}, _cPsi, _tA, _ ), r), k) -> 
              begin match LF.bvarSub x (cnormSub (r,t)) with
                | Head h  -> cnorm (Root (loc, Proj (h, k), cnormSpine (tS,t)), t)
              end

          | Proj (BVar i, k)
            -> Root (loc, Proj (BVar i, k), cnormSpine (tS, t))

          | Proj (PVar (Offset j, s), tupleIndex)
              (* cD' ; cPsi' |- s <= cPsi1 *)
              (* cD          |- t <= cD'   *)         
            -> begin
              let wrap head = Proj (head, tupleIndex) in
              let newHead =
                match LF.applyMSub j t with
                  | PObj (_phat, BVar i)   -> 
                      (*  i <= phat *) 
                      begin match LF.bvarSub i (cnormSub (s,t)) with
                        | Head (BVar j)      ->  wrap (BVar j)
                        | Head (PVar (p,r')) ->  wrap (PVar (p, r') )
                            (* other cases should not happen; 
                               term would be ill-typed *)
                      end
                  | PObj(_phat, Proj (PVar (Offset i, s'),  otherTupleIndex)) -> 
                      (* This case seems wrong 
                         This case is impossible since tuples cannot be nested;
                         PVar (Offset j) must have Sigma-type and hence when we replace j with 
                         an object is must be also of Sigma-type (otherwise substitution is 
                         ill-typed). But this would mean Proj (PVar (Offset i, s')) needs to 
                         have a Sigma-type, which is impossible since it would mean that 
                         PVar (Offset i) would need to have a type where Sigma-types are nested.

                         Mon Sep  7 11:41:40 2009 -bp *)
                      Proj (PVar (Offset i, LF.comp s' (cnormSub (s,t))),  otherTupleIndex)
                        

                  | PObj(_phat, PVar (Offset i, s')) ->
                      wrap (PVar (Offset i, LF.comp s' (cnormSub (s,t))))
                        
                  | PObj (_phat, PVar(PInst (_, {contents= None}, _, _, _) as p, r')) -> 
                      wrap (PVar (p, LF.comp r' (cnormSub (s,t))))

                  | PObj (_phat, PVar (PInst (_, {contents = Some (BVar x)}, _cPsi, _tA, _ ), r)) -> 
                      begin match LF.bvarSub x (cnormSub (r,t)) with
                        | Head h  -> wrap h
                      end 

                  | PObj (_phat, PVar (PInst (_, {contents = Some (PVar (x,r0))}, _cPsi, _tA, _ ), r')) -> 
                      wrap (PVar (x, LF.comp (LF.comp r0 r') (cnormSub (s,t))))

                  | MV  k'            -> wrap (PVar (Offset k', cnormSub (s, t)))
                  | _  -> (print_string ("[cnorm] non-exhaustive match : applying msub to "                                                                                 ^ what_head head ^  " is undefined ? \n"); 
                           exit 2)                      
              in
                Root (loc, newHead, cnormSpine (tS, t))
            end

          | head -> (print_string ("[cnorm] non-exhaustive match : missing case for " ^ what_head head ^  "\n"); exit 2)
        end
      (* Ignore other cases for destructive (free) parameter-variables *)
  
(* cnormHead (h,t) = h' 
   requires that h is a head such as bound variable or parameter variable associated with pattern sub 
   or projection of the previous two
 *)
  and cnormHead (h, t) = begin match h with 
    | BVar i -> BVar i
    | MPVar (p, (ms, s)) -> 
        if isPatSub s && isPatMSub ms then 
          begin match p with
            | MPInst (_, {contents = None}, _cD, _cPsi, _tA, _cnstr) -> 
                MPVar (p, (mcomp ms t, s))
            | MPInst (_, {contents = Some h0}, _cD, cPsi, _tA, _cnstr) -> 
                let h' = cnormHead (h0, ms) in 
                  begin match h' with
                    | BVar k -> let Head h1 = LF.bvarSub k s in cnormHead (h1, t) 
                    | PVar (p, s') -> cnormHead (PVar(p, LF.comp s s'), t)
                    | MPVar (q, (ms', s')) -> cnormHead (MPVar (q, (ms', LF.comp s' s)), t)
                  end 
          end 
        else 
          (* if this arises the function needs to be generalized to return not a head but "either a head or a term" *)
          raise (Error.Violation "Cannot guarantee that parameter variable remains head")
    | PVar (p, r) -> 
        if isPatSub r then 
          begin match p with 
            | PInst (_, {contents = None}, _cPsi, _tA, _ ) -> PVar (p, r)
            | PInst (_, {contents = Some (BVar x)}, _cPsi, _tA, _ ) -> 
                let Head h = LF.bvarSub x r in 
                  h
            | PInst (_, {contents = Some (Proj(BVar x, k))}, _cPsi, _tA, _ ) -> 
                let Head h = LF.bvarSub x r in 
                  Proj(h, k)

            | PInst (_, {contents = Some (PVar (q, s))}, _cPsi, _tA, _ ) -> 
                cnormHead (PVar (q, (LF.comp s r)), t)

            | PInst (_, {contents = Some (Proj(PVar (q, s), k))}, _cPsi, _tA, _ ) -> 
                cnormHead (Proj( PVar (q, (LF.comp s r)), k), t)

            | Offset k  -> 
                let _ = dprint (fun () -> "[cnormHead] Pvar offset") in 
                begin match LF.applyMSub k t with
                  | MV  k'            -> PVar (Offset k', cnormSub (r, t))
                  | PObj (_phat, BVar i) -> 
                      let Head h = LF.bvarSub i r in h
              | PObj (_phat, PVar(Offset i, r')) -> 
                  PVar(Offset i, LF.comp r' r)
                    
              | PObj (_phat, PVar(PInst (_, {contents = None}, _, _, _ ) as p, r')) -> 
                  PVar(p, LF.comp r' r)                   
                    
              | PObj (_phat, PVar(PInst (_, {contents = Some (PVar (x, rx))}, _, _, _ ), r')) -> 
                  PVar (x, LF.comp rx (LF.comp r' r))
                    
              | PObj (_phat, PVar(PInst (_, {contents = Some (BVar x)}, _, _, _ ), r')) -> 
                  begin match LF.bvarSub x r' with
                    | Head (BVar i)  ->  
                        let Head h = LF.bvarSub i r in h
                    | Head (PVar(q, s)) -> PVar(q,  LF.comp s r)
                        (* Other case MObj _ should not happen -- ill-typed *)
                  end
                    
                end
          end
        else 
          raise (Error.Violation "Cannot guarantee that parameter variable remains head")

    (* Projections *)
    | Proj(BVar i, k) -> Proj (BVar i, k)
    | Proj(PVar (p,r), k) -> 
        begin match cnormHead (PVar (p,r), t)  with
          | Proj _ -> raise (Error.Violation "Nested projections -- this is ill-typed")
          | h      -> Proj (h, k)
        end

    | Const k -> Const k
    | FPVar (p,s) -> FPVar (p,s)
    | MVar _ -> raise (Error.Violation "cnormHead MVar")
    | _      -> raise (Error.Violation "cnormHead ???")
  end 
        

          
  and cnormSpine (tS, t) = match tS with
    | Nil            -> Nil
    | App  (tN, tS)  -> App (cnorm (tN, t), cnormSpine (tS, t))
    | SClo (tS, s)   -> SClo(cnormSpine (tS, t), cnormSub (s, t))

  and cnormTuple (tuple, t) = match tuple with
    | Last tM -> Last (cnorm (tM, t))
    | Cons (tM, rest) ->
        let tM' = cnorm (tM, t) in
        let rest' = cnormTuple (rest, t) in
          Cons (tM', rest')

  and cnormSub (s, t) = match s with 
    | Shift (CtxShift (CInst (_n, {contents = Some cPhi }, _schema, _octx, _mctx)), k) -> 
        begin match Context.dctxToHat cPhi with
          | (Some ctx_v, d) -> 
              cnormSub (Shift (CtxShift ctx_v, k + d), t)
          | (None, d) ->
              cnormSub (Shift (NoCtxShift, k + d), t)
        end

    | Shift (NegCtxShift (CInst (_n, {contents = Some cPhi }, _schema, _octx, _mctx)), k) -> 
        let rec undef_sub d s = 
          if d = 0 then s 
          else undef_sub (d-1) (Dot(Undef, s)) 
        in 
          begin match Context.dctxToHat cPhi with
          | (Some ctx_v, d) -> 
          (* Phi |- s : psi  and psi not in Psi and |Psi| = k 
           * Psi |- Shift(negCtxShift(phi), k) . Undef ....  : phi, Phi 
           *)                      
              cnormSub (undef_sub d (Shift (NegCtxShift ctx_v, k)) , t )

          | (None, d) -> cnormSub (undef_sub d (Shift (NoCtxShift, k)), t)

          end

    | Shift (NegCtxShift (CtxOffset psi), k) -> 
        let rec undef_sub d s = 
          if d = 0 then s 
          else undef_sub (d-1) (Dot(Undef, s)) 
        in           
        begin match LF.applyMSub psi t with             
          | MV psi' -> Shift (NegCtxShift (CtxOffset psi'), k) 
          | CObj (CtxVar psi) -> Shift (NegCtxShift (psi), k)
          | CObj (Null) -> Shift (NoCtxShift, k)
          | CObj (DDec _ as cPsi) -> 
              begin match Context.dctxToHat cPsi with
                | (Some ctx_v, d) -> 
                    undef_sub d (Shift (NegCtxShift ctx_v, k))
                | (None, d) -> undef_sub d (Shift (NoCtxShift, k))
              end
        end

    | Shift (NoCtxShift, _k) -> s
    | Shift (CtxShift (CtxOffset psi), k) ->  
        (* let _ = dprint (fun () -> "[cnormSub] ctx_offset " ^ string_of_int  psi ) in  *)
        begin match LF.applyMSub psi t with             
          | MV psi' -> Shift (CtxShift (CtxOffset psi'), k)  
          | CObj (CtxVar psi) -> Shift (CtxShift (psi), k)
          | CObj (Null) -> Shift (NoCtxShift, k)
          | CObj (DDec _ as cPsi) -> 
            begin match Context.dctxToHat cPsi with
              | (Some ctx_v, d) -> 
                  Shift (CtxShift ctx_v, k + d)
                    
              | (None, d) ->
                  Shift (NoCtxShift, k + d)
            end
          | MObj _ -> (dprint (fun () -> "[applyMSub] ill-typed MObj for CObj");
                       dprint (fun () -> "[cnormSub] ctx_offset " ^ string_of_int  psi)
                  ; raise (Error.Violation "illtyped msub"))

                       
        end
    (* this case does happen during type reconstruction when we are inferring
       the type of a pattern which is a meta-object
    *)
    | Shift (CtxShift (CtxName psi), k) -> s 
    | Shift (_ , k ) -> s
    | Dot (ft, s')    -> Dot (cnormFront (ft, t), cnormSub (s', t))
    | SVar (Offset offset, s') -> SVar(Offset offset, cnormSub (s',t))
     (* substitution variables ignored for how -bp *)


  and cnormFront (ft, t) = match ft with
    | Head (BVar _ )            -> ft
    | Head (Const _ )           -> ft
    | Head (PVar (Offset i, r)) ->
        begin match LF.applyMSub i t with
          | PObj(_phat, PVar(Offset n, s')) -> 
             Head(PVar(Offset n, LF.comp s' (cnormSub (r,t))))
          | PObj (_phat, BVar j)    ->  LF.bvarSub j (cnormSub (r,t))
          | MV k -> Head(PVar (Offset k, cnormSub (r,t)))
              (* other case MObj _ cannot happen *)
        end

    | Head (PVar (p, r)) ->
        let r'  = cnormSub (r,t) in 
          Head (PVar (p, r'))

    | Head (MPVar (p, (mr, r))) -> 
        let r'  = cnormSub (r,t) in 
        let mr' = cnormMSub (mcomp mr t) in 
          Head (MPVar (p, (mr', r')))

    | Head (MMVar (u, (mr, r))) -> 
        let r'  = cnormSub (r,t) in 
        let mr' = cnormMSub (mcomp mr t) in 
          Head (MMVar (u, (mr', r')))
          
    | Head (MVar (Offset i, r)) -> 
        begin match LF.applyMSub i t with
          | MObj (_phat, tM)    -> Obj(Clo (tM, cnormSub (r,t)))
          | MV k -> Head(MVar (Offset k, cnormSub (r,t))) 
        end

    | Head (MVar (u, r)) -> 
        let r'  = cnormSub (r,t) in 
          Head (MVar (u, r'))

    | Head (Proj (BVar _, _))    -> ft
    | Head (Proj (PVar (Offset i, r), k)) -> 
        let r' = cnormSub (r,t) in 
        begin match LF.applyMSub i t with
          | PObj (_phat, BVar j)  -> 
              begin match LF.bvarSub j r' with
                | Head(BVar j') -> Head(Proj (BVar j', k))
                | Head(PVar (Offset j, s')) -> Head (Proj (PVar (Offset j, s'), k))
                (* other cases impossible for projections *)
              end
          | PObj (_phat, PVar(Offset j, s'))   ->  
              Head(Proj (PVar(Offset j, LF.comp s' r'), k))
          | MV j' -> Head (Proj (PVar (Offset j', r'), k))             
          (* other case MObj _ cannot happen *)
        end

    | Head (Proj (PVar (p, r), k)) -> 
        let r' = cnormSub (r,t) in 
          Head (Proj (PVar (p, r'), k))

    | Head (Proj (MVar _ , _)) -> raise (Error.Violation "Head MVar")
    | Head (Proj (Const _ , _)) -> raise (Error.Violation "Head Const")
    | Head (Proj (Proj _ , _)) -> raise (Error.Violation "Head Proj Proj")
    | Head (Proj (MMVar _ , _)) -> raise (Error.Violation "Head MMVar ")
    | Head (Proj (MPVar _ , _)) -> raise (Error.Violation "Head MPVar ")

    | Obj (tM) -> Obj(cnorm (tM, t))

    | Undef -> Undef
        
          
  (* cnormTyp (tA, t) = tA'

     If cD' ; cPsi  |- tA <= type
     cD |- t <= cD'
     then
     tA' = [|t|]tA  and cPsi' = [|t|]cPsi
     cD' ; cPsi' |- tA' <= type   
  *)
  and cnormTyp (tA, t) = match tA with
    | Atom (loc, a, tS) ->
        Atom (loc, a, cnormSpine (tS, t))

    | PiTyp ((TypDecl (_x, _tA) as decl, dep), tB)
      -> PiTyp ((cnormDecl (decl, t), dep), cnormTyp (tB, t))

    | TClo (tA, s)
      -> TClo(cnormTyp (tA,t), cnormSub (s,t))

    | Sigma recA
      -> Sigma(cnormTypRec (recA, t))

  and cnormTypRec (typRec, t) = match typRec with
    |  SigmaLast lastA -> SigmaLast(cnormTyp (lastA, t))
    |  SigmaElem (x, tA, recA') ->
         let tA = cnormTyp (tA, t) in
           SigmaElem (x, tA, cnormTypRec (recA', t))

  and cnormDecl (decl, t) = match decl with
    | TypDecl (x, tA) -> 
        TypDecl (x, cnormTyp (tA, t))
    | TypDeclOpt x -> TypDeclOpt x  



  (* cnormDCtx (cPsi, t) = cPsi 

   If cO ; cD  |- cPsi lf-dctx
      cO ; cD' |-  t_d <= cO ; cD
   then 
      cO  ; cD' |- [|t|]cPsi 

  *)
  and cnormDCtx (cPsi, t) = match cPsi with
    | Null       ->  Null 

    | CtxVar (CInst (_n, {contents = None} , _schema, _octx, _mctx )) -> cPsi

    | CtxVar (CInst (_n, {contents = Some cPhi} ,_schema, _octx, _mctx)) -> 
        cnormDCtx (cPhi, t)

    | CtxVar (CtxOffset psi) -> 
        begin match LF.applyMSub psi t with
          | CObj (cPsi') -> normDCtx cPsi'
          | MV k -> CtxVar (CtxOffset k)
        end


    | CtxVar (CtxName psi) -> CtxVar (CtxName psi)


    | DDec(cPsi, decl) ->  
        DDec(cnormDCtx(cPsi, t), cnormDecl(decl, t))



and cnormMSub t = match t with
  | MShift _n -> t
  | MDot (MObj(phat, tM), t) -> 
      MDot (MObj (cnorm_psihat phat m_id, 
                  norm(tM, LF.id)), cnormMSub t) 

  | MDot (CObj (cPsi), t) -> 
        let t' = cnormMSub t in 
        let cPsi' = normDCtx cPsi in 
          MDot (CObj cPsi' , t')

  | MDot (PObj(phat, PVar(Offset k, s)), t) -> 
      MDot (PObj(cnorm_psihat phat m_id, PVar(Offset k, s)), cnormMSub t)

  | MDot (PObj(phat, BVar k), t) -> 
      MDot (PObj(cnorm_psihat phat m_id, BVar k), cnormMSub t)

  | MDot (PObj(phat, PVar(PInst (_, {contents = None}, _cPsi, _tA, _ ) as p,  s)), t) -> 
      MDot (PObj(cnorm_psihat phat m_id, PVar(p, s)), cnormMSub t)

  | MDot(PObj(phat, PVar (PInst (_, {contents = Some (BVar x)}, _cPsi, _tA, _ ) , r)), t) -> 
        let t' = cnormMSub t in 
        begin match LF.bvarSub x r with
          | Head h  ->  
             MDot (PObj(cnorm_psihat phat m_id, h), t')
          | Obj tM  -> 
              MDot (MObj(cnorm_psihat phat m_id,  norm (tM, LF.id)), t')
        end

  | MDot(PObj(phat, PVar (PInst (_, {contents = Some (PVar (q,s))}, _cPsi, _tA, _ ) , r)), t) -> 
      cnormMSub (MDot (PObj (cnorm_psihat phat m_id, PVar(q, LF.comp s r)), t))

  | MDot (MV u, t) -> MDot (MV u, cnormMSub t)



(* ************************************************************** *)


and normKind sK = match sK with
  | (Typ, _s) ->
      Typ

  | (PiKind ((decl, dep), tK), s) ->
      PiKind ((normDecl (decl, s), dep), normKind (tK, LF.dot1 s))

and normDCtx cPsi = match cPsi with
  | Null -> Null

  | CtxVar (CInst (_n, {contents = None} , _schema, _octx, _mctx )) -> cPsi
      
  | CtxVar (CInst (_n, {contents = Some cPhi} ,_schema, _octx, _mctx)) -> 
      normDCtx cPhi

  | CtxVar psi -> CtxVar psi

  | DDec (cPsi1, TypDecl (x, Sigma typrec)) ->
      let cPsi1 = normDCtx cPsi1 in
      let typrec = normTypRec (typrec, LF.id) in
        DDec (cPsi1, TypDecl (x, Sigma typrec))

  | DDec (cPsi1, decl) ->
      DDec (normDCtx cPsi1, normDecl (decl, LF.id))


and normCDecl (decl, sigma) = match decl with
  | MDecl (x, tA, cPsi) ->
      MDecl (x, normTyp (tA, sigma) , normDCtx cPsi)

  | PDecl (x, tA, cPsi) ->
      PDecl (x, normTyp (tA, sigma) , normDCtx cPsi)

  | CDecl (x, schema, dep) ->
      CDecl (x, schema, dep)


  | SDecl (s, cPhi, cPsi) -> 
      SDecl (s, normDCtx cPhi, normDCtx cPsi)


and normMCtx cD = match cD with
  | Empty -> Empty
  | Dec(cD, cdecl) -> 
      Dec (normMCtx cD, normCDecl (cdecl, LF.id))
        

(* ---------------------------------------------------------- *)
(* Weak head normalization = applying simultaneous hereditary
 * substitution lazily
 *
 * Instead of fully applying the substitution sigma to an
 * LF term tM, we apply it incrementally, and delay its application
 * where appropriate using Clo, SClo.
 *
 * We assume that the LF term tM does not contain any closures
 * MClo (tN,t), TMClo(tA, t), SMClo(tS, t); this means we must
 * first call contextual normalization (or whnf) and then call
 * ordinary normalization, if these two substitutions interact.
 *)
(*
 * whnf(tM,s) = (tN,s')
 *
 * Invariant:
 * if cD ; cPsi'  |- tM <= tA
 *    cD ; cPsi   |- s <= cPsi'
 * then
 *    cD ; cPsi  |- s' <= cPsi''
 *    cD ; cPsi''  |- tN  <= tB
 *
 *    cD ; cPsi |- [s]tM = tN[s'] <= tA''
 *    cD ; cPsi |- [s]tA = [s']tB = tA'' <= type
 *
 *  Similar invariants for whnf, whnfTyp.
 *)
and whnf sM = match sM with
  | (Lam _, _s) -> sM

  | (Tuple _, _s) -> sM

  | (Clo (tN, s), s') -> whnf (tN, LF.comp s s')

  | (Root (loc, BVar i, tS), sigma) ->
      begin match LF.bvarSub i sigma with
        | Obj tM        -> whnfRedex ((tM, LF.id), (tS, sigma))
        | Head (BVar k) -> (Root (loc, BVar k, SClo (tS,sigma)), LF.id)
        | Head (Proj(BVar k, j)) -> (Root (loc, Proj(BVar k, j), SClo(tS, sigma)), LF.id)
        | Head head     -> whnf (Root (loc, head, SClo (tS,sigma)), LF.id)
            (* Undef should not happen! *)
      end

  (* Meta^2-variable *)
  | (Root (loc, MPVar (MPInst (_, {contents = Some h}, _cD, _cPsi, _tA, _), (t,r)), tS), sigma) ->
      (* constraints associated with q must be in solved form *)
      let h' = cnormHead (h, t) in 
        begin match h' with 
          | BVar i -> begin match LF.bvarSub i (LF.comp r sigma) with
                        | Obj tM -> whnfRedex ((tM, LF.id), (tS, sigma))
                        | Head (BVar k) -> (Root (loc, BVar k , SClo (tS, sigma)), LF.id)
                        | Head h        -> (Root (loc, h, SClo (tS, sigma)), LF.id)
                        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                            (* Undef should not happen ! *)
                      end 
          | PVar (p, s) -> (Root (loc, PVar (p, LF.comp (LF.comp s r) sigma), SClo (tS, sigma)), LF.id)
          | MPVar (q, (t', r')) -> (Root (loc, MPVar (q, (t', LF.comp r' r)), SClo (tS, sigma)), LF.id)
        end
     


  | (Root (loc, (MPVar (MPInst (_, {contents = None}, _cD, _cPsi, _tA, _), (t,r)) as h), tS), sigma) ->
      (* constraints associated with q must be in solved form *)
        (Root (loc, h,  SClo(tS, sigma)), LF.id)

  | (Root (_, MMVar (MInst (_, {contents = Some tM}, _cD, _cPsi, _tA, _), (t,r)), tS), sigma) ->
      (* constraints associated with u must be in solved form *)
      let tM' = cnorm (tM, t) in 
      let sR =  whnfRedex ((tM', LF.comp r sigma), (tS, sigma)) in
        sR

  | (Root (loc, MMVar (MInst (n, ({contents = None} as uref), cD, cPsi, tA, cnstr), (t, r)), tS), sigma) ->
      (* note: we could split this case based on tA;
       *      this would avoid possibly building closures with id
       *)
      begin match whnfTyp (tA, LF.id) with
        | (Atom (loc', a, tS'), _s (* id *)) ->
            (* meta-variable is of atomic type; tS = Nil  *)
            let u' = MInst (n, uref, cD, cPsi, Atom (loc', a, tS'), cnstr) in
              (Root (loc, MMVar (u', (t, LF.comp r sigma)), SClo (tS, sigma)), LF.id)
        | (PiTyp _, _s)->
            (* Meta-variable is not atomic and tA = Pi x:B1.B2:
             * lower u, and normalize the lowered meta-variable.
             * Note: we may expose and compose substitutions twice.
             *
             * Should be possible to extend it to m^2-variables; D remains unchanged
             * because we never arbitrarily mix pi and pibox.
             *)
            raise (Error.Violation "Meta^2-variable needs to be of atomic type")

      end

  (* Meta-variable *)
  | (Root (loc, MVar (Offset _k as u, r), tS), sigma) ->
      (Root (loc, MVar (u, LF.comp r sigma), SClo (tS, sigma)), LF.id)

  | (Root (loc, FMVar (u, r), tS), sigma) ->
      (Root (loc, FMVar (u, LF.comp r sigma), SClo (tS, sigma)), LF.id)

  | (Root (_, MVar (Inst (_, {contents = Some tM}, _cPsi, _tA, _), r), tS), sigma) ->
      (* constraints associated with u must be in solved form *)
      let tM' = begin match r with
                  | Shift (NoCtxShift, 0) -> tM 
                  | _ ->   norm(tM, r) (* this can be expensive -bp *)
                end  in 
     (* it does not work to call whnfRedex ((tM, LF.comp r sigma), (tS, sigma)) -bp *)
      let sR =  whnfRedex ((tM',  sigma), (tS, sigma)) in 
        sR 

  | (Root (loc, MVar (Inst (n, ({contents = None} as uref), cPsi, tA, cnstr) as u, r), tS) as tM, sigma) ->
      (* note: we could split this case based on tA;
       *      this would avoid possibly building closures with id
       *)
      begin match whnfTyp (tA, LF.id) with
        | (Atom (loc', a, tS'), _s (* id *)) ->
            (* meta-variable is of atomic type; tS = Nil  *)
            let u' = Inst (n, uref, cPsi, Atom (loc', a, tS'), cnstr) in
              (Root (loc, MVar (u', LF.comp r sigma), SClo (tS, sigma)), LF.id)
        | (PiTyp _, _s)->
            (* Meta-variable is not atomic and tA = Pi x:B1.B2:
             * lower u, and normalize the lowered meta-variable.
             * Note: we may expose and compose substitutions twice.
             *)
            let _ = lowerMVar u in
              whnf (tM, sigma)
      end

  (* Parameter variable *)
  | (Root (loc, PVar (Offset _k as p, r), tS), sigma) ->
      (Root (loc, PVar (p, LF.comp r sigma), SClo (tS, sigma)), LF.id)


  (* PVar None *)
  | (Root (loc, PVar (PInst(_, {contents = None}, _cPsi, _tA, _ ) as p, r), tS), sigma) ->
      (Root (loc, PVar (p, LF.comp r sigma), SClo (tS, sigma)), LF.id)


  | (Root (loc, PVar (PInst(_, {contents = Some (BVar x)}, _cPsi, _tA, _ ), r), tS), sigma) ->
        begin match LF.bvarSub x (LF.comp r sigma) with
          | Head h  ->  
              (Root (loc, h, SClo(tS, sigma)), LF.id)
          | Obj tM  -> whnfRedex ((tM, LF.id),  (tS, sigma))
        end

  (* PVar Some *)
  | (Root (loc, PVar (PInst (_, {contents = Some (PVar (q, r'))}, _, _, _), r), tS), sigma) -> 
      whnf (Root (loc, PVar (q, LF.comp r' r), tS), sigma) 

  | (Root (loc, PVar (PInst (_, {contents = Some (FPVar (q, r'))}, _, _, _), r), tS), sigma) -> 
      whnf (Root (loc, FPVar (q, LF.comp r' r), tS), sigma) 


  | (Root (loc, FPVar (p, r), tS), sigma) ->
      (Root (loc, FPVar (p, LF.comp r sigma), SClo (tS, sigma)), LF.id)

  | (Root (loc, Proj(FPVar (p, r), k), tS), sigma) ->
      let fpvar = FPVar (p, LF.comp r sigma) in
      (Root (loc, Proj(fpvar,k), SClo(tS,sigma)),  LF.id)

  (* Constant *)
  | (Root (loc, Const c, tS), sigma) ->
      (Root (loc, Const c, SClo (tS, sigma)), LF.id)

  (* Projections *)
  | (Root (loc, Proj (BVar i, k), tS), sigma) ->
      begin match LF.bvarSub i sigma with
        | Head (BVar j)      -> (Root (loc, Proj (BVar j, k)     , SClo (tS, sigma)), LF.id)
        | Head (PVar (q, s)) -> (Root (loc, Proj (PVar (q, s), k), SClo (tS, sigma)), LF.id)
      end

  | (Root (loc, Proj (PVar (Offset _ as q, s), k), tS), sigma) ->
      (Root (loc, Proj (PVar (q, LF.comp s sigma), k), SClo (tS, sigma)), LF.id)

  (* Proj PVar Some *)
  | (Root (loc, Proj (PVar (PInst (_, {contents = Some (PVar (q', r'))}, _, _, _), s), k), tS), sigma) ->
      whnf (Root (loc, Proj (PVar (q', LF.comp r' s), k), tS), sigma)



  | (Root (loc, Proj (PVar (PInst (_, {contents = Some (BVar x)}, _, _, _), r), k), tS), sigma) ->
        begin match LF.bvarSub x (LF.comp r sigma) with
          | Head (BVar x)  ->  
              (Root (loc, Proj (BVar x, k), SClo(tS, sigma)), LF.id)
          | Head (PVar (q,r')) -> 
                    whnf (Root (loc, Proj (PVar (q, LF.comp r' r), k), SClo(tS, sigma)), LF.id)
          | Head (FPVar (q,r')) -> 
                    whnf (Root (loc, Proj (FPVar (q, LF.comp r' r), k), SClo(tS, sigma)), LF.id)
        end



  | (Root (loc, Proj (PVar (PInst (_, {contents = Some (FPVar (q', r'))}, _, _, _), s), k), tS), sigma) ->
      whnf (Root (loc, Proj (FPVar (q', LF.comp r' s), k), tS), sigma)

  (* Proj PVar None *)
  | (Root (loc, Proj (PVar (PInst(_, {contents = None}, _cPsi, _tA, _ ) as p, r), projIndex), tS), sigma) ->
      (Root (loc, Proj (PVar (p, LF.comp r sigma), projIndex), SClo (tS, sigma)), LF.id)

  (* Free variables *)
  | (Root (loc, FVar x, tS), sigma) ->
      (Root (loc, FVar x, SClo (tS, sigma)), LF.id)

(*  | (Root (_, Proj (PVar (PInst ({contents = None}, _, _, _), _), _), _), _) -> (dprint (fun () -> "oops"); exit 1) *)
  | (Root (_, Proj (PVar _, _), _), _) -> (dprint (fun () -> "oops"); exit 2)
  | (Root (_, Proj (_, _), _), _) -> (dprint (fun () -> "oops"); exit 3)
  | _ -> (dprint (fun () -> "oops"); exit 4)

(* whnfRedex((tM,s1), (tS, s2)) = (R,s')
 *
 * If cD ; Psi1 |- tM <= tA       and cD ; cPsi |- s1 <= Psi1
 *    cD ; Psi2 |- tS > tA <= tP  and cD ; cPsi |- s2 <= Psi2
 * then
 *    cD ; cPsi |- s' : cPsi'    and cD ; cPsi' |- R' -> tP'
 *
 *    [s']tP' = [s2]tP and [s']R' = tM[s1] @ tS[s2]
 *)
and whnfRedex (sM, sS) = match (sM, sS) with
  | ((Root (_, _, _) as root, s1), (Nil, _s2)) ->
      whnf (root, s1)

  | ((Lam (_, _x, tM), s1), (App (tN, tS), s2)) ->
      let tN' = Clo (    tN , s2) in  (* cD ; cPsi |- tN'      <= tA' *)
      let s1' = Dot (Obj tN', s1) in  (* cD ; cPsi |- tN' . s1 <= Psi1, x:tA''
                                         tA'' = [s1]tA' *)
        whnfRedex ((tM, s1'), (tS, s2))

  | (sM, (SClo (tS, s2'), s2)) ->
      whnfRedex (sM, (tS, LF.comp s2' s2))

  | ((Clo (tM, s), s1), sS) ->
      whnfRedex ((tM, LF.comp s s1), sS)


(* whnfTyp (tA, sigma) = tA'
 *
 * If cD ; cPsi  |- tA <= type
 *    cD ; cPsi' |- sigma <= cPsi
 * then
 *    tA' = [sigma]tA
 *    cD ; cPsi' |- tA' <= type   and tA' is in weak head normal form
 *)
and whnfTyp (tA, sigma) = match tA with
  | Atom (loc, a, tS) -> (Atom (loc, a, SClo (tS, sigma)), LF.id)
  | PiTyp (_cD, _tB)  -> (tA, sigma)
  | TClo (tA, s)      -> whnfTyp (tA, LF.comp s sigma)
  | Sigma _typRec      -> (tA, sigma) 


(* ----------------------------------------------------------- *)
(* Check whether constraints are solved *)
and constraints_solved cnstr = match cnstr with
  | [] -> true
  | ({contents = Queued} :: cnstrs) -> 
      constraints_solved cnstrs 
  | ({contents = Eqn (_cD, _phat, tM, tN)} :: cnstrs) -> 
      if conv (tM, LF.id) (tN, LF.id) then 
        constraints_solved cnstrs
      else         
         false 
 | ({contents = Eqh (_cD, _phat, h1, h2)} :: cnstrs) -> 
      if convHead (h1, LF.id) (h2, LF.id) then 
        constraints_solved cnstrs
      else false 



(* Conversion :  Convertibility modulo alpha *)
(* convTyp (tA,s1) (tB,s2) = true iff [s1]tA = [s2]tB
 * conv (tM,s1) (tN,s2) = true    iff [s1]tM = [s2]tN
 * convSpine (S1,s1) (S2,s2) = true iff [s1]S1 = [s2]S2
 *
 * convSub s s' = true iff s = s'
 *
 * This is on normal forms -- needs to be on whnf.
 *)
and conv sM1 sN2 = conv' (whnf sM1) (whnf sN2)

and conv' sM sN = match (sM, sN) with
  | ((Lam (_, _, tM1), s1), (Lam (_, _, tM2), s2)) ->
      conv (tM1, LF.dot1 s1) (tM2, LF.dot1 s2)

  | ((Tuple (_, tuple1), s1), (Tuple (_, tuple2), s2)) ->
      convTuple (tuple1, s1) (tuple2, s2)

  | ((Root (_,AnnH (head, _tA), spine1), s1), sN) -> 
       conv' (Root (Syntax.Loc.ghost, head, spine1), s1) sN

  | (sM, (Root(_ , AnnH (head, _tA), spine2), s2)) ->
      conv' sM (Root (Syntax.Loc.ghost, head, spine2), s2)

  | ((Root (_, head1, spine1), s1), (Root (_, head2, spine2), s2)) ->
      (dprint (fun () -> "[conv ] check heads ") ; 
        convHead (head1,s1) (head2, s2) && convSpine (spine1, s1) (spine2, s2))

  | _ -> false

and convTuple (tuple1, s1) (tuple2, s2) = match (tuple1, tuple2) with
  | (Last tM1,  Last tM2) ->
      conv (tM1, s1) (tM2, s2)

  | (Cons (tM1, tuple1),  Cons(tM2, tuple2)) ->
         conv (tM1, s1) (tM2, s2)
      && convTuple (tuple1, s1) (tuple2, s2)

  | _ -> false

and convHead (head1, s1) (head2, s2) =  match (head1, head2) with
  | (BVar k1, BVar k2) ->
      k1 = k2

  | (Const c1, Const c2) ->
      c1 = c2

  | (MMVar (MInst(_n, u, _cD, _cPsi, _tA, _cnstr) , (_t', s')), MMVar (MInst(_, w, _, _, _, _ ), (_t'',s''))) ->
      u == w && convSub (LF.comp s' s1) (LF.comp s'' s2) 
        (* && convMSub   -bp *)

  | (MPVar (MPInst(_n, u, _cD, _cPsi, _tA, _cnstr) , (_t', s')), MPVar (MPInst(_, w, _, _, _, _ ), (_t'',s''))) ->
      u == w && convSub (LF.comp s' s1) (LF.comp s'' s2) 
        (* && convMSub   -bp *)

  | (PVar (p, s'), PVar (q, s'')) ->
      p = q && convSub (LF.comp s' s1) (LF.comp s'' s2)
  
  | (FPVar (p, s'), FPVar (q, s'')) ->
      p = q && convSub (LF.comp s' s1) (LF.comp s'' s2)
  
  | (MVar (Offset u , s'), MVar (Offset w, s'')) ->   
      (dprint (fun () -> "convHead - MVar Off MVar Off ") ; 
      u = w && convSub (LF.comp s' s1) (LF.comp s'' s2))
  
  | (MVar (Inst(_n, u, _cPsi, _tA, _cnstr) , s'), MVar (Inst(_, w, _, _, _ ), s'')) -> 
      u == w && convSub (LF.comp s' s1) (LF.comp s'' s2)
        
  | (FMVar (u, s'), FMVar (w, s'')) ->
      u = w && convSub (LF.comp s' s1) (LF.comp s'' s2)
          
  | (Proj (BVar k1, i), Proj (BVar k2, j)) ->
      k1 = k2 && i = j
          
  | (Proj (PVar (p, s'), i), Proj (PVar (q, s''), j)) ->
      p = q && i = j && convSub (LF.comp s' s1) (LF.comp s'' s2)
   (* additional case: p[x] = x ? -bp*)
          
  | (FVar x, FVar y) ->
      x = y
          
  | (_, _) -> (dprint (fun () -> "falls through ") ; 
      false)


and convSpine spine1 spine2 = match (spine1, spine2) with
  | ((Nil, _s1), (Nil, _s2)) ->
      true

  | ((App (tM1, spine1), s1), (App (tM2, spine2), s2)) ->
      (dprint (fun () -> "test spine element ") ; 
      conv (tM1, s1) (tM2, s2) && convSpine (spine1, s1) (spine2, s2))

  | (spine1, (SClo (tS, s), s')) ->
      convSpine spine1 (tS, LF.comp s s')

  | ((SClo (tS, s), s'), spine2) ->
      convSpine (tS, LF.comp s s') spine2

and convSub subst1 subst2 = match (subst1, subst2) with
  | (Shift (psi,n), Shift (psi', k)) ->
      n = k && psi = psi'

  | (SVar (Offset s1, sigma1), SVar (Offset s2, sigma2)) ->
      s1 = s2 && convSub sigma1 sigma2

  | (Dot (f, s), Dot (f', s')) ->
      convFront f f' && convSub s s'

  | (Shift (psi, n), Dot (Head BVar _k, _s')) ->
      convSub (Dot (Head (BVar (n + 1)), Shift (psi, n + 1))) subst2

  | (Dot (Head BVar _k, _s'), Shift (psi, n)) ->
      convSub subst1 (Dot (Head (BVar (n + 1)), Shift (psi, n + 1)))

  | _ ->
      false

and convFront front1 front2 = match (front1, front2) with
  | (Head (BVar i), Head (BVar k)) ->
      i = k

  | (Head (Const i), Head (Const k)) ->
      i = k

  | (Head (MMVar (u, (_t,s))), Head (MMVar (v, (_t',s')))) ->
      u = v && convSub s s' (* && convMSub ... to be added -bp *)

  | (Head (PVar (q, s)), Head (PVar (p, s'))) ->
      p = q && convSub s s'

  | (Head (FPVar (q, s)), Head (FPVar (p, s'))) ->
      p = q && convSub s s'

  | (Head (MVar (u, s)), Head (MVar (v, s'))) ->
      u = v && convSub s s'

  | (Head (FMVar (u, s)), Head (FMVar (v, s'))) ->
      u = v && convSub s s'

  | (Head (Proj (head, k)), Head (Proj (head', k'))) ->
      k = k' && convFront (Head head) (Head head')

  | (Head (FVar x), Head (FVar y)) ->
      x = y

  | (Obj tM, Obj tN) ->
      conv (tM, LF.id) (tN, LF.id)

  | (Head BVar i, Obj tN) ->
      begin match etaContract (norm (tN, LF.id)) with 
        | Head (BVar k) -> i = k 
        | _ -> false
      end 

  | (Obj tN, Head (BVar i)) ->
      begin match etaContract (norm (tN, LF.id)) with 
        | Head (BVar k) -> i = k 
        | _ -> false
      end 

  | (Undef, Undef) ->
      true

  | (_, _) ->
      false


and convMSub subst1 subst2 = match (subst1, subst2) with
  | (MShift n, MShift  k) ->
      n = k

  | (MDot (f, s), MDot (f', s')) ->
      convMFront f f' && convMSub s s'

  | (MShift n, MDot (MV _k, _s')) ->
      convMSub (MDot (MV (n + 1), MShift (n + 1))) subst2

  | (MDot (MV _k, _s'), MShift n) ->
      convMSub subst1 (MDot (MV (n + 1), MShift (n + 1)))

  | _ ->
      false

and convMFront front1 front2 = match (front1, front2) with
  | (CObj cPsi, CObj cPhi) ->
      convDCtx cPsi cPhi
  | (MObj (_phat, tM), MObj(_, tN)) ->
      conv (tM, LF.id) (tN, LF.id)
  | (PObj (phat, BVar k), PObj (phat', BVar k')) ->
      phat = phat' && k = k'
  | (PObj (phat, PVar(p,s)), PObj (phat', PVar(q, s'))) ->
      phat = phat' && p = q && convSub s s'
  | (_, _) ->
      false


and convTyp' sA sB = match (sA, sB) with
  | ((Atom (_, a1, spine1), s1), (Atom (_, a2, spine2), s2)) ->
      if a1 = a2 then 
        (dprint (fun () -> "[convTyp] agree on Atom Constant ") ;
           convSpine (spine1, s1) (spine2, s2))
      else false
(*      a1 = a2 && convSpine (spine1, s1) (spine2, s2)*)

  | ((PiTyp ((TypDecl (_, tA1), _ ), tB1), s1), (PiTyp ((TypDecl (_, tA2), _ ), tB2), s2)) ->
      (* G |- A1[s1] = A2[s2] by typing invariant *)
      convTyp (tA1, s1) (tA2, s2) && convTyp (tB1, LF.dot1 s1) (tB2, LF.dot1 s2)

  | ((Sigma typrec1, s1), (Sigma typrec2, s2)) ->
      convTypRec (typrec1, s1) (typrec2, s2)

  | _ ->
      false



and convTyp sA sB = convTyp' (whnfTyp sA) (whnfTyp sB)




(* convTypRec((recA,s), (recB,s'))
 *
 * Given: cD ; Psi1 |- recA <= type   and cD ; Psi2 |- recB  <= type
 *        cD ; cPsi  |- s <= cPsi       and cD ; cPsi  |- s' <= Psi2
 *
 * returns true iff recA and recB are convertible where
 *    cD ; cPsi |- [s]recA = [s']recB <= type
 *)
and convTypRec sArec sBrec = match (sArec, sBrec) with
  | ((SigmaLast lastA, s), (SigmaLast lastB, s')) ->
      convTyp (lastA, s) (lastB, s')

  | ((SigmaElem (_xA, tA, recA), s), (SigmaElem(_xB, tB, recB), s')) ->
      convTyp (tA, s) (tB, s') && convTypRec (recA, LF.dot1 s) (recB, LF.dot1 s')

  | (_, _) -> (* lengths differ *)
      false

(* convDCtx cPsi cPsi' = true iff
 * cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx
 *)
and convDCtx cPsi cPsi' = match (cPsi, cPsi') with
  | (Null, Null) ->
      true

  | (CtxVar c1, CtxVar c2) ->
      c1 = c2

  | (DDec (cPsi1, TypDecl (_, tA)), DDec (cPsi2, TypDecl (_, tB))) ->
      convTyp (tA, LF.id) (tB, LF.id) && convDCtx cPsi1 cPsi2

(*  | (SigmaDec (cPsi , SigmaDecl(_, typrec )),
     SigmaDec (cPsi', SigmaDecl(_, typrec'))) ->
      convDCtx cPsi cPsi' && convTypRec (typrec, LF.id) (typrec', LF.id)
*)
  | (_, _) ->
      false


(* convCtx cPsi cPsi' = true iff
 * cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx
 *)
let rec convCtx cPsi cPsi' = match (cPsi, cPsi') with
  | (Empty, Empty) ->
      true

  | (Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB))) ->
      convTyp (tA, LF.id) (tB, LF.id) && convCtx cPsi1 cPsi2

  | _ -> false

let rec convSchElem (SchElem(cSome1, typRec1)) (SchElem(cSome2, typRec2)) =
  convCtx cSome1 cSome2 && convTypRec (typRec1, LF.id) (typRec2, LF.id)

let rec convPrefixCtx cPsi cPsi' = match (cPsi, cPsi') with
  | (_ , Empty) ->
      true

  | (Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB))) ->
      convTyp (tA, LF.id) (tB, LF.id) && convCtx cPsi1 cPsi2

  | _ -> false


(* convPrefixTypRec((recA,s), (recB,s'))
 *
 * Given: cD ; Psi1 |- recA <= type   and cD ; Psi2 |- recB  <= type
 *        cD ; cPsi  |- s <= cPsi       and cD ; cPsi  |- s' <= Psi2
 *
 * returns true iff recA and recB are convertible where
 *    cD ; cPsi |-   [s']recB is a prefix of [s]recA
 *)
and convPrefixTypRec sArec sBrec = match (sArec, sBrec) with
  | ((SigmaLast lastA, s), (SigmaLast lastB, s')) ->
      convTyp (lastA, s) (lastB, s')

  | ((SigmaElem (_xA, tA, _recA), s), (SigmaLast tB, s')) ->
      convTyp (tA, s) (tB, s')

  | ((SigmaElem (_xA, tA, recA), s), (SigmaElem(_xB, tB, recB), s')) ->
      convTyp (tA, s) (tB, s') && convPrefixTypRec (recA, LF.dot1 s) (recB, LF.dot1 s')

  | (_, _) -> (* lengths differ *)
      false

let rec prefixSchElem (SchElem(cSome1, typRec1)) (SchElem(cSome2, typRec2)) = 
  convPrefixCtx cSome1 cSome2 && convPrefixTypRec (typRec1, LF.id) (typRec2, LF.id)

(* convHatCtx((psiOpt, l), cPsi) = true iff |cPsi| = |Psihat|
 *
 * where psiOpt is a context variable, l = |Psihat|
 *       cPsi is a object-level context.
 *)
let convHatCtx ((cvar, l), cPsi) =
  let (cvar', l') = dctxToHat cPsi in
    l' = l && cvar = cvar'


(* *********************************************************************** *)
(* Contextual substitutions                                                *)
(* Contextual Weak Head Normalization, Contextual Normalization, and 
   alpha-conversion for contextual substitutions                           *)

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

      ---??? but there is a constructor Syntax.LF.MShift of int... -jd 2010-08-10
   
   - We decided to not provide a constructor Id in msub
     (for similar reasons)
*)


  
(* ************************************************* *)



let rec cnormCSub (cs, t) = begin match cs with
  | CShift k -> CShift k
  | CDot (cPsi, cs) -> 
      CDot (cnormDCtx (cPsi, t) , cnormCSub (cs, t))
end 




(* ************************************************* *)

(*
*)
let rec mctxMDec cD' k = 
  let rec lookup cD k' = match (cD, k') with
    | (Dec (_cD, MDecl(u, tA, cPsi)), 1)
      -> (u, cnormTyp (tA, MShift k), cnormDCtx (cPsi, MShift k)) 
(*        (u, mshiftTyp tA k, mshiftDCtx cPsi k)*)
        
    | (Dec (_cD, PDecl _), 1)
      -> raise (Error.Violation "Expected meta-variable; Found parameter variable")
      
    | (Dec (cD, _), k')
      -> lookup cD (k' - 1)

    | (_ , _ ) -> raise (Error.Violation ("Meta-variable out of bounds -- looking for " ^ string_of_int k ^ "in context"))
  in 
    lookup cD' k


(*
*)
let rec mctxPDec cD k = 
  let rec lookup cD k' = match (cD, k') with
    | (Dec (_cD, PDecl (p, tA, cPsi)),  1)
      -> (p, cnormTyp (tA, MShift k), cnormDCtx (cPsi, MShift k)) 
        (* (p, mshiftTyp tA k, mshiftDCtx cPsi k)*)

(*    | (Dec (_cD, MDecl (p, tA, cPsi)),  1)
      -> (p, mshiftTyp tA k, mshiftDCtx cPsi k)
*)        
    | (Dec (_cD, MDecl  _),  1)
      -> raise (Error.Violation ("Expected parameter variable, but found meta-variable"))
    | (Dec (_cD, CDecl  _),  1)
      -> raise (Error.Violation ("Expected parameter variable, but found context variable"))
    | (Dec (_cD, SDecl  _),  1)
      -> raise (Error.Violation ("Expected parameter variable, but found substitution variable"))

    | (Dec (cD, _),  k')
      -> lookup cD (k' - 1)

    | (_ , _ ) -> raise (Error.Violation "Parameter variable out of bounds")
  in 
    lookup cD k


let rec mctxSDec cD' k = 
  let rec lookup cD k' = match (cD, k') with
    | (Dec (_cD, SDecl(u, cPhi, cPsi)), 1)
      -> (* (u,mshiftDCtx cPhi k, mshiftDCtx cPsi k) *)
        (u, cnormDCtx (cPhi, MShift k), cnormDCtx (cPsi, MShift k))
        
    | (Dec (_cD, PDecl _), 1)
      -> raise (Error.Violation "Expected substitution variable; found parameter variable")
    | (Dec (_cD, MDecl _), 1)
      -> raise (Error.Violation "Expected substitution variable; found meta-variable")
    | (Dec (_cD, CDecl _), 1)
      -> raise (Error.Violation "Expected substitution variable; found context-variable")

    | (Dec (cD, _), k')
      -> lookup cD (k' - 1)

    | (_ , _ ) -> raise (Error.Violation ("Substitution variable out of bounds -- looking for " ^ string_of_int k ^ "in context "))
  in 
    lookup cD' k


(*
*)
let rec mctxCDec cD k = 
  let rec lookup cD k' = match (cD, k') with
    | (Dec (_cD, CDecl (psi, sW, dep)),  1)
      -> (psi, sW)

    | (Dec (_cD, MDecl  _),  1)
      -> raise (Error.Violation ("Expected context variable, but found meta-variable"))
    | (Dec (_cD, PDecl  _),  1)
      -> raise (Error.Violation ("Expected context variable, but found parameter-variable"))
    | (Dec (_cD, SDecl  _),  1)
      -> raise (Error.Violation ("Expected context variable, but found substitution-variable"))
    | (Dec (cD, _),  k')
      -> lookup cD (k' - 1)

    | (_ , _ ) -> raise (Error.Violation "Context variable out of bounds")
  in 
    lookup cD k

let rec mctxCVarPos cD psi = 
  let rec lookup cD k = match cD  with
    | Dec (cD, CDecl(phi, s_cid, _))    -> 
        if psi = phi then 
          (k, s_cid)
        else 
          lookup cD (k+1)
              
    | Dec (cD, _) -> lookup cD (k+1)

    | Empty  -> (dprint (fun () -> "mctxCVarPos \n") ; raise Fmvar_not_found)
  in 
    lookup cD 1


let rec mctxMVarPos cD u = 
  let rec lookup cD k = match cD  with
    | Dec (cD, MDecl(v, tA, cPsi))    -> 
        if v = u then 
         (* (k, (mshiftTyp tA k, mshiftDCtx cPsi k)) *)
         (k, (cnormTyp (tA, MShift k), cnormDCtx (cPsi, MShift k)) )
        else 
          lookup cD (k+1)
              
    | Dec (cD, _) -> lookup cD (k+1)

    | Empty  -> (dprint (fun () -> "mctxMVarPos \n") ; raise Fmvar_not_found)
  in 
    lookup cD 1

let rec mctxPVarPos cD p = 
  let rec lookup cD k = match cD  with
    | Dec (cD, PDecl(q, tA, cPsi))    -> 
        if p = q then 
          (* (k, (mshiftTyp tA k, mshiftDCtx cPsi k)) *)
         (k, (cnormTyp (tA, MShift k), cnormDCtx (cPsi, MShift k)) )
        else 
          lookup cD (k+1)
              
    | Dec (cD, _) -> lookup cD (k+1)

    | Empty  -> (dprint (fun () -> "mctxPVarPos\n") ; raise Fmvar_not_found)
  in 
    lookup cD 1


  (******************************************
     Contextual weak head normal form for 
     computation-level types
   ******************************************)
  let rec normMetaObj mO = match mO with
    | Comp.MetaCtx (loc, cPsi) -> 
        Comp.MetaCtx (loc, normDCtx cPsi)
    | Comp.MetaObj (loc, phat, tM) -> 
        Comp.MetaObj (loc, phat, norm (tM, LF.id))
    | Comp.MetaObjAnn (loc, cPsi, tM) -> 
        Comp.MetaObjAnn (loc, normDCtx cPsi, norm (tM, LF.id))
    | Comp.MetaParam (loc, phat, PVar (PInst (_, {contents = Some h}, _, _, _ ), s)) -> 
        begin match h with
          | BVar k -> let Head h' = LF.bvarSub k s in Comp.MetaParam (loc, phat, h')
          | PVar (q, s') -> normMetaObj (Comp.MetaParam (loc, phat, PVar (q, LF.comp s' s)))
        end 

    | Comp.MetaParam (loc, phat, _ ) ->    mO

  and normMetaSpine mS = match mS with
    | Comp.MetaNil -> mS
    | Comp.MetaApp (mO, mS) -> 
        Comp.MetaApp (normMetaObj mO, normMetaSpine mS)

  let rec normCTyp tau = match tau with 
    | Comp.TypBase (loc, c, mS) -> 
        Comp.TypBase (loc, c, normMetaSpine mS)
    | Comp.TypBox (loc, tA, cPsi)     
      -> Comp.TypBox(loc, normTyp(tA, LF.id), normDCtx cPsi)

    | Comp.TypSub (loc, cPsi, cPsi') 
      -> Comp.TypSub (loc, normDCtx cPsi, normDCtx cPsi')

    | Comp.TypArr (tT1, tT2)   -> 
        Comp.TypArr (normCTyp tT1, normCTyp tT2)

    | Comp.TypCross (tT1, tT2)   -> 
        Comp.TypCross (normCTyp tT1, normCTyp tT2)

    | Comp.TypCtxPi (ctx_dec , tau)      -> 
         Comp.TypCtxPi (ctx_dec, normCTyp tau)

    | Comp.TypPiBox ((MDecl(u, tA, cPsi) , dep), tau)    -> 
        Comp.TypPiBox ((MDecl (u, normTyp (tA, LF.id), normDCtx cPsi), dep),
                       normCTyp tau)

    | Comp.TypPiBox ((PDecl(u, tA, cPsi) , dep), tau)    -> 
        Comp.TypPiBox ((PDecl (u, normTyp (tA, LF.id), normDCtx cPsi), dep),
                       normCTyp tau)

    | Comp.TypPiBox ((SDecl(u, cPhi, cPsi) , dep), tau)    -> 
        Comp.TypPiBox ((SDecl (u, normDCtx cPhi, normDCtx cPsi), dep),
                       normCTyp tau)

    | Comp.TypBool -> Comp.TypBool

  let rec cnormMetaTyp (mC, t) = match mC with
    | Comp.MetaTyp (tA, cPsi) -> 
        let tA'   = normTyp (cnormTyp(tA, t), LF.id) in 
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in 
          Comp.MetaTyp (tA', cPsi')
    | mC -> mC

  let rec cnormMetaObj (mO,t) = match mO with
    | Comp.MetaCtx (loc, cPsi) -> 
        Comp.MetaCtx (loc, cnormDCtx (cPsi,t))
    | Comp.MetaObj (loc, phat, tM) -> 
        Comp.MetaObj (loc, cnorm_psihat phat t, norm (cnorm (tM, t), LF.id))
    | Comp.MetaObjAnn (loc, cPsi, tM) -> 
        Comp.MetaObjAnn (loc, cnormDCtx (cPsi, t), norm (cnorm (tM, t), LF.id))
(*    | Comp.MetaParam (loc, phat, PVar (PInst (_, {contents = Some h}, _, _, _ ), s)) -> 
        begin match h with
          | BVar k -> let Head h' = LF.bvarSub k s in Comp.MetaParam (loc, phat, h')
          | PVar (q, s') -> cnormMetaObj (Comp.MetaParam (loc, phat, PVar (q, LF.comp s' s)), t)
        end 
*)
    | Comp.MetaParam (loc, phat, h ) ->  Comp.MetaParam (loc, phat, cnormHead (h, t))

  and cnormMetaSpine (mS,t) = match mS with
    | Comp.MetaNil -> mS
    | Comp.MetaApp (mO, mS) -> 
        Comp.MetaApp (cnormMetaObj (mO,t), cnormMetaSpine (mS,t))

  let rec cnormCTyp thetaT = 
    begin match thetaT with 
      | (Comp.TypBase (loc, a, mS), t) ->  
          let mS' = cnormMetaSpine (mS, t) in 
            Comp.TypBase (loc, a, mS')
      | (Comp.TypBox (loc, tA, cPsi), t) -> 
          let tA'   = normTyp (cnormTyp(tA, t), LF.id) in 
          let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in 
            Comp.TypBox(loc, tA', cPsi')
              
      | (Comp.TypSub (loc, cPsi, cPsi'), t) -> 
          Comp.TypSub (loc, cnormDCtx(cPsi, t), cnormDCtx(cPsi', t))
            
      | (Comp.TypArr (tT1, tT2), t)   -> 
          Comp.TypArr (cnormCTyp (tT1, t), cnormCTyp (tT2, t))

      | (Comp.TypCross (tT1, tT2), t)   -> 
          Comp.TypCross (cnormCTyp (tT1, t), cnormCTyp (tT2, t))          
            
      | (Comp.TypCtxPi (ctx_dec , tau), t)      -> 
          Comp.TypCtxPi (ctx_dec, cnormCTyp (tau, mvar_dot1 t))
            
      | (Comp.TypPiBox ((MDecl(u, tA, cPsi) , dep), tau), t)    -> 
          let tA'   = normTyp (cnormTyp(tA, t), LF.id) in 
          let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in 
          Comp.TypPiBox ((MDecl (u, tA', cPsi'), dep), 
                         cnormCTyp (tau, mvar_dot1 t))
            
      | (Comp.TypPiBox ((PDecl(u, tA, cPsi) , dep), tau), t)    -> 
          let tA'   = normTyp (cnormTyp(tA, t), LF.id) in 
          let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in 
          Comp.TypPiBox ((PDecl (u, tA', cPsi'), dep), 
                         cnormCTyp (tau, mvar_dot1 t))
            
      | (Comp.TypPiBox ((SDecl(u, cPhi, cPsi) , dep), tau), t)    -> 
          let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in 
          let cPhi' = normDCtx (cnormDCtx(cPhi, t)) in 
          Comp.TypPiBox ((SDecl (u, cPhi', cPsi'), dep), 
                         cnormCTyp (tau, mvar_dot1 t))

      | (Comp.TypClo (tT, t'), t)        -> 
          cnormCTyp (tT, mcomp t' t)
            
      | (Comp.TypBool, _t) -> Comp.TypBool
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
    | (Comp.TypBase (loc, c, mS) , t) -> 
        let mS' = normMetaSpine (cnormMetaSpine (mS, t)) in 
          (Comp.TypBase (loc, c, mS'), m_id)

    | (Comp.TypBox (loc, tA, cPsi), t)     
      -> 
        let tA' = normTyp (cnormTyp(tA, t), LF.id) in 
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in 

          (Comp.TypBox(loc, tA', cPsi') , m_id)


    | (Comp.TypSub (loc, cPsi, cPsi'), t)  
      -> (Comp.TypSub(loc, cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), m_id)

    | (Comp.TypArr (_tT1, _tT2), _t)   -> thetaT

    | (Comp.TypCross (_tT1, _tT2), _t)   -> thetaT

    | (Comp.TypCtxPi _, _)             -> thetaT

    | (Comp.TypPiBox (_, _) , _)       -> thetaT

    | (Comp.TypClo (tT, t'), t)        -> cwhnfCTyp (tT, mcomp t' t)

    | (Comp.TypBool, _t)               -> thetaT




  (* WHNF and Normalization for computation-level terms to be added -bp *)

  (* cnormExp (e, t) = e' 
   
     If cO ; cD  ; cG   |- e <= tau
        cO ; cD' ; cG'  |- [|t|]e <= tau'  where [|t|]cG = cG' and [|t|]tau = tau'
        cO ; cD'        |- t <= cD
    
     then e' = [|t|]e and cO ; cD' ; cG' |- e' <= tau'

  *)

  let rec cnormExp (e, t) = match (e,t) with
    | (Comp.Syn (loc, i), t) -> Comp.Syn (loc, cnormExp' (i, t))

    | (Comp.Rec (loc, f, e), t) -> Comp.Rec (loc, f, cnormExp (e,t))

    | (Comp.Fun (loc, x, e), t) -> Comp.Fun (loc, x, cnormExp (e,t))

    | (Comp.CtxFun (loc, psi, e) , t ) ->  
        Comp.CtxFun (loc, psi, cnormExp (e, mvar_dot1 t))

    | (Comp.MLam (loc, u, e), t) -> Comp.MLam (loc, u, cnormExp (e, mvar_dot1  t))

    | (Comp.Pair (loc, e1, e2), t) -> Comp.Pair (loc, cnormExp (e1, t), cnormExp (e2, t))

    | (Comp.LetPair (loc, i, (x, y, e)), t) -> 
        Comp.LetPair (loc, cnormExp' (i, t), (x, y, cnormExp (e, t)))

    | (Comp.Let (loc, i, (x, e)), t) -> 
        Comp.Let (loc, cnormExp' (i, t), (x, cnormExp (e, t)))

    | (Comp.Box (loc, psihat, tM), t) -> 
        Comp.Box (loc, (cnorm_psihat psihat t), 
                  norm (cnorm (tM, t), LF.id))

    | (Comp.SBox (loc, psihat, sigma), t) -> 
        Comp.SBox (loc, (cnorm_psihat psihat t), 
                  normSub (cnormSub (sigma, t)))

    | (Comp.Case (loc, prag, i, branches), t) -> 
        Comp.Case (loc, prag, cnormExp' (i,t), 
                   List.map (function b -> cnormBranch (b, t)) branches)

    | (Comp.Value v, _ ) -> Comp.Value v

    | (Comp.If (loc, i, e1, e2), t) -> 
        Comp.If (loc, cnormExp' (i,t),  
                 cnormExp (e1, t), cnormExp (e2, t))

    | (Comp.Hole (loc), _) -> Comp.Hole (loc)
 
  and cnormExp' (i, t) = match (i,t) with
    | (Comp.Var _, _ ) -> i 
    | (Comp.DataConst _, _ ) -> i 
    | (Comp.Const _, _ ) -> i 

    | (Comp.Apply (loc, i, e), t) -> Comp.Apply (loc, cnormExp' (i, t), cnormExp (e,t))
        
        
    | (Comp.PairVal (loc, i1, i2), t) -> 
        Comp.PairVal (loc, cnormExp' (i1,t), cnormExp' (i2, t))
    | (Comp.CtxApp (loc, i, cPsi), t) -> Comp.CtxApp (loc, cnormExp' (i, t), normDCtx (cnormDCtx (cPsi, t)))

    | (Comp.MApp (loc, i, (psihat, Comp.NormObj tM)), t) -> 
        Comp.MApp (loc, cnormExp' (i, t), (cnorm_psihat psihat t, Comp.NormObj (norm (cnorm (tM, t), LF.id))))

    | (Comp.MApp (loc, i, (psihat, Comp.NeutObj h)), t) -> 
       begin match normFt (Head (cnormHead (h,t))) with 
          | Head h' ->  Comp.MApp (loc, cnormExp' (i, t), (cnorm_psihat psihat t, Comp.NeutObj h'))
          | _       -> raise (Error.Violation ("Object does not remain head under msub"))
       end 


    | (Comp.MApp (loc, i, (psihat, Comp.SubstObj s)), t) -> 
        let s' = normSub (cnormSub (s,t)) in 
        Comp.MApp (loc, cnormExp' (i, t), (cnorm_psihat psihat t, Comp.SubstObj s'))

    | (Comp.Ann (e, tau), t') -> Comp.Ann (cnormExp (e, t), cnormCTyp (tau, mcomp t' t))

    | (Comp.Equal (loc, i1, i2), t) -> 
        let i1' = cnormExp' (i1, t) in 
        let i2' = cnormExp' (i2, t) in 
         (Comp.Equal (loc, i1', i2'))

    | (Comp.Boolean b, t) -> Comp.Boolean(b)

  and cnormPattern (pat, t) = match pat with 
    | Comp.PatEmpty (loc, cPsi) -> 
        Comp.PatEmpty (loc, cnormDCtx (cPsi, t))
    | Comp.PatMetaObj (loc, mO) -> 
        Comp.PatMetaObj (loc, cnormMetaObj (mO, t))
    | Comp.PatConst (loc, c, patSpine) -> 
        Comp.PatConst (loc, c, cnormPatSpine (patSpine, t))
    | Comp.PatFVar _ -> pat
    | Comp.PatVar _ -> pat
    | Comp.PatPair (loc, pat1, pat2) -> 
        Comp.PatPair (loc, cnormPattern (pat1, t), 
                      cnormPattern (pat2, t))
    | Comp.PatTrue loc -> pat
    | Comp.PatFalse loc -> pat
    | Comp.PatAnn (loc, pat, tau) -> 
        Comp.PatAnn (loc, cnormPattern (pat, t), 
                     cnormCTyp (tau, t))

  and cnormPatSpine (patSpine, t) = match patSpine with 
    | Comp.PatNil -> Comp.PatNil
    | Comp.PatApp (loc, pat, patSpine) -> 
        Comp.PatApp (loc, cnormPattern (pat, t), 
                     cnormPatSpine (patSpine, t))


  (* cnormBranch (BranchBox (cO, cD, (psihat, tM, (tA, cPsi)), e), theta, cs) = 

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

  BROKEN 

  *)
  and cnormBranch = function
    | (Comp.EmptyBranch (loc, cD, pat, t), theta) -> 
         (* THIS IS WRONG. -bp *)
         Comp.EmptyBranch (loc, cD, pat, cnormMSub t)

    | (Comp.Branch (loc, cD, cG, Comp.PatMetaObj (loc', mO), t, e), theta) -> 
    (* cD' |- t <= cD    and   FMV(e) = cD' while 
       cD' |- theta' <= cD0
       cD0' |- theta <= cD0 
     * Hence, no substitution into e at this point -- technically, we
     * need to unify theta' and theta and then create a new cD'' under which the
     * branch makes sense -bp
     *)
        Comp.Branch (loc, cD, cG, Comp.PatMetaObj (loc', normMetaObj mO), cnormMSub t, 
                     cnormExp (e, m_id))

 | (Comp.Branch (loc, cD, cG, pat, t, e), theta) -> 
     (* THIS IS WRONG. -bp *)
     Comp.Branch (loc, cD, cG, pat, 
                  cnormMSub t, cnormExp (e, m_id))

    | (Comp.BranchBox (cO, cD', (cPsi, Comp.NormalPattern(tM, e), t, cs)),  theta) ->
    (* cD' |- t <= cD    and   FMV(e) = cD' while 
       cD' |- theta' <= cD0
       cD0' |- theta <= cD0 
     * Hence, no substitution into e at this point -- technically, we
     * need to unify theta' and theta and then create a new cD'' under which the
     * branch makes sense
     *)
      Comp.BranchBox (cO, cD', (cPsi,
                                Comp.NormalPattern (norm (tM,LF.id), cnormExp (e,m_id)),
                                cnormMSub t,
                                cs))

    | (Comp.BranchBox (cO, cD', (cPsi, Comp.EmptyPattern, t, cs)),  theta) ->
          Comp.BranchBox (cO, cD', (cPsi,
                                    Comp.EmptyPattern,
                                    cnormMSub t,
                                    cs))
        

  let rec cwhnfCtx (cG, t) = match cG with 
    | Empty  -> Empty
    | Dec(cG, Comp.CTypDecl (x, tau)) -> Dec (cwhnfCtx (cG,t), Comp.CTypDecl (x, Comp.TypClo (tau, t)))


  let rec cnormCtx (cG, t) = match cG with
    | Empty -> Empty
    | Dec(cG, Comp.CTypDecl(x, tau)) -> 
        let tdcl = Comp.CTypDecl (x, cnormCTyp (tau, t)) in 
        Dec (cnormCtx (cG, t), tdcl)
    | Dec(cG, Comp.CTypDeclOpt x) -> 
        Dec (cnormCtx (cG, t), Comp.CTypDeclOpt x)

  let rec normCtx cG = match cG with
    | Empty -> Empty
    | Dec(cG, Comp.CTypDecl (x, tau)) -> Dec (normCtx cG, Comp.CTypDecl(x, normCTyp (cnormCTyp (tau, m_id))))

  let rec normMCtx cD = match cD with
    | Empty -> Empty
    | Dec(cD, MDecl(u, tA, cPsi)) -> 
        Dec (normMCtx cD, MDecl (u, normTyp (tA, LF.id), normDCtx cPsi))

    | Dec(cD, PDecl(p, tA, cPsi)) -> 
        Dec (normMCtx cD, PDecl (p, normTyp (tA, LF.id), normDCtx cPsi))

    | Dec(cD, SDecl(u, cPhi, cPsi)) -> 
        Dec (normMCtx cD, SDecl (u, normDCtx cPhi, normDCtx cPsi))


    | Dec(cD, decl) -> 
        Dec(normMCtx cD, decl)


  (* ----------------------------------------------------------- *)
  (* Conversion: Convertibility modulo alpha for 
     computation-level types
  *)



  let rec convMetaObj mO mO' = match (mO , mO) with
    | (Comp.MetaCtx (_loc, cPsi) , Comp.MetaCtx (_ , cPsi'))  -> 
        convDCtx  cPsi cPsi'
    | (Comp.MetaObj (_, _phat, tM) , Comp.MetaObj (_, _phat', tM')) -> 
        conv (tM, LF.id) (tM', LF.id)
    | _ -> false

  and convMetaSpine mS mS' = match (mS, mS') with
    | (Comp.MetaNil , Comp.MetaNil) -> true
    | (Comp.MetaApp (mO, mS) , Comp.MetaApp (mO', mS')) -> 
        convMetaObj mO mO' && convMetaSpine mS mS'

  (* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)

  let rec convCTyp thetaT1 thetaT2 = convCTyp' (cwhnfCTyp thetaT1) (cwhnfCTyp thetaT2)

  and convCTyp' thetaT1 thetaT2 = match (thetaT1, thetaT2) with 
    | ((Comp.TypBase (_, c1, mS1), _t1), (Comp.TypBase (_, c2, mS2), _t2)) ->  
          if c1 = c2 then 
            (* t1 = t2 = id by invariant *)
            convMetaSpine mS1 mS2
          else false

    | ((Comp.TypBox (_, tA1, cPsi1), _t1), (Comp.TypBox (_, tA2, cPsi2), _t2)) (* t1 = t2 = id *)
      -> 
        convDCtx cPsi1 cPsi2
        &&
          convTyp (tA1, LF.id) (tA2, LF.id)
       
    | ((Comp.TypSub (_, cPsi1, cPsi2), _t), (Comp.TypSub (_, cPsi1', cPsi2'), _t'))  (* t1 = t2 = id *)
      -> convDCtx cPsi1 cPsi1'
        &&
          convDCtx cPsi2 cPsi2'

    | ((Comp.TypArr (tT1, tT2), t), (Comp.TypArr (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
        &&
          convCTyp (tT2, t) (tT2', t')

    | ((Comp.TypCross (tT1, tT2), t), (Comp.TypCross (tT1', tT2'), t')) 
      -> convCTyp (tT1, t) (tT1', t') 
        &&
          convCTyp (tT2, t) (tT2', t')


    | ((Comp.TypCtxPi ((_psi, cid_schema, _ ), tT1), t) , (Comp.TypCtxPi ((_psi', cid_schema', _ ), tT1'), t'))
      -> cid_schema = cid_schema'
        && 
          convCTyp (tT1, mvar_dot1 t) (tT1', mvar_dot1 t')

    | ((Comp.TypPiBox ((MDecl(_, tA, cPsi), dep), tT), t), (Comp.TypPiBox ((MDecl(_, tA', cPsi'), dep'), tT'), t'))
      -> dep = dep' 
        &&
          convTyp (cnormTyp (tA, t), LF.id) (cnormTyp (tA', t'), LF.id)
        &&
          convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
        && 
          convCTyp (tT, mvar_dot1 t) (tT', mvar_dot1 t') 

    | ((Comp.TypPiBox ((PDecl(_, tA, cPsi), dep), tT), t), (Comp.TypPiBox ((PDecl(_, tA', cPsi'), dep'), tT'), t'))
      -> dep = dep' 
        &&
          convTyp (cnormTyp (tA, t), LF.id) (cnormTyp (tA', t'), LF.id)
        &&
          convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
        && 
          convCTyp (tT, mvar_dot1 t) (tT', mvar_dot1 t') 

    | ((Comp.TypPiBox ((SDecl(_, cPhi, cPsi), dep), tT), t), (Comp.TypPiBox ((SDecl(_, cPhi', cPsi'), dep'), tT'), t'))
      -> dep = dep' 
        &&
          convDCtx (cnormDCtx (cPhi, t)) (cnormDCtx (cPhi', t'))
        &&
          convDCtx (cnormDCtx (cPsi, t)) (cnormDCtx (cPsi', t'))
        && 
          convCTyp (tT, mvar_dot1 t) (tT', mvar_dot1 t') 



    | ((Comp.TypBool, _t ), (Comp.TypBool, _t')) -> true

    | ( _ , _ ) -> false

(* For now we omit PDecl, SDecl - bp *)

and convSchema (Schema fs) (Schema fs') =  List.for_all2 convSchElem fs fs' 

and convSchElem (SchElem (cPsi, trec)) (SchElem (cPsi', trec')) = 
    convCtx cPsi cPsi'
  &&
    convTypRec (trec, LF.id) (trec', LF.id)


(* ----------------------------------------------------------- *)
(* makePatSub s = Some(s') if s is convertible to a patSub
 *                None otherwise
 *
 * Invariant:
 * If    cPsi |- s : cPsi'
 * and   s = n1 .. nm ^k
 * then  tB iff  n1, .., nm pairwise distinct
 *         and  ni <= k or ni = _ for all 1 <= i <= m
 *)
let rec mkPatSub s = match s with
  | Shift (NoCtxShift, _k) ->
      s

  | Shift (CtxShift (_psi), _k) ->
      s

  | Shift (NegCtxShift _,  _k) ->
      raise (Error (Syntax.Loc.ghost, NotPatSub))

  | Dot (Head (BVar n), s) ->
      let s' = mkPatSub s in
      let rec checkBVar s = match s with
        | Shift (_ , k)            -> n <= k
        | Dot (Head (BVar n'), s') -> n <> n' && checkBVar s'
        | Dot (Undef, s')          ->            checkBVar s' in
      let _ = checkBVar s' in
        Dot (Head (BVar n), s')

  | Dot (Undef, s) ->
      Dot (Undef, mkPatSub s)

  | Dot (Obj tM, s) ->
      begin match whnf (tM, LF.id) with
        | (Root (_, BVar k, Nil), _id) -> Dot (Head (BVar k), mkPatSub s)
        | _                            -> raise (Error (Syntax.Loc.ghost, NotPatSub))
      end

  | _ ->
      raise (Error (Syntax.Loc.ghost, NotPatSub))


let rec makePatSub s = try Some (mkPatSub s) with Error _ -> None

(* ------------------------------------------------------------ *)


(* etaExpandMV cPsi sA s' = tN
 *
 *  cPsi'  |- s'   <= cPsi
 *  cPsi   |- [s]A <= typ
 *
 *  cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMV cPsi sA n s' = etaExpandMV' cPsi (whnfTyp sA) n s'

and etaExpandMV' cPsi sA n s' = match sA with
  | (Atom (_, _a, _tS) as tP, s) ->
      
      let u = newMVar (Some n) (cPsi, TClo(tP,s)) in
        Root (Syntax.Loc.ghost, MVar (u, s'), Nil)

  | (PiTyp ((TypDecl (x, _tA) as decl, _ ), tB), s) ->
      Lam (Syntax.Loc.ghost, x, etaExpandMV (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) n (LF.dot1 s'))



(* etaExpandMMV cD cPsi sA s' = tN
 *
 *  cD ; cPsi'  |- s'   <= cPsi
 *  cD ; cPsi   |- [s]A <= typ
 *
 *  cD ; cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMMV loc cD cPsi sA n s' = etaExpandMMV' loc cD cPsi (whnfTyp sA) n s'

and etaExpandMMV' loc cD cPsi sA n s' = match sA with
  | (Atom (_, _a, _tS) as tP, s) ->
      let u = newMMVar None (cD , cPsi, TClo(tP,s)) in
        Root (loc, MMVar (u, (m_id, s')), Nil)

  | (PiTyp ((TypDecl (x, _tA) as decl, _ ), tB), s) ->
      Lam (loc, x, etaExpandMMV loc cD (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) n (LF.dot1 s'))
 

let rec closed sM = closedW (whnf sM) 

and closedW (tM,s) = match  tM with 
  | Lam (_ , _x, tM) -> closed (tM, LF.dot1 s)
  | Root (_ , h, tS) -> 
      closedHead h &&  
      closedSpine (tS,s)

and closedHead h = match h with 
  | MMVar (MInst (_, {contents = None}, _, _, _, _), _) -> false
  | MVar (Inst (_, {contents = None}, _, _, _), _) -> false
  | PVar (PInst (_, {contents = None}, _, _, _), _) -> false
  | PVar (Offset _, r) -> 
      closedSub r
  | MVar (Offset _, r) -> 
      closedSub r
  | _ -> true

and closedSpine (tS,s) = match tS with
  | Nil -> true
  | App (tN, tS') -> closed (tN, s) && closedSpine (tS', s)
  | SClo(tS', s')  -> closedSpine (tS', LF.comp s' s)

and closedSub s = match s with
  | Shift _ -> true
  | Dot (ft, s) -> closedFront ft && closedSub s

and closedFront ft = match ft with
  | Head h -> closedHead h
  | Obj tM -> closed (tM, LF.id)
  | Undef  -> false


let rec closedTyp sA = closedTypW (whnfTyp sA) 

and closedTypW (tA,s) = match tA with
  | Atom (_, _a, tS) -> closedSpine (tS, s)
  | PiTyp ((t_dec, _ ), tA) -> 
      closedDecl (t_dec, s) && 
      closedTyp (tA, LF.dot1 s)
  | Sigma recA ->  closedTypRec (recA, s)

and closedTypRec (recA, s) = match recA with
  | SigmaLast tA -> closedTyp (tA,s)
  | SigmaElem (_, tA, recA') -> 
      closedTyp (tA, s) &&
      closedTypRec (recA', LF.dot1 s)

and closedDecl (tdecl, s) = match tdecl with 
  | TypDecl (_, tA) -> closedTyp (tA, s)
  | _ -> true


let rec closedDCtx cPsi = match cPsi with
  | Null     -> true
  | CtxVar (CInst (_, {contents = None}, _, _, _)) -> false
  | CtxVar _ -> true
  | DDec (cPsi' , tdecl) -> closedDCtx cPsi' && closedDecl (tdecl, LF.id)
  

let rec closedMetaSpine mS = match mS with
  | Comp.MetaNil -> true
  | Comp.MetaApp (mO, mS) -> 
      closedMetaObj mO && closedMetaSpine mS

and closedMetaObj mO = match mO with
  | Comp.MetaCtx (_, cPsi) -> closedDCtx cPsi 
  | Comp.MetaObj (_, phat, tM) -> 
      closedDCtx (Context.hatToDCtx phat) && closed (tM, LF.id)

let rec closedCTyp cT = match cT with
  | Comp.TypBool -> true
  | Comp.TypBase (_, _c, mS) -> closedMetaSpine mS 
  | Comp.TypBox (_ , tA, cPsi) -> closedTyp (tA, LF.id) && closedDCtx cPsi 
  | Comp.TypSub (_ , cPhi, cPsi) -> closedDCtx cPhi && closedDCtx cPsi 
  | Comp.TypArr (cT1, cT2) -> closedCTyp cT1 && closedCTyp cT2 
  | Comp.TypCross (cT1, cT2) -> closedCTyp cT1 && closedCTyp cT2 
  | Comp.TypCtxPi (_ctx_decl, cT) -> closedCTyp cT
  | Comp.TypPiBox ((ctyp_decl, _ ), cT) -> 
      closedCTyp cT && closedCDecl ctyp_decl  
  | Comp.TypClo (cT, t) -> closedCTyp(cnormCTyp (cT, t))  (* to be improved Sun Dec 13 11:45:15 2009 -bp *)

and closedCDecl ctyp_decl = match ctyp_decl with  
  | MDecl(_, tA, cPsi) -> closedTyp (tA, LF.id) && closedDCtx cPsi 
  | PDecl(_, tA, cPsi) -> closedTyp (tA, LF.id) && closedDCtx cPsi 
  | SDecl(_, cPhi, cPsi) -> closedDCtx cPhi && closedDCtx cPsi 
  | _ -> true

let rec closedGCtx cG = match cG with 
  | Empty -> true
  | Dec(cG, Comp.CTypDecl(_ , cT)) -> 
      closedCTyp cT && closedGCtx cG
  | Dec(cG, Comp.CTypDeclOpt _ ) -> closedGCtx cG
