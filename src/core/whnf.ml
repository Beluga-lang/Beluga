(**

   @author Brigitte Pientka
   modified:  Joshua Dunfield

*)

(* Weak Head Normalization,
 * Normalization, and alpha-conversion
 *)

open Syntax.Int.LF
open Syntax.Int
open Substitution


module R = Store.Cid.DefaultRenderer
module T = Store.Cid.Typ

exception Fmvar_not_found
exception FreeMVar of head
exception NonInvertible
exception InvalidLFHole of Loc.t

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [18])

let rec raiseType cPsi tA = match cPsi with
  | Null -> tA
  | DDec (cPsi', decl) ->
      raiseType cPsi' (PiTyp ((decl, Maybe), tA))

(* isPatSub s = B

   Invariant:

   If    Psi |- s : Psi'
   and   s = n1 .. nm ^k
   then  B iff  n1, .., nm pairwise distinct
   and  ni <= k or ni = _ for all 1 <= i <= m
*)
(* let rec isPatSub = function
  | Shift (_,_k)              -> true
  | Dot (Head(BVar n), s) ->
    let rec checkBVar s' = match s' with
      | Shift (_ , k)           -> n <= k
      | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
      | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s
      | Dot (Undef, s)          -> checkBVar s
      | _                       -> false in
    checkBVar s && isPatSub s
  | Dot (Undef, s)        -> isPatSub s
  | _                     -> false

*)

let rec isPatSVSub = function
  | EmptySub -> true
  | Undefs -> true
  | Shift _              -> true
  | SVar _ -> true
  | Dot (Head(BVar n), s) ->
    let rec checkBVar s' = match s' with
      | Shift k           -> n <= k
      | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
      | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s
      | Dot (Undef, s)          -> checkBVar s
      | _                       -> false in
    checkBVar s && isPatSVSub s
  | Dot (Undef, s)        -> isPatSVSub s
  | _                     -> false




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
let etaContract tM = begin match tM with
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
        | _ -> false (* previously (dprint (fun () -> "[etaSpine] _ ") ; raise (Error.Violation ("etaSpine undefined\n"))) *)
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
  | None -> CInst (Id.mk_name Id.NoName, ref None, sW, Empty, MShift 0)
  | Some name -> CInst (name, ref None, sW, Empty, MShift 0)

(* newMVar n (cPsi, tA) = newMVarCnstr (cPsi, tA, [])
 *
 * Invariant:
 *
 *       tA =   Atom (a, S)
 *   or  tA =   Pi (x:tB, tB')
 *   but tA =/= TClo (_, _)
 *)


let newMVar n (cPsi, tA) = match n with
  | None -> Inst (Id.mk_name (Id.MVarName (T.gen_var_name tA)), ref None, cPsi, tA, ref [], Maybe)
  | Some name -> Inst (name, ref None, cPsi, tA, ref [], if name.Id.was_generated then Maybe else No)

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
  | None -> MInst (Id.mk_name (Id.MVarName (T.gen_var_name tA)), ref None, cD, cPsi, tA, ref [], Maybe)
  | Some name -> MInst (name, ref None, cD, cPsi, tA, ref [], if name.Id.was_generated then Maybe else No)

let newMPVar n (cD, cPsi, tA) = match n with
  | None -> MPInst (Id.mk_name (Id.PVarName (T.gen_var_name tA)), ref None, cD, cPsi, tA, ref [], Maybe)
  | Some name -> MPInst (name, ref None, cD, cPsi, tA, ref [], if name.Id.was_generated then Maybe else No)


let newMSVar n (cD, cPsi, cPhi)  = match n with
  | None -> MSInst (Id.mk_name (Id.SVarName None), ref None, cD, cPsi, cPhi, ref [], Maybe)
  | Some name -> MSInst (name, ref None, cD, cPsi, cPhi, ref [], if name.Id.was_generated then Maybe else No)
  (* Note : cPsi | - s : cPhi *)

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
      let u' = newMVar None (cPsi, Atom (loc, a, SClo (tS, s')))  in 
        (u', Root (Syntax.Loc.ghost, MVar (u', LF.id), Nil)) (* cvar * normal *)


(* lowerMVar1 (u, tA[s]), tA[s] in whnf, see lowerMVar *)
and lowerMVar1 u sA = match (u, sA) with
  | (Inst (_n, r, cPsi, _, _, _), (PiTyp _, _)) ->
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
  | Inst (_n, _r, _cPsi, tA, { contents = [] }, mdep) as u ->
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
      let phat = cnorm_psihat phat t in
        MObj (phat, cnorm(tM, t))
  | SObj (phat, tM)     ->
      let phat = cnorm_psihat phat t in
        SObj (phat, cnormSub(tM, t))
  | PObj (phat, h) ->
    let phat = cnorm_psihat phat t in
    PObj (phat, cnormHead (h, t))
  | CObj (cPsi) -> CObj (cnormDCtx (cPsi, t))

  | MV k ->
      begin match LF.applyMSub k t with  (* DOUBLE CHECK - bp Wed Jan  7 13:47:43 2009 -bp *)
        | PObj(phat, p) ->  PObj(phat, p)
        | MObj(phat, tM) ->  MObj(phat, tM)
        | CObj(cPsi) -> CObj (cPsi)
        | SObj(phat, s) -> SObj(phat,s)
        | MV k'         -> MV k'
        (* other cases impossible *)
      end

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

    | MDot (MObj(_phat, Root(_, MVar (Offset k, Shift 0), Nil)), t') ->
        if k = p then
          Some n
        else lookup (n + 1) t' p

    | MDot (PObj (_phat, PVar (k, Shift 0)), t') ->
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
  | LFHole _ -> tM
  | Root (loc, HClo (i, s, sigma'), tS) ->
    let sigma'' = normSub (LF.comp sigma' sigma) in
    let tS'     = normSpine (tS, sigma) in
      Root (loc, HClo (i, s, sigma''), tS')

  | Root (loc, HMClo (i, s, (theta,sigma')), tS) ->
    let sigma'' = normSub (LF.comp sigma' sigma) in
    let tS'     = normSpine (tS, sigma) in
      Root (loc, HMClo (i, s, (theta,sigma'')), tS')

  | Root (loc, BVar i, tS) ->
      begin match LF.bvarSub i sigma with
        | Obj tM        -> reduce (tM, LF.id) (normSpine (tS, sigma))
        | Head (BVar k) ->  Root (loc, BVar k, normSpine (tS, sigma))
        | Head head     ->  norm (Root (loc, head, normSpine (tS, sigma)), LF.id)
        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
            (* Undef should not happen ! *)
      end

  | Root (_, MMVar (MInst (_, { contents = Some tM}, _, _, _, _, _),(t, r)), tS) ->
      (* constraints associated with u must be in solved form *)
      let tM' = cnorm (tM, t) in
      let tM'' = norm (tM', r) in
      reduce (tM'', sigma) (normSpine (tS, sigma))

  | Root (loc, MMVar (MInst (_, {contents = None}, _, _, Atom _, _, _) as u, (t, r)), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)
      Root (loc, MMVar (u, (t, normSub (LF.comp r sigma))), normSpine (tS, sigma))

  | Root (loc, MMVar (MInst (n, ({contents = None} as r), cD, cPsi, TClo (tA, s'), cnstr, mdep), (t, s)), tS) ->
      Root (loc, MMVar (MInst (n, r, cD, cPsi, normTyp (tA, s'), cnstr, mdep),
                        (t, normSub (LF.comp s sigma))), normSpine (tS, sigma))

  (* Meta-variables *)

  | Root (loc, MVar (Offset _ as u, r), tS) ->
      Root (loc, MVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  | Root (_, MVar (Inst (_, { contents = Some tM}, _, _, _, _), r), tS) ->
      (* constraints associated with u must be in solved form *)
        reduce (norm (tM, r),  sigma) (normSpine (tS, sigma))
      (* reduce (norm (tM, LF.id), LF.comp r sigma) (normSpine (tS, sigma))   *)

  | Root (loc, MVar (Inst (_, {contents = None}, _, Atom _, _, _) as u, r), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)
      let s' =  normSub (LF.comp r sigma) in
      Root (loc, MVar (u, s'), normSpine (tS, sigma))

  | Root (loc, MVar (Inst (n, ({contents = None} as r), cPsi, TClo (tA, s'), cnstr, mdep), s), tS) ->
      let tAn = normTyp (tA, s') in
        norm (Root (loc, MVar (Inst (n, r, cPsi, tAn, cnstr, mdep), s), tS), sigma)

  | Root (_, MVar (Inst (_, {contents = None}, _, _tA, _, _) as u, _r), _tS) ->
      (* Meta-variable is not atomic and tA = Pi x:B1.B2
       * lower u, and normalize the lowered meta-variable
       *)
      let _ = lowerMVar u in
        norm (tM, sigma)

  (* Parameter variables *)
  | Root (loc, FMVar (u, r), tS) ->
      Root (loc, FMVar (u, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  (* Parameter variables *)
  | Root (loc, PVar (p, r), tS) ->
      Root (loc, PVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  (* Parameter variables *)
  | Root (loc, FPVar (p, r), tS) ->
      Root (loc, FPVar (p, normSub (LF.comp r sigma)), normSpine (tS, sigma))

  | Root (loc, MPVar (MPInst (_, { contents = Some h}, _, _, _, _, _),(t, r)), tS) ->
      (* constraints associated with u must be in solved form *)
      let _ = dprint (fun () -> "[norm] MPVar MPInst Some" ) in
      let h' = cnormHead (h, t) in
        begin match h' with
          | BVar i -> begin match LF.bvarSub i (LF.comp r sigma) with
                        | Obj tM -> reduce (tM, LF.id) (normSpine (tS, sigma))
                        | Head (BVar k) -> Root (loc, BVar k , normSpine (tS, sigma))
                        | Head h        -> norm (Root (loc, h, normSpine (tS, sigma)), LF.id)
                        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                            (* Undef should not happen ! *)
                      end
          | PVar (p, s) -> Root (loc, PVar (p, LF.comp(LF.comp s r) sigma), normSpine (tS, sigma))
          | MPVar (q, (t', r')) ->
              norm (Root (loc, MPVar (q, (t', LF.comp r' r)), tS), sigma)
          (* anything else not allowed *)
        end

  | Root (loc, MPVar (MPInst (_n, ({contents = None} as pref), cD, cPsi, tA, cnstr, mDep), (t, r)), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)
      let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
      let p = MPInst (_n, pref, cD, cPsi', tA', cnstr, mDep) in
      Root (loc, MPVar (p, (t, normSub (LF.comp r sigma))), normSpine (tS, sigma))


  (* Constants *)
  | Root (loc, Const c, tS) ->
      Root (loc, Const c, normSpine (tS, sigma))

  (* Projections *)
  | Root (loc, Proj (BVar i, k), tS) ->
      begin match LF.bvarSub i sigma with
        | Head (BVar j)      -> Root (loc, Proj (BVar j, k), normSpine (tS, sigma))
        | Head (PVar (p, s)) ->  norm (Root (loc, Proj (PVar (p, s), k), SClo (tS, sigma)), LF.id)
        | Obj (Tuple (_ , tup)) -> Clo (whnfRedex ((whnfTupleRedex (tup, LF.id) k),  (tS, sigma)))

                (* Root (loc, Proj (PVar (p, s), k), normSpine (tS, sigma)) *)
      end

  | Root (loc, Proj (FPVar(p,r), k),  tS) ->
      Root (loc, Proj (FPVar (p, normSub (LF.comp r sigma)), k), normSpine (tS, sigma))

  | Root (loc, Proj (PVar (q, s), k), tS) ->
      Root (loc, Proj (PVar (q, LF.comp s sigma), k), normSpine (tS, sigma))

  | Root (loc, Proj (MPVar (MPInst (_, { contents = Some h}, _, _, _, _, _),(t, r)), index), tS) ->
      (* constraints associated with u must be in solved form *)
      let _ = dprint (fun () -> "[norm] Proj MPVar MPInst Some" ) in
      let h' = cnormHead (h, t) in
        begin match h' with
          | BVar i -> begin match LF.bvarSub i (LF.comp r sigma) with
                        | Obj tM -> reduce (tM, LF.id) (normSpine (tS, sigma))
                        | Head (BVar k) -> Root (loc, Proj(BVar k , index), normSpine (tS, sigma))
                        | Head h        -> norm (Root (loc, Proj(h, index), tS), sigma)
                        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                            (* Undef should not happen ! *)
                      end
          | PVar (p, s) -> norm (Root (loc, Proj(PVar (p, LF.comp (LF.comp s r) sigma), index), normSpine (tS, sigma)), LF.id)
          | MPVar (q, (t', r')) -> norm (Root (loc, Proj(MPVar (q, (t', LF.comp r' r)), index), tS), sigma)
          (* anything else not allowed *)
        end

  | Root (loc, Proj(MPVar (MPInst (_n, ({contents = None} as pref), cD, cPsi, tA, cnstr, mDep), (t, r)), index), tS) ->
      (* meta-variable is of atomic type; tS = Nil *)
      let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
      let p = MPInst (_n, pref, cD, cPsi', tA', cnstr, mDep) in
      Root (loc, Proj(MPVar (p, (t, normSub (LF.comp r sigma))), index), normSpine (tS, sigma))

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
  | ((LFHole l, _), _) -> raise (InvalidLFHole l)
  | ((Root (_, _, _) as root, s), Nil)    -> norm (root, s)
  | ((Lam (_, _y, tM'), s), App (tM, tS)) -> reduce (tM', Dot (Obj tM, s)) tS
  | ((Clo (tM, s'), s), tS)               ->
(*      reduce (norm (tM, s'), s) tS *)
      reduce (tM , LF.comp s' s) tS
      (* other cases are impossible *)


and normSub s = match s with
  | EmptySub -> EmptySub
  | Undefs -> Undefs
  | Shift _      -> s
  | Dot (ft, s') -> Dot(normFt ft, normSub s')
  | FSVar ( s , n, sigma) -> FSVar (s, n, normSub sigma)
  | SVar (offset, n, s') -> SVar (offset, n, normSub s')
  | MSVar (MSInst (_n, {contents = Some s}, _cD0, _cPhi, _cPsi, _cnstrs, mDep),
    n, (mt, s')) ->
      let s0 = cnormSub (LF.comp (normSub s) (normSub s'), mt) in
      LF.comp (Shift n) s0

  | MSVar (sigma, n, (mt,s')) ->
      MSVar (sigma, n, (mt, normSub s'))

and normFt ft = match ft with
  | Obj tM ->
      etaContract(norm (tM, LF.id))
  | Head (BVar _k)                -> ft
  | Head (FVar _k)                -> ft
  | Head (MPVar (MPInst (_n, { contents = Some h}, _, _, _, _, _), (t, r))) ->
      let h' = cnormHead (h,t) in
        begin match h' with
          | BVar i -> LF.bvarSub i r
          | PVar (p, s) -> Head (PVar (p, LF.comp r s))
          | MPVar (q, (t',r')) -> normFt (Head (MPVar (q, (t', LF.comp r' r))))
        end
  | Head (MPVar (p, (t, s')))     -> Head (MPVar (p, (cnormMSub t, normSub s')))
  | Head (MMVar (MInst (_n, { contents = Some tN}, _, _, _, _, _), (t, s'))) ->
     Obj (norm (cnorm (tN, t), s'))
  | Head (MMVar (u, (t, s')))     -> Head (MMVar (u, (cnormMSub t, normSub s')))
  | Head (MVar (Inst (_, { contents = Some tM}, _, _, _, _), s)) ->
      Obj(norm (tM, s))
  | Head (MVar (u, s'))           -> Head (MVar (u, normSub s'))
  | Head (FMVar (u, s'))          -> Head (FMVar (u, normSub s'))
  | Head (PVar (p, s'))           -> Head (PVar (p, normSub s'))
  | Head (FPVar (p, s'))          -> Head (FPVar (p, normSub s'))
  | Head (Proj (PVar (p, s'), k)) -> Head (Proj (PVar (p, normSub s'), k))
  | Head (Proj(MPVar (MPInst (_n, { contents = Some h}, _, _, _, _, _), (t, r)),k)) ->
      let h' = cnormHead (h,t) in
        begin match h' with
          | BVar i -> let Head h = LF.bvarSub i r in Head (Proj(h,k))
          | PVar (p, s) -> Head (Proj(PVar (p, LF.comp r s), k))
          | MPVar (q, (t',r')) -> Head (Proj(MPVar (q, (t', LF.comp r' r)), k))
        end
  | Head (Proj (MPVar (p, (ms,s')), k)) -> Head (Proj (MPVar (p, (cnormMSub ms, normSub s')), k))
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
  | SigmaLast (n, lastA) ->
      let tA = normTyp (lastA, sigma) in
      SigmaLast(n,tA)

  | SigmaElem (x, tA, recA') ->
      let tA = normTyp (tA, sigma) in
        SigmaElem(x, tA, normTypRec (recA', LF.dot1 sigma))

and normDecl (decl, sigma) = match decl with
  | TypDecl (x, tA) ->
      TypDecl (x, normTyp (tA, sigma))

  | _ -> decl

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
  | HClo _ -> "HClo"
  | HMClo _ -> "HMClo"



and cnorm_psihat (phat: psi_hat) t = match phat with
  | (None , _ ) -> phat
  | (Some (CInst (_n, ({contents = None} as cvar_ref), _schema, _cD, theta)),  k) ->
      (Some (CInst (_n, cvar_ref, _schema, _cD, mcomp theta t)), k)
  | (Some (CInst (_n, {contents = Some cPsi}, _schema, _cD, theta)),  k) ->
      begin match Context.dctxToHat (cnormDCtx (cPsi, mcomp theta t))  with
        | (None, i) -> (None, k+i) (* cnorm_psihat (None, k+i) t *)
        | (Some cvar', i) -> (Some cvar', i+k) (* cnorm_psihat (Some cvar', i+k) t *)
      end
  | (Some (CtxOffset offset), k) ->
      begin match LF.applyMSub offset t with
        | CObj(cPsi) ->
            begin match Context.dctxToHat (cPsi) with
              | (None, i) -> (None, k+i)
              | (Some cvar', i) -> (Some cvar', i+k)
            end
        | MV offset' -> (Some (CtxOffset offset'), k)
      end
  |  _ -> phat


and cnorm (tM, t) = match tM with
    | Lam (loc, y, tN)   -> Lam (loc, y, cnorm (tN, t))

    | Tuple (loc, tuple) -> Tuple (loc, cnormTuple (tuple, t))

    | Clo (tN, s)        -> Clo(cnorm (tN, t), cnormSub(s, t))

    | LFHole _loc -> LFHole _loc
    
    | Root (loc, head, tS) ->
        begin match head with
          | HClo (h, i, sigma) ->
            begin match LF.applyMSub i t with
              | MV k -> Root (loc, HClo (h, k, cnormSub (sigma, t)), cnormSpine (tS, t))
              | SObj (phat, s) ->
                let s' = cnormSub (sigma, t) in
                begin  match LF.bvarSub h (LF.comp s s') with
                  | Head h -> Root (loc, h, cnormSpine (tS, t))
                  | Obj tM -> reduce (tM, s') (cnormSpine (tS, t))
                end
            end
          | HMClo (h, s, (t',sigma)) ->
            (match s with
              | MSInst (_n, {contents = None}, _cD0, _cPhi, _cPsi, _cnstr, _) ->
                let sigma' = cnormSub (sigma,t) in
                let t'' = cnormMSub (mcomp t' t) in
                let tS' = cnormSpine (tS, t) in
                Root(loc, HMClo(h, s, (t'',sigma')), tS')
              | MSInst (_n, {contents = Some s}, _cD0, cPhi, _cPsi, _constr, _) ->
                (* -ac: double check! *)
                begin match LF.bvarSub h (cnormSub (LF.comp (cnormSub (s, t')) sigma, t)) with
                  | Obj tM        ->  reduce (tM, LF.id) (cnormSpine (tS, t))
                  | Head (BVar k) ->  Root (loc, BVar k, cnormSpine (tS, t))
                  | Head head     ->  cnorm (Root (loc, head, cnormSpine (tS, t)), m_id)
                  | Undef         -> raise (Error.Violation ("Encountered undef while solving HClo\n"))
                     (* Undef should not happen ! *)
                end)

          | BVar i -> Root(loc, BVar i, cnormSpine (tS, t))

          | MMVar (MInst (_n, {contents = Some tN}, _D, _cPsi, _tA, _cnstr, _), (t',s')) ->
              (* Assumes tS = Nil because _n is of atomic type *)
              (*   cD, cPsi |- tM <= tA   and   r = (t,s)
               *   cD'      |- t <= cD   and cD' ; cPsi' |- s <= |[t]|cPsi
               *   cD ; |[t]|cPsi |- |[t]|tM <= |[t]|tA
               *   cD' ; cPsi' |- [s]|[t] tM <= [s]|[t]|tA
               *)
              let tN'  = cnorm (tN, t') in
              let tN'' = norm (tN', s') in
                cnorm (tN'', t)

          | MMVar (MInst (_n, {contents = None}, _cD , _cPsi, _tA, _cnstr, _) as u , (t', r)) ->
              (* if constraints_solved (!cnstr) then  *)
                (* raise (Error "Encountered Un-Instantiated MVar with reference ?\n") *)
                let r'  = cnormSub (r, t) in
                let t'' = cnormMSub (mcomp t' t) in
                Root (loc, MMVar(u, (t'', r')), cnormSpine (tS, t))
              (* else
                raise (Error.Violation "uninstantiated meta-variables with unresolved constraints") *)

          | MPVar (MPInst (_n, {contents = Some h}, _D, _cPsi, _tA, _cnstr, mDep), (t',s')) ->
              (*   cD, cPsi |- tM <= tA   and   r = (t,s)
               *   cD'      |- t <= cD   and cD' ; cPsi' |- s <= |[t]|cPsi
               *   cD ; |[t]|cPsi |- |[t]|tM <= |[t]|tA
               *   cD' ; cPsi' |- [s]|[t] tM <= [s]|[t]|tA
               *)
              let _ = dprint (fun () -> "[cnorm] MPVar MPInst Some ") in
              let h'  = cnormHead (h, t') in
                begin match h' with
                  | BVar i -> begin match LF.bvarSub i s' with
                              | Obj tM -> reduce (cnorm (tM, t),LF.id) (cnormSpine (tS, t))
                              | Head (BVar k) -> Root (loc, BVar k , cnormSpine (tS, t))
                              | Head h        -> cnorm (Root (loc, h, cnormSpine (tS, t)), m_id)
                              | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                               (* Undef should not happen ! *)
                    end
                  | Proj(BVar i,k) -> begin match LF.bvarSub i s' with
                                       | Head h -> Root (loc, Proj(h, k), cnormSpine (tS,t))
                                      end
                  | Proj(PVar (p, s),k) ->
                      let _ = dprint (fun () -> "   ..... h' = Proj PVar ") in
                      cnorm(Root (loc, Proj(PVar (p, LF.comp s s'), k), cnormSpine (tS, t)), m_id)
                  | PVar (p, s) ->
                      (dprint (fun () -> "h' = PVar ");
                       (match (s, s') with
                          | Shift 0, Shift 0 -> dprint (fun () -> " compose id ")
                          | Shift 0, _ -> dprint (fun () -> " s' not id ")
                          | _ , _ -> dprint (fun () -> " s  not id "));
                      norm (Root (loc, PVar (p, LF.comp s s'), cnormSpine (tS, t)), LF.id))
                  | MPVar (q, (t', r')) ->
                      cnorm (Root (loc, MPVar (q, (mcomp t' t, LF.comp r' s')), cnormSpine (tS, t)), m_id)
                      (* anything else not allowed *)
                end

          | MPVar (MPInst (_n, ({contents = None} as pref), cD , cPsi, tA, cnstr, mDep), (t', r)) ->
              (* if constraints_solved (!cnstr) then  *)
                (* raise (Error "Encountered Un-Instantiated MVar with reference ?\n") *)
                let r'  = cnormSub (r, t) in
                let t'' = cnormMSub (mcomp t' t) in
                let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
                let p = MPInst (_n, pref, cD, cPsi', tA', cnstr, mDep) in
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

          | MVar (Inst (_n, {contents = Some tM}, _cPsi, _tA, _cnstr, _), r) ->
              (* We could normalize [r]tM *)
              let tM' = norm (tM, r) in
                cnorm (tM', t)

          (*        Root (MVar(Inst (_n, {contents = Some (cnorm (tM, t))}, cPsi, tA, cnstr),
                    cnormSub (r, t)), cnormSpine (tS, t))

          *)
          (* CHECK HERE IF THERE ARE ANY LEFTOVER CONSTRAINTS! *)
          | MVar (Inst (_n, {contents = None}, _cPsi, _tA, cnstr, _) as u , r) ->
              (* if constraints_solved (!cnstr) then *)
                (* raise (Error "Encountered Uninstantiated MVar with reference ?\n") *)
                Root (loc, MVar(u, cnormSub (r, t)), cnormSpine (tS, t))
(*              else
                raise (Error.Violation "uninstantiated meta-variables with unresolved constraints")*)

        (* Parameter variables *)
          | PVar (k, r)
        (* cD' ; cPsi' |- r <= cPsi1
           cD          |- t <= cD'

           [|t|](p[r] . S)  = [r']h . [|t|]S
           where r' = [|t|] r                          *)
            ->
              let pobj_base_cases h = begin match h with
                | PVar(i, r') -> PVar(i, LF.comp r' (cnormSub (r,t)))
                | MPVar (MPInst (_n, ({contents = None} as pref), cD, cPsi, tA, cnstr, mDep) , (mr, r')) ->
                  let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
                  let p' = MPInst (_n, pref, cD, cPsi', tA', cnstr, mDep) in
                    MPVar(p', (mr, LF.comp r' (cnormSub (r,t))))
                | FPVar (p,r') -> FPVar (p, LF.comp r' (cnormSub (r,t)))
                |  _ -> (print_string "encountered parameter object not covered \n"; exit 189)
              end
              in
              begin match LF.applyMSub k t with
              | MV  k'            -> Root (loc, PVar (k', cnormSub (r, t)), cnormSpine (tS, t))
              | PObj(_phat, BVar i) -> begin match LF.bvarSub i (cnormSub (r,t)) with
                    | Head h  -> Root(loc, h, cnormSpine (tS, t))
                    | Obj tM  -> Clo (whnfRedex ((tM, LF.id), (cnormSpine (tS, t), LF.id)))
                end
              | PObj(_phat, Proj(BVar i, k)) -> begin match LF.bvarSub i (cnormSub (r,t)) with
                    | Head h  -> Root(loc, Proj(h,k), cnormSpine (tS, t))
(*                    | Obj tM  -> Clo (whnfRedex ((tM, LF.id), (cnormSpine (tS, t), LF.id))) *)
                end
              | PObj (_phat, MPVar (MPInst (_, {contents = Some h}, _cD, _cPsi, _tA, _, _), (mr, r'))) ->
                  let h' = cnormHead (h, mr) in
                  let _ = dprint (fun () -> "[cnorm] Offset replaced by MPVar MPInst Some ") in
                    begin match h' with
                      | BVar i -> begin match LF.bvarSub i (LF.comp r' r) with
                              | Obj tM -> reduce (cnorm (tM, t),LF.id) (cnormSpine (tS, t))
                              | Head (BVar k) -> Root (loc, BVar k , cnormSpine (tS, t))
                              | Head h        -> cnorm (Root (loc, h, tS), t)
                              | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                               (* Undef should not happen ! *)
                              end
                      | PVar (p, s) -> norm (Root (loc, PVar (p, LF.comp (LF.comp s r') r), cnormSpine (tS, t)), LF.id)
                      | MPVar (q, (ms, s')) -> norm (Root (loc, MPVar (q, (mcomp ms t, LF.comp (LF.comp s' r') r)), cnormSpine (tS, t)), LF.id)
                      (* anything else not allowed *)
                end

              | PObj (_phat, Proj(MPVar (MPInst (_, {contents = Some h}, _cD, _cPsi, _tA, _, _), (mr, r')), k)) ->
                  let h' = cnormHead (h, mr) in
                  let _ = dprint (fun () -> "[cnorm] Offset replaced by Proj MPVar MPInst Some ") in
                    begin match h' with
                      | BVar i -> begin match LF.bvarSub i (LF.comp r' r) with
                              (* | Obj tM -> reduce (cnorm (tM, t),LF.id) (cnormSpine (tS, t))*)
                              | Head (BVar x) -> Root (loc, Proj(BVar x, k) , cnormSpine (tS, t))
                              | Head h        -> cnorm (Root (loc, Proj(h,k), tS), t)
                              | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                               (* Undef should not happen ! *)
                              end
                      | PVar (p, s) -> norm (Root (loc, Proj(PVar (p, LF.comp s r'), k), cnormSpine (tS, t)), LF.id)
                      | MPVar (q, (ms, s')) -> norm (Root (loc, Proj(MPVar (q, (mcomp ms t, LF.comp s' r')), k), cnormSpine (tS, t)), LF.id)
                      (* anything else not allowed *)
                end

              | PObj (_phat, Proj (h,k)) ->
                  let h' = pobj_base_cases h in
                  let tS' = cnormSpine (tS, t) in
                    Root (loc, Proj(h',k), tS')

              | PObj (_phat, h) ->
                  Root (loc,pobj_base_cases h, cnormSpine (tS, t))

              | MObj (_phat, Root(_, MVar _, _)) -> (print_string "whnf MObj 827 crash -- MVar\n"; exit 190)
            end

          | FPVar (p, r) -> Root(loc, FPVar (p, cnormSub (r,t)), cnormSpine (tS, t))

          (* Ignore other cases for destructive (free) parameter variables *)

          (* Constants *)
          | Const c
            -> Root (loc, Const c, cnormSpine (tS, t))

          (* Free Variables *)
          | FVar x ->
              raise (Error.Violation "Encountered a free variable during normalization.")

          (* Projections *)
          | Proj(MPVar (MPInst (_n, {contents = Some h}, _D, _cPsi, _tA, _cnstr, _), (t',s')), k) ->
              (*   cD, cPsi |- tM <= tA   and   r = (t,s)
               *   cD'      |- t <= cD   and cD' ; cPsi' |- s <= |[t]|cPsi
               *   cD ; |[t]|cPsi |- |[t]|tM <= |[t]|tA
               *   cD' ; cPsi' |- [s]|[t] tM <= [s]|[t]|tA
               *)
              let h'  = cnormHead (h, t') in
              let _ = dprint (fun () -> "[cnorm] Proj MPVar MPInst Some ") in
                begin match h' with
                  | BVar i -> begin match LF.bvarSub i s' with
                              | Head (BVar x) -> Root (loc, Proj (BVar x, k) , cnormSpine (tS, t))
                              | Head h        ->
                                  cnorm (Root (loc, Proj (h, k), cnormSpine (tS, t)), m_id)
                              | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                               (* Undef should not happen ! *)
                              end
                  | PVar (p, s) ->
                      (dprint (fun () -> ".... Proj h' = Proj PVar ");
                       (match (s, s') with
                          | Shift 0, Shift 0 -> dprint (fun () -> " compose id ")
                          | Shift 0, _ -> dprint (fun () -> " s' not id ")
                          | _ , _ -> dprint (fun () -> " s  not id "));
                      norm (Root (loc, Proj(PVar (p, LF.comp s s'), k), cnormSpine (tS, t)), LF.id))
                  | MPVar (q, (t', r')) ->
                      cnorm (Root (loc, Proj(MPVar (q, (mcomp t' t, LF.comp r' s')), k), cnormSpine (tS, t)), m_id)
                      (* anything else not allowed *)
                end

          | Proj(MPVar (MPInst (_n, ({contents = None} as pref), cD , cPsi, tA, cnstr, mDep) , (t', r)), k) ->
              (* if constraints_solved (!cnstr) then  *)
                (* raise (Error "Encountered Un-Instantiated MVar with reference ?\n") *)
                let r'  = cnormSub (r, t) in
                let t'' = cnormMSub (mcomp t' t) in
                let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
                let p' = MPInst (_n, pref, cD, cPsi', tA', cnstr, mDep) in
                Root (loc, Proj(MPVar(p', (t'', r')),k), cnormSpine (tS, t))
          | Proj (BVar i, k)
            -> Root (loc, Proj (BVar i, k), cnormSpine (tS, t))

          | Proj (FPVar (p, r), tupleIndex) ->
              Root(loc, Proj (FPVar (p, cnormSub (r,t)), tupleIndex), cnormSpine (tS, t))

          | Proj (PVar (j, s), tupleIndex)
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
                  | PObj(_phat, Proj (PVar (i, s'),  otherTupleIndex)) ->
                      (* This case seems wrong
                         This case is impossible since tuples cannot be nested;
                         PVar (Offset j) must have Sigma-type and hence when we replace j with
                         an object is must be also of Sigma-type (otherwise substitution is
                         ill-typed). But this would mean Proj (PVar (Offset i, s')) needs to
                         have a Sigma-type, which is impossible since it would mean that
                         PVar (Offset i) would need to have a type where Sigma-types are nested.

                         Mon Sep  7 11:41:40 2009 -bp *)
                      Proj (PVar (i, LF.comp s' (cnormSub (s,t))),  otherTupleIndex)


                  | PObj(_phat, PVar (i, s')) ->
                      wrap (PVar (i, LF.comp s' (cnormSub (s,t))))

                  | MV  k'            -> wrap (PVar (k', cnormSub (s, t)))

                  | PObj (_phat, MPVar (MPInst (_, {contents=None}, _cD, _cPsi, _tA, _cnstr, _) as p, (mr, r))) ->
                      wrap  (MPVar (p, (mr, LF.comp r (cnormSub (s,t)))))


                  | PObj (_phat, MPVar (MPInst (_, {contents=Some h}, _cD, _cPsi, _tA, _cnstr, _), (mr, r))) ->
                  let h' = cnormHead (h, mr) in
                  let _ = dprint (fun () -> "[cnorm] Proj PVar Offset replaced by MPVar MPInst Some -1-") in
                  let h''= begin match h' with
                      | BVar i -> begin match LF.bvarSub i (LF.comp r (cnormSub (s,t))) with
                              | Head (BVar k) -> BVar k
                              | Head h        -> h
                              | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                               (* Undef should not happen ! *)
                              end
                      | PVar (p, s') -> PVar (p, LF.comp (LF.comp s' r) (cnormSub (s,t)))
                      | MPVar (q, (t', r')) -> MPVar (q, (mcomp t' mr,  LF.comp (LF.comp r' r) (cnormSub (s,t))))
                      (* anything else not allowed *)
                  end in
                    wrap  h''

                  | PObj(_phat, FPVar (p,s'))  -> wrap (FPVar (p, LF.comp s' (cnormSub (s,t))))

                  | PObj (_phat, h) -> (print_string ("[cnorm]  non-exhaustive match : applying msub to " ^
                                                        what_head head ^ "  yields "                                                                                 ^ what_head h ^  " is undefined ? \n");
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
        let _ = dprint (fun () -> "[cnormHead] MPVar ] ") in
        if isPatSVSub s && isPatMSub ms then
          begin match p with
            | MPInst (_, {contents = None}, _cD, _cPsi, _tA, _cnstr, _) ->
                MPVar (p, (mcomp ms t, s))
            | MPInst (_, {contents = Some h0}, _cD, cPsi, _tA, _cnstr, _) ->
                let _ = dprint (fun () -> "[cnormHead] MPVar - MPInst " ) in
                let h' = cnormHead (h0, ms) in
                  begin match h' with
                    | BVar k -> let Head h1 = LF.bvarSub k s in cnormHead (h1, t)
                    | PVar (p, s') -> (dprint (fun () -> "[cnormHead] MPVar - MPInst - PVar ");
                                       cnormHead (PVar(p, LF.comp s' s), t))
                    | MPVar (q, (ms', s')) ->
                        (dprint (fun () -> "[cnormHead] MPVar - MPInst - MPVar ");
                        cnormHead (MPVar (q, (ms',  LF.comp s' s)), t))
                  end
          end
        else
          (* if this arises the function needs to be generalized to return not a head but "either a head or a term" *)
          raise (Error.Violation "Cannot guarantee that parameter variable remains head(2)")
    | PVar (p, r) ->
        if isPatSVSub r then
	  let Root (_,h,Nil) = cnorm (Root(Syntax.Loc.ghost,h,Nil), t)
	  in h (* This is weird. We should factor out a normHead to avoid this *)
        else
          raise (Error.Violation "Cannot guarantee that parameter variable remains head(3)")

    (* Projections *)
    | Proj(BVar i, k) -> Proj (BVar i, k)
    | Proj(PVar (p,r), k) ->
        let _ = dprint (fun () -> "[cnormHead] Proj - Pvar") in
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
    | EmptySub -> EmptySub
    | Undefs -> Undefs
    | Shift k -> s
    | Dot (ft, s')    -> Dot (cnormFront (ft, t), cnormSub (s', t))
    | SVar (offset, n, s') ->
      begin match LF.applyMSub offset t with
        | MV offset' -> SVar (offset', n, cnormSub (s', t))
        | SObj (_phat, r) ->
              LF.comp (LF.comp (Shift n) r) (cnormSub (s',t))
      end

    | FSVar (s_name, n, s') ->
        FSVar (s_name, n, cnormSub (s', t))

    | MSVar (MSInst (_n, {contents = Some s}, _cD0, _cPhi, _cPsi, _cnstrs, _),
             n, (mt,s')) ->
        let _ = dprint (fun () -> "[cnormSub] MSVar - MSInst") in
        let s0 = cnormSub (LF.comp (normSub s) (normSub s') , mt) in
        let s0' = LF.comp (Shift n) s0 in
          cnormSub (s0', t)

    | MSVar (s ,
             (* s = MSInst (_n, {contents = None}, _cD0, _cPhi, _cPsi, _cnstrs) *)
             n, (mt,s')) ->
          MSVar (s, n, (cnormMSub (mcomp mt t), s'))

  and cnormFront (ft, t) = match ft with
    | Head (HClo (h , i , sigma))  ->
        begin match LF.applyMSub i t with
          | MV k -> Head (HClo (h, k, cnormSub (sigma, t)))
          | SObj (phat, s) ->
            let s' = cnormSub (sigma, t) in
              LF.bvarSub h (LF.comp s s')
        end
    | Head (HMClo (h , s, (theta,sigma)))  ->
      (match s with
        | MSInst (_n, {contents = None}, _cD,_cPhi, _cPsi, _cnstr, _) ->
          let t'' = cnormMSub (mcomp theta t) in
          let s' = cnormSub (sigma, t) in
          Head (HMClo (h, s, (t'', s')))
        | MSInst (_n, {contents = Some s}, _cD, _cPhi, _cPsi, _cnstr, _) ->
          let s' = cnormSub (sigma, t) in
          let t'' = cnormMSub (mcomp theta t) in
          cnormFront (LF.bvarSub h (LF.comp s s'), t'')
      )

    | Head (BVar _ )            -> ft
    | Head (Const _ )           -> ft
    | Head (PVar (i, r)) ->
        begin match LF.applyMSub i t with
          | PObj(_phat, PVar(n, s')) ->
             Head(PVar(n, LF.comp s' (cnormSub (r,t))))
          | PObj (_phat, BVar j)    ->  LF.bvarSub j (cnormSub (r,t))
          | MV k -> Head(PVar (k, cnormSub (r,t)))
          | PObj(_phat, FPVar (p, s)) ->
              Head (FPVar (p, LF.comp s (cnormSub (r,t))))
          | PObj(_phat, MPVar(p, (mt,s))) ->
              let mt' = cnormMSub (mcomp mt t) in
              Head (MPVar (p, (mt', LF.comp s (cnormSub (r,t)))))
          | _ -> raise (Error.Violation "PVar is replaced by an MVar")
              (* other case MObj _ cannot happen *)
        end

    | Head (FPVar (p, r)) ->
        let r'  = cnormSub (r,t) in
          Head (FPVar (p, r'))


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
    | Head (Proj (PVar (i, r), k)) ->
        let r' = cnormSub (r,t) in
        begin match LF.applyMSub i t with
          | PObj (_phat, BVar j)  ->
              begin match LF.bvarSub j r' with
                | Head(BVar j') -> Head(Proj (BVar j', k))
                | Head(PVar (j, s')) -> Head (Proj (PVar (j, s'), k))
                (* other cases impossible for projections *)
              end
          | PObj (_phat, PVar(j, s'))   ->
              Head(Proj (PVar(j, LF.comp s' r'), k))
          | MV j' -> Head (Proj (PVar (j', r'), k))
          (* other case MObj _ cannot happen *)
        end
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
    |  SigmaLast (n,lastA) -> SigmaLast(n, cnormTyp (lastA, t))
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

    | CtxVar (CInst (_n, ({contents = None} as cvar_ref), _schema,  _mctx, theta )) ->
        CtxVar (CInst (_n, cvar_ref , _schema,  _mctx, mcomp theta t))

    | CtxVar (CInst (_n, {contents = Some cPhi} ,_schema, _mctx, theta)) ->
        cnormDCtx (cPhi, mcomp theta t)

    | CtxVar (CtxOffset psi) ->
        begin match LF.applyMSub psi t with
          | CObj (cPsi') -> normDCtx cPsi'
          | MV k -> CtxVar (CtxOffset k)
        end


    | CtxVar (CtxName psi) -> CtxVar (CtxName psi)


    | DDec(cPsi, decl) ->
        DDec(cnormDCtx(cPsi, t), cnormDecl(decl, t))
and cnormMTyp (mtyp, t) = match mtyp with
    | MTyp (tA, cPsi, dep) ->
        let tA'   = normTyp (cnormTyp(tA, t), LF.id) in
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
          MTyp (tA', cPsi', dep)
    | PTyp (tA, cPsi, dep) ->
        let tA'   = normTyp (cnormTyp(tA, t), LF.id) in
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
          PTyp (tA', cPsi', dep)
    | STyp (cPhi, cPsi, dep) ->
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
        let cPhi' = normDCtx (cnormDCtx(cPhi, t)) in
          STyp (cPhi', cPsi', dep)
    | CTyp (sW, dep) -> CTyp (sW, dep)

and cnormMSub t = match t with
  | MShift _n -> t
  | MDot (MObj(phat, tM), t) ->
      MDot (MObj (cnorm_psihat phat m_id,
                  norm (cnorm (tM, m_id), LF.id)) , cnormMSub t)
  | MDot (SObj(phat, s), t) ->
      MDot (SObj(cnorm_psihat phat m_id,
                normSub (cnormSub (s, m_id))), cnormMSub t)
  | MDot (CObj (cPsi), t) ->
        let t' = cnormMSub t in
        let cPsi' = cnormDCtx (normDCtx cPsi, m_id) in
          MDot (CObj cPsi' , t')
  | MDot (PObj(phat, h), t) ->
    MDot (PObj(cnorm_psihat phat m_id, cnormHead (h, m_id)), cnormMSub t)

  | MDot (MV u, t) -> MDot (MV u, cnormMSub t)

  | MDot (MUndef, t) -> MDot (MUndef, cnormMSub t)

(* ************************************************************** *)


and normKind sK = match sK with
  | (Typ, _s) ->
      Typ

  | (PiKind ((decl, dep), tK), s) ->
      PiKind ((normDecl (decl, s), dep), normKind (tK, LF.dot1 s))

and normDCtx cPsi = match cPsi with
  | Null -> Null

  | CtxVar (CInst (_n, {contents = None} , _schema, _mctx, _theta )) -> cPsi

  | CtxVar (CInst (_n, {contents = Some cPhi} ,_schema, _mctx, theta)) ->
      normDCtx (cnormDCtx (cPhi,theta))

  | CtxVar psi -> CtxVar psi

  | DDec (cPsi1, TypDecl (x, Sigma typrec)) ->
      let cPsi1 = normDCtx cPsi1 in
      let typrec = normTypRec (typrec, LF.id) in
        DDec (cPsi1, TypDecl (x, Sigma typrec))

  | DDec (cPsi1, decl) ->
      DDec (normDCtx cPsi1, normDecl (decl, LF.id))

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
  | (Root (loc, MPVar (MPInst (_, {contents = Some h}, _cD, _cPsi, _tA, _, _), (t,r)), tS), sigma) ->
      (* constraints associated with q must be in solved form *)
      let h' = cnormHead (h, t) in
        begin match h' with
          | BVar i -> begin match LF.bvarSub i (LF.comp r sigma) with
                        | Obj tM -> whnfRedex ((tM, LF.id), (tS, sigma))
                        | Head (BVar k) -> (Root (loc, BVar k , SClo (tS, sigma)), LF.id)
                        | Head h        -> whnf (Root (loc, h, SClo (tS, sigma)), LF.id)
                        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                            (* Undef should not happen ! *)
                      end
          | PVar (p, s) -> whnf (Root (loc, PVar (p, LF.comp (LF.comp s r) sigma), SClo (tS, sigma)), LF.id)
          | MPVar (q, (t', r')) -> whnf (Root (loc, MPVar (q, (t', LF.comp r' r)), SClo (tS, sigma)), LF.id)
        end

  | (Root (loc, MPVar (MPInst (n, ({contents = None} as pref), cD, cPsi, tA, cnstr, mDep), (t,r)), tS), sigma) ->
      (* constraints associated with q must be in solved form *)
      let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
      let p' = MPInst (n, pref, cD, cPsi', tA', cnstr, mDep) in
        (Root (loc, MPVar (p', (t, LF.comp r sigma)),  SClo(tS, sigma)), LF.id)

  | (Root (_, MMVar (MInst (_, {contents = Some tM}, _cD, _cPsi, _tA, _, _), (t,r)), tS), sigma) ->
      (* constraints associated with u must be in solved form *)
      let tM' = cnorm (tM, t) in
      let tM'' = norm (tM', r) in
      let sR =  whnfRedex ((tM'', sigma), (tS, sigma)) in

(*      let sR =  whnfRedex ((tM', LF.comp r sigma), (tS, sigma)) in *)
        sR

  | (Root (loc, MMVar (MInst (n, ({contents = None} as uref), cD, cPsi, tA, cnstr, mdep), (t, r)), tS), sigma) ->
      (* note: we could split this case based on tA;
       *      this would avoid possibly building closures with id
       *)
      begin match whnfTyp (tA, LF.id) with
        | (Atom (loc', a, tS'), _s (* id *)) ->
            (* meta-variable is of atomic type; tS = Nil  *)
            let u' = MInst (n, uref, cD, cPsi, Atom (loc', a, tS'), cnstr, mdep) in
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
      (Root (loc, MVar (u, LF.comp (normSub r) sigma), SClo (tS, sigma)), LF.id)

  | (Root (loc, FMVar (u, r), tS), sigma) ->
      (Root (loc, FMVar (u, LF.comp (normSub r) sigma), SClo (tS, sigma)), LF.id)

  | (Root (_, MVar (Inst (_, {contents = Some tM}, _cPsi, _tA, _, _), r), tS), sigma) ->
      (* constraints associated with u must be in solved form *)
      let r' = normSub r in
      let tM' = begin match r' with
                  | Shift 0 -> tM
                  | _ ->   norm(tM, r') (* this can be expensive -bp *)
                end  in
     (* it does not work to call whnfRedex ((tM, LF.comp r sigma), (tS, sigma)) -bp *)
      let sR =  whnfRedex ((tM',  sigma), (tS, sigma)) in
        sR

  | (Root (loc, MVar (Inst (n, ({contents = None} as uref), cPsi, tA, cnstr, mdep) as u, r), tS) as tM, sigma) ->
      (* note: we could split this case based on tA;
       *      this would avoid possibly building closures with id
       *)
      let r' = normSub r in
      begin match whnfTyp (tA, LF.id) with
        | (Atom (loc', a, tS'), _s (* id *)) ->
            (* meta-variable is of atomic type; tS = Nil  *)
            let u' = Inst (n, uref, cPsi, Atom (loc', a, tS'), cnstr, mdep) in
              (Root (loc, MVar (u', LF.comp r' sigma), SClo (tS, sigma)), LF.id)
        | (PiTyp _, _s)->
            (* Meta-variable is not atomic and tA = Pi x:B1.B2:
             * lower u, and normalize the lowered meta-variable.
             * Note: we may expose and compose substitutions twice.
             *)
            let _ = lowerMVar u in
              whnf (tM, sigma)
      end

  (* Parameter variable *)
  | (Root (loc, PVar (p, r), tS), sigma) ->
      (Root (loc, PVar (p, LF.comp (normSub r) sigma), SClo (tS, sigma)), LF.id)

  | (Root (loc, FPVar (p, r), tS), sigma) ->
      (Root (loc, FPVar (p, LF.comp (normSub r) sigma), SClo (tS, sigma)), LF.id)

  | (Root (loc, Proj(FPVar (p, r), k), tS), sigma) ->
      let fpvar = FPVar (p, LF.comp (normSub r) sigma) in
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

  | (Root (loc, Proj (PVar (q, s), k), tS), sigma) ->
      (Root (loc, Proj (PVar (q, LF.comp s sigma), k), SClo (tS, sigma)), LF.id)

  (* Free variables *)
  | (Root (loc, FVar x, tS), sigma) ->
      (Root (loc, FVar x, SClo (tS, sigma)), LF.id)
  | (Root (loc, Proj(MPVar (MPInst (_, {contents = Some h}, _cD, _cPsi, _tA, _, _), (t,r)), k), tS), sigma) ->
      (* constraints associated with q must be in solved form *)
      let h' = cnormHead (h, t) in
        begin match h' with
          | BVar i -> begin match LF.bvarSub i (LF.comp r sigma) with
                        | Head (BVar x) -> (Root (loc, Proj(BVar x,k) , SClo (tS, sigma)), LF.id)
                        | Head h        -> (Root (loc, Proj(h, k), SClo (tS, sigma)), LF.id)
                        | Undef         -> raise (Error.Violation ("Looking up " ^ string_of_int i ^ "\n"))
                            (* Undef should not happen ! *)
                      end
          | PVar (p, s) -> (Root (loc, Proj(PVar (p, LF.comp (LF.comp s r) sigma),k), SClo (tS, sigma)), LF.id)
          | MPVar (q, (t', r')) -> (Root (loc, Proj(MPVar (q, (t', LF.comp (LF.comp r' r) sigma)),k), SClo (tS, sigma)), LF.id)
        end


  | (Root (loc, Proj(MPVar (MPInst (n, ({contents = None} as pref), cD, cPsi, tA, cnstr, mDep), (t,r)), k), tS), sigma) ->
      (* constraints associated with q must be in solved form *)
      let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
      let p' = MPInst (n, pref, cD, cPsi', tA', cnstr, mDep) in
        (Root (loc, Proj(MPVar (p', (t, LF.comp r sigma)) , k), SClo(tS, sigma)), LF.id)

  | (Root (_, Proj (MPVar _, _), _), _) -> (dprint (fun () -> "oops 3"); exit 3)

  | (LFHole _loc, _s) -> (LFHole _loc, _s)
  | _ -> (dprint (fun () -> "oops 4"); exit 4)

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
  | ((LFHole l, s1), _) -> raise (InvalidLFHole l)
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

and whnfTupleRedex (tup,s) k = match (tup, k) with
  | (Last tM, 1)  -> (tM,s)
  | (Cons (tM, _rest) , 1) -> (tM,s)
  | (Cons (_ , rest) , k) -> whnfTupleRedex (rest,s) (k-1)

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
      convHead (head1,s1) (head2, s2) && convSpine (spine1, s1) (spine2, s2)

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

  | (MMVar (MInst(_n, u, _cD, _cPsi, _tA, _cnstr, _) , (_t', s')), MMVar (MInst(_, w, _, _, _, _ , _), (_t'',s''))) ->
      u == w && convSub (LF.comp s' s1) (LF.comp s'' s2)
        (* && convMSub   -bp *)

  | (MPVar (MPInst(_n, u, _cD, _cPsi, _tA, _cnstr, _) , (_t', s')), MPVar (MPInst(_, w, _, _, _, _, _ ), (_t'',s''))) ->
      u == w && convSub (LF.comp s' s1) (LF.comp s'' s2)
        (* && convMSub   -bp *)

  | (PVar (p, s'), PVar (q, s'')) ->
      p = q && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (FPVar (p, s'), FPVar (q, s'')) ->
      p = q && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (MVar (Offset u , s'), MVar (Offset w, s'')) ->
      u = w && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (MVar (Inst(_n, u, _cPsi, _tA, _cnstr, _) , s'), MVar (Inst(_, w, _, _, _ , _), s'')) ->
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
      conv (tM1, s1) (tM2, s2) && convSpine (spine1, s1) (spine2, s2)

  | (spine1, (SClo (tS, s), s')) ->
      convSpine spine1 (tS, LF.comp s s')

  | ((SClo (tS, s), s'), spine2) ->
      convSpine (tS, LF.comp s s') spine2

and convSub subst1 subst2 = match (subst1, subst2) with
  | (EmptySub, _) -> true (* this relies on the assumption that both are the same type... *)
  | (_,EmptySub) -> true
  | (Undefs,_) -> true (* hopefully Undefs only show up with empty domain? *)
  | (_,Undefs) -> true
  | (Shift n, Shift k) -> n = k 
  | (SVar (s1, k, sigma1), SVar (s2, k', sigma2)) ->
     k = k' &&
     s1 = s2 &&
     convSub sigma1 sigma2

  | (Dot (f, s), Dot (f', s')) ->
      convFront f f' && convSub s s'

  | (Shift n, Dot (Head BVar _k, _s')) ->
      convSub (Dot (Head (BVar (n + 1)), Shift (n + 1))) subst2

  | (Dot (Head BVar _k, _s'), Shift n) ->
      convSub subst1 (Dot (Head (BVar (n + 1)), Shift (n + 1)))

  | _ ->
     (dprint (fun () -> "[convSub] unspecified case"); false)

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
  | ((Atom (_, (a, b), spine1), s1), (Atom (_, (a', b'), spine2), s2)) ->
      if a = a' && b = b' then
           convSpine (spine1, s1) (spine2, s2)
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
  | ((SigmaLast(_, lastA), s), (SigmaLast(_, lastB), s')) ->
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
  | ((SigmaLast (_,lastA), s), (SigmaLast (_,lastB), s')) ->
      convTyp (lastA, s) (lastB, s')

  | ((SigmaElem (_xA, tA, _recA), s), (SigmaLast(_, tB), s')) ->
      convTyp (tA, s) (tB, s')

  | ((SigmaElem (_xA, tA, recA), s), (SigmaElem(_xB, tB, recB), s')) ->
      convTyp (tA, s) (tB, s') && convPrefixTypRec (recA, LF.dot1 s) (recB, LF.dot1 s')

  | (_, _) -> (* lengths differ *)
      false

let prefixSchElem (SchElem(cSome1, typRec1)) (SchElem(cSome2, typRec2)) =
  convPrefixCtx cSome1 cSome2 && convPrefixTypRec (typRec1, LF.id) (typRec2, LF.id)

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

let mctxLookup cD k = 
 let rec lookup cD k' = 
   match (cD, k') with
    | (Dec (_cD, Decl (u, mtyp)), 1)
      -> (u, cnormMTyp (mtyp, MShift k))
     | (Dec (_cD, DeclOpt u), 1)
      -> raise (Error.Violation "Expected declaration to have type")
    | (Dec (cD, _), k') -> lookup cD (k' - 1)
    | (Empty , _ ) -> raise (Error.Violation ("Meta-variable out of bounds -- looking for " ^ string_of_int k ^ "in context"))
 in
 lookup cD k

(* ************************************************* *)

(* Note: If we don't actually handle this particular exception gracefully, then
   there's no need to have these four distinct functions. Inline them and let it throw
   the match exception instead. *)
let mctxMDec cD' k =
 match (mctxLookup cD' k) with
   | (u, MTyp (tA, cPsi, _)) -> (u, tA, cPsi)
   | _ -> raise (Error.Violation "Expected ordinary meta-variable")

let mctxPDec cD k =
  match (mctxLookup cD k) with
    | (u, PTyp (tA, cPsi, _)) -> (u, tA, cPsi)
    | _ -> raise (Error.Violation ("Expected parameter variable"))

let mctxSDec cD' k =
  match (mctxLookup cD' k) with
    | (u, STyp (cPhi, cPsi, _)) -> (u, cPhi, cPsi)
    | _ -> raise (Error.Violation "Expected substitution variable")

let mctxCDec cD k =
  match (mctxLookup cD k) with
    | (u, CTyp (sW, _)) -> (u, sW)
    | _ -> raise (Error.Violation ("Expected context variable"))

let mctxMVarPos cD u =
  let rec lookup cD k = match cD with
    | Dec (cD, Decl(v, mtyp))    ->
        if v = u then
         (k, cnormMTyp (mtyp, MShift k))
        else
          lookup cD (k+1)
    | Dec (cD, _) -> lookup cD (k+1)
    | Empty  -> raise Fmvar_not_found
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
        Comp.MetaObj (loc, cnorm_psihat phat m_id, norm (tM, LF.id))
    | Comp.MetaObjAnn (loc, cPsi, tM) ->
        Comp.MetaObjAnn (loc, normDCtx cPsi, norm (tM, LF.id))
    | Comp.MetaSObj (loc, phat, tM) ->
        Comp.MetaSObj (loc, cnorm_psihat phat m_id, normSub tM)
    | Comp.MetaSObjAnn (loc, cPsi, tM) ->
        Comp.MetaSObjAnn (loc, normDCtx cPsi, normSub tM)

    | Comp.MetaParam (loc, phat, _ ) ->    mO

  and normMetaSpine mS = match mS with
    | Comp.MetaNil -> mS
    | Comp.MetaApp (mO, mS) ->
        Comp.MetaApp (normMetaObj mO, normMetaSpine mS)
 
  let normMTyp = function
    | MTyp (tA, cPsi, dep) -> MTyp (normTyp (tA, LF.id), normDCtx cPsi, dep)
    | PTyp (tA, cPsi, dep) -> PTyp (normTyp (tA, LF.id), normDCtx cPsi, dep)
    | STyp (cPhi,cPsi, dep) -> STyp (normDCtx cPhi, normDCtx cPsi, dep)
    | CTyp (g,d) -> CTyp (g,d)

  let normMetaTyp = function
    | Comp.MetaTyp (tA, cPsi) -> Comp.MetaTyp (normTyp (tA, LF.id), normDCtx cPsi)
    | Comp.MetaParamTyp (tA, cPsi) -> Comp.MetaParamTyp (normTyp (tA, LF.id), normDCtx cPsi)
    | Comp.MetaSubTyp (cPhi,cPsi) -> Comp.MetaSubTyp (normDCtx cPhi, normDCtx cPsi)
    | Comp.MetaSchema (g) -> Comp.MetaSchema (g)

  let rec normCTyp tau = match tau with
    | Comp.TypBase (loc, c, mS) ->
        Comp.TypBase (loc, c, normMetaSpine mS)
    | Comp.TypCobase (loc, c, mS) ->
        Comp.TypCobase (loc, c, normMetaSpine mS)
    | Comp.TypBox (loc, mT)
      -> Comp.TypBox(loc, normMetaTyp mT)
    | Comp.TypParam (loc, tA, cPsi)
      -> Comp.TypParam(loc, normTyp(tA, LF.id), normDCtx cPsi)
    | Comp.TypSub (loc, cPsi, cPsi')
      -> Comp.TypSub (loc, normDCtx cPsi, normDCtx cPsi')

    | Comp.TypArr (tT1, tT2)   ->
        Comp.TypArr (normCTyp tT1, normCTyp tT2)

    | Comp.TypCross (tT1, tT2)   ->
        Comp.TypCross (normCTyp tT1, normCTyp tT2)

    | Comp.TypPiBox ((Decl(u, mtyp)), tau)    ->
        Comp.TypPiBox ((Decl (u, normMTyp mtyp)),
                       normCTyp tau)

    | Comp.TypBool -> Comp.TypBool

  let cnormMetaTyp (mC, t) = match mC with
    | Comp.MetaTyp (tA, cPsi) ->
        let tA'   = normTyp (cnormTyp(tA, t), LF.id) in
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
          Comp.MetaTyp (tA', cPsi')
    | Comp.MetaParamTyp (tA, cPsi) ->
        let tA'   = normTyp (cnormTyp(tA, t), LF.id) in
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
          Comp.MetaParamTyp (tA', cPsi')
    | Comp.MetaSubTyp (cPhi, cPsi) ->
        let cPhi' = normDCtx (cnormDCtx(cPhi, t)) in
        let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
          Comp.MetaSubTyp (cPhi', cPsi')
    | mC -> mC

  let rec cnormMetaObj (mO,t) = match mO with
    | Comp.MetaCtx (loc, cPsi) ->
        Comp.MetaCtx (loc, cnormDCtx (cPsi,t))
    | Comp.MetaObj (loc, phat, tM) ->
        Comp.MetaObj (loc, cnorm_psihat phat t, norm (cnorm (tM, t), LF.id))
    | Comp.MetaObjAnn (loc, cPsi, tM) ->
        Comp.MetaObjAnn (loc, cnormDCtx (cPsi, t), norm (cnorm (tM, t), LF.id))
    | Comp.MetaSObj (loc, phat, sigma) ->
        Comp.MetaSObj (loc, cnorm_psihat phat t, normSub (cnormSub (sigma, t)))
    | Comp.MetaSObjAnn (loc, cPsi, sigma) ->
        Comp.MetaSObjAnn (loc, cnormDCtx (cPsi, t), normSub (cnormSub (sigma, t)))
    | Comp.MetaParam (loc, phat, h ) ->  Comp.MetaParam (loc, cnorm_psihat phat t, cnormHead (h, t))

  and cnormMetaSpine (mS,t) = match mS with
    | Comp.MetaNil -> mS
    | Comp.MetaApp (mO, mS) ->
        Comp.MetaApp (cnormMetaObj (mO,t), cnormMetaSpine (mS,t))
  
  let cnormCDecl (cdecl, t) = match cdecl with
    | Decl(u, mtyp) -> Decl (u, cnormMTyp (mtyp, t))

  let rec cnormCTyp thetaT =
    begin match thetaT with
      | (Comp.TypBase (loc, a, mS), t) ->
          let mS' = cnormMetaSpine (mS, t) in
            Comp.TypBase (loc, a, mS')
      | (Comp.TypCobase (loc, a, mS), t) ->
          let mS' = cnormMetaSpine (mS, t) in
            Comp.TypCobase (loc, a, mS')

      | (Comp.TypBox (loc, cT), t) ->
	 Comp.TypBox (loc, cnormMetaTyp (cT, t))

      | (Comp.TypParam (loc, tA, cPsi), t) ->
          let tA'   = normTyp (cnormTyp(tA, t), LF.id) in
          let cPsi' = normDCtx (cnormDCtx(cPsi, t)) in
            Comp.TypParam(loc, tA', cPsi')

      | (Comp.TypSub (loc, cPsi, cPsi'), t) ->
          Comp.TypSub (loc, cnormDCtx(cPsi, t), cnormDCtx(cPsi', t))

      | (Comp.TypArr (tT1, tT2), t)   ->
          Comp.TypArr (cnormCTyp (tT1, t), cnormCTyp (tT2, t))

      | (Comp.TypCross (tT1, tT2), t)   ->
          Comp.TypCross (cnormCTyp (tT1, t), cnormCTyp (tT2, t))

      | (Comp.TypPiBox (cdecl, tau), t)    ->
          let cdecl' = cnormCDecl (cdecl, t) in
          Comp.TypPiBox ((cdecl'),
                         cnormCTyp (tau, mvar_dot1 t))

      | (Comp.TypClo (tT, t'), t)        ->
          cnormCTyp (tT, mcomp t' t)

      | (Comp.TypBool, _t) -> Comp.TypBool
    end

  let rec cnormCKind (cK, t) = match cK with
    | Comp.Ctype loc -> Comp.Ctype loc
    | Comp.PiKind (loc, cdecl , cK) ->
        let cdecl' = cnormCDecl (cdecl, t) in
          Comp.PiKind (loc, cdecl', cnormCKind (cK, mvar_dot1 t))

(*
     cD        |- [|t2|]cG2 = [|t1|]cG1 = cG'
     cD ; cG'  |- [|t2|]tT2 = [|t1|]tT2 = tT
  *)


  let rec cwhnfCTyp thetaT = match thetaT with
    | (Comp.TypBase (loc, c, mS) , t) ->
        let mS' = normMetaSpine (cnormMetaSpine (mS, t)) in
          (Comp.TypBase (loc, c, mS'), m_id)
    | (Comp.TypCobase (loc, c, mS) , t) ->
        let mS' = normMetaSpine (cnormMetaSpine (mS, t)) in
          (Comp.TypCobase (loc, c, mS'), m_id)

    | (Comp.TypBox (loc, cT), t)  -> (Comp.TypBox(loc, cnormMetaTyp (cT, t)), m_id) 

    | (Comp.TypSub (loc, cPsi, cPsi'), t)
      -> (Comp.TypSub(loc, cnormDCtx(cPsi, t), cnormDCtx(cPsi', t)), m_id)

    | (Comp.TypArr (_tT1, _tT2), _t)   -> thetaT

    | (Comp.TypCross (_tT1, _tT2), _t)   -> thetaT

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

    | (Comp.Cofun (loc, bs), t) ->
        Comp.Cofun (loc, List.map (fun (cps, e) -> (cps, cnormExp (e, t))) bs)

    | (Comp.MLam (loc, u, e), t) -> Comp.MLam (loc, u, cnormExp (e, mvar_dot1  t))

    | (Comp.Pair (loc, e1, e2), t) -> Comp.Pair (loc, cnormExp (e1, t), cnormExp (e2, t))

    | (Comp.LetPair (loc, i, (x, y, e)), t) ->
        Comp.LetPair (loc, cnormExp' (i, t), (x, y, cnormExp (e, t)))

    | (Comp.Let (loc, i, (x, e)), t) -> 
        Comp.Let (loc, cnormExp' (i, t), (x, cnormExp (e, t)))

    | (Comp.Box (loc, cM), t) ->
        Comp.Box (loc, cnormMetaObj (cM,t))

    | (Comp.Case (loc, prag, i, branches), t) ->
        Comp.Case (loc, prag, cnormExp' (i,t),
                   List.map (function b -> cnormBranch (b, t)) branches)

    | (Comp.If (loc, i, e1, e2), t) ->
        Comp.If (loc, cnormExp' (i,t),
                 cnormExp (e1, t), cnormExp (e2, t))

    | (Comp.Hole (loc, f), _) -> Comp.Hole (loc,f)

  and cnormExp' (i, t) = match (i,t) with
    | (Comp.Var _, _ ) -> i
    | (Comp.DataConst _, _ ) -> i
    | (Comp.DataDest _, _ ) -> i
    | (Comp.Const _, _ ) -> i

    | (Comp.Apply (loc, i, e), t) -> Comp.Apply (loc, cnormExp' (i, t), cnormExp (e,t))


    | (Comp.PairVal (loc, i1, i2), t) ->
        Comp.PairVal (loc, cnormExp' (i1,t), cnormExp' (i2, t))

    | (Comp.MApp (loc, i, cM), t) ->
        Comp.MApp (loc, cnormExp' (i, t),  cnormMetaObj (cM, t))

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


  let cnormMTyp (ctyp, mtt') = match ctyp with
     | CTyp (w, dep) -> CTyp (w, dep)
     | MTyp (tA, cPsi, dep) -> MTyp (cnormTyp (tA, mtt'), cnormDCtx (cPsi, mtt'), dep)
     | PTyp (tA, cPsi, dep) -> PTyp (cnormTyp (tA, mtt'), cnormDCtx (cPsi, mtt'), dep)
     | STyp (cPhi, cPsi, dep) -> STyp (cnormDCtx (cPhi, mtt'), cnormDCtx (cPsi, mtt'), dep)

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
    | Dec(cD, Decl (u, mtyp)) -> Dec(normMCtx cD, Decl (u, normMTyp mtyp))


  (* ----------------------------------------------------------- *)
  (* Conversion: Convertibility modulo alpha for
     computation-level types
  *)



  let rec convMetaObj mO mO' = match (mO , mO) with
    | (Comp.MetaCtx (_loc, cPsi) , Comp.MetaCtx (_ , cPsi'))  ->
        convDCtx  cPsi cPsi'
    | (Comp.MetaObj (_, _phat, tM) , Comp.MetaObj (_, _phat', tM')) ->
        conv (tM, LF.id) (tM', LF.id)
    | (Comp.MetaParam (_, _phat, tH) , Comp.MetaParam (_, _phat', tH')) ->
        convHead (tH, LF.id) (tH', LF.id)
    | (Comp.MetaSObj (_, _phat, s) , Comp.MetaSObj (_, _phat', s')) ->
        convSub s s'
    | _ -> false

  and convMetaSpine mS mS' = match (mS, mS') with
    | (Comp.MetaNil , Comp.MetaNil) -> true
    | (Comp.MetaApp (mO, mS) , Comp.MetaApp (mO', mS')) ->
        convMetaObj mO mO' && convMetaSpine mS mS'

  (* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)
  
  let convMTyp thetaT1 thetaT2 = match (thetaT1, thetaT2) with
    | (MTyp (tA1, cPsi1, dep)) , (MTyp (tA2, cPsi2, dep')) ->
        dep = dep' && convTyp (tA1, LF.id) (tA2, LF.id) && convDCtx cPsi1 cPsi2
    | (STyp (cPhi, cPsi, dep)) , (STyp (cPhi', cPsi', dep')) ->
        dep = dep' && convDCtx cPhi cPhi' && convDCtx cPsi cPsi'
    | (PTyp (tA, cPsi, dep)) , (PTyp (tA', cPsi', dep')) ->
        dep = dep' && convTyp (tA, LF.id) (tA', LF.id)  && convDCtx cPsi cPsi'
    | (CTyp (cid_schema, dep)) , (CTyp (cid_schema', dep')) ->
        dep = dep' && cid_schema = cid_schema'

  let convMetaTyp thetaT1 thetaT2 = match (thetaT1, thetaT2) with
    | (Comp.MetaTyp (tA1, cPsi1) , Comp.MetaTyp (tA2, cPsi2)) ->
        convTyp (tA1, LF.id) (tA2, LF.id) && convDCtx cPsi1 cPsi2
    | (Comp.MetaSubTyp (cPhi, cPsi) , Comp.MetaSubTyp (cPhi', cPsi')) ->
        convDCtx cPhi cPhi' && convDCtx cPsi cPsi'
    | (Comp.MetaParamTyp (tA, cPsi) , Comp.MetaParamTyp (tA', cPsi')) ->
       convTyp (tA, LF.id) (tA', LF.id)  && convDCtx cPsi cPsi'
    | (Comp.MetaSchema (cid_schema) , Comp.MetaSchema (cid_schema')) ->
        cid_schema = cid_schema'

  let rec convCTyp thetaT1 thetaT2 = convCTyp' (cwhnfCTyp thetaT1) (cwhnfCTyp thetaT2)

  and convCTyp' thetaT1 thetaT2 = match (thetaT1, thetaT2) with
    | ((Comp.TypBase (_, c1, mS1), _t1), (Comp.TypBase (_, c2, mS2), _t2)) ->
          if c1 = c2 then
            (* t1 = t2 = id by invariant *)
            convMetaSpine mS1 mS2
          else false

    | ((Comp.TypCobase (_, c1, mS1), _t1), (Comp.TypCobase (_, c2, mS2), _t2)) ->
          if c1 = c2 then
            (* t1 = t2 = id by invariant *)
            convMetaSpine mS1 mS2
          else false

    | ((Comp.TypBox (_, cT1), _t1) , (Comp.TypBox (_, cT2), _t2)) (* t1 = t2 = id *)
      ->
        convMetaTyp cT1 cT2

    | ((Comp.TypSub (_, cPsi1, cPsi2), _t), (Comp.TypSub (_, cPsi1', cPsi2'), _t'))  (* t1 = t2 = id *)
      -> convDCtx cPsi1 cPsi1'
        &&
          convDCtx cPsi2 cPsi2'

    | ((Comp.TypArr (tT1, tT2), t), (Comp.TypArr (tT1', tT2'), t'))
      -> (dprint (fun () -> "[convCtyp] arr part 1");
          convCTyp (tT1, t) (tT1', t'))
        &&
          (dprint (fun () -> "[convCtyp] arr part 2");
           convCTyp (tT2, t) (tT2', t'))

    | ((Comp.TypCross (tT1, tT2), t), (Comp.TypCross (tT1', tT2'), t'))
      -> convCTyp (tT1, t) (tT1', t')
        &&
          convCTyp (tT2, t) (tT2', t')

    | ((Comp.TypPiBox ((Decl(_, mtyp1)), tT), t), (Comp.TypPiBox ((Decl(_, mtyp2)), tT'), t'))
      ->
        (dprint (fun () -> "[convCtyp] PiBox Mdec");
          convMTyp (cnormMTyp (mtyp1, t)) (cnormMTyp (mtyp2, t'))
        &&
         (dprint (fun () -> "[convCtyp] PiBox decl done");
        convCTyp (tT, mvar_dot1 t) (tT', mvar_dot1 t')))

    | ((Comp.TypBool, _t ), (Comp.TypBool, _t')) -> true

    | ( _ , _ ) -> (dprint (fun () -> "[convCtyp] falls through?");false)

and convSchElem (SchElem (cPsi, trec)) (SchElem (cPsi', trec')) =
    convCtx cPsi cPsi'
  &&
    convTypRec (trec, LF.id) (trec', LF.id)


(* ------------------------------------------------------------ *)


(* etaExpandMV cPsi sA s' = tN
 *
 *  cPsi'  |- s'   <= cPsi
 *  cPsi   |- [s]A <= typ
 *
 *  cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMV cPsi sA n s' =  etaExpandMV' cPsi (whnfTyp sA) n s'
and etaExpandMV' cPsi sA n s' = match sA with
  | (Atom (_, _a, _tS) as tP, s) ->

      let u = newMVar (Some n) (cPsi, TClo(tP,s)) in 
        Root (Syntax.Loc.ghost, MVar (u, s'), Nil)

  | (PiTyp ((TypDecl (x, _tA) as decl, _ ), tB), s) ->
      Lam (Syntax.Loc.ghost, x, etaExpandMV (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) n (LF.dot1 s'))

(* Coverage.etaExpandMVstr s' cPsi sA *)

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
      let u = newMMVar None (cD , cPsi, TClo(tP,s))  in 
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
  | MMVar (MInst (_, {contents = None}, _, _, _, _, _), _) -> false
  | MVar (Inst (_, {contents = None}, _, _, _, _), _) -> false
  | PVar (_, r) ->
      closedSub r
  | MVar (Offset _, r) ->
      closedSub r
  | _ -> true

and closedSpine (tS,s) = match tS with
  | Nil -> true
  | App (tN, tS') -> closed (tN, s) && closedSpine (tS', s)
  | SClo(tS', s')  -> closedSpine (tS', LF.comp s' s)

and closedSub s = match s with
 | EmptySub -> true
 | Undefs -> true
 | SVar (_ , _ , sigma) ->
        closedSub sigma
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
  | SigmaLast (_, tA) -> closedTyp (tA,s)
  | SigmaElem (_, tA, recA') ->
      closedTyp (tA, s) &&
      closedTypRec (recA', LF.dot1 s)

and closedDecl (tdecl, s) = match tdecl with
  | TypDecl (_, tA) -> closedTyp (tA, s)
  | _ -> true


let rec closedDCtx cPsi = match cPsi with
  | Null     -> true
  | CtxVar (CInst (_, {contents = None}, _, _, _)) -> false
  | CtxVar (CInst (_, {contents = Some cPsi}, _,_ , theta)) ->
     closedDCtx (cnormDCtx (cPsi, theta))
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
  | Comp.MetaSObj (_, phat, sigma) ->
      closedDCtx (Context.hatToDCtx phat) && closedSub sigma

let closedMetaTyp cT = match cT with 
  | Comp.MetaTyp (tA, cPsi) -> closedTyp (tA, LF.id) && closedDCtx cPsi
  | Comp.MetaSchema _ -> true
  | Comp.MetaParamTyp (tA, cPsi) -> closedTyp (tA, LF.id) && closedDCtx cPsi
  | Comp.MetaSubTyp (cPhi, cPsi) -> closedDCtx cPhi && closedDCtx cPsi

let rec closedCTyp cT = match cT with
  | Comp.TypBool -> true
  | Comp.TypBase (_, _c, mS) -> closedMetaSpine mS
  | Comp.TypCobase (_, _c, mS) -> closedMetaSpine mS
  | Comp.TypBox (_ , cT)  -> closedMetaTyp cT
  | Comp.TypSub (_ , cPhi, cPsi) -> closedDCtx cPhi && closedDCtx cPsi
  | Comp.TypArr (cT1, cT2) -> closedCTyp cT1 && closedCTyp cT2
  | Comp.TypCross (cT1, cT2) -> closedCTyp cT1 && closedCTyp cT2
  | Comp.TypPiBox (ctyp_decl, cT) ->
      closedCTyp cT && closedCDecl ctyp_decl
  | Comp.TypClo (cT, t) -> closedCTyp(cnormCTyp (cT, t))  (* to be improved Sun Dec 13 11:45:15 2009 -bp *)

and closedCDecl ctyp_decl = match ctyp_decl with
  | Decl(_, MTyp (tA, cPsi, _)) -> closedTyp (tA, LF.id) && closedDCtx cPsi
  | Decl(_, PTyp (tA, cPsi, _)) -> closedTyp (tA, LF.id) && closedDCtx cPsi
  | Decl(_, STyp (cPhi, cPsi, _)) -> closedDCtx cPhi && closedDCtx cPsi
  | _ -> true

let rec closedGCtx cG = match cG with
  | Empty -> true
  | Dec(cG, Comp.CTypDecl(_ , cT)) ->
      closedCTyp cT && closedGCtx cG
  | Dec(cG, Comp.CTypDeclOpt _ ) -> closedGCtx cG
