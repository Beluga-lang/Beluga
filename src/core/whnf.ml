open Support.Equality
(**

   @author Brigitte Pientka
   modified:  Joshua Dunfield

*)

(* Weak Head Normalization,
 * Normalization, and alpha-conversion
 *)

open Support
open Syntax.Int.LF
open Syntax.Int
open Substitution

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [11]))
open Debug.Fmt

module T = Store.Cid.Typ

exception Fmvar_not_found
exception FreeMVar of head
exception NonInvertible
exception InvalidLFHole of Loc.t

let m_id = MShift 0

type mm_res =
  | ResMM of mm_var_inst'
  | Result of iterm

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [18])

let rec raiseType cPsi tA =
  match cPsi with
  | Null -> tA
  | DDec (cPsi', decl) ->
     raiseType cPsi' (PiTyp ((decl, Maybe), tA))

(* Eta-contract elements in substitutions *)
let etaContract =
  function
  | Root (_, ((BVar _ | PVar _ | Proj _ | MPVar _) as h), Nil, _) ->
     Head h
  | Lam _ as tM ->
     let rec etaUnroll k =
       function
       | Lam (_, _, tN) ->
          dprint (fun () -> "etaUnroll k =" ^ string_of_int k ^ "\n");
          etaUnroll (k + 1) tN
       | _ ->
          dprint (fun () -> "etaUnroll k =" ^ string_of_int k ^ "\n");
          (k, tM)
     in
     let rec etaSpine k tS =
       match (k, tS) with
       | (0, Nil) -> true
       | (k', App (Root (_, BVar x, Nil, _), tS')) ->
          if k' = x
          then etaSpine (k' - 1) tS'
          else false
       | _ ->
          false
          (* previously
             dprint (fun () -> "[etaSpine] _ ");
             raise (Error.Violation "etaSpine undefined\n")
           *)
     in
     begin match etaUnroll 0 tM with
     | (k, Root (_, BVar x, tS, _)) ->
        dprint (fun () -> "check etaSpine k =" ^ string_of_int k ^ "\n");
        if etaSpine k tS && x > k
        then Head (BVar (x - k))
        else Obj tM
     | _ -> Obj tM
     end
  | tM -> Obj tM

(*************************************)
(* Creating new contextual variables *)
(*************************************)
(* newCVar n sW = psi
 *
 *)

(* newMVar n (cPsi, tA) = newMVarCnstr (cPsi, tA, [])
 *
 * Invariant:
 *
 *       tA =   Atom (a, S)
 *   or  tA =   Pi (x:tB, tB')
 *   but tA =/= TClo _
 *)


let newMTypName =
  function
  | ClTyp (MTyp tA, _) -> Id.MVarName (T.gen_mvar_name tA)
  | ClTyp (PTyp tA, _) -> Id.PVarName (T.gen_var_name tA)
  | ClTyp (STyp _, _) -> Id.SVarName None
  | CTyp _ -> Id.NoName

let next_mmvar_id =
  let c = ref 0 in
  fun () ->
  incr c;
  !c

let newMMVar' n (cD, mtyp) depend =
  let name =
    match n with
    | None ->
      Id.mk_name (newMTypName mtyp)
    | Some n ->
       Id.inc n
  in
  { name
  ; instantiation = ref None
  ; mmvar_id = next_mmvar_id ()
  ; cD
  ; typ = mtyp
  ; constraints = ref []
  ; depend
  }

let newMMVar n (cD, cPsi, tA) dep = newMMVar' n (cD, ClTyp (MTyp tA, cPsi)) dep
let newMPVar n (cD, cPsi, tA) dep = newMMVar' n (cD, ClTyp (PTyp tA, cPsi)) dep

let newMSVar n (cD, cl, cPsi, cPhi) dep = newMMVar' n (cD, ClTyp (STyp (cl, cPhi), cPsi)) dep
let newCVar n cD (sW) dep = CInst (newMMVar' n (cD, CTyp sW) dep, MShift 0)

let newMVar n (cPsi, tA) dep = Inst (newMMVar' n (Empty, ClTyp (MTyp tA, cPsi)) dep)

(******************************)
(* Lowering                   *)
(******************************)

(* lowerMVar' cPsi tA[s] = (u, tM), see lowerMVar *)
let rec lowerMVar' cPsi sA' dep =
  match sA' with
  | (PiTyp ((decl, _), tA'), s') ->
     let (u', tM) =
       lowerMVar'
         (DDec (cPsi, LF.decSub decl s'))
         (tA', LF.dot1 s')
         dep
     in
     (u', Lam (Syntax.Loc.ghost, Id.mk_name Id.NoName, tM))

  | (TClo (tA, s), s') ->
     lowerMVar' cPsi (tA, LF.comp s s') dep

  | (Atom (loc, a, tS), s') ->
     let u' = newMVar None (cPsi, Atom (loc, a, SClo (tS, s'))) dep in
     (u', Root (Syntax.Loc.ghost, MVar (u', LF.id), Nil, Depend.to_plicity dep)) (* cvar * normal *)

(* lowerMVar1 (u, tA[s]), tA[s] in whnf, see lowerMVar *)
and lowerMVar1 u sA =
  match (u, sA) with
  | ( Inst { instantiation; typ = ClTyp (_, cPsi); depend; _ }
    , (PiTyp _, _)
    ) ->
     let (u', tM) = lowerMVar' cPsi sA depend in
     instantiation := Some (INorm tM); (* [| tM / u |] *)
     u' (* this is the new lowered meta-variable of atomic type *)

  | (_, (TClo (tA, s), s')) -> lowerMVar1 u (tA, LF.comp s s')

  | (_, (Atom _, _)) -> u

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
and lowerMVar =
  function
  | Inst { typ = ClTyp (MTyp tA, _); constraints = { contents = [] }; _ } as u ->
     lowerMVar1 u (tA, LF.id)

  | _ ->
     (* It is not clear if it can happen that cnstr =/= nil *)
     (* 2011/01/14: Changed this to a violation for now, to avoid a cyclic dependency on Reconstruct. -mb *)
     raise (Error.Violation "Constraints left")

(*

(* lowerMMVar' cD cPsi tA[s] = (u, tM), see lowerMVar *)
and lowerMMVar' cD cPsi sA' dep =
  match sA' with
  | (PiTyp ((decl, _), tA'), s') ->
     let (u', tM) = lowerMMVar' cD (DDec (cPsi, LF.decSub decl s')) (tA', LF.dot1 s') dep in
     (u', Lam (Syntax.Loc.ghost, Id.mk_name Id.NoName, tM))

  | (TClo (tA, s), s') ->
     lowerMMVar' cD cPsi (tA, LF.comp s s') dep

  | (Atom (loc, a, tS), s') ->
     let u' = newMMVar None (cD, cPsi, Atom (loc, a, SClo (tS, s'))) dep in
     (u', Root (Syntax.Loc.ghost, MMVar ((u', MShift 0), LF.id), Nil)) (* cvar * normal *)


(* lowerMMVar1 (u, tA[s]), tA[s] in whnf, see lowerMMVar *)
and lowerMMVar1 cD u sA =
  match (u, sA) with
  | ((_, r, _, ClTyp (_, cPsi), _, dep), (PiTyp _, _)) ->
     let (u', tM) = lowerMMVar' cD cPsi sA dep in
     r := Some (INorm tM); (* [| tM / u |] *)
     u' (* this is the new lowered meta-variable of atomic type *)

  | (_, (TClo (tA, s), s')) ->
     lowerMMVar1 cD u (tA, LF.comp s s')

  | (_, (Atom _, _)) -> u



(* lowerMMVar (u:cvar) = u':cvar
 *
 * Invariant: (same as for lowerMVar)
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
and lowerMMVar cD =
  function
  | _, _, _, ClTyp (MTyp tA, _), { contents = [] }, mdep as u ->
     lowerMMVar1 cD u (tA, LF.id)

  | _ ->
     (* It is not clear if it can happen that cnstr =/= nil *)
     (* 2011/01/14: Changed this to a violation for now, to avoid a cyclic dependency on Reconstruct. -mb *)
     raise (Error.Violation "Constraints left")

*)

(*************************************)

(* mvar_dot1 t = t'
   Invariant:

   If  cD |- t : cD'

   then t' = u. (mshift t 1)
       and  for all A s.t.  D' ; Psi |- A : type

              D, u::[|t|](A[Psi]) |- t' : D', A[Psi]
 *)
let rec mvar_dot1 t =
  (* MDot (MV 1, mshift t 1) *)
  MDot (MV 1, mcomp t (MShift 1))

and pvar_dot1 t =
  MDot (MV 1, mcomp t (MShift 1))


(* mvar_dot t cD = t'

     if cD1 |- t <= cD2
     then cD1, cD |- t <= cD2, cD
 *)
and mvar_dot t =
  function
  | Empty -> t
  | Dec (cD, _) ->
     mvar_dot (mvar_dot1 t) cD



and mcomp t1 t2 =
  match (t1, t2) with
  | (MShift 0, t) -> t
  | (t, MShift 0) -> t
  | (MShift n, MShift k) -> MShift (n + k)
  | (MShift n, MDot (_, t)) ->
     mcomp (MShift (n - 1)) t
  | (MDot (mft, t), t') ->
     MDot (mfrontMSub mft t', mcomp t t')


(* mfrontMSub Ft t = Ft'

   Invariant:

   If   D |- t : D'     D' ; Psi |- Ft <= A
   then Ft' =  [|t|] Ft
   and  D ; [|t|]Psi |- Ft' : [|t|]A
*)
and mfrontMSub ft t =
  match ft with
  | ClObj (phat, tM) ->
     ClObj (cnorm_psihat phat t, cnormClObj tM t)
  | CObj cPsi -> CObj (cnormDCtx (cPsi, t))
  | MV k -> LF.applyMSub k t
  | MUndef -> MUndef

(* m_invert t = t'

   Invariant:

   If   D  |- t  <= D'    (and s !!!patsub!!!)
   then D' |- t' <= D
   s.t. t o t' = id    (mcomp t' t = id)
*)
and m_invert s =
  let rec lookup n s p =
    match s with
    | MShift _ -> None
    | MDot (MUndef, t') -> lookup (n + 1) t' p

    | MDot (MV k, t')
      | MDot (CObj (CtxVar (CtxOffset k)), t')
      | MDot (ClObj (_, MObj (Root (_, MVar (Offset k, Shift 0), Nil, _))), t')
      | MDot (ClObj (_, PObj (PVar (k, Shift 0))), t') ->
       if k = p
       then Some n
       else lookup (n + 1) t' p
  in

  let rec invert'' p ti =
    match p with
    | 0 -> ti
    | p ->
       let front =
         match lookup 1 s p with
         | Some k -> MV k (* or MObj (phat, Root (MVar (Offset k), id), Nil) *)
         | None -> MUndef
       in
       invert'' (p - 1) (MDot (front, ti))
  in

  let rec invert' n =
    function
    | MShift p -> invert'' p (MShift n)
    | MDot (_, t') -> invert' (n + 1) t'
  in

  invert' 0 s

(* Normalization = applying simultaneous hereditary substitution
 *
 * Applying the substitution ss to an LF term tM yields again
 * a normal term. This corresponds to normalizing the term [s]tM.
 *
 * We assume that the LF term tM does not contain any closures
 * MClo (tN, t), TMClo (tA, t), SMClo (tS, t); this means we must
 * first call contextual normalization and then call ordinary
 * normalization.
 *)
(*
 * norm (tM, s) = [s]tM
 *
 * Invariant:
 * if cD ; cPsi  |- tM <= tA
 *    cD ; cPsi' |- s <= cPsi
 * then
 *    cD ; cPsi' |- [s]tM <= [s]tA
 *
 * Similar invariants for norm, normSpine.
 *)
and norm (tM, sigma) =
  match tM with
  | Lam (loc, y, tN) ->
     Lam (loc, y, norm (tN, LF.dot1 sigma))
  | Tuple (loc, tuple) ->
     Tuple (loc, normTuple (tuple, sigma))
  | Clo (tN, s) ->
     norm (tN, LF.comp s sigma)
  | LFHole _ -> tM
  | Root (loc, h, tS, plicity) ->
     begin match normHead (h, sigma) with
     | Head h' -> Root (loc, h', normSpine (tS, sigma), plicity)
     | Obj tM -> reduce (tM, LF.id) (normSpine (tS, sigma))
     end


and normHead (h, sigma) =
  match h with
  | BVar k -> LF.bvarSub k sigma
  | Const c -> Head (Const c)
  | PVar (p, s) -> Head (PVar (p, normSub' (s, sigma)))
  | AnnH (h, t) -> normHead (h, sigma)
  | Proj (h, i) -> reduceTupleFt (normHead (h, sigma), i)
  | FVar n -> Head (FVar n)
  | FMVar (n, s) -> Head (FMVar (n, normSub' (s, sigma)))
  | FPVar (n, s) -> Head (FPVar (n, normSub' (s, sigma)))
  | HClo (k, sv, r) -> Head (HClo (k, sv, normSub' (r, sigma)))
  | HMClo (k, (mmt, s)) -> (* TODO: This is kind of repetitive...*)
     begin match normMMVar mmt with
     | ResMM mmt' -> Head (HMClo (k, (mmt', normSub' (s, sigma))))
     | Result (ISub r) -> normFt' (normFt' (LF.bvarSub k r, s), sigma)
     end
  | MMVar (mmt, s) ->
     begin match normMMVar mmt with
     (* The order in which we normalize mm, n, s, and sigma seems to matter..*)
     | ResMM mmt' -> Head (MMVar (mmt', normSub' (s, sigma)))
     | Result (INorm n) -> Obj (norm (norm (n, s), sigma))
     end
  | MPVar (mmt, s) ->
     begin match normMMVar mmt with
     | ResMM mmt' -> Head (MPVar (mmt', normSub' (s, sigma)))
     | Result (IHead h) -> normFt' (normHead (h, s), sigma)
     | Result (INorm n) -> Obj (norm (norm (n, s), sigma))
     end
  | MVar (Offset u, s) -> Head (MVar (Offset u, normSub' (s, sigma)))
  | MVar (Inst mm, s) ->
     begin match normMMVar (mm, MShift 0) with
     | ResMM (mm', _) -> Head (MVar (Inst mm', normSub' (s, sigma)))
     | Result (INorm n) -> Obj (norm (norm (n, s), sigma))
     end

and normMMVar (mmvar, t) =
  match mmvar.instantiation.contents with
  | None ->
     ResMM
       ( { mmvar with typ = normITyp mmvar.typ }
       , t
       )
  | Some tM -> Result (cnormITerm (tM, t))

and normClTyp (tp, s) =
  match tp with
  | MTyp tA -> MTyp (normTyp (tA, s))
  | PTyp tA -> PTyp (normTyp (tA, s))
  | STyp (cl, cPhi) -> STyp (cl, cPhi)

and normITyp =
  function
  | ClTyp (tp, cPsi) -> ClTyp (normClTyp (tp, LF.id), cPsi)
  | CTyp g -> CTyp g

and normFt' (ft, s) =
  match ft with
  | Head h -> normHead (h, s)
  | Obj tM -> Obj (norm (tM, s))

and cnormITerm (tM, mt) =
  match tM with
  | INorm n -> INorm (cnorm (n, mt))
  | IHead h -> IHead (cnormHead (h, mt))
  | ISub s -> ISub (cnormSub (s, mt))

and normMObj (tM, s) =
  match tM with
  | MObj n -> MObj (norm (n, s))
  | PObj h ->
     begin match normHead (h, s) with
     | Obj tM -> MObj tM
     | Head h' -> PObj h'
     end
  | SObj r -> SObj (normSub' (r, s))

and reduceTupleFt (ft, i) =
  match ft with
  | Head h -> Head (Proj (h, i))
  | Obj (Tuple (_, tM)) -> Obj (reduceTuple (tM, i))
  | Obj _ -> Error.violation "[reduceTupleFt] not a tuple"

and reduceTuple =
  function
  | (Last tM, 1) -> tM
  | (Cons (tM, _), 1) -> tM
  | (Cons (_, rest), k) -> reduceTuple (rest, k-1)

and normSub' (r, sigma) = normSub (LF.comp r sigma) (* this is slightly weird *)

and normTuple (tuple, t) =
  match tuple with
  | Last tM -> Last (norm (tM, t))
  | Cons (tM, rest) ->
     let tM' = norm (tM, t) in
     let rest' = normTuple (rest, t) in
     Cons (tM', rest')

and normSpine (tS, sigma) =
  match tS with
  | Nil -> Nil
  | App (tN, tS) ->
     let tN' = norm (tN, sigma) in
     App (tN', normSpine (tS, sigma))
  | SClo (tS, s) -> normSpine (tS, LF.comp s sigma)

(*  reduce (sM, tS) = M'
 *
 *  cPsi | tS > tA' <= tP
 *  cPsi |  s  : cPsi''      cPsi'' |- tM <= tA''       [s]tA'' = tA'
 *)
and reduce sM spine = reduce' (norm sM, spine)

and reduce' =
  function
  | (LFHole (l, _, _), _) ->
     raise (InvalidLFHole l)

  | (Root (loc, h, sp, plicity), spine) ->
     Root (loc, h, appendSpine (sp, spine), plicity)

  | (Lam (loc, n, tM'), App (tN, tS)) ->
     reduce (tM', Dot (Obj tN, LF.id)) tS

  | (Lam (loc, n, tM'), Nil) ->
     Lam (loc, n, tM')

  | (Clo sM, tS) ->
     reduce sM tS

and appendSpine =
  function
  | (Nil, s) -> s
  | (App (tN, tS), s) -> App (tN, appendSpine (tS, s))

and normSub =
  function
  | EmptySub -> EmptySub
  | Undefs -> Undefs
  | Shift _ as s -> s
  | Dot (ft, s') -> Dot (normFt ft, normSub s')
  | FSVar (n, (s, sigma)) -> FSVar (n, (s, normSub sigma))
  | SVar (offset, n, s') -> SVar (offset, n, normSub s')
  | MSVar (n, ((mmvar (* (_, { contents = Some (ISub s) }, _, ClTyp (STyp _, _), _, mDep) *), mt), s')) ->
     begin match mmvar.instantiation.contents with
     | Some (ISub s) ->
        let s0 = cnormSub (LF.comp (normSub s) (normSub s'), mt) in
        LF.comp (Shift n) s0
     | None ->
        MSVar (n, ((mmvar, mt), normSub s'))
     end

and normFt =
  function
  | Obj tM -> etaContract (norm (tM, LF.id))
  | Head h -> normHead (h, LF.id)
  | Undef -> Undef



(* normType (tA, sigma) = tA'
 *
 * If cD ; G |- tA <= type
 *    cD ; G' |- sigma <= G
 * then
 *    tA' = [sigma]tA
 *    cD ; G' |- tA' <= type   and tA' is in normal form
 *)
and normTyp (tA, sigma) =
  match tA with
  | Atom (loc, a, tS) ->
     Atom (loc, a, normSpine (tS, sigma))

  | PiTyp ((TypDecl _ as decl, dep), tB) ->
     PiTyp ((normDecl (decl, sigma), dep), normTyp (tB, LF.dot1 sigma))

  | TClo (tA, s) ->
     normTyp (tA, LF.comp s sigma)

  | Sigma recA ->
     Sigma (normTypRec (recA, sigma))

and normTypRec (recA, sigma) =
  match recA with
  | SigmaLast (n, lastA) ->
     let tA = normTyp (lastA, sigma) in
     SigmaLast (n, tA)

  | SigmaElem (x, tA, recA') ->
     let tA = normTyp (tA, sigma) in
     SigmaElem (x, tA, normTypRec (recA', LF.dot1 sigma))

and normDecl (decl, sigma) =
  match decl with
  | TypDecl (x, tA) ->
     TypDecl (x, normTyp (tA, sigma))

  | _ -> decl

(* ********************************************************************* *)
(* Normalization = applying simultaneous modal substitution

     Applying the modal substitution t to a normal LF term tM
     yields a normal term. This corresponds to normalizing the term [|t|]tM.
*)

  (*
     cnorm (tM, t) = [|t|]tM

     Invariant:
     if cD ; cPsi  |- tM <= tA
     cD'  |- t <= cD
     then
     [|t|] cPsi = cPsi' , [|t|]tA = tA', [|t|]tM = tM'
     cD' ; cPsi' |- tM' <= tA'

     Similar invariants for cnorm, cnormSpine.

     If tM is in cnormal form, then [|t|]tM is also in cnormal form.

  *)

and cnorm_psihat (phat : dctx_hat) t =
  match phat with
  | (None, _) -> phat
  | (Some (CInst (mmvar (* (_, ({ contents = None } as cvar_ref), cD, schema, cnstr, dep) *), theta)), k) ->
     let u = mmvar.instantiation in
     begin match !u with
     | None ->
        (Some (CInst (mmvar, mcomp theta t)), k)
     | Some (ICtx cPsi) ->
        (* | (Some (CInst ((_, { contents = Some (ICtx cPsi) }, _, _, _, _), theta)), k) -> *)
        begin match Context.dctxToHat (cnormDCtx (cPsi, mcomp theta t)) with
        | (None, i) -> (None, k+i) (* cnorm_psihat (None, k+i) t *)
        | (Some cvar', i) -> (Some cvar', i+k) (* cnorm_psihat (Some cvar', i+k) t *)
        end
     end
  | (Some (CtxOffset offset), k) ->
     begin match LF.applyMSub offset t with
     | CObj cPsi ->
        begin match Context.dctxToHat cPsi with
        | (None, i) -> (None, k + i)
        | (Some cvar', i) -> (Some cvar', i + k)
        end
     | MV offset' -> (Some (CtxOffset offset'), k)
     | ClObj _ ->
        Error.violation
          ("[cnorm_psihat] ClObj impossible; offset " ^ string_of_int offset)
     end
  | _ -> phat

and cnormHead' (h, t) =
  match h with
  | BVar k -> Head (BVar k)
  | Const c -> Head (Const c)
  | AnnH (h, _) -> cnormHead' (h, t)
  | Proj (h, k) ->
     reduceTupleFt (cnormHead' (h, t), k)
  | FVar x -> Head (FVar x)
  | FMVar (n, s) -> Head (FMVar (n, cnormSub (s, t)))
  | FPVar (n, s) -> Head (FPVar (n, cnormSub (s, t)))
  | MVar (Offset k, s) ->
     let s' = cnormSub (s, t) in
     begin match LF.applyMSub k t with
     | MV k' -> Head (MVar (Offset k', s'))
     | ClObj (_, MObj tM) -> Obj (norm (tM, s'))
     end
  | PVar (k, s) ->
     let s' = cnormSub (s, t) in
     begin match LF.applyMSub k t with
     | MV k' -> Head (PVar (k', s'))
     | ClObj (_, PObj h) -> normHead (h, s')
     | ClObj (_, MObj tM) -> Obj (norm (tM, s'))
     end
  | HClo (k, sv, s) ->
     let s' = cnormSub (s, t) in
     begin match LF.applyMSub sv t with
     | MV sv' -> Head (HClo (k, sv', s'))
     | ClObj (_, SObj r) -> normFt' (LF.bvarSub k r, s')
     end
  | MMVar (mmt, s) ->
     begin match normMMVar mmt with
     | ResMM (mm', mt) -> Head (MMVar ((mm', cnormMSub' (mt, t)), cnormSub (s, t)))
     | Result (INorm n) -> Obj (cnorm (norm (n, s), t))
     end
  | MPVar (mmt, s) ->
     begin match normMMVar mmt with
     | ResMM (mm', mt) -> Head (MPVar ((mm', cnormMSub' (mt, t)), cnormSub (s, t)))
     | Result (IHead h) -> cnormFt' (normHead (h, s), t)
     | Result (INorm n) ->
        Obj (cnorm (norm (n, s), t))
     end
  | HMClo (k, (mmt, s)) ->
     begin match normMMVar mmt with
     | ResMM (mm', mt) -> Head (HMClo (k, ((mm', cnormMSub' (mt, t)), cnormSub (s, t))))
     | Result (ISub r) -> cnormFt' (normFt' (LF.bvarSub k r, s), t)
     end
  | MVar (Inst mm, s) ->
     begin match normMMVar (mm, MShift 0) with
     | ResMM (mm', _) -> Head (MVar (Inst mm', cnormSub (s, t)))
     | Result (INorm n) -> Obj (norm (n, s))
     end

and cnormMSub' (mt, t) = cnormMSub (mcomp mt t)
and cnormFt' =
  function
  | (Head h, t) -> cnormHead' (h, t)
  | (Obj tM, t) -> Obj (cnorm (tM, t))

and cnorm (tM, t) =
  match tM with
  | Lam (loc, y, tN) -> Lam (loc, y, cnorm (tN, t))

  | Tuple (loc, tuple) -> Tuple (loc, cnormTuple (tuple, t))

  | Clo (tN, s) -> Clo (cnorm (tN, t), cnormSub (s, t))

  | LFHole (loc, id, name) -> LFHole (loc, id, name)

  | Root (loc, head, tS, plicity) ->
     begin match cnormHead' (head, t) with
     | Head h' -> Root (loc, h', cnormSpine (tS, t), plicity)
     | Obj tM ->
        (* in this ends up evaluating to a Root, we want to keep the
           plicity that we had here *)
        map_plicity
          (fun _ -> plicity)
          (reduce (tM, LF.id) (cnormSpine (tS, t)))
     end

(* cnormHead (h, t) = h'
   requires that h is a head such as bound variable or parameter variable associated with pattern sub
   or projection of the previous two
 *)
and cnormHead (h, t) =
  match cnormHead' (h, t) with
  | Head h' -> h'

and cnormSpine (tS, t) =
  match tS with
  | Nil -> Nil
  | App (tN, tS) -> App (cnorm (tN, t), cnormSpine (tS, t))
  | SClo (tS, s) -> SClo (cnormSpine (tS, t), cnormSub (s, t))

and cnormTuple (tuple, t) =
  match tuple with
  | Last tM -> Last (cnorm (tM, t))
  | Cons (tM, rest) ->
     let tM' = cnorm (tM, t) in
     let rest' = cnormTuple (rest, t) in
     Cons (tM', rest')

and cnormSub (s, t) =
  match s with
  | EmptySub -> EmptySub
  | Undefs -> Undefs
  | Shift k -> s
  | Dot (ft, s') -> Dot (cnormFront (ft, t), cnormSub (s', t))
  | SVar (offset, n, s') ->
     begin match LF.applyMSub offset t with
     | MV offset' -> SVar (offset', n, cnormSub (s', t))
     | ClObj (_, SObj r) ->
        LF.comp (LF.comp (Shift n) r) (cnormSub (s', t))
     | ClObj _ ->
        Error.violation "[cnormSub] t @ offset must give an MV or ClObj SObj"
     end

  | FSVar (n, (s_name, s')) ->
     FSVar (n, (s_name, cnormSub (s', t)))

  | MSVar (n, ((mmvar, mt), s')) ->
     match mmvar.instantiation.contents with
     | Some (ISub s) ->
        dprintf
          begin fun p ->
          p.fmt "[cnormSub] @[<v>MSVar - MSInst for @[%s@]@]"
            (Id.render_name mmvar.name)
          end;
        let s0 = cnormSub (LF.comp (normSub s) (normSub s'), mt) in
        let s0' = LF.comp (Shift n) s0 in
        cnormSub (s0', t)
     | None ->
        MSVar (n, ((mmvar, cnormMSub (mcomp mt t)), s'))

and cnormFront =
  function
  | (Head h, t) -> cnormHead' (h, t)
  | (Obj tM, t) -> Obj (cnorm (tM, t))
  | (Undef, t) -> Undef


(* cnormTyp (tA, t) = tA'

     If cD' ; cPsi  |- tA <= type
     cD |- t <= cD'
     then
     tA' = [|t|]tA  and cPsi' = [|t|]cPsi
     cD' ; cPsi' |- tA' <= type
 *)
and cnormTyp (tA, t) =
  match tA with
  | Atom (loc, a, tS) ->
     Atom (loc, a, cnormSpine (tS, t))

  | PiTyp ((TypDecl _ as decl, dep), tB) ->
     PiTyp ((cnormDecl (decl, t), dep), cnormTyp (tB, t))

  | TClo (tA, s) -> normTyp (cnormTyp (tA, t), cnormSub (s, t))

  | Sigma recA ->
     Sigma (cnormTypRec (recA, t))

and cnormTypRec (typRec, t) =
  match typRec with
  | SigmaLast (n, lastA) -> SigmaLast (n, cnormTyp (lastA, t))
  | SigmaElem (x, tA, recA') ->
     let tA = cnormTyp (tA, t) in
     SigmaElem (x, tA, cnormTypRec (recA', t))

and cnormDecl (decl, t) =
  match decl with
  | TypDecl (x, tA) ->
     TypDecl (x, cnormTyp (tA, t))
  | TypDeclOpt x -> TypDeclOpt x

  (* cnormDCtx (cPsi, t) = cPsi

   If cO ; cD  |- cPsi lf-dctx
      cO ; cD' |-  t_d <= cO ; cD
   then
      cO  ; cD' |- [|t|]cPsi

  *)
and cnormDCtx (cPsi, t) =
  match cPsi with
  | Null -> Null

  | CtxVar (CInst (mmvar, theta)) ->
     let u = mmvar.instantiation in
     begin match !u with
     | None ->
        CtxVar (CInst (mmvar, mcomp theta t))
     | Some (ICtx cPhi) ->
        cnormDCtx (cPhi, mcomp theta t)
     end

  | CtxVar (CtxOffset psi) ->
     begin match LF.applyMSub psi t with
     | CObj cPsi' -> normDCtx cPsi'
     | MV k -> CtxVar (CtxOffset k)
     end


  | CtxVar (CtxName psi) -> CtxVar (CtxName psi)


  | DDec (cPsi, decl) ->
     DDec (cnormDCtx (cPsi, t), cnormDecl (decl, t))

and cnormClTyp (mtyp, t) =
  match mtyp with
  | MTyp tA -> MTyp (normTyp (cnormTyp (tA, t), LF.id))
  | PTyp tA -> PTyp (normTyp (cnormTyp (tA, t), LF.id))
  | STyp (cl, cPhi) -> STyp (cl, normDCtx (cnormDCtx (cPhi, t)))
and cnormMTyp (mtyp, t) =
  match mtyp with
  | ClTyp (tA, cPsi) -> ClTyp (cnormClTyp (tA, t), normDCtx (cnormDCtx (cPsi, t)))
  | CTyp sW -> CTyp sW

and cnormClObj m t =
  match m with
  | MObj tM -> MObj (norm (cnorm (tM, t), LF.id))
  | SObj s -> SObj (normSub (cnormSub (s, t)))
  | PObj h -> PObj (cnormHead (h, t))
and cnormMFt mft = mfrontMSub mft
and cnormMSub =
  function
  | MShift _ as t -> t
  | MDot (mft, t) -> MDot (cnormMFt mft m_id, cnormMSub t)

(* ************************************************************** *)


and normKind =
  function
  | (Typ, _) -> Typ
  | (PiKind ((decl, dep), tK), s) ->
     PiKind ((normDecl (decl, s), dep), normKind (tK, LF.dot1 s))

and normDCtx =
  function
  | Null -> Null
  | CtxVar (CInst (mmvar, theta)) as cPsi ->
     begin match mmvar.instantiation.contents with
     | None -> cPsi
     | Some (ICtx cPhi) -> normDCtx (cnormDCtx (cPhi, theta))
     end
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
 * MClo (tN, t), TMClo (tA, t), SMClo (tS, t); this means we must
 * first call contextual normalization (or whnf) and then call
 * ordinary normalization, if these two substitutions interact.
 *)
(*
 * whnf (tM, s) = (tN, s')
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
and whnf  =
  function
  | (Lam _, _) as sM -> sM

  | (Tuple _, _) as sM -> sM

  | (Clo (tN, s), s') -> whnf (tN, LF.comp s s')

  | (Root (loc, BVar i, tS, plicity), sigma) ->
     begin match LF.bvarSub i sigma with
     | Obj tM ->
        whnfRedex ((tM, LF.id), (tS, sigma))

     | Head (BVar k) ->
        (Root (loc, BVar k, SClo (tS, sigma), plicity), LF.id)

     | Head (Proj (BVar k, j)) ->
        (Root (loc, Proj (BVar k, j), SClo (tS, sigma), plicity), LF.id)

     | Head head ->
        whnf (Root (loc, head, SClo (tS, sigma), plicity), LF.id)

     | Undef -> Error.violation "[whnf] Undef impossible"
     end

  (* Meta^2-variable *)
  | Root (loc, MPVar ((mmvar, t), r), tS, plicity), sigma ->
     (* MPVar must have a PTyp *)
     let ClTyp (PTyp tA, cPsi) = mmvar.typ in
     let u = mmvar.instantiation.contents in
     begin match u with
     (* MPVar instantiation must be a head *)
     | Some (IHead h) ->
        let h' = cnormHead (h, t) in
        begin match h' with
        | BVar i ->
           begin match LF.bvarSub i (LF.comp r sigma) with
           | Obj tM -> whnfRedex ((tM, LF.id), (tS, sigma))
           | Head (BVar k) -> (Root (loc, BVar k, SClo (tS, sigma), plicity), LF.id)
           | Head h -> whnf (Root (loc, h, SClo (tS, sigma), plicity), LF.id)
           | Undef ->
              Error.violation ("[whnf] Undef looked up at " ^ string_of_int i)
           end
        | PVar (p, s) ->
           let h' = PVar (p, LF.comp (LF.comp s r) sigma) in
           whnf (Root (loc, h', SClo (tS, sigma), plicity), LF.id)
        | MPVar ((q, t'), r') -> whnf (Root (loc, MPVar ((q, t'), LF.comp r' r), SClo (tS, sigma), plicity), LF.id)
        end
     | None ->
        (* constraints associated with q must be in solved form *)
        let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
        let p' = { mmvar with typ = ClTyp (PTyp tA', cPsi') } in
        (Root (loc, MPVar ((p', t), LF.comp r sigma), SClo (tS, sigma), plicity), LF.id)
     end

  | Root (loc, MMVar ((mmvar, t), r), tS, plicity), sigma ->
     (* MMVar must have an MTyp *)
     let ClTyp (MTyp tA, cPsi) = mmvar.typ in
     let u = mmvar.instantiation.contents in
     begin match u with
     (* MMVar instantiation must be normal *)
     | Some (INorm tM) ->
        (* constraints associated with u must be in solved form *)
        let tM' = cnorm (tM, t) in
        let tM'' = norm (tM', r) in
        let sR = whnfRedex ((tM'', sigma), (tS, sigma)) in
        (* let sR = whnfRedex ((tM', LF.comp r sigma), (tS, sigma)) in *)
        sR
     | None ->
        begin match whnfTyp (tA, LF.id) with
        | (Atom (loc', a, tS'), _ (* id *)) ->
           (* meta-variable is of atomic type; tS = Nil *)
           let u' = { mmvar with typ = ClTyp (MTyp (Atom (loc', a, tS')), cPsi) } in
           (Root (loc, MMVar ((u', t), LF.comp r sigma), SClo (tS, sigma), plicity), LF.id)
        | (PiTyp _, _)->
           (* Meta-variable is not atomic and tA = Pi x:B1.B2:
            * lower u, and normalize the lowered meta-variable.
            * Note: we may expose and compose substitutions twice.
            *
            * Should be possible to extend it to m^2-variables; D remains unchanged
            * because we never arbitrarily mix pi and pibox.
            *)
           (* let _ = lowerMMVar cD u in
              whnf (tM, sigma) *)
           Error.violation "Meta^2-variable needs to be of atomic type"
        end
     end

  (* Meta-variable *)
  | (Root (loc, MVar (Offset _ as u, r), tS, plicity), sigma) ->
     (Root (loc, MVar (u, LF.comp (normSub r) sigma), SClo (tS, sigma), plicity), LF.id)

  | (Root (loc, FMVar (u, r), tS, plicity), sigma) ->
     (Root (loc, FMVar (u, LF.comp (normSub r) sigma), SClo (tS, sigma), plicity), LF.id)

  | Root (loc, MVar (Inst mmvar as cvar, r), tS, plicity) as tM, sigma ->
     let u = mmvar.instantiation.contents in
     begin match u with
     | Some (INorm tM) ->
        (* constraints associated with u must be in solved form *)
        let r' = normSub r in
        let tM' =
          begin match r' with
          | Shift 0 -> tM
          | _ -> norm (tM, r') (* this can be expensive -bp *)
          end in
        (* it does not work to call whnfRedex ((tM, LF.comp r sigma), (tS, sigma)) -bp *)
        let sR = whnfRedex ((tM', sigma), (tS, sigma)) in
        sR
     | None ->
        let ClTyp (MTyp tA, cPsi) = mmvar.typ in
        (* note: we could split this case based on tA;
         *      this would avoid possibly building closures with id
         *)
        let r' = normSub r in
        begin match whnfTyp (tA, LF.id) with
        | (Atom (loc', a, tS'), _ (* id *)) ->
           (* meta-variable is of atomic type; tS = Nil *)
           let u' = Inst { mmvar with typ = ClTyp (MTyp (Atom (loc', a, tS')), cPsi) } in
           (Root (loc, MVar (u', LF.comp r' sigma), SClo (tS, sigma), plicity), LF.id)
        | (PiTyp _, _)->
           (* Meta-variable is not atomic and tA = Pi x:B1.B2:
            * lower u, and normalize the lowered meta-variable.
            * Note: we may expose and compose substitutions twice.
            *)
           ignore (lowerMVar cvar);
           whnf (tM, sigma)
        end
     end

  (* Parameter variable *)
  | (Root (loc, PVar (p, r), tS, plicity), sigma) ->
     (Root (loc, PVar (p, LF.comp (normSub r) sigma), SClo (tS, sigma), plicity), LF.id)

  | (Root (loc, FPVar (p, r), tS, plicity), sigma) ->
     (Root (loc, FPVar (p, LF.comp (normSub r) sigma), SClo (tS, sigma), plicity), LF.id)

  | (Root (loc, Proj (FPVar (p, r), k), tS, plicity), sigma) ->
     let fpvar = FPVar (p, LF.comp (normSub r) sigma) in
     (Root (loc, Proj (fpvar, k), SClo (tS, sigma), plicity), LF.id)

  (* Constant *)
  | (Root (loc, Const c, tS, plicity), sigma) ->
     (Root (loc, Const c, SClo (tS, sigma), plicity), LF.id)

  (* Projections *)
  | (Root (loc, Proj (BVar i, k), tS, plicity), sigma) ->
     begin match LF.bvarSub i sigma with
     | Head (BVar j) ->
        ( Root (loc, Proj (BVar j, k), SClo (tS, sigma), plicity)
        , LF.id
        )
     | Head (PVar (q, s)) ->
        ( Root (loc, Proj (PVar (q, s), k), SClo (tS, sigma), plicity)
        , LF.id
        )
     end

  | (Root (loc, Proj (PVar (q, s), k), tS, plicity), sigma) ->
     ( Root (loc, Proj (PVar (q, LF.comp s sigma), k), SClo (tS, sigma), plicity)
     , LF.id
     )

  (* Free variables *)
  | (Root (loc, FVar x, tS, plicity), sigma) ->
     (Root (loc, FVar x, SClo (tS, sigma), plicity), LF.id)
  | (Root (loc, Proj (MPVar ((mmvar, t), r), k), tS, plicity), sigma) ->
     begin match mmvar.instantiation.contents with
     | Some (IHead h) ->
        (* constraints associated with q must be in solved form *)
        begin match cnormHead (h, t) with
        | BVar i ->
           begin match LF.bvarSub i (LF.comp r sigma) with
           | Head (BVar x) ->
              ( Root (loc, Proj (BVar x, k), SClo (tS, sigma), plicity)
              , LF.id
              )
           | Head h ->
              ( Root (loc, Proj (h, k), SClo (tS, sigma), plicity)
              , LF.id
              )
           | Undef ->
              Error.violation ("[whnf] Undef looked up at " ^ string_of_int i)
           end
        | PVar (p, s) ->
           let h' = Proj (PVar (p, LF.comp (LF.comp s r) sigma), k) in
           ( Root (loc, h', SClo (tS, sigma), plicity)
           , LF.id
           )
        | MPVar ((q, t'), r') ->
           let h' = Proj (MPVar ((q, t'), LF.comp (LF.comp r' r) sigma), k) in
           (Root (loc, h', SClo (tS, sigma), plicity), LF.id)
        end
     | None ->
        let ClTyp (PTyp tA, cPsi) = mmvar.typ in
        (* constraints associated with q must be in solved form *)
        let (cPsi', tA') = (normDCtx cPsi, normTyp (tA, LF.id)) in
        let p' = { mmvar with typ = ClTyp (PTyp tA', cPsi') } in
        let h' = Proj (MPVar ((p', t), LF.comp r sigma), k) in
        ( Root (loc, h', SClo (tS, sigma), plicity)
        , LF.id
        )
     end

  | (LFHole _, _) as sM -> sM
  | _ -> Error.violation "oops 4"

(* whnfRedex ((tM, s1), (tS, s2)) = (R, s')
 *
 * If cD ; Psi1 |- tM <= tA       and cD ; cPsi |- s1 <= Psi1
 *    cD ; Psi2 |- tS > tA <= tP  and cD ; cPsi |- s2 <= Psi2
 * then
 *    cD ; cPsi |- s' : cPsi'    and cD ; cPsi' |- R' -> tP'
 *
 *    [s']tP' = [s2]tP and [s']R' = tM[s1] @ tS[s2]
 *)
and whnfRedex =
  function
  | ((LFHole (l, id, name), s1), _) -> raise (InvalidLFHole l)
  | ((Root _ as root, s1), (Nil, _)) -> whnf (root, s1)

  | ((Lam (_, _, tM), s1), (App (tN, tS), s2)) ->
     let tN' = Clo (tN, s2) in      (* cD ; cPsi |- tN'      <= tA' *)
     let s1' = Dot (Obj tN', s1) in (* cD ; cPsi |- tN' . s1 <= Psi1, x:tA''
                                         tA'' = [s1]tA' *)
     whnfRedex ((tM, s1'), (tS, s2))

  | (sM, (SClo (tS, s2'), s2)) ->
     whnfRedex (sM, (tS, LF.comp s2' s2))

  | ((Clo (tM, s), s1), sS) ->
     whnfRedex ((tM, LF.comp s s1), sS)

(* and whnfTupleRedex (tup, s) k = reduceTuple (tup, k), s *)

(* whnfTyp (tA, sigma) = tA'
 *
 * If cD ; cPsi  |- tA <= type
 *    cD ; cPsi' |- sigma <= cPsi
 * then
 *    tA' = [sigma]tA
 *    cD ; cPsi' |- tA' <= type   and tA' is in weak head normal form
 *)
and whnfTyp (tA, sigma) =
  match tA with
  | Atom (loc, a, tS) -> (Atom (loc, a, SClo (tS, sigma)), LF.id)
  | PiTyp _ -> (tA, sigma)
  | TClo (tA, s) -> whnfTyp (tA, LF.comp s sigma)
  | Sigma _ -> (tA, sigma)


(* ----------------------------------------------------------- *)
(* Check whether constraints are solved *)
and constraints_solved =
  function
  | [] -> true
  | ({ contents = Queued _ } :: cnstrs) ->
      constraints_solved cnstrs
  | ({ contents = Eqn (_, _, _, INorm tM, INorm tN) } :: cnstrs) ->
     if conv (tM, LF.id) (tN, LF.id)
     then constraints_solved cnstrs
     else false
  | ({ contents = Eqn (_, _, _, IHead h1, IHead h2) } :: cnstrs) ->
     if convHead (h1, LF.id) (h2, LF.id)
     then constraints_solved cnstrs
     else false



(* Conversion :  Convertibility modulo alpha *)
(* convTyp (tA, s1) (tB, s2) = true iff [s1]tA = [s2]tB
 * conv (tM, s1) (tN, s2) = true    iff [s1]tM = [s2]tN
 * convSpine (S1, s1) (S2, s2) = true iff [s1]S1 = [s2]S2
 *
 * convSub s s' = true iff s = s'
 *
 * This is on normal forms -- needs to be on whnf.
 *)
and conv sM1 sN2 = conv' (whnf sM1, whnf sN2)

and conv' =
  function
  | ((Lam (_, _, tM1), s1), (Lam (_, _, tM2), s2)) ->
     conv (tM1, LF.dot1 s1) (tM2, LF.dot1 s2)

  | ((Tuple (_, tuple1), s1), (Tuple (_, tuple2), s2)) ->
     convTuple (tuple1, s1) (tuple2, s2)

  | ((Root (loc, AnnH (head, _), spine1, plicity), s1), sN) ->
     conv' ((Root (loc, head, spine1, plicity), s1), sN)

  | (sM, (Root (loc, AnnH (head, _), spine2, plicity), s2)) ->
     conv' (sM, (Root (loc, head, spine2, plicity), s2))

  | ((Root (_, head1, spine1, _), s1), (Root (_, head2, spine2, _), s2)) ->
     convHead (head1, s1) (head2, s2) && convSpine (spine1, s1) (spine2, s2)

  | _ -> false

and convTuple (tuple1, s1) (tuple2, s2) =
  match (tuple1, tuple2) with
  | (Last tM1, Last tM2) ->
     conv (tM1, s1) (tM2, s2)

  | (Cons (tM1, tuple1), Cons (tM2, tuple2)) ->
     conv (tM1, s1) (tM2, s2)
     && convTuple (tuple1, s1) (tuple2, s2)

  | _ -> false

and convHead (head1, s1) (head2, s2) =
  match (head1, head2) with
  | (BVar k1, BVar k2) ->
     k1 = k2

  | (Const c1, Const c2) ->
     Id.cid_equals c1 c2

  | (MVar (Offset u, s'), MVar (Offset w, s'')) ->
     u = w
     && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (MVar (Inst mv1, s'), MVar (Inst mv2, s''))
    | (MMVar ((mv1, _), s'), MMVar ((mv2, _), s''))
    | (MPVar ((mv1, _), s'), MPVar ((mv2, _), s'')) ->
     mv1.instantiation == mv2.instantiation
     && convSub (LF.comp s' s1) (LF.comp s'' s2)
  (* && convMSub   -bp *)
  (* why isn't convertibility of the msubs checked for MMVar & MPVar ? -je *)

  | (PVar (p, s'), PVar (q, s'')) ->
     p = q
     && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (FPVar (p, s'), FPVar (q, s'')) ->
     Id.equals p q
     && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (FMVar (u, s'), FMVar (w, s'')) ->
     Id.equals u w
     && convSub (LF.comp s' s1) (LF.comp s'' s2)

  | (Proj (BVar k1, i), Proj (BVar k2, j)) ->
     k1 = k2 && i = j

  | (Proj (PVar (p, s'), i), Proj (PVar (q, s''), j)) ->
     p = q && i = j
     && convSub (LF.comp s' s1) (LF.comp s'' s2)
  (* additional case: p[x] = x ? -bp*)

  | (FVar x, FVar y) -> Id.equals x y
  | _ ->
     dprint (fun () -> "[convHead] falls through ");
     false


and convSpine spine1 spine2 =
  match (spine1, spine2) with
  | ((Nil, _), (Nil, _)) -> true
  | ((App (tM1, spine1), s1), (App (tM2, spine2), s2)) ->
     conv (tM1, s1) (tM2, s2) && convSpine (spine1, s1) (spine2, s2)
  | (spine1, (SClo (tS, s), s')) -> convSpine spine1 (tS, LF.comp s s')
  | ((SClo (tS, s), s'), spine2) -> convSpine (tS, LF.comp s s') spine2

and convSub subst1 subst2 =
  match (subst1, subst2) with
  | (EmptySub, _) -> true (* this relies on the assumption that both are the same type... *)
  | (_, EmptySub) -> true
  | (Undefs, _) -> true (* hopefully Undefs only show up with empty domain? *)
  | (_, Undefs) -> true
  | (Shift n, Shift k) -> n = k
  | (SVar (s1, k, sigma1), SVar (s2, k', sigma2)) ->
     k = k'
     && s1 = s2
     && convSub sigma1 sigma2

  | FSVar (k1, (u1, s1)), FSVar (k2, (u2, s2)) ->
     k1 = k2 && Id.equals u1 u2 && convSub s1 s2

  | (Dot (f, s), Dot (f', s')) ->
     convFront f f' && convSub s s'

  | (Shift n, Dot (Head (BVar _), _)) ->
     convSub (Dot (Head (BVar (n + 1)), Shift (n + 1))) subst2

  | (Dot (Head (BVar _), _), Shift n) ->
     convSub subst1 (Dot (Head (BVar (n + 1)), Shift (n + 1)))

  | MSVar (k, ((_, mt), s0)), MSVar (k', ((_, mt'), s0')) ->
     k = k' && convSub s0 s0' && convMSub mt mt' (* assumes that subst1 and subst2 have been normalized *)

  | _ -> false

and convFront front1 front2 =
  match (front1, front2) with
  | (Head h1, Head h2) -> convHead (h1, LF.id) (h2, LF.id)
  | (Obj tM, Obj tN) -> conv (tM, LF.id) (tN, LF.id)

  | (Head h, Obj tN) ->
     begin match etaContract (norm (tN, LF.id)) with
     | Head h' -> convFront (Head h) (Head h')
     | _ -> false
     end

  | (Obj tN, Head h) ->
     begin match etaContract (norm (tN, LF.id)) with
     | Head h' -> convFront (Head h) (Head h')
     | _ -> false
     end

  | (Undef, Undef) -> true

  | _ ->
     dprint (fun () -> "[convFront] Falls through");
     false

and convMSub subst1 subst2 =
  match (subst1, subst2) with
  | (MShift n, MShift k) -> n = k

  | (MDot (f, s), MDot (f', s')) ->
     convMFront f f' && convMSub s s'

  | (MShift n, MDot (MV _, _)) ->
     convMSub (MDot (MV (n + 1), MShift (n + 1))) subst2

  | (MDot (MV _, _), MShift n) ->
     convMSub subst1 (MDot (MV (n + 1), MShift (n + 1)))

  | _ -> false

and convClObj m1 m2 =
  match (m1, m2) with
  | (MObj tM, MObj tN) -> conv (tM, LF.id) (tN, LF.id)
  | (PObj h1, PObj h2) -> convHead (h1, LF.id) (h2, LF.id)
  | (SObj s1, SObj s2) -> convSub s1 s2
  | _ -> false

and convMFront front1 front2 =
  match (front1, front2) with
  | (CObj cPsi, CObj cPhi) -> convDCtx cPsi cPhi
  | (ClObj (phat, m1), ClObj (phat', m2)) -> convDCtxHat phat phat' && convClObj m1 m2
  | _ -> false


and convTyp' sA sB =
  match (sA, sB) with
  | ((Atom (_, (a, b), spine1), s1), (Atom (_, (a', b'), spine2), s2)) ->
     if a = a' && b = b'
     then convSpine (spine1, s1) (spine2, s2)
     else false
  (*      a1 = a2 && convSpine (spine1, s1) (spine2, s2)*)

  | ((PiTyp ((TypDecl (_, tA1), _), tB1), s1), (PiTyp ((TypDecl (_, tA2), _), tB2), s2)) ->
     (* G |- A1[s1] = A2[s2] by typing invariant *)
     convTyp (tA1, s1) (tA2, s2) && convTyp (tB1, LF.dot1 s1) (tB2, LF.dot1 s2)

  | ((Sigma typrec1, s1), (Sigma typrec2, s2)) ->
     convTypRec (typrec1, s1) (typrec2, s2)

  | _ -> false


and convTyp sA sB = convTyp' (whnfTyp sA) (whnfTyp sB)




(* convTypRec ((recA, s), (recB, s'))
 *
 * Given: cD ; Psi1 |- recA <= type   and cD ; Psi2 |- recB  <= type
 *        cD ; cPsi  |- s <= cPsi       and cD ; cPsi  |- s' <= Psi2
 *
 * returns true iff recA and recB are convertible where
 *    cD ; cPsi |- [s]recA = [s']recB <= type
 *)
and convTypRec sArec sBrec =
  match (sArec, sBrec) with
  | ((SigmaLast (_, lastA), s), (SigmaLast (_, lastB), s')) ->
     convTyp (lastA, s) (lastB, s')

  | ((SigmaElem (_, tA, recA), s), (SigmaElem (_, tB, recB), s')) ->
     convTyp (tA, s) (tB, s') && convTypRec (recA, LF.dot1 s) (recB, LF.dot1 s')

  | _ -> (* lengths differ *)
     false

and convCtxVar psi psi' =
  match (psi, psi') with
  | (CtxName n1, CtxName n2) -> Id.equals n1 n2
  | (CtxOffset k1, CtxOffset k2) -> k1 = k2
  | _ -> false

(* convDCtx cPsi cPsi' = true iff
 * cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx
 *)
and convDCtx cPsi cPsi' =
  match (cPsi, cPsi') with
  | (Null, Null) -> true

  | (CtxVar c1, CtxVar c2) -> convCtxVar c1 c2

  | (DDec (cPsi1, TypDecl (_, tA)), DDec (cPsi2, TypDecl (_, tB))) ->
     convTyp (tA, LF.id) (tB, LF.id) && convDCtx cPsi1 cPsi2

  | _ -> false

and convDCtxHat (c1, d1) (c2, d2) =
  Maybe.equals convCtxVar c1 c2 && d1 = d2

(* convCtx cPsi cPsi' = true iff
 * cD |- cPsi = cPsi'  where cD |- cPsi ctx,  cD |- cPsi' ctx
 *)
let rec convCtx cPsi cPsi' =
  match (cPsi, cPsi') with
  | (Empty, Empty) -> true
  | (Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB))) ->
     convTyp (tA, LF.id) (tB, LF.id) && convCtx cPsi1 cPsi2
  | _ -> false
(* convPrefixCtx and convSubsetCtx should take into account subordination
let rec convPrefixCtx cPsi cPsi' =
  match (cPsi, cPsi') with
  | (_, Empty) ->
      true

  | (Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB))) ->
      convTyp (tA, LF.id) (tB, LF.id) && convPrefixCtx cPsi1 cPsi2

  | _ -> false
 *)
let rec convSubsetCtx cPsi cPsi' =
  match (cPsi, cPsi') with
  | (_, Empty) -> true
  | Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB)) ->
     if convTyp (tA, LF.id) (tB, LF.id)
     then convSubsetCtx cPsi1 cPsi2
     else
       (* keep tBs around and check that tA is a subordinate of tB,
       i.e. anything in tA cannot influence tB *)
       convSubsetCtx cPsi1 cPsi'

(* convPrefixTypRec ((recA, s), (recB, s'))
 *
 * Given: cD ; Psi1 |- recA <= type   and cD ; Psi2 |- recB  <= type
 *        cD ; cPsi  |- s <= cPsi       and cD ; cPsi  |- s' <= Psi2
 *
 * returns true iff recA and recB are convertible where
 *    cD ; cPsi |-   [s']recB is a prefix (subset) of [s]recA
 *)
and convPrefixTypRec sArec sBrec =
  match (sArec, sBrec) with
  | ((SigmaLast (_, lastA), s), (SigmaLast (_, lastB), s')) ->
     convTyp (lastA, s) (lastB, s')

  | ((SigmaElem (_, tA, recA), s), (SigmaLast (_, tB), s')) ->
     convTyp (tA, s) (tB, s') ||
       convPrefixTypRec (recA, LF.dot1 s) sBrec

  | ((SigmaElem (_, tA, recA), s), (SigmaElem (_, tB, recB), s')) ->
     if convTyp (tA, s) (tB, s')
     then convPrefixTypRec (recA, LF.dot1 s) (recB, LF.dot1 s')
     else convPrefixTypRec (recA, LF.dot1 s) sBrec

  | ((SigmaLast _, _), _) -> false

let prefixSchElem (SchElem (cSome1, typRec1)) (SchElem (cSome2, typRec2)) =
  convSubsetCtx cSome1 cSome2 && convPrefixTypRec (typRec1, LF.id) (typRec2, LF.id)

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

let mctxLookupDep cD k =
  Context.lookup' cD k
  |> Maybe.get'
       (Error.Violation
          ( "Meta-variable out of bounds -- looking for "
            ^ string_of_int k
            ^ " in context of length "
            ^ string_of_int (List.length (Context.to_list cD))
          )
       )
  |> function
    | Decl (u, mtyp, dep) ->
       (u, cnormMTyp (mtyp, MShift k), dep)
    | DeclOpt _ ->
       raise (Error.Violation "Expected declaration to have a type")

let mctxLookup cD k =
  let (u, tp, dep) = mctxLookupDep cD k in
  (u, tp)

(* ************************************************* *)

(* Note: If we don't actually handle this particular exception gracefully, then
   there's no need to have these four distinct functions. Inline them and let it throw
   the match exception instead. *)
let mctxMDec cD' k =
  match mctxLookup cD' k with
  | (u, ClTyp (MTyp tA, cPsi)) -> (u, tA, cPsi)
  | _ -> raise (Error.Violation "Expected ordinary meta-variable")

let mctxPDec cD k =
  match mctxLookup cD k with
  | (u, ClTyp (PTyp tA, cPsi)) -> (u, tA, cPsi)
  | _ -> raise (Error.Violation ("Expected parameter variable"))

let mctxSDec cD' k =
  match mctxLookup cD' k with
  | (u, ClTyp (STyp (cl, cPhi), cPsi)) -> (u, cPhi, cl, cPsi)
  (* u : [cPsi |- cPhi] *)
  | _ -> raise (Error.Violation "Expected substitution variable")

let mctxCDec cD k =
  match mctxLookup cD k with
  | (u, CTyp (Some sW)) -> (u, sW)
  | _ -> raise (Error.Violation ("Expected context variable"))

let mctxMVarPos cD u =
  let rec lookup cD k =
    match cD with
    | Dec (cD, Decl (v, mtyp, _)) ->
       if Id.equals v u
       then (k, cnormMTyp (mtyp, MShift k))
       else lookup cD (k + 1)
    | Dec (cD, _) -> lookup cD (k + 1)
    | Empty -> raise Fmvar_not_found
  in
  lookup cD 1

(******************************************
     Contextual weak head normal form for
     computation-level types
 ******************************************)

let normMTyp = normITyp

let normMetaTyp = normITyp

let rec normMetaObj (loc, mO) =
  let mO' =
    match mO with
    | CObj cPsi -> CObj (normDCtx cPsi)
    | ClObj (phat, n) -> ClObj (cnorm_psihat phat m_id, normMObj (n, LF.id))
  in
  (loc, mO')

and normMetaSpine =
  function
  | Comp.MetaNil -> Comp.MetaNil
  | Comp.MetaApp (mO, mT, mS, plicity) ->
     Comp.MetaApp (normMetaObj mO, normMetaTyp mT, normMetaSpine mS, plicity)

let rec normCTyp =
  function
  | Comp.TypBase (loc, c, mS) ->
     Comp.TypBase (loc, c, normMetaSpine mS)
  | Comp.TypCobase (loc, c, mS) ->
     Comp.TypCobase (loc, c, normMetaSpine mS)
  | Comp.TypBox (loc, mT) ->
     Comp.TypBox (loc, normMetaTyp mT)
  | Comp.TypArr (loc, tT1, tT2) ->
     Comp.TypArr (loc, normCTyp tT1, normCTyp tT2)

  | Comp.TypCross (loc, tT1, tT2) ->
     Comp.TypCross (loc, normCTyp tT1, normCTyp tT2)

  | Comp.TypPiBox (loc, (Decl (u, mtyp, dep)), tau) ->
     Comp.TypPiBox (loc, (Decl (u, normMTyp mtyp, dep)), normCTyp tau)

  | Comp.TypInd tau -> Comp.TypInd (normCTyp tau)

let rec cnormMetaObj ((loc, mO), t) = (loc, mfrontMSub mO t)

and cnormMetaSpine (mS, t) =
  match mS with
  | Comp.MetaNil -> Comp.MetaNil
  | Comp.MetaApp (mO, mT, mS, plicity) ->
     Comp.MetaApp
       ( cnormMetaObj (mO, t)
       , cnormMTyp (mT, t)
       , cnormMetaSpine (mS, t)
       , plicity
       )

let cnormCDecl (cdecl, t) =
  match cdecl with
  | Decl (u, mtyp, dep) -> Decl (u, cnormMTyp (mtyp, t), dep)

let rec cnormCTyp =
  function
  | (Comp.TypBase (loc, a, mS), t) ->
     let mS' = cnormMetaSpine (mS, t) in
     Comp.TypBase (loc, a, mS')
  | (Comp.TypCobase (loc, a, mS), t) ->
     let mS' = cnormMetaSpine (mS, t) in
     Comp.TypCobase (loc, a, mS')
  | (Comp.TypBox (loc, cT), t) ->
     Comp.TypBox (loc, cnormMTyp (cT, t))

  | (Comp.TypArr (loc, tT1, tT2), t) ->
     Comp.TypArr (loc, cnormCTyp (tT1, t), cnormCTyp (tT2, t))

  | (Comp.TypCross (loc, tT1, tT2), t) ->
     Comp.TypCross (loc, cnormCTyp (tT1, t), cnormCTyp (tT2, t))

  | (Comp.TypPiBox (loc, cdecl, tau), t) ->
     let cdecl' = cnormCDecl (cdecl, t) in
     Comp.TypPiBox (loc, cdecl', cnormCTyp (tau, mvar_dot1 t))

  | (Comp.TypClo (tT, t'), t) ->
     cnormCTyp (tT, mcomp t' t)

  | (Comp.TypInd tau, t) -> Comp.TypInd (cnormCTyp (tau, t))

let rec cnormCKind (cK, t) =
  match cK with
  | Comp.Ctype loc -> Comp.Ctype loc
  | Comp.PiKind (loc, cdecl, cK) ->
     let cdecl' = cnormCDecl (cdecl, t) in
     Comp.PiKind (loc, cdecl', cnormCKind (cK, mvar_dot1 t))

(*
  cD        |- [|t2|]cG2 = [|t1|]cG1 = cG'
  cD ; cG'  |- [|t2|]tT2 = [|t1|]tT2 = tT
 *)


let rec cwhnfCTyp =
  function
  | (Comp.TypBase (loc, c, mS), t) ->
     let mS' = normMetaSpine (cnormMetaSpine (mS, t)) in
     (Comp.TypBase (loc, c, mS'), m_id)
  | (Comp.TypCobase (loc, c, mS), t) ->
     let mS' = normMetaSpine (cnormMetaSpine (mS, t)) in
     (Comp.TypCobase (loc, c, mS'), m_id)

  | (Comp.TypBox (loc, cT), t) -> (Comp.TypBox (loc, cnormMTyp (cT, t)), m_id)

  | (Comp.TypArr _, _ as thetaT)
    | (Comp.TypCross _, _ as thetaT)
    | (Comp.TypPiBox _, _ as thetaT) -> thetaT

  | (Comp.TypClo (tT, t'), t) -> cwhnfCTyp (tT, mcomp t' t)

  | (Comp.TypInd tau, t) -> (Comp.TypInd (Comp.TypClo (tau, t)), m_id)


(* WHNF and Normalization for computation-level terms to be added -bp *)

(* cnormExp (e, t) = e'

   If cO ; cD  ; cG   |- e <= tau
      cO ; cD' ; cG'  |- [|t|]e <= tau'  where [|t|]cG = cG' and [|t|]tau = tau'
      cO ; cD'        |- t <= cD

   then e' = [|t|]e and cO ; cD' ; cG' |- e' <= tau'
 *)

let rec cnormExp =
  function
  | (Comp.Syn (loc, i), t) -> Comp.Syn (loc, cnormExp' (i, t))
  | (Comp.Fn (loc, x, e), t) -> Comp.Fn (loc, x, cnormExp (e, t))
  | (Comp.Fun (loc, fbr), t) -> Comp.Fun (loc, cnormFBranches (fbr, t))
  | (Comp.MLam (loc, u, e, plicity), t) -> Comp.MLam (loc, u, cnormExp (e, mvar_dot1 t), plicity)
  | (Comp.Pair (loc, e1, e2), t) -> Comp.Pair (loc, cnormExp (e1, t), cnormExp (e2, t))
  | (Comp.Impossible (loc, i), t) -> Comp.Impossible (loc, cnormExp' (i, t))
  | (Comp.LetPair (loc, i, (x, y, e)), t) ->
     Comp.LetPair (loc, cnormExp' (i, t), (x, y, cnormExp (e, t)))
  | (Comp.Let (loc, i, (x, e)), t) ->
     Comp.Let (loc, cnormExp' (i, t), (x, cnormExp (e, t)))

  | (Comp.Box (loc, cM, cU), t) ->
     let cM' = cnormMetaObj (cM, t) in
     let cU' = cnormMTyp (cU, t) in
     Comp.Box (loc, cM', cU')

  | (Comp.Case (loc, prag, i, branches), t) ->
     let i' = cnormExp' (i, t) in
     let branches' = List.map (fun b -> cnormBranch (b, t)) branches in
     Comp.Case (loc, prag, i', branches')

  | (Comp.Hole (loc, id, name), _) -> Comp.Hole (loc, id, name)

and cnormExp' =
  function
  | (Comp.Var _ as i, _) -> i
  | (Comp.DataConst _ as i, _) -> i
  | (Comp.Const _ as i, _) -> i
  | (Comp.Obs (loc, e, t', obs), t) ->
     Comp.Obs (loc, cnormExp (e, t), cnormMSub' (t', t), obs)
  | (Comp.Apply (loc, i, e), t) ->
     Comp.Apply (loc, cnormExp' (i, t), cnormExp (e, t))
  | (Comp.PairVal (loc, i1, i2), t) ->
     Comp.PairVal (loc, cnormExp' (i1, t), cnormExp' (i2, t))
  | (Comp.MApp (loc, i, cM, cU, pl), t) ->
     Comp.MApp (loc, cnormExp' (i, t), cnormMetaObj (cM, t), cnormMTyp (cU, t), pl)

  | (Comp.AnnBox (cM, cT), t') ->
     let cM' = cnormMetaObj (cM, t') in
     let cT' = cnormMTyp (cT, t') in
     Comp.AnnBox (cM', cT')

and cnormPattern (pat, t) =
  match pat with
  | Comp.PatMetaObj (loc, mO) ->
     Comp.PatMetaObj (loc, cnormMetaObj (mO, t))
  | Comp.PatConst (loc, c, patSpine) ->
     Comp.PatConst (loc, c, cnormPatSpine (patSpine, t))
  | Comp.PatFVar _ -> pat
  | Comp.PatVar _ -> pat
  | Comp.PatPair (loc, pat1, pat2) ->
     Comp.PatPair
       ( loc
       , cnormPattern (pat1, t)
       , cnormPattern (pat2, t)
       )
  | Comp.PatAnn (loc, pat, tau, plicity) ->
     Comp.PatAnn
       ( loc
       , cnormPattern (pat, t)
       , cnormCTyp (tau, t)
       , plicity
       )

and cnormPatSpine (patSpine, t) =
  match patSpine with
  | Comp.PatNil -> Comp.PatNil
  | Comp.PatApp (loc, pat, patSpine) ->
     Comp.PatApp
       ( loc
       , cnormPattern (pat, t)
       , cnormPatSpine (patSpine, t)
       )
  | Comp.PatObs (loc, obs, msub, patSpine) ->
     Comp.PatObs
       ( loc
       , obs
       , cnormMSub' (msub, t)
       , cnormPatSpine (patSpine, t)
       )

(* cnormBranch (BranchBox (cO, cD, (psihat, tM, (tA, cPsi)), e), theta, cs) =

   If  cD1 ; cG         |- BranchBox (cD, (psihat, tM, (tA, cPsi)), e) <= [|theta|]tau

       cD ; cPsi        |- tM <= tA

       cD1              |- theta <= cD1'

       cD1' ; cG'       |- BranchBox (cD, (psihat, tM, (tA, cPsi)), e') <= tau'

       cD1', cD ; cG    |- e' <= tau'

       cG = [|theta|]cG'   and    e  = [|theta|]e'

       |cD| = k

       cD1, cD          |- 1 .... k , (theta o ^k) <= cD1', cD

       cD1, cD          |- (theta o ^k) <= cD1

  then

       cD1, cD ; cG     |- [1...k, (theta o ^k)|]e'  <= [|theta o ^k |]tau

  BROKEN

 *)
and cnormBranch =
  function
  | ( Comp.Branch (loc, cD, cG, Comp.PatAnn (loc'', Comp.PatMetaObj (loc', mO), tau, plicity), t, e)
    , theta
    ) ->
     Comp.Branch
       ( loc
       , cD
       , cG
       , Comp.PatAnn (loc'', Comp.PatMetaObj (loc', normMetaObj mO), cnormCTyp (tau, m_id), plicity)
       , cnormMSub t
       , cnormExp (e, m_id)
       )

  | (Comp.Branch (loc, cD, cG, Comp.PatMetaObj (loc', mO), t, e), theta) ->
     (* cD' |- t <= cD    and   FMV(e) = cD' while
       cD' |- theta' <= cD0
       cD0' |- theta <= cD0
     * Hence, no substitution into e at this point -- technically, we
     * need to unify theta' and theta and then create a new cD'' under which the
     * branch makes sense -bp
     *)
     Comp.Branch
       ( loc
       , cD
       , cG
       , Comp.PatMetaObj (loc', normMetaObj mO)
       , cnormMSub t
       , cnormExp (e, m_id)
       )

  | (Comp.Branch (loc, cD, cG, pat, t, e), theta) ->
     (* THIS IS WRONG. -bp *)
     Comp.Branch (loc, cD, cG, pat, cnormMSub t, cnormExp (e, m_id))

and cnormFBranches (fbr, t) =
  match fbr with
  | Comp.NilFBranch loc -> fbr
  | Comp.ConsFBranch (loc, (cD, cG, patS, e), fbr') ->
     Comp.ConsFBranch (loc, (cD, cG, patS, cnormExp (e, t)), cnormFBranches (fbr', t))

let cnormThm (t, theta) =
  match t with
  | Comp.Program e -> Comp.Program (cnormExp (e, theta))
  | Comp.Proof p ->
     dprnt "[cnormThm] WARNING: normalizing a proof: no-op";
     (* XXX how should contextual substitution work with proofs? *)
     Comp.Proof p

let rec cwhnfCtx (cG, t) =
  match cG with
  | Empty -> Empty
  | Dec (cG, Comp.CTypDecl (x, tau, flag)) ->
     Dec (cwhnfCtx (cG, t), Comp.CTypDecl (x, Comp.TypClo (tau, t), flag))

let cnormCTypDecl (d, t) =
  match d with
  | Comp.CTypDecl (x, tau, flag) ->
     Comp.CTypDecl (x, cnormCTyp (tau, t), flag)
  | Comp.CTypDeclOpt x ->
     Comp.CTypDeclOpt x

let normIHArg =
  function
  | Comp.M cM -> Comp.M (normMetaObj (cnormMetaObj (cM, m_id)))
  | m -> m

let normIHDecl =
  function
  | Comp.WfRec (f, args, tau) ->
     let tau' = normCTyp (cnormCTyp (tau, m_id)) in
     let args' = List.map normIHArg args in
     Comp.WfRec (f, args', tau')

let normCTypDecl =
  function
  | Comp.CTypDecl (x, tau, flag) ->
     Comp.CTypDecl (x, normCTyp (cnormCTyp (tau, m_id)), flag)

let cnormIHArg (a, t) =
  match a with
  | Comp.M cM -> Comp.M (cnormMetaObj (cM, t))
  | _ -> a

let cnormIHDecl (d, t) =
  match d with
  | Comp.WfRec (f, args, tau) ->
     Comp.WfRec
       ( f
       , List.map (fun a -> cnormIHArg (a, t)) args
       , cnormCTyp (tau, t)
       )

let cnormIHCtx (cIH, t) =
  Context.map (fun d -> cnormIHDecl (d, t)) cIH

let cnormGCtx (cG, t) =
  Context.map (fun d -> cnormCTypDecl (d, t)) cG

let normIHCtx = Context.map normIHDecl

let normGCtx = Context.map normCTypDecl

let rec normMCtx cD =
  match cD with
  | Empty -> Empty
  | Dec (cD, Decl (u, mtyp, dep)) -> Dec (normMCtx cD, Decl (u, normMTyp mtyp, dep))


(* ----------------------------------------------------------- *)
(* Conversion: Convertibility modulo alpha for
     computation-level types
 *)

(* convCTyp (tT1, t1) (tT2, t2) = true iff [|t1|]tT1 = [|t2|]tT2 *)
let convClTyp =
  function
  | (MTyp tA, MTyp tA')
    | (PTyp tA, PTyp tA') ->
     convTyp (tA, LF.id) (tA', LF.id)
  | (STyp (_, cPhi), STyp (_, cPhi')) -> convDCtx cPhi cPhi'
  | _ -> false

let convMTyp thetaT1 thetaT2 =
  match (thetaT1, thetaT2) with
  | ((ClTyp (t1, cPsi1)), (ClTyp (t2, cPsi2))) ->
     convClTyp (t1, t2) && convDCtx cPsi1 cPsi2
  | ((CTyp cid_schema), (CTyp cid_schema')) ->
     Maybe.equals Id.cid_equals cid_schema cid_schema'
  | _ -> false (* ClTyp is never convertible to CTyp *)

let convMetaTyp thetaT1 thetaT2 = convMTyp thetaT1 thetaT2

let convITerm tM1 tM2 =
  match (tM1, tM2) with
  | (INorm n1, INorm n2) -> conv (n1, LF.id) (n2, LF.id)
  | (ISub s1, ISub s2) -> convSub s1 s2
  | (IHead h1, IHead h2) -> convHead (h1, LF.id) (h2, LF.id)

let rec convMetaObj (_, mO) (_, mO') = convMFront (mfrontMSub mO m_id) (mfrontMSub mO' m_id)

and convMetaSpine mS mS' =
  match (mS, mS') with
  | (Comp.MetaNil, Comp.MetaNil) -> true
  | (Comp.MetaApp (mO, mT, mS, p1), Comp.MetaApp (mO', mT', mS', p2)) ->
     convMetaObj mO mO'
     && convMetaTyp mT mT'
     && convMetaSpine mS mS'
     && Stdlib.(=) p1 p2

let rec convCTyp thetaT1 thetaT2 = convCTyp' (cwhnfCTyp thetaT1) (cwhnfCTyp thetaT2)

and convCTyp' thetaT1 thetaT2 =
  match (thetaT1, thetaT2) with
  | ((Comp.TypBase (_, c1, mS1), _), (Comp.TypBase (_, c2, mS2), _)) ->
     (* t1 = t2 = id by invariant *)
     Id.cid_equals c1 c2
     && convMetaSpine (cnormMetaSpine (mS1, m_id)) (cnormMetaSpine (mS2, m_id))

  | ((Comp.TypCobase (_, c1, mS1), _), (Comp.TypCobase (_, c2, mS2), _)) ->
     (* t1 = t2 = id by invariant *)
     Id.cid_equals c1 c2
     && convMetaSpine mS1 mS2

  | ((Comp.TypBox (_, cT1), _), (Comp.TypBox (_, cT2), _)) (* t1 = t2 = id *) ->
     convMetaTyp cT1 cT2

  | ((Comp.TypArr (_, tT1, tT2), t), (Comp.TypArr (_, tT1', tT2'), t')) ->
     convCTyp (tT1, t) (tT1', t') && convCTyp (tT2, t) (tT2', t')

  | ((Comp.TypCross (_, tT1, tT2), t), (Comp.TypCross (_, tT1', tT2'), t')) ->
     convCTyp (tT1, t) (tT1', t') && convCTyp (tT2, t) (tT2', t')

  | ( (Comp.TypPiBox (_, Decl (_, mtyp1, _), tT), t)
    , (Comp.TypPiBox (_, Decl (_, mtyp2, _), tT'), t')
    ) ->
     convMTyp (cnormMTyp (mtyp1, t)) (cnormMTyp (mtyp2, t'))
     && convCTyp (tT, mvar_dot1 t) (tT', mvar_dot1 t')

  | ((Comp.TypInd tau, t), ttau') ->
     convCTyp (tau, t) ttau'

  | (ttau, (Comp.TypInd tau', t')) ->
     convCTyp ttau (tau', t')

  | _ ->
     dprint (fun () -> "[convCtyp] falls through?");
     false

and convSchElem (SchElem (cPsi, trec)) (SchElem (cPsi', trec')) =
  convCtx cPsi cPsi'
  && convTypRec (trec, LF.id) (trec', LF.id)

let convCTypDecl d1 d2 =
  match (d1, d2) with
  | (Decl (x1, cT1, dep1), Decl (x2, cT2, dep2)) ->
     Id.equals x1 x2 && Depend.equals dep1 dep2
     && convMTyp cT1 cT2
  | (DeclOpt (x1, _), DeclOpt (x2, _)) ->
     Id.equals x1 x2

(** Checks if two declarations are convertible.
      If they're coming from a metacontext you should shift them so
      they make sense in the same context.
 *)
let convCompCTypDecl d1 d2 =
  let open Comp in
  match (d1, d2) with
  | (CTypDeclOpt x1, CTypDeclOpt x2) -> Id.equals x1 x2
  | (CTypDecl (x1, tau1, w1), CTypDecl (x2, tau2, w2)) ->
     Id.equals x1 x2 && Stdlib.(=) w1 w2
     && convCTyp (tau1, m_id) (tau2, m_id)

let mctx_to_list_shifted x =
  let f i d = cnormCDecl (d, MShift (i + 1)) in
  x |> Context.to_list |> List.mapi f

(* ------------------------------------------------------------ *)


(* etaExpandMV cPsi sA s' = tN
 *
 *  cPsi'  |- s'   <= cPsi
 *  cPsi   |- [s]A <= typ
 *
 *  cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMV cPsi sA n s' dep =
  etaExpandMV' cPsi (whnfTyp sA) n s' dep

and etaExpandMV' cPsi sA n s' dep =
  match sA with
  | (Atom (loc, _, _) as tP, s) ->
     let u = newMVar (Some (Id.inc n)) (cPsi, tclo tP s) dep in
     Root (loc, MVar (u, s'), Nil, Depend.to_plicity dep)

  | (PiTyp ((TypDecl (x, _) as decl, _), tB), s) ->
     Lam
       ( Id.loc_of_name x
       , x
       , etaExpandMV (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) n (LF.dot1 s') dep
       )

(* Coverage.etaExpandMVstr s' cPsi sA *)

(* etaExpandMMV cD cPsi sA s' = tN
 *
 *  cD ; cPsi'  |- s'   <= cPsi
 *  cD ; cPsi   |- [s]A <= typ
 *
 *  cD ; cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMMV loc cD cPsi sA n s' dep =
  etaExpandMMV' loc cD cPsi (whnfTyp sA) n s' dep

and etaExpandMMV' loc cD cPsi sA n s' dep =
  match sA with
  | (Atom _ as tP, s) ->
     let u = newMMVar (Some (Id.inc n)) (cD, cPsi, tclo tP s) dep in
     Root (loc, MMVar ((u, m_id), s'), Nil, Depend.to_plicity dep)

  | (PiTyp ((TypDecl (x, _) as decl, _), tB), s) ->
     Lam (loc, x, etaExpandMMV loc cD (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) n (LF.dot1 s') dep)

let rec closed sM = closedW (whnf sM)

and closedW (tM, s) =
  match tM with
  | Lam (_, _, tM) -> closed (tM, LF.dot1 s)
  | Root (_, h, tS, _) ->
     closedHead h
     && closedSpine (tS, s)
  | LFHole _ -> false
  | Tuple (_, tup) -> closedTuple (tup, s)

and closedTuple =
  function
  | (Last tM, s) -> closedW (tM, s)
  | (Cons (tM, tup), s) -> closedW (tM, s) && closedTuple (tup, s)

and closedHead =
  function
  | (MMVar ((mmvar, _), _) | MPVar ((mmvar, _), _) | MVar (Inst mmvar, _))
       when not (is_mmvar_instantiated mmvar) ->
     false
  | PVar (_, r) ->
     closedSub r
  | MVar (Offset _, r) ->
     closedSub r
  | _ -> true

and closedSpine (tS, s) =
  match tS with
  | Nil -> true
  | App (tN, tS') -> closed (tN, s) && closedSpine (tS', s)
  | SClo (tS', s') -> closedSpine (tS', LF.comp s' s)

and closedSub =
  function
  | EmptySub -> true
  | Undefs -> true
  | SVar (_, _, sigma) -> closedSub sigma
  | Shift _ -> true
  | Dot (ft, s) -> closedFront ft && closedSub s
  | MSVar (_, ((v, t), s)) ->
     (* the case for MMVar doesn't also check the substitution -je *)
     is_mmvar_instantiated v (* && closedSub s *)

and closedFront =
  function
  | Head h -> closedHead h
  | Obj tM -> closed (tM, LF.id)
  | Undef -> false

let rec closedTyp sA = closedTypW (whnfTyp sA)

and closedTypW (tA, s) =
  match tA with
  | Atom (_, _, tS) -> closedSpine (tS, s)
  | PiTyp ((t_dec, _), tA) ->
     closedDecl (t_dec, s)
     && closedTyp (tA, LF.dot1 s)
  | Sigma recA -> closedTypRec (recA, s)

and closedTypRec (recA, s) =
  match recA with
  | SigmaLast (_, tA) -> closedTyp (tA, s)
  | SigmaElem (_, tA, recA') ->
     closedTyp (tA, s)
     && closedTypRec (recA', LF.dot1 s)

and closedDecl (tdecl, s) =
  match tdecl with
  | TypDecl (_, tA) -> closedTyp (tA, s)
  | _ -> true

let rec closedDCtx =
  function
  | Null -> true
  | CtxVar (CInst (mmvar, theta)) ->
     begin match mmvar.instantiation.contents with
     | None -> false
     | Some (ICtx cPsi) -> closedDCtx (cnormDCtx (cPsi, theta))
     end
  | CtxVar _ -> true
  | DDec (cPsi', tdecl) -> closedDCtx cPsi' && closedDecl (tdecl, LF.id)


let closedClTyp =
  function
  | MTyp tA
    | PTyp tA ->
     closedTyp (tA, LF.id)
  | STyp (_, cPhi) -> closedDCtx cPhi

let closedMetaTyp =
  function
  | ClTyp (t, cPsi) -> closedClTyp t && closedDCtx cPsi
  | CTyp _ -> true

let rec closedMetaSpine =
  function
  | Comp.MetaNil -> true
  | Comp.MetaApp (mO, mT, mS, _) ->
     closedMetaObj mO && closedMetaTyp mT && closedMetaSpine mS

and closedMObj =
  function
  | MObj tM -> closed (tM, LF.id)
  | SObj s -> closedSub s
  | PObj h -> closedHead h

and closedMFront =
  function
  | CObj cPsi -> closedDCtx cPsi
  | ClObj (phat, t) ->
     closedDCtx (Context.hatToDCtx phat) && closedMObj t

and closedMetaObj (_, mF) = closedMFront mF

let closedDecl =
  function
  | Decl (_, cU, _) -> closedMetaTyp cU
  | DeclOpt _ ->
     Error.violation "[closedDecl] DeclOpt outside printing"

let rec closedCTyp =
  function
  | Comp.TypBase (_, _, mS) -> closedMetaSpine mS
  | Comp.TypCobase (_, _, mS) -> closedMetaSpine mS
  | Comp.TypBox (_, cT) -> closedMetaTyp cT
  | Comp.TypArr (_, cT1, cT2) -> closedCTyp cT1 && closedCTyp cT2
  | Comp.TypCross (_, cT1, cT2) -> closedCTyp cT1 && closedCTyp cT2
  | Comp.TypPiBox (_, ctyp_decl, cT) ->
      closedCTyp cT && closedDecl ctyp_decl
  | Comp.TypClo (cT, t) -> closedCTyp (cnormCTyp (cT, t)) (* to be improved Sun Dec 13 11:45:15 2009 -bp *)
  | Comp.TypInd tau -> closedCTyp tau

let closedCtx closedDecl =
  let rec go =
    function
    | Empty -> true
    | Dec (ctx, d) ->
       closedDecl d && go ctx
  in
  go

let closedCTypDecl =
  function
  | Comp.CTypDecl (_, tau, _) -> closedCTyp tau
  | Comp.CTypDeclOpt _ ->
     Error.violation
       "[closedCTypDecl] CTypDeclOpt outside printing"

let closedGCtx = closedCtx closedCTypDecl
let closedMCtx = closedCtx closedDecl

let rec closedMSub =
  function
  | MShift _ -> true
  | MDot (mF, t) ->
     closedMFront mF && closedMSub t

let rec closedExp =
  function
  | Comp.Syn (_, i) -> closedExp' i
  | Comp.Fn (_, _, e) -> closedExp e
  | Comp.Fun (_, bs) -> closedFunBranches bs
  | Comp.MLam (_, _, e, plicity) -> closedExp e
  | Comp.Pair (_, e1, e2) -> closedExp e1 && closedExp e2
  | Comp.LetPair (_, i, (_, _, e)) -> closedExp' i && closedExp e
  | Comp.Let (_, i, (_, e)) -> closedExp' i && closedExp e
  | Comp.Box (_, cM, cU) -> closedMetaObj cM && closedMetaTyp cU
  | Comp.Case (_, _, i, bs) -> closedExp' i && List.for_all closedBranch bs
  | Comp.Impossible (_, i) -> closedExp' i
  | Comp.Hole _ -> false

and closedExp' =
  function
  | Comp.Var _
    | Comp.DataConst _
    | Comp.Const _ ->
     true
  | Comp.Obs (_, e, t, _) -> closedExp e && closedMSub t
  | Comp.Apply (_, i, e) -> closedExp' i && closedExp e
  | Comp.MApp (_, i, cM, cU, _) ->
     closedExp' i && closedMetaObj cM && closedMetaTyp cU
  | Comp.AnnBox (cM, cU) ->
     closedMetaObj cM && closedMetaTyp cU
  | Comp.PairVal (_, i1, i2) ->
     closedExp' i1 && closedExp' i2

and closedBranch =
  function
  | Comp.Branch (_, _, (cD, cG), pat, t, e) ->
     closedMCtx cD
     && closedGCtx cG
     && closedPattern pat
     && closedMSub t
     && closedExp e

and closedFunBranches =
  function
  | Comp.NilFBranch _ -> true
  | Comp.ConsFBranch (_, (cD, cG, patS, e), bs) ->
     closedMCtx cD
     && closedGCtx cG
     && closedPatSpine patS
     && closedExp e
     && closedFunBranches bs

and closedPatSpine =
  function
  | Comp.PatNil -> true
  | Comp.PatApp (_, pat, patS) ->
     closedPattern pat && closedPatSpine patS
  | Comp.PatObs (_, _, t, patS) ->
     closedMSub t && closedPatSpine patS

and closedPattern =
  function
  | Comp.PatMetaObj (_, cM) -> closedMetaObj cM
  | Comp.PatConst (_, _, patS) -> closedPatSpine patS
  | Comp.PatFVar _ ->
     Error.violation "[closedPattern] PatFVar outside coverage"
  | Comp.PatVar _ -> true
  | Comp.PatPair (_, pat1, pat2) ->
     closedPattern pat1 && closedPattern pat2
  | Comp.PatAnn (_, pat, tau, _) ->
     closedPattern pat && closedCTyp tau

let mcomp' = Misc.Function.flip mcomp

let collapse_sigma =
  function
  | SigmaLast (_, tA) -> tA
  | SigmaElem _ as typ_rec -> Sigma typ_rec

let rec conv_subgoal_path p1 p2 =
  let open Comp.SubgoalPath in
  match (p1, p2) with
  | (Here, Here) -> true
  | (Intros p1, Intros p2) -> conv_subgoal_path p1 p2
  | (Suffices (_, k1, p1), Suffices (_, k2, p2))
       when k1 = k2 ->
     conv_subgoal_path p1 p2
  | (MetaSplit (_, `pvar k1, p1), MetaSplit (_, `pvar k2, p2))
       when Maybe.equals (=) k1 k2 ->
     conv_subgoal_path p1 p2
  | (MetaSplit (_, `ctor c1, p1), MetaSplit (_, `ctor c2, p2))
       when Id.cid_equals c1 c2 ->
     conv_subgoal_path p1 p2
  | (MetaSplit (_, `bvar, p1), MetaSplit (_, `bvar, p2)) ->
     conv_subgoal_path p1 p2
  | (CompSplit (_, c1, p1), CompSplit (_, c2, p2))
       when Id.cid_equals c1 c2 ->
     conv_subgoal_path p1 p2
  | (ContextSplit (_, Comp.EmptyContext _, p1), ContextSplit (_, Comp.EmptyContext _, p2)) ->
     conv_subgoal_path p1 p2
  | (ContextSplit (_, Comp.ExtendedBy (_, k1), p1), ContextSplit (_, Comp.ExtendedBy (_, k2), p2))
       when k1 = k2 ->
     conv_subgoal_path p1 p2
  | _ -> false

let conv_subgoal_path_builder b1 b2 =
  Comp.SubgoalPath.(conv_subgoal_path (b1 Here) (b2 Here))

(** General convertibility of contexts, provided a function to check
    convertibility of declarations.
    This is a quite strong notion of convertibility that requires that
    both contexts have the same length and that declarations are
    pairwise convertible.
 *)
let conv_ctx conv_decl =
  let rec go ctx1 ctx2 =
    match (ctx1, ctx2) with
    | (Empty, Empty) -> true
    | (Dec (ctx1, d1), Dec (ctx2, d2))
         when conv_decl d1 d2 ->
       go ctx1 ctx2
    | _ -> false
  in
  go

let convGCtx (cG1, t1) (cG2, t2) =
  let f (Comp.CTypDecl (_, tau1, _)) (Comp.CTypDecl (_, tau2, _)) =
    convCTyp (tau1, t1) (tau2, t2)
  in
  conv_ctx f cG1 cG2

let convMCtx cD1 cD2 =
  let f (Decl (_, cU1, _)) (Decl (_, cU2, _)) =
    convMetaTyp cU1 cU2
  in
  conv_ctx f cD1 cD2

let rec lowerTyp cPsi =
  function
  | (Atom _, _) as sA -> (cPsi, whnfTyp sA)
  | (PiTyp ((decl, _), tB), s) -> lowerTyp (DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s)

let mmVarToClObj loc' (mV : mm_var) : cltyp -> clobj =
  function
  | MTyp tA -> MObj (Root (loc', MMVar ((mV, m_id), LF.id), Nil, `explicit))
  | PTyp tA -> PObj (MPVar ((mV, m_id), LF.id))
  | STyp (_, cPhi) -> SObj (MSVar (0, ((mV, m_id), LF.id)))

let mmVarToMFront loc' mV =
  function
  | ClTyp (mt, cPsi) ->
     ClObj (Context.dctxToHat cPsi, mmVarToClObj loc' mV mt)
  | CTyp schema_cid ->
     CObj (CtxVar (CInst (mV, m_id)))

(** Extends the given meta-substitution with a fresh unification
    variable for the contextual declaration (u, cU, dep).
    Returns a meta-object containing the MMVar and the extended
    substitution.

    dotMMVar loc' cD t (u, cU, dep) = (cM, t') if
    * cD |- [t]cU metatype

    This function is useful when eliminating PiBoxes via unification.

    See {!require_decl}.
 *)
let dotMMVar loc' cD t (u, cU, dep) =
  let cU = cnormMTyp (cU, t) in
  let mO = mmVarToMFront loc' (newMMVar' (Some u) (cD, cU) dep) cU in
  ((loc', mO), MDot (mO, t))
