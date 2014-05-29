(** Substitutions

    @author Brigitte Pientka
*)


open Syntax.Int.LF

module LF = struct

  exception Error of string
  exception NotComposable of string

  (**************************)
  (* Explicit Substitutions *)
  (**************************)

  (* id = ^0
   *
   * Invariant:
   *
   * cPsi |- id : cPsi      id is patsub
   *
   * Note: we do not take into account weakening here.
   *)
  let id =  Shift 0

  (* shift = ^1
   *
   * Invariant:
   *
   * cPsi, x:tA |- ^ : cPsi     ^ is patsub
   *)
  let shift =  Shift 1

  (* invShift = ^-1 = _.^0
   *
   * Invariant:
   *
   * Psi |- ^-1 : Psi, A    ^-1 is patsub
   *)
  let invShift = Dot (Undef, id)

  let shiftComp n s2 = match (n, s2) with
    | (0,s) -> s
    | (n,EmptySub) -> raise (NotComposable "Shift, EmptySub")
    | (n,Undefs) -> Undefs
    | (n,SVar(s, k, r)) -> SVar (s, (k+n), r)
    | (n,MSVar(s, k, (t,r))) -> MSVar (s, (k+n), (t,r))
    | (n,FSVar (s, k, tau)) -> FSVar (s, (k+n), tau)
    | (n,Shift m) -> Shift (n + m)
    | (n,Dot (_ft, s)) -> shiftComp (n - 1) s
 
  (* comp s1 s2 = s'
   *
   * Invariant:
   *
   * If   Psi'  |- s1 : Psi
   * and  Psi'' |- s2 : Psi'
   * then s'  =  s1 o s2
   * and  Psi'' |- s1 o s2 : Psi
   *
   * If   s1, s2 patsub
   * then s' patsub
   *)
  let rec comp s1 s2 = match (s1, s2) with
    | (EmptySub, s2) -> EmptySub
    | (Undefs, s2) -> Undefs
    | (s, Shift 0) -> s (* Optimization *)
    | (Shift n , s2) -> shiftComp n s2
    | (SVar (s, n, tau), s2) ->
        SVar (s, n, comp tau s2)

    | (MSVar (s, n, (theta, tau)), s2) ->
        MSVar (s, n, (theta, comp tau s2))

    | (FSVar (s, n, tau), s2) ->
        FSVar (s, n, comp tau s2)

    | (Dot (ft, s), s') ->
        (* comp(s[tau], Shift(k)) = s[tau]
         * where s :: Psi[Phi]  and |Psi| = k
         *
         * comp(s[tau], Shift(k)) = Dot(Id(1), ... Dot(Id(k0), s[tau]))
         * where s :: Psi[Phi]  and |Psi| = k'
         * k = k' + k0
         *)
        let h = frontSub ft s' in
          Dot (h, comp s s')

  (* bvarSub n s = Ft'
   *
   * Invariant:
   *
   * If    Psi |- s <= Psi'    Psi' |- n <= A
   * then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
   * or  Ft' = ^(n + k)      if  s = Ft1 .. Ftm ^k   and m < n
   * and Psi |- Ft' <= [s]A
   *)
  and bvarSub n s = match (n, s) with
    | (_, Undefs) -> Undef
    | (1, Dot (ft, _s))  -> ft
    | (n, Dot (_ft, s))  -> bvarSub (n - 1) s
    | (n, Shift k) -> Head (BVar (n + k))
(*    | (n, MSVar (s, (_cshift, k), (mt, sigma ))) ->
        (* Should be fixed; we really need phat of n to avoid printing
           Free BVar (n+k) ...
           (Head (HClo (phat. BVar n+k , s , sigma ))
           -bp *)
        Head (HMClo(n+k, s, (mt,sigma)))

      Can this happen ?
*)
    | (n, SVar (s, k, sigma )) ->
        (* Should be fixed; we really need phat of n to avoid printing
           Free BVar (n+k) ... -bp *)
        Head (HClo(n+k, s, sigma))
    | (n, MSVar (s, k, (t,sigma ))) ->
      Head (HMClo (n+k, s, (t,sigma)))
(*        (print_string "[bvarSub] n, MSVar - not implemented";
        raise (NotComposable "grr"))
*)

  (* frontSub Ft s = Ft'
   *
   * Invariant:
   *
   * If   Psi |- s : Psi'     Psi' |- Ft : A
   * then Ft' = Ft [s]
   * and  Psi |- Ft' : [s]A
   *)
  and frontSub ft s = match ft with
    | Head (HClo(n, s', sigma)) -> Head (HClo (n, s', comp sigma s))
    | Head (HMClo(n, s', (theta,sigma))) -> Head (HMClo (n, s', (theta, comp sigma s)))
    | Head (BVar n)       ->  bvarSub n s
    | Head (FVar _)       -> ft
    | Head (MVar (u, s')) -> Head (MVar (u, comp s' s))
    | Head (PVar (u, s')) -> Head (PVar (u, comp s' s))

    | Head (Proj (BVar n, k))  ->
        begin match bvarSub n s with
          | Head (BVar x) ->
              Head (Proj (BVar x, k))

          | Head (PVar _ as h) ->
              Head (Proj (h, k))

          | Obj (Tuple (_, tuple)) ->
              let rec nth s = function
                | (Last u, 1) -> (u, s)
                | (Cons (u, _), 1) -> (u, s)
                | (Cons (u, tuple), n) -> nth (Dot(Obj u, s)) (tuple, n - 1)
              in
(*              Obj (Clo (nth s (tuple, k))) *)
                Obj (fst (nth s (tuple, k)))
        end

    | Head (Proj (h, k))  ->
        begin match frontSub (Head h) s with
          | Head h' ->
              Head (Proj (h', k))

          | Obj (Tuple (_, tuple)) ->
              let rec nth s = function
                | (Last u, 1) -> (u, s)
                | (Cons (u, _), 1) -> (u, s)
                | (Cons (u, tuple), n) -> nth (Dot(Obj u, s)) (tuple, n - 1)
              in
(*              Obj (Clo (nth s (tuple, k))) *)
                Obj (fst (nth s (tuple, k)))
        end

    | Head (AnnH (h, a))  ->
        let Head h' = frontSub (Head h) s in
          Head (AnnH (h', a))

    | Head (Const c)      -> Head (Const c)
    | Obj u               -> Obj (Clo (u, s))
    | Undef               -> Undef
    | Head (MMVar (_n, _ )) -> raise (Error "[frontSub] mmvar undefined ")
    | Head (FPVar (_n, _s' )) -> ft
(*    | Head (HMClo(n, s', (theta, sigma))) ->
        Head (HMClo (n, s', (mt, comp sigma s)) ?? *)

  (* dot1 (s) = s'
   *
   * Invariant:
   *
   * If   Psi |- s : Psi'
   * then s' = 1. (s o ^)
   * and  for all A s.t.  Psi' |- A : type
   * Psi, [s]A |- s' : Psi', A
   *
   * If s patsub then s' patsub
   *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  and dot1 s = match s with
    | Shift 0 -> s
    | s             -> Dot (Head (BVar 1), comp s shift)



  (* decSub (x:tA) s = (x:tA[s])
   *
   * Invariant:
   *
   * If   D ; Psi  |- s     <= Psi'    D ; Psi' |- A <= type
   * then D ; Psi  |- [s]A] <= type
   *)

  (* First line is an optimization suggested by cs *)
  (* Dec[id] = Dec *)
  (* Sat Feb 14 18:37:44 1998 -fp *)
  (* seems to have no statistically significant effect *)
  (* undo for now Sat Feb 14 20:22:29 1998 -fp *)
  (*
    fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, A), s) = Dec (x, Clo (A, s))
  *)
  let decSub (TypDecl (x, tA)) s = TypDecl (x, TClo (tA, s))


  (* invDot1 (s)         = s'
   * invDot1 (1. s' o ^) = s'
   *
   * Invariant:
   *
   * s = 1 . s' o ^
   * If Psi' |- s' : Psi
   * (so Psi',A[s] |- s : Psi,A)
   *)
  (*  let invDot1 s = comp (comp shift s) invShift *)


  (***************************)
  (* Inverting Substitutions *)
  (***************************)

  (* invert s = s'
   *
   * Invariant:
   *
   * If   D ; Psi  |- s  <= Psi'    (and s patsub)
   * then D ; Psi' |- s' <= Psi
   * s.t. s o s' = id    (comp s' s = id)
   *)
  let invert s =
    let rec lookup n s p = match s with
      | EmptySub                -> None
      | Undefs                  -> None
      | Shift _                 -> None
      | Dot (Undef, s')         -> lookup (n + 1) s' p
      | Dot (Head (BVar k), s') ->
          if k = p then
            Some (Head (BVar n))
          else
            lookup (n + 1) s' p
    in

    let rec invert'' p si = match p with
      | 0 -> si
      | p ->
          let front = match lookup 1 s p with
            | Some h -> h
            | None   -> Undef
          in
            invert'' (p - 1) (Dot (front, si)) in

    let rec invert' n s maxoffset = match s with
      | EmptySub ->
          invert'' maxoffset Undefs
      | Undefs ->
          invert'' maxoffset Undefs

      | Shift p ->
          invert'' p (Shift n)

      | Dot (Head (BVar k), s') ->
          invert' (n + 1) s' (max k maxoffset)

      | Dot (_,s') -> (* Is this really necessary? -ac *)
          invert' (n + 1) s' maxoffset

    in
      invert' 0 s 0


  (* strengthen s Psi = Psi'
   *
   * If   D ; Psi'' |- s : Psi  (* and s is a pattern sub *)
   * then D ; Psi'  |- s : Psi  and Psi' subcontext of Psi
   *)
  let rec strengthen s cPsi = match (s, cPsi) with
    | (Shift  _ (* 0 *) , Null) ->
        Null

    | (Shift _ , CtxVar psi) ->
        CtxVar psi

    | (Dot (Head (BVar _k) (* k = 1 *), t), DDec (cPsi, decl)) ->
        let t' = comp t invShift in
          (* Psi  |- x:A dec where decl = x:A
           * Psi' |- t' : Psi
           * Psi' |- x:[t']A dec
           *)
          DDec (strengthen t' cPsi, decSub decl t')

    | (Dot (Undef, t), DDec (cPsi, _)) ->
        strengthen t cPsi

    | (Shift n, cPsi) ->
        strengthen (Dot (Head (BVar (n + 1)), Shift (n + 1))) cPsi


  (* isId : sub -> bool
   *
   * Invariant:
   *
   * Given   Psi |- s: Psi', s weakensub
   * isId s  returns true iff  s = id and Psi' = Psi.
   *)
  let isId s =
    let rec isId' s k' = match s with
      | Shift k   -> k = k'
      | Dot (Head (BVar n), s') -> n = (k' + 1) && isId' s' (k' + 1)
      | _                       -> false
    in
      isId' s 0


(* cloInv (U, w) = U[w^-1]
 *
 * Invariant:
 *
 * If Psi |- M <= A
 * Psi |- w  <= Psi'  w pattern subst
 * [w^-1]M defined (without pruning or constraints)
 *
 * then Psi' |- [w^-1]M : [w^-1]A
 *
 * Effects: None
 *)
(*   let cloInv (tM, w) = Clo (tM, invert w) *)



(* compInv s w = t
 *
 * Invariant:
 *
 * If  D ; Psi |- s <= Psi1
 * D ; Psi |- w <= Psi'
 * then  t = s o (w^-1)
 * and   D ; Psi' |- t <= Psi1
 *)
(*  let compInv s w = comp s (invert w) *)

  (* isMId t = B
   *
   * Invariant:
   *
   * If   cD |- t: cD', t weaken_msub
   * then B holds
   * iff t = id, cD' = cD
   *)
  let isMId t =
    let rec isId' s k' = match s with
      | MShift k   -> k = k'
      | MDot (MV n, s') -> n = k' && isId' s' (k' + 1)
      | _                       -> false
    in
      isId' t 0


(* applyMSub n t = MFt'

   Invariant:

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ft_n      if  t = Ft_1 .. Ft_n .. ^0
     and D ; [|t|]Psi |- Ft' <= [|t|]A
 *)
let rec applyMSub n t = match (n, t) with
    | (1, MDot (ft, _t)) -> ft
    | (n, MDot (_ft, t)) -> applyMSub (n - 1) t
    | (n, MShift k)       -> MV (k + n)

  (* identity : dctx -> sub
   *
   * identity cPsi = id(cPsi),
   * e.g.
   *      identity (psi, x:A, y:B) = Dot(Head (BVar 1, Dot(Head(BVar 2, Shift(NoCtxShift, 2)))))
   *)
  let identity cPsi =
    let rec inner n = function
    | Null -> Shift n
    | CtxVar _ -> Shift n
    | DDec(cPsi, _) -> let n = n + 1 in Dot(Head (BVar n), inner n cPsi)
    in
      inner 0 cPsi


  (* justCtxVar : dctx -> sub
   *
   * justCtxVar cPsi = id[\psi]  where \psi is cPsi's context variable
   * e.g.
   *      justCtxVar (psi, x:A, y:B) = Shift(NoCtxShift, 2)
   *)
  let justCtxVar cPsi =
    let rec inner n = function
    | Null -> Shift n
    | CtxVar _ -> Shift n
    | DDec(cPsi, _) -> let n = n + 1 in inner n cPsi
    in
      inner 0 cPsi


end
