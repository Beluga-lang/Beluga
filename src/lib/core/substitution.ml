(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Substitutions

    @author Brigitte Pientka
*)

open Syntax.Int.LF

module LF = struct

  (**************************)
  (* Explicit Substitutions *)
  (**************************)


  (* id = ^0 
     
     Invariant:

     cPsi |- id : cPsi      id is patsub

     Note: we do not take into account weakening here. 
  *)
  let id = Shift 0



  (* shift = ^1
     
     Invariant:

     cPsi, x:tA |- ^ : cPsi     ^ is patsub
  *)
  let shift = Shift 1



  (* invShift = ^-1 = _.^0

     Invariant:

     Psi |- ^-1 : Psi, A    ^-1 is patsub
  *)
  let invShift = Dot (Undef, id)



  (* comp (s1, s2) = s'

     Invariant:

     If   Psi'  |- s1 : Psi 
     and  Psi'' |- s2 : Psi'
     then s'  =  s1 o s2
     and  Psi'' |- s1 o s2 : Psi

     If   s1, s2 patsub
     then s' patsub
  *)
  let rec comp s1 s2 = match (s1, s2) with
    | (Shift 0, s)             -> s
	(* next line is an optimization *)
	(* roughly 15% on standard suite for Twelf 1.1 *)
	(* Sat Feb 14 10:15:16 1998 -fp *)
    | (s, Shift 0)             -> s
    | (SVar (s, tau), s2)      -> SVar (s, comp tau s2)
	(* (s1, SVar(s,tau)) => undefined ? -bp *)
    | (Shift n, Dot (_ft, s))  -> comp (Shift (n - 1)) s
    | (Shift n, Shift m)       -> Shift (n + m)
    | (Dot (ft, s), s')        -> Dot (frontSub ft s', comp s s')
	(* comp(s[tau], Shift(k)) = s[tau]
	   where s :: Psi[Phi]  and |Psi| = k 

	   comp(s[tau], Shift(k)) = Dot(Id(1), ... Dot(Id(k0), s[tau]))
	   where s :: Psi[Phi]  and |Psi| = k'
	   k = k' + k0  
	*)



  (* bvarSub n s = Ft'
     
     Invariant: 

     If    Psi |- s <= Psi'    Psi' |- n <= A
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
     or  Ft' = ^(n + k)    if  s = Ft1 .. Ftm ^k   and m < n
     and Psi |- Ft' <= [s]A
  *)
  and bvarSub n s = match (n, s) with
    | (1, Dot (ft, _s)) -> ft
    | (n, Dot (_ft, s)) -> bvarSub (n - 1) s
    | (n, Shift k)      -> Head (BVar (n + k))



  (* frontSub Ft s = Ft'

     Invariant:

     If   Psi |- s : Psi'     Psi' |- Ft : A
     then Ft' = Ft [s]
     and  Psi |- Ft' : [s]A
  *)
  and frontSub ft s = match ft with
    | Head (BVar n)       -> bvarSub n s
    | Head (MVar (u, s')) -> Head (MVar (u, comp s' s))
    | Head (PVar (u, s')) -> Head (PVar (u, comp s' s))

    | Head (Proj (h, k))  ->
	let Head h' = frontSub (Head h) s in
          Head (Proj (h', k))

    | Head (AnnH (h, a))  ->
	let Head h' = frontSub (Head h) s in
          Head (AnnH (h', a))

    | Head (Const c)      -> Head (Const c)
    | Obj u               -> Obj (Clo (u, s))
    | Undef               -> Undef



  (* dot1 (s) = s'

     Invariant:

     If   Psi |- s : Psi'
     then s' = 1. (s o ^)
     and  for all A s.t.  Psi' |- A : type
     Psi, [s]A |- s' : Psi', A 

     If s patsub then s' patsub
  *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  and dot1 s = match s with
    | Shift 0 -> s
    | s       -> Dot (Head (BVar 1), comp s shift)



  (* decSub (x:tA) s = (x:tA[s])

     Invariant:

     If   D ; Psi  |- s     <= Psi'    D ; Psi' |- A <= type
     then D ; Psi  |- [s]A] <= type
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
     invDot1 (1. s' o ^) = s'

     Invariant:

     s = 1 . s' o ^
     If Psi' |- s' : Psi
     (so Psi',A[s] |- s : Psi,A)
  *)
  let invDot1 s = comp (comp shift s) invShift



  (***************************)
  (* Inverting Substitutions *)
  (***************************)

  (* invert s = s'

     Invariant:

     If   D ; Psi  |- s  <= Psi'    (and s patsub)
     then D ; Psi' |- s' <= Psi
     s.t. s o s' = id  
  *)
  let invert s =
    let rec lookup n s p = match s with
      | Shift _                 -> None
      | Dot (Undef, s')         -> lookup (n + 1) s' p
      | Dot (Head (BVar k), s') ->
          if k = p
          then Some n
          else lookup (n + 1) s' p in

    let rec invert'' p si = match p with
      | 0 -> si
      | p ->
          let front = match lookup 1 s p with
            | Some k -> Head (BVar k)
            | None   -> Undef
          in
            invert'' (p - 1) (Dot (front, si)) in

    let rec invert' n s = match s with
      | Shift p     -> invert'' p (Shift n)
      | Dot (_, s') -> invert' (n + 1) s'

    in
      invert' 0 s



  (* strengthen t Psi = Psi'

     Invariant:

     If   D ; Psi'' |- t : Psi  (* and t is a pattern sub *)
     then D ; Psi'  |- t : Psi  and cPsi' subcontext of cPsi
  *)
  let rec strengthen s cPsi = match (s, cPsi) with
    | (Shift _n (* = 0 *), Null)
      -> Null

    | (Dot (Head (BVar _k) (* k = 1 *), t), DDec (cPsi, decl))
      -> let t' = comp t invShift in
        (* Psi  |- x:A dec where decl = x:A    *)
        (* Psi' |- t' : Psi    *)
        (* Psi' |- x:[t']A dec *)
        DDec (strengthen t' cPsi, decSub decl t')

    | (Dot (Undef, t), DDec (cPsi, _))
      -> strengthen t cPsi

    | (Shift n, cPsi)
      -> strengthen (Dot (Head(BVar (n + 1)), Shift (n + 1))) cPsi



  (* isId s = B
     
     Invariant:

     If   Psi |- s: Psi', s weakensub
     then B holds 
     iff s = id, Psi' = Psi
  *)
  let isId s =
    let rec isId' s k' = match s with
      | Shift k                 -> k = k'
      | Dot (Head (BVar n), s') -> n = k' && isId' s' (k' + 1)
      | _                       -> false
    in
      isId' s 0



  (* cloInv (U, w) = U[w^-1]

     Invariant:

     If Psi |- M <= A
     Psi |- w  <= Psi'  w pattern subst
     [w^-1]M defined (without pruning or constraints)

     then Psi' |- [w^-1]M : [w^-1]A

     Effects: None
  *)
  let cloInv (tM, w) = Clo (tM, invert w)



  (* compInv s w = t

     Invariant:

     If  D ; Psi |- s <= Psi1 
     D ; Psi |- w <= Psi'
     then  t = s o (w^-1)
     and   D ; Psi' |- t <= Psi1
  *)
  let compInv s w = comp s (invert w)



  (* isPatSub s = B

     Invariant:

     If    Psi |- s : Psi' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  let rec isPatSub s = match s with
    | Shift _k              -> true
    | Dot (Head(BVar n), s) ->
	let rec checkBVar s' = match s' with
          | Shift k                 -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Undef, s)          -> checkBVar s
          | _                       -> false
	in
          checkBVar s && isPatSub s
    | Dot (Undef, s)        -> isPatSub s
    | _                     -> false

end

module Ctx = struct 

  (*************************************)
  (* Contextual Explicit Substitutions *)
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


  (* comp (t1, t2) = t'

     Invariant:

     If   D'  |- t1 : D 
     and  D'' |- t2 : D'
     then s'  =  t1 o t2
     and  D'' |- t1 o t2 : D

  *)
  let rec comp t1 t2 = match (t1, t2) with
    | (MShift 0, t)             -> t
    | (t, MShift 0)             -> t
    | (MShift n, MDot (_ft, t))  -> comp (MShift (n - 1)) t
    | (MShift n, MShift m)       -> MShift (n + m)
    | (MDot (mft, t), t')        -> MDot (mfrontMSub mft t', comp t t')

  (* mvarMSub n t = MFt'
     
     Invariant: 

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
     or  Ft' = ^(n + k)    if  s = Ft1 .. Ftm ^k   and m < n
     and Psi |- Ft' <= [|t|]A
  *)

  and mvarMSub n t = match (n, t) with
    | (1, MDot (ft, _t)) -> ft
    | (n, MDot (_ft, t)) -> mvarMSub (n - 1) t
    | (n, MShift k)      -> Id (n + k)

  (* mfrontMSub Ft t = Ft'

     Invariant:

     If   D |- t : D'     D' ; Psi |- Ft <= A
     then Ft' =  [|t|] Ft
     and  D ; [|t|]Psi |- Ft' : [|t|]A
  *)
  and mfrontMSub ft t = match ft with
    | Id n       -> mvarMSub n t
    | MObj (phat, tM)     -> MObj (phat, MClo (tM, t))


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


  (* wcnfCtx cPsi t = cPsi' 
     Invariant: 

     If cD |- cPsi ctx   and cD' |- t : cD
     the cD' |- cPsi' ctx

  *)
  let rec wcnfCtx cPsi t = match cPsi with
    | Null             -> Null
    | CtxVar _         -> cPsi
    | DDec (cPsi', TypDecl(x,tA)) -> 
	DDec (wcnfCtx cPsi' t, TypDecl (x, TMClo(tA, t)))

  (* mdecMSub (u::tA[cPsi]) t = (x: (tA'[cPsi'])
     Invariant:

     If   D   |- t     <= D'    D' ; cPsi |- tA <= type
     then [|t|]tA = tA'  and [|t|]cPsi = cPsi'
     D ; Psi'  |- A' <= type
  *)

  let mdecMSub (MDecl (u, tA, cPsi)) t = 
    let cPsi' = wcnfCtx cPsi t in 
      MDecl (u, TMClo (tA, t), cPsi')



  (* ismId t = B
     
     Invariant:

     If   D |- t: D',
     then B holds 
     iff t = id, D' = D
  *)
  let ismId t =
    let rec ismId' t k' = match t with
      | MShift k                 -> k = k'
      | MDot (Id n, t') -> n = k' && ismId' t' (k' + 1)
      | _                       -> false
    in
      ismId' t 0

end
