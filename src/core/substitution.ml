(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Substitutions

    @author Renaud Germain
    @author Darin Morrison
    @author Brigitte Pientka
*)

open Syntax.Int



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

     G |- ^-1 : G, V    ^-1 is patsub
*)
let invShift = Dot (Undef, id)



(* comp (s1, s2) = s'

   Invariant:

   If   G'  |- s1 : G 
   and  G'' |- s2 : G'
   then s'  =  s1 o s2
   and  G'' |- s1 o s2 : G

   If   s1, s2 patsub
   then s' patsub
*)
let rec comp s1 s2 = match (s1, s2) with
  | (Shift 0, s)             -> s
  (* next line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:15:16 1998 -fp *)
  | (s, Shift 0)             -> s
  | (SVar (s, tau), s2)      -> SVar(s, comp tau s2)
  (* (s1, SVar(s,tau)) => undefined ? -bp *)
  | (Shift (n), Dot (ft, s)) -> comp (Shift (n-1)) s
  | (Shift (n), Shift (m))   -> Shift (n+m)
  | (Dot (ft, s), s')        -> Dot (frontSub ft s', comp s s')
  (* comp(s[tau], Shift(k)) = s[tau]
     where s :: Psi[Phi]  and |Psi| = k 

     comp(s[tau], Shift(k)) = Dot(Id(1), ... Dot(Id(k0), s[tau]))
     where s :: Psi[Phi]  and |Psi| = k'
     k = k' + k0  
  *)



(* bvarSub n s = Ft'
     
   Invariant: 

     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n + k)    if  s = Ft1 .. Ftm ^k   and m < n
       and G |- Ft' : V [s]
*)
and bvarSub n s = match (n, s) with
  | (1, Dot (ft, s)) -> ft
  | (n, Dot (ft, s)) -> bvarSub (n-1) s
  | (n, Shift k)     -> Head (BVar (n+k))



(* frontSub Ft s = Ft'

   Invariant:

     If   G |- s : G'     G' |- Ft : V
     then Ft' = Ft [s]
     and  G |- Ft' : V [s]
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

     If   G |- s : G'
     then s' = 1. (s o ^)
     and  for all V s.t.  G' |- V : L
       G, V[s] |- s' : G', V 

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

     If   cD ; cPsi  |- s     <= cPsi'    cD ; cPsi' |- tA <= type
     then cD ; cPsi  |- tA[s] <= type
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
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
*)
let invDot1 s = comp (comp shift s) invShift



(***************************)
(* Inverting Substitutions *)
(***************************)

(* invert s = s'

   Invariant:

     If   cD ; cPsi  |- s  <= cPsi'    (and s patsub)
     then cD ; cPsi' |- s' <= cPsi
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

     If   cD ; cPsi'' |- t : cPsi  (* and t is a pattern sub *)
     then cD ; cPsi'  |- t : cPsi  and cPsi' subcontext of cPsi
*)
let rec strengthen s cPsi = match (s, cPsi) with
  | (Shift n (* = 0 *), Null) -> Null

  | (Dot (Head (BVar k) (* k = 1 *), t), DDec (cPsi, decl)) ->
      let t' = comp t invShift in
        (* cPsi  |- decl dec     *)
        (* cPsi' |- t' : cPsi    *)
        (* cPsi' |- decl[t'] dec *)
        DDec (strengthen t' cPsi, decSub decl t')

  | (Dot (Undef, t), DDec (cPsi, _)) ->
      strengthen t cPsi

  | (Shift n, cPsi) ->
      strengthen (Dot (Head(BVar (n + 1)), Shift (n + 1))) cPsi



(* isId s = B
     
   Invariant:

     If   cPsi |- s: cPsi', s weakensub
     then B holds 
       iff s = id, cPsi' = cPsi
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

     If cPsi |- tM <= tA
        cPsi |- w  <= cPsi'  w pattern subst
        tM[w^-1] defined (without pruning or constraints)

     then cPsi' |- tM[w^-1] : tA[w^-1]

   Effects: None
*)
let cloInv (tM, w) = Clo (tM, invert w)



(* compInv s w = t

   Invariant:

     If  cD ; cPsi |- s <= cPsi1 
         cD ; cPsi |- w <= cPsi'
     then  t = s o (w^-1)
     and   cD ; cPsi' |- t <= cPsi1
*)
let compInv s w = comp s (invert w)



(* isPatSub s = B

   Invariant:

     If    cPsi |- s : cPsi' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
             and  ni <= k or ni = _ for all 1 <= i <= m
*)
let rec isPatSub s = match s with
  | Shift k               -> true
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
