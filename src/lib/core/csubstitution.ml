(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contextual Substitutions (as explicit substitutions)

    @author Brigitte Pientka
*)

open Syntax.Int.LF


(*************************************)
(* Contextual Explicit Substitutions *)
(*************************************)


(* m_id = ^0 
     
   Invariant:

     cD |- m_id : cD      

   Note: we do not take into account weakening here. 
*)
let m_id = MShift 0



(* m_shift = ^1
  
   Invariant:

     cD, u:tA[cPsi] |- ^ : cD     
*)
let m_shift = MShift 1


(* m_comp (t1, t2) = t'

   Invariant:

   If   D'  |- t1 : D 
   and  D'' |- t2 : D'
   then s'  =  t1 o t2
   and  D'' |- t1 o t2 : D

*)
let rec m_comp t1 t2 = match (t1, t2) with
  | (MShift 0, t)             -> t
  | (t, MShift 0)             -> t
  | (MShift n, MDot (_ft, t))  -> m_comp (MShift (n - 1)) t
  | (MShift n, MShift m)       -> MShift (n + m)
  | (MDot (mft, t), t')        -> MDot (mfrontMSub mft t', m_comp t t')

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


(* m_dot1 (t) = t'

   Invariant:

     If   D |- t : D'
     then t' = 1. (t o ^)
     and  for all A s.t.  D' ; Psi |- A : type
       D, u::[|t|](A[Psi] |- t' : D', A[Psi]
*)
and m_dot1 t = match t with
  | MShift 0 -> t
  | t        -> MDot (Id 1, m_comp t m_shift)


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



