(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contexts

    @author Renaud Germain
    @author Darin Morrison
    @author Brigitte Pientka
*)

open Syntax.Int



(* More approriate: Psi into psihat  Sat Oct  4 11:44:55 2008 -bp *)
let dctxToHat cPsi =
  let rec length = function
    | Null               -> (None    , 0)

    | CtxVar psi         -> (Some psi, 0)

    | DDec (cPsi', _)     ->
        let (cVopt, i) = length cPsi' in
          (cVopt, i + 1)

    | SigmaDec (cPsi', _) ->
        let (cVopt, i) = length cPsi' in
          (cVopt, i + 1)

  in
    length cPsi



(************************)
(* Declaration Contexts *)
(************************)

let rec sigmaShift tArec k = match tArec with
  | []          -> []
  | tA :: tArec -> TClo (tA, Shift k) :: sigmaShift tArec (k + 1)



let rec ctxShift cPsi k = match cPsi with
  | Null
    -> Null

  | CtxVar psi
    -> CtxVar psi

  | DDec (cPsi, TypDecl(x, tA))
    -> DDec (ctxShift cPsi k, TypDecl (x, TClo (tA, Shift k)))

  | SigmaDec (cPsi, SigmaDecl (x, tArec))
    -> SigmaDec (ctxShift cPsi k, SigmaDecl (x, sigmaShift tArec k))



(* ctxDec Psi k = x:A

   Invariant: 

     If      |Psi| >= k, where |Psi| is size of Psi,
     then    D ; Psi |- k => A  and  x:A in Psi at position k,
             D ; Psi |- A <= type
*)
let ctxDec cPsi k =
  (* ctxDec' (Psi'', k') = x:V
     where Psi |- ^(k-k') : Psi'', 1 <= k' <= k
  *)
  let rec ctxDec' = function
    | (DDec     (_cPsi', TypDecl   (x, tA'    )), 1 )
      -> TypDecl (x, TClo (tA', Shift k))

    | (DDec     (cPsi' , TypDecl   (_x, _tA'  )), k' )
      -> ctxDec' (cPsi', k' - 1)

    | (SigmaDec (cPsi', SigmaDecl  (_x, _tArec)), k')
      -> ctxDec' (cPsi', k' - 1)
    (* ctxDec' (Null    , k') should not occur by invariant *)
    (* ctxDec' (CtxVar _, k') should not occur by invariant *)
  in
    ctxDec' (cPsi, k)



(* ctxSigmaDec (Psi, k,i) = x:A

   Invariant: 

     If      |Psi| >= k, where |Psi| is size of Psi,
     then    D ; Psi |- k => Sigma x1:A1, ... xn:An  
             A = Sigma x1:A1, ... xn:An, and x:A is in Psi
        and  D ; Psi |- Sigma x1:A1, ... xn:An  <= type
*)
let ctxSigmaDec cPsi k =
  (* ctxDec' (Psi'', k') = x:V
     where Psi |- ^(k-k') : Psi'', 1 <= k' <= k
  *)
  let rec ctxDec' = function
    | (DDec (cPsi', TypDecl (_x, _tA')), k')
      -> ctxDec' (cPsi', k' - 1)

    | (SigmaDec (_cPsi', SigmaDecl (x, tArec)), 1)
      -> SigmaDecl (x, sigmaShift tArec k) (* ? -bp *)
         (* ctxDec' (Null    , k') should not occur by invariant *)
         (* ctxDec' (CtxVar _, k') should not occur by invariant *)
  in
    ctxDec' (cPsi, k)



(* ctxVar(Psi) = psi opt

   Invariant: 

     If Psi is a data-level context then 
     return Some psi if context variable exists
     otherwise None
*)
let rec ctxVar = function
  | Null                -> None
  | CtxVar   psi        -> Some psi
  | DDec     (cPsi, _x) -> ctxVar cPsi
  | SigmaDec (cPsi, _x) -> ctxVar cPsi



(*
*)
let rec mctxMDec cD k' = match (cD, k') with
  | (Dec (_cD, MDecl(_u, tA, cPsi)), 1)
    -> (TClo (tA, Shift k'), ctxShift cPsi k')

  | (Dec (cD, _), k)
    -> mctxMDec cD (k - 1)



(*
*)
let rec mctxPDec cD k' = match (cD, k') with
  | (Dec (_cD, PDecl (_u, tA, cPsi)), 1)
    -> (TClo (tA, Shift k'), ctxShift cPsi k')

  | (Dec (cD, _), k)
    -> mctxPDec cD (k - 1)



(*************************************)
(* Creating new contextual variables *)
(*************************************)

(* newMVar (cPsi, tA) = newMVarCnstr (cPsi, tA, [])

   Invariant:

         tA =   Atom (a, S)
     or  tA =   Pi (x:tB, tB')
     but tA =/= TClo (_, _)
*)
let newMVar (cPsi, tA) = Inst (ref None, cPsi, tA, ref [])



(* newPVar (cPsi, tA) = p

   Invariant:

         tA =   Atom (a, S)
     or  tA =   Pi (x:tB, tB')
     but tA =/= TClo (_, _)
*)
let newPVar (cPsi, tA) = PInst (ref None, cPsi, tA, ref [])
