(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF

exception Error of string

(* More appropriate: Psi into psihat  Sat Oct  4 11:44:55 2008 -bp *)
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


let rec sigmaShift typrec k = match typrec with
  | SigmaLast tA          -> SigmaLast (TClo (tA, Shift  (NoCtxShift, k)))
  | SigmaElem(x, tA, typrec) -> SigmaElem(x, TClo (tA, Shift (NoCtxShift, k)), sigmaShift typrec (k + 1))


let rec ctxShift cPsi k = match cPsi with
  | Null
    -> Null

  | CtxVar psi
    -> CtxVar psi

  | DDec (cPsi, TypDecl(x, tA))
    -> DDec (ctxShift cPsi k, TypDecl (x, TClo (tA, Shift (NoCtxShift, k))))

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
      -> TypDecl (x, TClo (tA', Shift (NoCtxShift, k)))

    | (DDec     (cPsi' , TypDecl   (_x, _tA'  )), k' )
      -> ctxDec' (cPsi', k' - 1)

    | (SigmaDec (cPsi', SigmaDecl  (_x, _tArec)), k')
      -> ctxDec' (cPsi', k' - 1)
    | (Null, _ ) -> raise (Error "Looked-up index bigger than length of context\n")
    | (CtxVar _ , _ ) -> raise (Error "Looked-up index bigger than length of context\n")
    (* ctxDec' (Null    , k') should not occur by invariant *)
    (* ctxDec' (CtxVar _, k') should not occur by invariant *)
  in
   try 
    ctxDec' (cPsi, k)
   with Error s -> (Printf.printf "\n Looking up index %s in context %s \n  \n" 
                      (string_of_int k) 
                      (Pretty.Int.DefaultPrinter.dctxToString cPsi)
                   ;
                    raise (Error s))
       
      

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
      -> SigmaDecl (x, sigmaShift tArec  k) (* ? -bp *)
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




(* append cD1 cD2 = (cD1, cD2) *)
let rec append cD1 cD2 = match cD2 with 
  | Empty -> cD1
  | Dec (cD2', dec) -> 
      let cD1' = append cD1 cD2' in 
        Dec (cD1', dec)


let rec length cD = match cD with
  | Empty -> 0
  | Dec(cD', _ ) -> 1 + length cD'
