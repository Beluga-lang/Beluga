(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF
open Syntax.Int
open Error 

exception Error of error

(* More appropriate: Psi into psihat  Sat Oct  4 11:44:55 2008 -bp *)
let dctxToHat cPsi =
  let rec length = function
    | Null ->
        (None, 0)

    | CtxVar psi ->
        (Some psi, 0)

    | DDec (cPsi', _) ->
        let (cVopt, i) = length cPsi' in
          (cVopt, i + 1)

    | SigmaDec (cPsi', _) ->
        let (cVopt, i) = length cPsi' in
          (cVopt, i + 1)
  in
    length cPsi


let rec hatToDCtx phat = match phat with 
  | (None,      0) -> LF.Null
  | (Some psi , 0) -> LF.CtxVar psi
  | (ctx_v    , k) -> 
      LF.DDec (hatToDCtx (ctx_v, k-1), LF.TypDeclOpt (Id.mk_name Id.NoName)) 
        

(* Declaration Contexts *)

let rec sigmaShift typrec k = match typrec with
  | SigmaLast tA -> 
      SigmaLast (TClo (tA, Shift  (NoCtxShift, k)))

  | SigmaElem (x, tA, typrec) -> 
      SigmaElem (x, TClo (tA, Shift (NoCtxShift, k)), sigmaShift typrec (k (*+ 1*) ))


let rec ctxShift cPsi k = match cPsi with
  | Null ->
      Null

  | CtxVar psi ->
      CtxVar psi

  | DDec (cPsi, TypDecl (x, tA)) ->
      DDec (ctxShift cPsi k, TypDecl (x, TClo (tA, Shift (NoCtxShift, k))))

  | SigmaDec (cPsi, SigmaDecl (x, tArec)) ->
      SigmaDec (ctxShift cPsi k, SigmaDecl (x, sigmaShift tArec k))


(* ctxDec Psi k = x:A
 *
 * Invariant:
 *
 *   If      |Psi| >= k, where |Psi| is size of Psi,
 *   then    D ; Psi |- k => A  and  x:A in Psi at position k,
 *           D ; Psi |- A <= type
 *)
let ctxDec cPsi k =
  (* ctxDec' (Psi'', k') = x:V
   * where Psi |- ^(k-k') : Psi'', 1 <= k' <= k
   *)
  let rec ctxDec' = function
    | (DDec (_cPsi', TypDecl (x, tA')), 1) ->
        TypDecl (x, TClo (tA', Shift (NoCtxShift, k)))

    | (DDec (cPsi', TypDecl (_x, _tA')), k') ->
        ctxDec' (cPsi', k' - 1)

    | (SigmaDec (cPsi', SigmaDecl (_x, _tArec)), k') ->
        ctxDec' (cPsi', k' - 1)
    (* (Null, _) and (CtxVar _, _) should not occur by invariant *)
  in
    ctxDec' (cPsi, k)

(* ctxSigmaDec (Psi, k,i) = x:A
 *
 * Invariant:
 *
 *   If      |Psi| >= k, where |Psi| is size of Psi,
 *   then    D ; Psi |- k => Sigma x1:A1, ... xn:An
 *           A = Sigma x1:A1, ... xn:An, and x:A is in Psi
 *      and  D ; Psi |- Sigma x1:A1, ... xn:An  <= type
 *)
let ctxSigmaDec cPsi k =
  (* ctxDec' (Psi'', k') = x:V
   * where Psi |- ^(k-k') : Psi'', 1 <= k' <= k
   *)
  let rec ctxDec' = function
    | (SigmaDec (_cPsi', SigmaDecl (x, tArec)), 1) ->
        SigmaDecl (x, sigmaShift tArec  k) (* ? -bp *)

    | (SigmaDec (cPsi', _), k') ->
        ctxDec' (cPsi', k' - 1)

    | (DDec (cPsi', TypDecl (_x, _tA')), k') ->
        ctxDec' (cPsi', k' - 1)

    (* (Null, k') and (CtxVar _, k') should not occur by invariant *)
  in
    ctxDec' (cPsi, k)


(* ctxVar(Psi) = psi opt
 *
 * Invariant:
 *
 *   If Psi is a data-level context then
 *   return Some psi if context variable exists
 *   otherwise None
 *)
let rec ctxVar = function
  | Null                -> None
  | CtxVar   psi        -> Some psi
  | DDec     (cPsi, _x) -> ctxVar cPsi
  | SigmaDec (cPsi, _x) -> ctxVar cPsi


(* append cD1 cD2 = (cD1, cD2) *)
let rec append cD1 cD2 = match cD2 with
  | Empty -> 
      cD1

  | Dec (cD2', dec) ->
      let cD1' = append cD1 cD2' in
        Dec (cD1', dec)


let rec length cD = match cD with
  | Empty        -> 0
  | Dec (cD', _) -> 1 + length cD'



(* Lookup name in context
 * 
 * getNameDCtx cPsi k = x 
 *  
 * If |cPsi| <= k then x is the name of the k-th declaration in cPsi
 *
 * Invariants for lookup in cD and cG similar.
 *)

let rec getNameDCtx cPsi k = match (cPsi, k) with
  | (DDec (_cPsi, TypDecl (x, _ )), 1) -> x
  | (DDec (_cPsi, TypDeclOpt x) , 1)   -> x
  | (SigmaDec (_cPsi, SigmaDecl (x, _ )), 1 ) -> x
  | (DDec (cPsi, _ ) , k) -> getNameDCtx cPsi (k-1)
  | (SigmaDec (cPsi, _ ) , k) -> getNameDCtx cPsi (k-1)

let rec getNameMCtx cD k = match (cD, k) with 
  | (Dec (_cD, MDecl(u, _, _ )), 1) -> u 
  | (Dec (_cD, PDecl(u, _, _ )), 1) -> u 
  | (Dec (_cD, CDecl(u, _)), 1) -> u 
  | (Dec (_cD, MDeclOpt u), 1) -> u 
  | (Dec (_cD, PDeclOpt u), 1) -> u 
  | (Dec (_cD, CDeclOpt u), 1) -> u 
  | (Dec (cD, _ ) , k) -> 
      getNameMCtx cD (k-1)

let rec getNameCtx cG k = match (cG, k) with 
  | (Dec(_cG, Comp.CTypDecl (x, _ )), 1 ) -> x 
  | (Dec(_cG, Comp.CTypDeclOpt x), 1) -> x
  | (Dec(cG, _ ) , k) -> getNameCtx cG (k-1)


