(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF
open Syntax.Int


exception NoTypAvailable

let addToHat (ctxvarOpt, length) =
  (ctxvarOpt, length + 1)

(* More appropriate: Psi into psihat  Oct  4 2008 -bp *)
let rec dctxToHat = function
  | Null            -> (None, 0)
  | CtxVar (CInst (_, {contents = Some cPsi}, _G, _cD, _ ))   ->
      dctxToHat cPsi
  | CtxVar psi      -> (Some psi, 0)
  | DDec (cPsi', _) -> addToHat (dctxToHat cPsi')

let rec hatToDCtx phat = match phat with
  | (None,      0) -> LF.Null
  | (Some psi , 0) -> LF.CtxVar psi
  | (ctx_v    , k) ->
      LF.DDec (hatToDCtx (ctx_v, k-1), LF.TypDeclOpt (Id.mk_name Id.NoName))


(* Declaration Contexts *)
(*
let rec sigmaShift typrec k = match typrec with
  | SigmaLast tA ->
      SigmaLast (TClo (tA, Shift  (NoCtxShift, k)))

  | SigmaElem (x, tA, typrec) ->
      SigmaElem (x, TClo (tA, Shift (NoCtxShift, k)), sigmaShift typrec (k (*+ 1*) ))
*)
let rec sigmaShift typrec s = match typrec with
  | SigmaLast tA ->
      SigmaLast (TClo (tA, s))

  | SigmaElem (x, tA, typrec) ->
      SigmaElem (x, TClo (tA, s), sigmaShift typrec (Substitution.LF.dot1 s))

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

    | (DDec (cPsi', TypDeclOpt _ ), 1) ->
        raise NoTypAvailable

    | (DDec (cPsi', _), k') ->
        ctxDec' (cPsi', k'-1)

    | (CtxVar (CInst (_psiname, {contents = Some (cPsi)}, _, _, _ )), k) ->
        ctxDec' (cPsi, k)
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
    | (DDec (_cPsi', TypDecl (x, Sigma tArec)), 1) ->
        TypDecl (x, Sigma (sigmaShift tArec  (Shift (NoCtxShift, k))))

    | (DDec (cPsi', TypDecl (_x, Sigma _)), k') ->
        ctxDec' (cPsi', k' - 1)

    | (DDec (cPsi', TypDecl (_x, _tA')), k') ->
        ctxDec' (cPsi', k' - 1)
    | (CtxVar (CInst (_n, {contents = Some cPhi }, _schema, _octx, _mctx)) , k) ->
        ctxDec' (cPhi, k)
    (* (Null, k') and (CtxVar _, k') should not occur by invariant *)
  in
    ctxDec' (cPsi, k)


(* ctxVar(Psi) = psi opt
 *
 * Invariant:
 *
 *   Given a data-level context Psi,
 *    returns Some psi if Psi has the form  psi, ...
 *    otherwise returns None
 *)
let rec ctxVar = function
  | Null              -> None
  | CtxVar psi        -> Some psi
  | DDec   (cPsi, _x) -> ctxVar cPsi

let hasCtxVar cPsi = match ctxVar cPsi with
  | Some _ -> true
  | None -> false

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


let rec dctxLength = function
  | Null           -> 0
  | CtxVar _       -> 0
  | DDec (cPsi, _) -> 1 + dctxLength cPsi


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
  | (DDec (cPsi, _ ) , k) -> getNameDCtx cPsi (k-1)

let rec getNameMCtx cD k = match (cD, k) with
  | (Dec (_cD, Decl(u, _ )), 1) -> u
  | (Dec (_cD, MDeclOpt u), 1) -> u
  | (Dec (_cD, PDeclOpt u), 1) -> u
  | (Dec (_cD, CDeclOpt u), 1) -> u
  | (Dec (cD, _ ) , k) ->
      getNameMCtx cD (k-1)

let rec getNameCtx cG k = match (cG, k) with
  | (Dec(_cG, Comp.CTypDecl (x, _ )), 1 ) -> x
  | (Dec(_cG, Comp.CTypDeclOpt x), 1) -> x
  | (Dec(cG, _ ) , k) -> getNameCtx cG (k-1)



let rec projectCtxIntoDctx = function
  | Empty            -> Null
  | Dec (rest, last) -> DDec (projectCtxIntoDctx rest, last)

(*
let typdeclToCtypdecl cPsi = function
  | TypDecl (name, typ) -> MDecl(name, typ, cPsi)
  | TypDeclOpt name -> MDeclOpt name

let rec typdeclCtxToMctx cPsi = function
  | Empty            -> Empty
  | Dec (rest, last) -> Dec (typdeclCtxToMctx (DDec(cPsi, rest))
                                              typdeclToCtypdecl cPsi last)
      *)

(* Given cPsi = g, ...,
   return cPsi = g, x:A, ... *)
let splitContextVariable cPsi new_typ_decl =
  let rec inner = function
    | CtxVar ctx_var -> DDec(CtxVar ctx_var, new_typ_decl)
    | DDec (cPsi, concrete) -> DDec(inner cPsi, concrete)
  in
    inner cPsi

let emptyContextVariable cPsi = (* wrong *)
  let rec inner = function
    | CtxVar ctx_var -> Null
    | DDec (cPsi, concrete) -> DDec(inner cPsi, concrete)
  in
    inner cPsi

let rec lookup cG k = match (cG, k) with
  | (Dec (_cG', Comp.CTypDecl (_,  tau)), 1) ->  Some tau
  | (Dec (_cG', _ ), 1) ->  None
  | (Dec ( cG', _ ), k) ->
      lookup cG' (k - 1)

let rec lookupSchema cD psi_offset = match (cD, psi_offset) with
  | (Dec (_cD, Decl (_, CTyp (cid_schema, _))), 1) -> cid_schema
  | (Dec (cD, _) , i) ->
      lookupSchema cD (i-1)

and lookupCtxVar cD cvar =
  let rec lookup cD offset = match cD with
      | Empty -> raise (Error.Violation "Context variable not found")
      | Dec (cD, Decl (psi, CTyp (schemaName, _))) ->
          begin match cvar with
            | CtxName phi when psi = phi ->  (psi, schemaName)
            | (CtxName _phi)             -> lookup cD (offset+1)
            | CtxOffset n                ->
                if (n - offset) = 1 then
                  (psi, schemaName)
                else
                  lookup cD (offset+1)
          end
      | Dec (cD, _ ) -> lookup cD (offset+1)
  in
    lookup cD 0

and lookupCtxVarSchema cO phi = snd (lookupCtxVar cO phi)
