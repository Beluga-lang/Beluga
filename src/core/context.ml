(** Contexts

    @author Brigitte Pientka
*)

open Support
open Syntax.Int.LF
open Syntax.Int

exception NoTypAvailable

let addToHat (ctxvarOpt, length) =
  (ctxvarOpt, length + 1)

(* More appropriate: Psi into psihat  Oct  4 2008 -bp *)
let rec dctxToHat = function
  | Null            -> (None, 0)
  | CtxVar (CInst ((_, {contents = Some (ICtx cPsi)}, _cD, _G, _, _), _ ))   ->
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
  | SigmaLast(n, tA) ->
      SigmaLast (n, TClo (tA, s))

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
        TypDecl (x, TClo (tA', Shift k))

    | (DDec (cPsi', TypDecl (_x, _tA')), k') ->
        ctxDec' (cPsi', k' - 1)

    | (DDec (cPsi', TypDeclOpt _ ), 1) ->
        raise NoTypAvailable

    | (DDec (cPsi', _), k') ->
        ctxDec' (cPsi', k'-1)

    | (CtxVar (CInst ((_psiname, {contents = Some (ICtx cPsi)}, _, _, _, _), _ )), k) ->
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
        TypDecl (x, Sigma (sigmaShift tArec  (Shift k)))

    | (DDec (cPsi', TypDecl (_x, Sigma _)), k') ->
        ctxDec' (cPsi', k' - 1)

    | (DDec (cPsi', TypDecl (_x, _tA')), k') ->
        ctxDec' (cPsi', k' - 1)
    | (CtxVar (CInst ((_n, {contents = Some (ICtx cPhi) }, _schema, _octx, _, _), _mctx)) , k) ->
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

let hasCtxVar cPsi = Maybe.is_some (ctxVar cPsi)

(* append cD1 cD2 = (cD1, cD2) *)
let rec append cD1 cD2 = match cD2 with
  | Empty ->
      cD1

  | Dec (cD2', dec) ->
      let cD1' = append cD1 cD2' in
        Dec (cD1', dec)

(** Transforms a context into a list by applying the given function.
    The list order will be the reverse of the context,
    i.e. the rightmost entry of the context (which is the first entry)
    will be the rightmost entry of the lsit (which is the last entry).
 *)
let rec to_list_map_rev (ctx : 'a LF.ctx) (f : 'a LF.ctx -> 'a -> 'b) : 'b list =
  match ctx with
  | Empty -> []
  | Dec (ctx', x) -> f ctx' x :: to_list_map_rev ctx' f

(** Converts the context to a list by applying a given function.
    The list order will be the same as the context,
    i.e. the rightmost entry of the context (the first entry)
    will be the _leftmost_ entry of the list (the first entry).
 *)
let to_list_map (ctx : 'a LF.ctx) (f : 'a LF.ctx -> 'a -> 'b) : 'b list =
  let rec go (ctx : 'a LF.ctx) (acc : 'b list) : 'b list =
    match ctx with
    | Empty -> acc
    | Dec (ctx', x) -> go ctx' (f ctx' x :: acc)
  in
  go ctx []

(** Convert the context to a list.
    See `to_list_map_rev` for a remark about the "reverse" nature of this.
 *)
let to_list_rev (ctx : 'a LF.ctx) : 'a list =
  to_list_map_rev ctx (Misc.const Misc.id)

(** Convert the context to a list, with subcontexts.
    See `to_list_map_rev` for a remark about the "reverse" nature of this.
 *)
let to_sublist_rev (ctx : 'a LF.ctx) : ('a LF.ctx * 'a) list =
  to_list_map_rev ctx Misc.tuple

(** Convert the context to a list.
 *)
let to_list (ctx : 'a LF.ctx) : 'a list =
  to_list_map ctx (Misc.const Misc.id)

let to_sublist (ctx : 'a LF.ctx) : ('a LF.ctx * 'a) list =
  to_list_map ctx Misc.tuple

(** Iterate over a context from left to right (oldest variable first).
    The callback `f` gets both the subcontext of the variable _and_ the variable as input.
    Not tail-recursive, since contexts are snoc-lists.
 *)
let rec iter (ctx : 'a LF.ctx) (f : 'a LF.ctx -> 'a -> unit) : unit =
  match ctx with
  | Empty -> ()
  | Dec (ctx', x) -> iter ctx' f; f ctx' x

let iter' (ctx : 'a LF.ctx) (f : 'a -> unit) : unit =
  iter ctx (fun _ -> f)

(** Iterate over a context from right to left (most recent variable first)
    Tail recursive.
 *)
let rec iter_rev (ctx : 'a LF.ctx) (f : 'a LF.ctx -> 'a -> unit) : unit =
  match ctx with
  | Empty -> ()
  | Dec (ctx', x) -> f ctx' x; iter_rev ctx' f

let iter_rev' (ctx : 'a LF.ctx) (f : 'a -> unit) : unit =
  iter_rev ctx (fun _ -> f)

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
  | (Dec (_cD, Decl(u, _ ,_ )), 1) -> u
  | (Dec (_cD, DeclOpt u), 1) -> u
  | (Dec (cD, _ ) , k) ->
      getNameMCtx cD (k-1)

let rec getNameCtx cG k = match (cG, k) with
  | (Dec(_cG, Comp.CTypDecl (x, _ , _ )), 1 ) -> x
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

let rec lookup' ctx k = match ctx, k with
  | Dec (_, x), 1 -> Some x
  | Dec (ctx', _), k -> lookup' ctx' (k - 1)
  | _ -> None

let lookup_dep (cD : LF.mctx) k =
  let open Maybe in
  lookup' cD k
  $ function
    | LF.Decl (_, tau, dep) -> Some (tau, dep)
    | _ -> None

let lookup cG k =
  let open Maybe in
  lookup' cG k
  $ function
    | Comp.CTypDecl (_, tau, _) -> Some tau
    | _ -> None

let rec lookupSchema cD psi_offset = match (cD, psi_offset) with
  | (Dec (_cD, Decl (_, CTyp (Some cid_schema), _)), 1) -> cid_schema
  | (Dec (cD, _) , i) ->
      lookupSchema cD (i-1)

and lookupCtxVar cD cvar =
  let rec lookup cD offset = match cD with
      | Empty -> raise (Error.Violation "Context variable not found")
      | Dec (cD, Decl (psi, CTyp (Some schemaName), _)) ->
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
