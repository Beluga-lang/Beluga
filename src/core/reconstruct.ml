(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**

   @author Brigitte Pientka
*)


open Store
open Store.Cid
open Syntax
open Substitution
open Error
open Id
open ConvSigma

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail 
module C     = Whnf

module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer
module RR = Pretty.Int.NamedRenderer


let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

exception NotImplemented
(* exception Error of Syntax.Loc.t option * error
exception Violation of string *)
exception SpineMismatch
exception NotPatSpine

let rec conv_listToString clist = match clist with 
  | [] -> " "
  | x::xs -> string_of_int x ^ ", " ^ conv_listToString xs

let rec what_head = function
  | Apx.LF.BVar _ -> "BVar"
  | Apx.LF.Const _ -> "Const"
  | Apx.LF.MVar _ -> "MVar"
  | Apx.LF.PVar (Apx.LF.Offset _ , _ ) -> "PVar Offset "
  | Apx.LF.PVar (Apx.LF.PInst _ , _ ) -> "PVar PInst "
  | Apx.LF.Proj (head, k) -> "Proj " ^ what_head head ^ "." ^ string_of_int k
  | Apx.LF.FVar _ -> "FVar"
  | Apx.LF.FMVar _ -> "FMVar"
  | Apx.LF.FPVar _ -> "FPVar"



exception Violation of string

type reconType = PiboxRecon | PiRecon

type caseType  = IndexObj of Int.LF.psi_hat * Int.LF.normal | DataObj

type typAnn    = FullTyp of Apx.LF.typ | PartialTyp of cid_typ

type free_cvars = 
    FMV of Id.name | FPV of Id.name | FSV of Id.name

let rec pruningTyp locOpt cD cPsi phat sA (ms, ss)  = 
  if Substitution.LF.isId ss then 
    Whnf.normTyp sA 
  else 
    begin try
      Unify.pruneTyp cD cPsi phat sA (ms, ss) (Unify.MVarRef (ref None))
    with _ -> raise (Error (locOpt, PruningFailed) )
    end 


let rec unify_phat psihat ctx_var = 
  match ctx_var with
    | (Some (Int.LF.CInst ({contents = None} as cref, _, _, _ )), d) -> 
        begin match psihat with 
          | ((Some (c_var)) , d') -> 
              if d = d' then
                (cref := Some (Int.LF.CtxVar (c_var))  ; true)
              else                 
                (dprint (fun () -> "[unify_phat - 1] unify ctx_var with a full context");
                 raise NotImplemented)
          | (None , d') -> 
              if d = d' then 
                (cref := Some (Int.LF.Null) ; true)
              else 
                (dprint (fun () -> "[unify_phat - 2] unify ctx_var with a full context");
                 raise NotImplemented)
        end 

    | _ ->  (psihat = ctx_var)


let rec unifyDCtx cPsi1 cPsi2 (cs, cO) = match (cPsi1 , cPsi2) with 
      | (Int.LF.Null , Int.LF.Null) -> (cO, cs)

      | (cPsi1 , Int.LF.CtxVar (Int.LF.CtxOffset psi2_var)) -> 
        let _ = dprint (fun () -> "[unifyDCtx' - 1] instantiate " ^ P.dctxToString cO Int.LF.Empty cPsi1 
                          ^ " with " ^ P.dctxToString cO Int.LF.Empty cPsi2 ^ "\n") in 
          Ctxsub.inst_csub cPsi1 psi2_var cs cO

      | (Int.LF.CtxVar (Int.LF.CtxOffset psi1_var), cPsi2) -> 
        let _ = dprint (fun () -> "cO = " ^ P.octxToString cO ) in
        let _ = dprint (fun () -> "[unifyDCtx' - 2] instantiate " ^ P.dctxToString cO Int.LF.Empty cPsi1 ^ 
                          " with " ^ P.dctxToString cO Int.LF.Empty cPsi2 ^ "\n") in
          Ctxsub.inst_csub cPsi2 psi1_var cs cO

      | (Int.LF.DDec (cPsi1, Int.LF.TypDecl(_ , _tA1)) , Int.LF.DDec (cPsi2, Int.LF.TypDecl(_ , _tA2))) ->  
          unifyDCtx cPsi1 cPsi2  (cs, cO) 
      | _ -> raise (Violation "Context clash")


(* let rec remove_name n n_list - match n_list with 
  | [ ] -> [ ] 
  | n'::n_list' -> if n = n' then n_list else n'::(remove_name n n_list')
*)

let rec lookup_fv fvars m = begin  match (fvars, m) with 
     ([], _ ) -> false
  | (FMV n :: fvars' , FMV m) -> 
      if n = m then true
      else lookup_fv fvars' (FMV m) 

  | (FPV p :: fvars' , FPV q) -> 
      if p = q then true
      else lookup_fv fvars' m 
  | (FPV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m

end

let rec projectCtxIntoDctx = function
  | Int.LF.Empty            -> Int.LF.Null
  | Int.LF.Dec (rest, last) -> Int.LF.DDec (projectCtxIntoDctx rest, last)


let ctxShift = Ctxsub.ctxShift

let ctxToSub' = Ctxsub.ctxToSub'



let rec raiseType cPsi tA = match cPsi with
  | Int.LF.Null -> tA
  | Int.LF.DDec (cPsi', decl) ->
      raiseType cPsi' (Int.LF.PiTyp ((decl, Int.LF.Maybe), tA))

(* patSpine s = true iff
 *
 *     cPsi |- s : A <- P  and
 *     s is a pattern spine (simple approximate),
 *     i.e. it consists of distinct bound variables
 *)
let rec patSpine spine =
  let _ = dprint (fun () -> "[reconstruct.ml] check pat spine") in
  let rec etaUnroll k m= begin match m with
    | Apx.LF.Lam (_ , _, n) ->  etaUnroll (k+1) n
    |  _ ->  (k, m) 
  end in
         
  let rec patSpine' seen_vars spine = match spine with
    | Apx.LF.Nil ->
        (0, spine)

    | Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), spine) ->
        if not (List.mem x seen_vars) then
          let (k, p_spine) = patSpine' (x :: seen_vars) spine in
            (k+1, Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), p_spine))
        else
           raise NotPatSpine

    | Apx.LF.App (Apx.LF.Lam _ as m, spine) -> 
        begin match etaUnroll 0 m with 
          | (k, Apx.LF.Root( loc , Apx.LF.BVar x, spine')) -> 
              (let (l', _p_spine') = patSpine spine' in  
                 if l' = k && x > k then 
                    let (l, p_spine) = patSpine'  ((x-k)::seen_vars) spine in 
                      (l+1, Apx.LF.App(Apx.LF.Root(loc, Apx.LF.BVar (x-k), Apx.LF.Nil), p_spine))
                  else 
                    raise NotPatSpine
              )
          | (k, Apx.LF.Root( loc , Apx.LF.FVar x, spine')) -> 
              let (l', _p_spine') = patSpine spine' in  
                (if l' = k  then 
                   let (l, p_spine) = patSpine' seen_vars spine in 
                     (l+1, Apx.LF.App(Apx.LF.Root(loc, Apx.LF.FVar x, Apx.LF.Nil), p_spine))
                 else 
                   raise NotPatSpine)                  
          | _ ->  raise NotPatSpine
        end 
    | _ ->  raise NotPatSpine 

  in
  let s = patSpine' [] spine in 
    (dprint (fun () -> "[check pat spine] done" ) ; s)

let rec mkShift recT cPsi = match recT with
  | PiboxRecon -> 
      Int.LF.Shift (Int.LF.NoCtxShift, 0)

  | PiRecon ->
      let (None, d) = Context.dctxToHat cPsi in
        Int.LF.Shift (Int.LF.NoCtxShift, d) 



(* isPatSub s = bool *)
let rec isPatSub s = match s with
  | Apx.LF.Id ->
      true

  | Apx.LF.EmptySub ->
      true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar _k), s) ->
      isPatSub s

  | Apx.LF.Dot (Apx.LF.Head _, _s) -> false

  | Apx.LF.Dot (Apx.LF.Obj  _, _s) -> false




(* -------------------------------------------------------------*)
(* isProjPatSub s = true *)
let rec isProjPatSub s = match s with
  | Apx.LF.Id -> true

  | Apx.LF.EmptySub -> true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      isProjPatSub s

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar _k,_j)), s) ->
     isProjPatSub s

  | Apx.LF.Dot (Apx.LF.Head _, _s) -> false

  | Apx.LF.Dot (Apx.LF.Obj  _, _s) -> false




let rec flattenProjPat s conv_list = match s with
  | Apx.LF.Id -> Apx.LF.Id
  | Apx.LF.EmptySub -> Apx.LF.EmptySub
  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) -> 
      let s' = flattenProjPat s conv_list in 
        Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar (new_index k conv_list )), s')

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar k, j)), s) ->
      let s' = flattenProjPat s conv_list in 
      let _ = dprint (fun () -> "flattenProjPat Proj Case: k = " ^ string_of_int k ^ "    j = "  ^ string_of_int j ^ "\n") in 
      let k' = (new_index k conv_list) - j + 1  in
        Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k'), s')

 (* these are the only cases which can happen *)



(* -------------------------------------------------------------*)

let rec lengthApxMCtx cD = match cD with
  | Apx.LF.Empty -> 0
  | Apx.LF.Dec (cD, _) -> 1 + lengthApxMCtx cD


let rec lookupFun cG f = match cG with
  | Int.LF.Dec (cG', Int.Comp.CTypDecl (f',  tau)) ->  
      if f = f' then tau else         
      lookupFun cG' f

let mctxToMSub = Ctxsub.mctxToMSub

(* -------------------------------------------------------------*)
(* EtaExpansion of approximate terms *)
let rec shiftApxTerm k m = begin match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam(loc, x, shiftApxTerm (k+1) m')
  | Apx.LF.Root (loc, h , spine) -> 
      let h' = shiftApxHead k h in 
      let spine' = shiftApxSpine k spine in 
        Apx.LF.Root(loc, h', spine')
end

and shiftApxHead k h = begin match h with
  | Apx.LF.BVar x -> Apx.LF.BVar (x+k)
  | Apx.LF.FMVar (u, s) -> Apx.LF.FMVar (u, shiftApxSub k s)
  | Apx.LF.FPVar (p, s) -> Apx.LF.FMVar (p, shiftApxSub k s)
  | Apx.LF.MVar (u, s) -> Apx.LF.MVar (u, shiftApxSub k s)
  | _ -> h
end

and shiftApxSpine k spine = begin match spine with
  | Apx.LF.Nil -> spine
  | Apx.LF.App (m, spine') -> 
      let spine'' = shiftApxSpine k spine' in 
        Apx.LF.App (shiftApxTerm k m, spine'') 
end 
  
and shiftApxSub k s = begin match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id -> s
  | Apx.LF.Dot(Apx.LF.Head h, s) -> 
      let h' = shiftApxHead k h in 
      let s' = shiftApxSub k s in
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot(Apx.LF.Obj m, s) -> 
      let m' = shiftApxTerm k m in 
      let s' = shiftApxSub k s in
        Apx.LF.Dot (Apx.LF.Obj m', s')
end


(* Eta-expansion of bound variables which have function type *)
let rec etaExpandHead loc h tA = 
  let rec etaExpSpine k tS tA = begin match  tA with
    | Int.LF.Atom _  -> (k, tS)
        
    | Int.LF.PiTyp (_ , tA') -> 
        let tN = Int.LF.Root(Some loc, Int.LF.BVar k, Int.LF.Nil) in                   
          etaExpSpine (k+1)  (Int.LF.App(tN, tS)) tA'
  end in 
    
  let rec etaExpPrefix loc (tM, tA) = begin match tA with
    | Int.LF.Atom _ -> tM
    | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ), _ ) , tA') -> 
        Int.LF.Lam (loc, x, etaExpPrefix loc (tM, tA')) 
  end in
    
  let (k, tS') = etaExpSpine 1 (Int.LF.Nil) tA in 
  let h'       =  begin match h with 
                    | Int.LF.BVar x -> Int.LF.BVar (x+k-1)
                    | Int.LF.FVar _ -> h 
                  end  in
    etaExpPrefix (Some loc) (Int.LF.Root(Some loc, h' , tS'), tA)   



let rec etaExpandApxHead loc h tA = 
  let rec etaExpApxSpine k tS tA = begin match  tA with
    | Int.LF.Atom _  -> (k, tS)
        
    | Int.LF.PiTyp (_ , tA') -> 
        let tN = Apx.LF.Root(loc, Apx.LF.BVar k, Apx.LF.Nil) in                   
          etaExpApxSpine (k+1)  (Apx.LF.App(tN, tS)) tA'
  end in 
    
  let rec etaExpApxPrefix loc (tM, tA) = begin match tA with
    | Int.LF.Atom _ -> tM
    | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ), _ ) , tA') -> 
        Apx.LF.Lam (loc, x, etaExpApxPrefix loc (tM, tA')) 
  end in
    
  let (k, tS') = etaExpApxSpine 1 (Apx.LF.Nil) tA in 
  let h'       =  begin match h with 
                    | Apx.LF.BVar x -> Apx.LF.BVar (x+k-1)
                    | Apx.LF.FVar _ -> h 
                  end  in
    etaExpApxPrefix loc (Apx.LF.Root(loc, h' , tS'), tA)   


let rec etaExpandApxTerm  loc h tS tA = 
  let rec etaExpApxSpine k tS tA = begin match  tA with
    | Int.LF.Atom _  -> (k, tS)
        
    | Int.LF.PiTyp (_ , tA') -> 
        let tN = Apx.LF.Root(loc, Apx.LF.BVar k, Apx.LF.Nil) in                   
          etaExpApxSpine (k+1)  (Apx.LF.App(tN, tS)) tA'
  end in 
    
  let rec etaExpApxPrefix loc (tM, tA) = begin match tA with
    | Int.LF.Atom _ -> tM
    | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ), _ ) , tA') -> 
        let _ = dprint (fun () -> "eta - add Lam ") in
        Apx.LF.Lam (loc, x, etaExpApxPrefix loc (tM, tA')) 
  end in

  let rec appendSpine tS1 tS2 = begin match tS1 with
    | Apx.LF.Nil -> tS2
    | Apx.LF.App (tM, tS) -> 
        Apx.LF.App (tM, appendSpine tS tS2) 
  end in 

  let (k, tS') = etaExpApxSpine 1 (Apx.LF.Nil) tA in 
  let _ = dprint (fun () -> "etaExpApxSpine k = " ^ string_of_int k )in
  let tS''     = appendSpine (shiftApxSpine (k-1) tS) tS' in 
  (* let tS''     = appendSpine tS tS' in  *)
    
  let h'       =  begin match h with 
                    | Apx.LF.BVar x -> Apx.LF.BVar (x+k-1)
                    |  _ -> h 
                  end  in
    etaExpApxPrefix loc (Apx.LF.Root(loc, h' , tS''), tA)   

(* -------------------------------------------------------------*)
  let rec addPrefix loc m tA = 
    begin match tA with
      | Int.LF.Atom _ -> m
      | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ) , _ ) , tA') -> 
          let _ = dprint (fun () -> "eta FMV - add Lam ") in             
        Apx.LF.Lam (loc, x, addPrefix loc m tA')
    end 
  let rec etaExpSub k s tA = begin match tA with
    | Int.LF.Atom _ -> (k, s)
    | Int.LF.PiTyp (_ , tA') -> 
        let (k',s') = etaExpSub (k+1) s tA' in 
       (k'-1, Apx.LF.Dot(Apx.LF.Head(Apx.LF.BVar(k')),s'))
  end 

  let rec etaExpandFMV  loc (Apx.LF.FMVar (x, s)) tA = 
    let ( _ , s') = etaExpSub 0 s tA  in 
      addPrefix loc (Apx.LF.Root(loc, Apx.LF.FMVar(x, s'), Apx.LF.Nil)) tA

  let rec etaExpandMV loc (Apx.LF.MVar (x,s)) tA = 
    let ( _ , s') = etaExpSub 0 s tA  in 
      addPrefix loc (Apx.LF.Root(loc, Apx.LF.MVar(x, s'), Apx.LF.Nil)) tA



(* -------------------------------------------------------------*)
let rec lookup cG k = match (cG, k) with
  | (Int.LF.Dec(_cG', Int.Comp.CTypDecl (_, tau)), 1) ->   tau
  | (Int.LF.Dec( cG', Int.Comp.CTypDecl (_, _tau)), k) ->
      lookup cG' (k-1)

let rec get_ctxvar psi = match psi with
  | Ext.LF.Null -> None
  | Ext.LF.CtxVar (_loc, psi_name) -> Some psi_name
  | Ext.LF.DDec (psi, _ ) -> get_ctxvar psi


let rec apxget_ctxvar psi  = match psi with
  | Apx.LF.Null -> None
  | Apx.LF.CtxVar (psi_name) -> Some psi_name
  | Apx.LF.DDec (psi, _ ) -> apxget_ctxvar psi


(* index_of cQ n = i
   where cQ = cQ1, Y, cQ2 s.t. n = Y and length cQ2 = i
*)

let rec index_of cQ n = match cQ with
  | [] -> 
      raise (Violation "index_of for a free variable does not exist -- should be impossible")
        (* impossible due to invariant on collect *)
  | (x, _ )::cQ' -> if x = n then 1 else (index_of cQ' n) + 1



let rec index_kind cvars bvars fvars = function
  | Ext.LF.Typ _ ->
      (Apx.LF.Typ, fvars)

  | Ext.LF.ArrKind (_, a, k) ->
      let x            = Id.mk_name Id.NoName
      and (a', fvars1) = index_typ cvars bvars fvars a in
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (k', fvars2) = index_kind cvars bvars' fvars1 k in
        (Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.No), k') , fvars2)

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let (a', fvars1) = index_typ cvars bvars fvars a
      and bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (k', fvars2) = index_kind cvars bvars' fvars1 k in
        (Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), k') , fvars2)

and index_typ cvars bvars fvars = function
  | Ext.LF.Atom (loc, a, s) ->
      begin try 
        let _        = dprint (fun () -> "Indexing type constant " ^ a.string_of_name) in 
        let a' = Typ.index_of_name a
        and (s', fvars') = index_spine cvars bvars fvars s in
          (Apx.LF.Atom (loc, a', s') , fvars')
      with Not_found ->
       raise (Error (Some loc, UnboundName a))
      end
    

  | Ext.LF.ArrTyp (_loc, a, b) ->
      let x            = Id.mk_name Id.NoName
      and (a', fvars1) = index_typ cvars bvars fvars a in
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (b', fvars2) = index_typ cvars bvars' fvars1 b in
        (Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.No), b') , fvars2)

  | Ext.LF.PiTyp (_loc, Ext.LF.TypDecl (x, a), b) ->
      let (a', fvars1)  = index_typ cvars bvars  fvars a
      and bvars'        = BVar.extend bvars (BVar.mk_entry x) in
      let (b', fvars2)  = index_typ cvars bvars' fvars1 b in
        (Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), b') , fvars2)
  
  | Ext.LF.Sigma (_, typRec) ->
      let (typRec', fvars') = index_typ_rec cvars bvars fvars typRec in
      (Apx.LF.Sigma typRec' , fvars')

and index_typ_rec cvars bvars fvars = function
  | Ext.LF.SigmaLast a -> 
      let (last, fvars') = index_typ cvars bvars fvars a in 
        (Apx.LF.SigmaLast last , fvars')
  | Ext.LF.SigmaElem (x, a, rest) ->
      let (a', fvars1)    = index_typ cvars bvars fvars a
      and bvars'          = BVar.extend bvars (BVar.mk_entry x) in
      let (rest', fvars2) = index_typ_rec cvars bvars' fvars1 rest in
        (Apx.LF.SigmaElem (x, a', rest') , fvars2)

and index_tuple cvars bvars fvars = function
  | Ext.LF.Last m -> 
      let (m', fvars') = index_term cvars bvars fvars m in 
        (Apx.LF.Last m', fvars')
  | Ext.LF.Cons (m, rest) ->
      let (m', fvars1) = index_term cvars bvars fvars m in
      let (rest', fvars2) = index_tuple cvars bvars fvars1 rest in
        (Apx.LF.Cons (m', rest') , fvars2)

and index_term cvars bvars fvars = function
  | Ext.LF.Lam (loc, x, m) ->
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let (m', fvars')     = index_term cvars bvars' fvars m in
        (Apx.LF.Lam (loc, x, m') , fvars')

  | Ext.LF.Tuple (loc, tuple) ->
      let (tuple', fvars') = index_tuple cvars bvars fvars tuple in
        (Apx.LF.Tuple (loc, tuple') , fvars')

  | Ext.LF.Root (loc, h, s) ->
      let (h', fvars1) = index_head  cvars bvars fvars h in
      let (s', fvars2) = index_spine cvars bvars fvars1 s in
        (Apx.LF.Root (loc, h', s') , fvars2)

and index_head cvars bvars fvars = function
  | Ext.LF.Name (_, n) ->
      let _        = dprint (fun () -> "Indexing name " ^ n.string_of_name) in 
      begin try
        (Apx.LF.BVar (BVar.index_of_name bvars n) , fvars)
      with Not_found -> try
        (Apx.LF.Const (Term.index_of_name n) , fvars)
      with Not_found -> 
        (dprint (fun () -> "FVar " ^ n.string_of_name );
        (Apx.LF.FVar n , fvars))
          
      end

  | Ext.LF.ProjName (loc, k, n) ->
      let (bvar, fvars') = index_head cvars bvars fvars (Ext.LF.Name (loc, n)) in
        (Apx.LF.Proj(bvar, k), fvars')

  | Ext.LF.PVar (_, p, s) ->
      begin try
        let offset = CVar.index_of_name cvars p in
        let (s' , fvars') = index_sub cvars bvars fvars s in
          (Apx.LF.PVar (Apx.LF.Offset offset, s') , fvars')
      with Not_found ->
        let _ = dprint (fun () -> "PVar Not_found " ^ R.render_name p) in
        let (s', fvars')     = index_sub cvars bvars fvars s in
          (Apx.LF.FPVar (p, s') , FPV p :: fvars' )
      end

  | Ext.LF.ProjPVar (loc, k, (p, s)) ->
      let (pvar, fvars') = index_head cvars bvars fvars (Ext.LF.PVar (loc, p, s)) in
        (Apx.LF.Proj (pvar, k), fvars')

        
  | Ext.LF.Hole _loc -> 
      (Apx.LF.Hole , fvars)

  | Ext.LF.MVar (_, u, s) ->
      if lookup_fv fvars (FMV u) then 
        let (s', fvars')     = index_sub cvars bvars fvars s in
          (Apx.LF.FMVar (u, s') , fvars')
      else 
        begin try
          let offset = CVar.index_of_name cvars u in
          let (s', fvars')     = index_sub cvars bvars fvars s in
            (Apx.LF.MVar (Apx.LF.Offset offset, s') , fvars')
        with Not_found ->
          let (s', fvars')     = index_sub cvars bvars fvars s in
            (Apx.LF.FMVar (u, s') , FMV u :: fvars')
        end

  | Ext.LF.SVar (loc, n, _sigma) -> 
      let _        = dprint (fun () -> "Indexing head : SVar " ^ n.string_of_name) in 
        raise (Error (Some loc, UnboundName n))

and index_spine cvars bvars fvars = function
  | Ext.LF.Nil ->
      (Apx.LF.Nil , fvars)

  | Ext.LF.App (_, m, s) ->
      let (m', fvars')  = index_term  cvars bvars fvars m in
      let (s', fvars'') = index_spine cvars bvars fvars' s in
        (Apx.LF.App (m', s') , fvars'')

and index_sub cvars bvars fvars = function
  | Ext.LF.Id _ -> (Apx.LF.Id , fvars)

  | Ext.LF.Dot (_, s, Ext.LF.Head h) ->
      let (s', fvars')  = index_sub cvars bvars fvars s  in
      let (h', fvars'') = index_head cvars bvars fvars' h in
        (Apx.LF.Dot (Apx.LF.Head h', s') , fvars'')

  | Ext.LF.Dot (_, s, Ext.LF.Normal m) ->
      let (s', fvars')  = index_sub cvars bvars fvars s  in
      let (m', fvars'') = index_term cvars bvars fvars' m in
        (Apx.LF.Dot (Apx.LF.Obj  m', s') , fvars'')

  | Ext.LF.EmptySub _ ->
      (Apx.LF.EmptySub, fvars)

        

let index_decl cvars bvars fvars (Ext.LF.TypDecl(x, a)) =
  let (a', fvars') = index_typ cvars bvars fvars a in
  let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDecl (x,a'), bvars', fvars')

let rec index_dctx ctx_vars cvars bvars fvars = function
  | Ext.LF.Null        -> (Apx.LF.Null , bvars, fvars)

  | Ext.LF.CtxVar (loc, psi_name)  ->
      begin try
        let offset = CVar.index_of_name ctx_vars psi_name in
          (Apx.LF.CtxVar (Apx.LF.CtxOffset offset) , bvars, fvars)
      with Not_found ->
        raise (Error (Some loc, UnboundCtxName psi_name))
        (* (Apx.LF.CtxVar (Apx.LF.CtxName psi_name) , bvars) *)
      end
  | Ext.LF.DDec (psi, decl) ->
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars bvars fvars psi in
      let (decl', bvars'', fvars'')  = index_decl cvars bvars' fvars' decl in
        (Apx.LF.DDec (psi', decl'), bvars'', fvars'')

let index_psihat ctx_vars explicit_psihat =
  let bv = BVar.create () in

  let rec index_hat bvars = function
    | [] -> (0, bvars)
    | x :: psihat ->
        let bvars' = BVar.extend bvars (BVar.mk_entry x) in
        let (l, bvars'') = index_hat bvars' psihat in
          (l + 1, bvars'')

  in
    begin match explicit_psihat with
      | [] -> ((None, 0), bv)
      |  x :: psihat ->
          begin try
            let ctx_var = CVar.index_of_name ctx_vars x in
            let (d, bvars) = index_hat bv psihat in
              ((Some (Int.LF.CtxOffset ctx_var), d) , bvars)
          with Not_found ->
            let (d, bvars ) = index_hat bv explicit_psihat in
              ((None, d) , bvars)
          end
    end


let rec index_ctx cvars bvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty , bvars, fvars)

  | Ext.LF.Dec (psi, dec) ->
      let (psi', bvars', fvars')   = index_ctx  cvars bvars fvars psi in
      let (dec', bvars'', fvars'') = index_decl cvars bvars' fvars' dec in
        (Apx.LF.Dec (psi', dec'), bvars'', fvars'')

let index_cdecl ctx_vars cvars fvars = function
  | Ext.LF.MDecl (_, u, a, psi) ->
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
      let (a', fvars'')          = index_typ  cvars bvars' fvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry u) in
        (Apx.LF.MDecl (u, a', psi'), ctx_vars, cvars', fvars'')

  | Ext.LF.PDecl (_, p, a, psi) ->
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
      let (a', fvars')           = index_typ  cvars bvars' fvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry p) in
        (Apx.LF.PDecl (p, a', psi') , ctx_vars, cvars', fvars')

  | Ext.LF.SDecl (_, s, phi, psi) ->
      let (psi', _bvars', fvars') = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
      let (phi', _bvars', fvars'') = index_dctx ctx_vars cvars (BVar.create ()) fvars' phi in
      let _ = dprint (fun () -> "Extend cvars with " ^ R.render_name s) in 
      let cvars'         = CVar.extend cvars (CVar.mk_entry s) in
        (Apx.LF.SDecl (s, phi', psi') , ctx_vars, cvars', fvars'')

  | Ext.LF.CDecl (loc , ctx_name, schema_name) -> 
    begin try 
      let ctx_vars'        = CVar.extend ctx_vars (CVar.mk_entry ctx_name) in
      let schema_cid       = Schema.index_of_name schema_name in
        (Apx.LF.CDecl (ctx_name, schema_cid), ctx_vars', cvars, fvars)
    with 
        Not_found -> raise (Error (Some loc, UnboundCtxSchemaName schema_name))
    end



let rec index_mctx ctx_vars cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty, Apx.LF.Empty , ctx_vars, cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (omega', delta', ctx_vars', cvars', fvars') = index_mctx ctx_vars cvars fvars delta in
      let (cdec', ctx_vars', cvars'', fvars'') = index_cdecl ctx_vars' cvars' fvars' cdec in
        begin match cdec' with 
          | Apx.LF.CDecl _ -> (Apx.LF.Dec(omega', cdec'), delta', ctx_vars', cvars'', fvars'')
          | _       -> (omega', Apx.LF.Dec (delta', cdec'), ctx_vars', cvars'', fvars'')
        end 



(* Records are not handled in a general manner
 * We need to change the datatype for typ_rec to be typ_decl ctx
 *)
let rec index_typrec cvars bvars fvars = function
  | Ext.LF.SigmaLast last_a ->
      let (last, fvars') = index_typ cvars bvars fvars last_a in 
      (Apx.LF.SigmaLast last, fvars')

  | Ext.LF.SigmaElem (x, a, arec) ->
      let (a', fvars') = index_typ cvars bvars fvars a in
      let  bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let (arec', fvars'') = index_typrec cvars bvars' fvars' arec in 
        (Apx.LF.SigmaElem (x, a', arec'), fvars'')


(* Translation of external schemas into approximate schemas *)
let rec index_elements el_list = List.map index_el el_list

and index_el (Ext.LF.SchElem (_, typ_ctx, typ_rec)) =
  let cvars = (CVar.create ()) in
  let bvars = (BVar.create ()) in
  let fvars = [] in 
  let (typ_ctx', bvars', _ ) = index_ctx cvars bvars fvars typ_ctx in
  let (typ_rec', _ )         = index_typrec cvars bvars' fvars typ_rec in
    Apx.LF.SchElem (typ_ctx', typ_rec')


let index_schema (Ext.LF.Schema el_list) =
  Apx.LF.Schema (index_elements el_list)


(* Translation of external computations into approximate computations *)
let rec index_comptyp ctx_vars cvars  fvars = 
  function
  | Ext.Comp.TypBox (loc, a, psi)    ->
      begin try 
        let Ext.LF.Atom (_ , name, Ext.LF.Nil) = a in 
        let offset = CVar.index_of_name ctx_vars name in           
        let (psi', _ , _ ) = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
        let _ = dprint (fun () -> "Indexing TypSub -- turning TypBox into TypSub") in
          Apx.Comp.TypSub (loc, Apx.LF.CtxVar (Apx.LF.CtxOffset offset), psi')
      with _  -> 
        let (psi', bvars', _ ) = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
        let (a', _ )           = index_typ cvars bvars' fvars a   in
          Apx.Comp.TypBox (loc, a', psi')
      end 

  | Ext.Comp.TypSub (loc, phi, psi)    ->
      let (psi', _ , _ ) = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
      let (phi', _ , _ ) = index_dctx ctx_vars cvars (BVar.create ()) fvars phi in
        Apx.Comp.TypSub (loc, phi', psi')


  | Ext.Comp.TypArr (_loc, tau, tau') ->
      Apx.Comp.TypArr (index_comptyp ctx_vars cvars fvars tau, 
                       index_comptyp ctx_vars cvars fvars tau')

  | Ext.Comp.TypCross (_loc, tau, tau') ->
      Apx.Comp.TypCross (index_comptyp ctx_vars cvars fvars tau, 
                         index_comptyp ctx_vars cvars fvars tau')

  | Ext.Comp.TypPiBox (_loc, cdecl, tau)    ->
      let (cdecl', ctx_vars', cvars', _) = index_cdecl ctx_vars cvars fvars cdecl in
        Apx.Comp.TypPiBox (cdecl', index_comptyp ctx_vars' cvars' fvars tau)

  | Ext.Comp.TypCtxPi (loc, (ctx_name, schema_name, dep), tau)    ->
    begin try 
      let ctx_vars'        = CVar.extend ctx_vars (CVar.mk_entry ctx_name) in
      let schema_cid       = Schema.index_of_name schema_name in
        (* if exception Not_found is raised, it means schema_name does not exist *)
      let apxdep = match dep with Ext.Comp.Explicit -> Apx.Comp.Explicit | Ext.Comp.Implicit -> Apx.Comp.Implicit in 
        Apx.Comp.TypCtxPi ((ctx_name, schema_cid, apxdep), index_comptyp ctx_vars' cvars fvars tau)
    with 
        Not_found -> raise (Error (Some loc, UnboundCtxSchemaName schema_name))
    end

  | Ext.Comp.TypBool -> Apx.Comp.TypBool

let rec index_exp ctx_vars cvars vars fvars = function
  | Ext.Comp.Syn (loc , i)   ->
      Apx.Comp.Syn (loc, index_exp' ctx_vars cvars vars fvars i)

  | Ext.Comp.Fun (loc, x, e) ->
      let vars' = Var.extend vars (Var.mk_entry x) in
        Apx.Comp.Fun (loc, x, index_exp ctx_vars cvars vars' fvars e)

  | Ext.Comp.CtxFun (loc, psi_name, e) ->
      let ctx_vars' = CVar.extend ctx_vars (CVar.mk_entry psi_name) in
        Apx.Comp.CtxFun (loc, psi_name, index_exp ctx_vars' cvars vars fvars e)

  | Ext.Comp.MLam (loc, u, e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry u) in
        Apx.Comp.MLam (loc, u, index_exp ctx_vars cvars' vars fvars e)

  | Ext.Comp.Pair (loc, e1, e2) ->
      let e1 = index_exp ctx_vars cvars vars fvars e1 in
      let e2 = index_exp ctx_vars cvars vars fvars e2 in
        Apx.Comp.Pair (loc, e1, e2)

  | Ext.Comp.LetPair (loc, i, (x, y, e)) ->
      let i' = index_exp' ctx_vars cvars vars fvars i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let vars2 = Var.extend vars1 (Var.mk_entry y) in
      let e' = index_exp ctx_vars cvars vars2 fvars e in
        Apx.Comp.LetPair(loc, i', (x,y,e'))

  (* SVars are parsed as terms but are actually substitutions *)
  | Ext.Comp.Box (loc1, psihat, Ext.LF.Root(loc2, Ext.LF.SVar(loc3,s, sigma), spine)) -> 
      let (psihat' , bvars) = index_psihat ctx_vars psihat in 
      let rec create_sub s spine = match spine with
        | Ext.LF.Nil -> s
        | Ext.LF.App (loc, m', spine') -> 
            let (m', _ ) = index_term cvars bvars [] m' in 
             create_sub (Apx.LF.Dot (Apx.LF.Obj m', s)) spine' 
      in 
      let (sigma', _ ) =  index_sub cvars bvars [] sigma in 
        begin try
          let offset = CVar.index_of_name cvars s in
            Apx.Comp.SBox (loc1, psihat', 
                           create_sub (Apx.LF.SVar (Apx.LF.Offset offset, sigma')) spine )
        with Not_found -> 
          raise (Error (Some loc3, UnboundName s))
        end 


  | Ext.Comp.Box (loc, psihat, m) ->
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let (m', _ ) = index_term cvars bvars [] (* fvars *) m in  
        Apx.Comp.Box (loc, psihat', m')


  | Ext.Comp.SBox (loc, psihat,s) -> 
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let (s', _ ) = index_sub cvars bvars [] s in 
        Apx.Comp.SBox (loc, psihat', s')

  | Ext.Comp.Case (loc, prag, i, branches) ->
      let i' = index_exp' ctx_vars cvars vars fvars i in
      let branches' = List.map (function b -> index_branch ctx_vars cvars vars fvars b) branches in
        Apx.Comp.Case (loc, prag, i', branches')


  | Ext.Comp.If (loc, i, e1, e2) -> 
      let i' = index_exp' ctx_vars cvars vars fvars i in
      let e1' = index_exp ctx_vars cvars vars fvars e1 in
      let e2' = index_exp ctx_vars cvars vars fvars e2 in
        Apx.Comp.If(loc, i', e1', e2')

and index_exp' ctx_vars cvars vars fvars = function
  | Ext.Comp.Var (loc, x) ->
      begin try
        Apx.Comp.Var (Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (Comp.index_of_name x)
      with Not_found ->
        raise (Error (Some loc, UnboundCompName x))
      end

  | Ext.Comp.Apply (loc, i, e) ->
      let i' = index_exp' ctx_vars cvars vars fvars i in
      let e' = index_exp  ctx_vars cvars vars fvars e in
        Apx.Comp.Apply (loc, i', e')

  | Ext.Comp.CtxApp (loc, i, psi) ->
      let i'   = index_exp' ctx_vars cvars vars fvars i in
      let (psi', _ , _ ) = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
        Apx.Comp.CtxApp (loc, i', psi')

  | Ext.Comp.MApp (loc, i, (psihat, m)) ->
      let i'      = index_exp' ctx_vars cvars vars fvars i in
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let (m', _ ) = index_term cvars bvars fvars m in
        Apx.Comp.MApp (loc, i', (psihat', m'))

  | Ext.Comp.MAnnApp (loc, i, (psi, m)) ->
      let i'      = index_exp' ctx_vars cvars vars fvars i in
      let (psi', bvars, _ ) = index_dctx ctx_vars cvars  (BVar.create ()) [] (* fvars *) psi in
      let (m', _ ) = index_term cvars bvars fvars m in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Ext.Comp.BoxVal (loc, psi, m) ->
      let (psi', bvars, _ ) = index_dctx ctx_vars cvars  (BVar.create ()) [] (* fvars *) psi in
      let (m', _ ) = index_term cvars bvars fvars m in 
        Apx.Comp.BoxVal (loc, psi', m') 

  | Ext.Comp.Ann (_loc, e, tau) ->
      Apx.Comp.Ann (index_exp  ctx_vars cvars vars fvars e,
                         index_comptyp ctx_vars cvars fvars tau)

  | Ext.Comp.Equal (loc, i, i') ->
      let i1 = index_exp' ctx_vars cvars vars fvars i in 
      let i2 = index_exp' ctx_vars cvars vars fvars i' in 
        Apx.Comp.Equal (loc, i1, i2)

  | Ext.Comp.Boolean (loc , b) -> Apx.Comp.Boolean (loc, b)


and index_branch ctx_vars cvars vars fvars branch = match branch with
  | Ext.Comp.BranchBox(loc, delta, (psi1, pattern, Some (a, psi))) ->
    let empty_fvars = [] in 
    let _ = dprint (fun () -> "index_branch") in 
    let ctx_vars' = begin match get_ctxvar psi1 with 
                     | None -> CVar.create () 
                     | Some psi_name -> CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) 
                    end in
    
    let (omega, delta', ctx_vars', cvars', fvars1)  = 
      index_mctx ctx_vars' ctx_vars' empty_fvars delta in
    let (psi1', bvars, fvars2)   = index_dctx ctx_vars' cvars' (BVar.create ()) fvars1 psi1 in 
    let (m'opt, fvars3)       = match pattern with
                                     | Ext.Comp.EmptyPattern -> (None, fvars2)
                                     | Ext.Comp.NormalPattern (m, e) ->
                                         let (m', fvars3) = index_term cvars' bvars fvars2 m in
                                           (Some m', fvars3)
    in
    let (psi', _bvars, fvars4)   = index_dctx ctx_vars' cvars' (BVar.create ()) fvars3 psi in
    (* _bvars = bvars *)
    let (a', fvars5)             = index_typ cvars' bvars fvars4 a in

    let cvars_all        = CVar.append cvars' cvars in
    let ctxvars_all      = CVar.append ctx_vars' ctx_vars in

    let fvars6 = List.append fvars5 fvars in

    let pattern' =
      match (pattern, m'opt) with
        | (Ext.Comp.EmptyPattern, None) -> Apx.Comp.EmptyPattern
        | (Ext.Comp.NormalPattern (_, e), Some m') -> Apx.Comp.NormalPattern (m', index_exp ctxvars_all cvars_all vars fvars6 e)
    in
      Apx.Comp.BranchBox (loc, omega, delta', (psi1', pattern', Some (a', psi')))

  | Ext.Comp.BranchBox (loc, delta, (psi, pattern, None)) ->
    let empty_fvars = [] in 
    let ctx_vars' = begin match get_ctxvar psi with 
                     | None -> CVar.create () 
                     | Some psi_name -> CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) 
                    end in

    let (omega, delta', ctx_vars', cvars', fvars1)  = 
      index_mctx ctx_vars' (CVar.create()) empty_fvars delta in
    let (psi1', bvars, fvars2)    = index_dctx ctx_vars' cvars' (BVar.create ()) fvars1 psi in

      begin match pattern with 
        | Ext.Comp.EmptyPattern ->
            Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.EmptyPattern, None))
            
        | Ext.Comp.NormalPattern (Ext.LF.Root(_, Ext.LF.SVar (loc, s, sigma), Ext.LF.Nil),  e) -> 
            let (s_var, fvars3) = begin try
                          let offset = CVar.index_of_name cvars' s in
                          let (sigma' , fvars') = index_sub cvars' bvars fvars2 sigma in
                            (Apx.LF.SVar (Apx.LF.Offset offset, sigma') , fvars')
                        with Not_found ->
                          let _ = dprint (fun () -> "SVar Not_found " ^ R.render_name s) in
                          let (sigma', fvars')     = index_sub cvars bvars fvars sigma in
                          let _ = dprint (fun () -> "Created FSVar " ^ R.render_name s) in
                            (Apx.LF.FSVar (s, sigma') , FSV s :: fvars' )
                        end in 

            let cvars_all        = CVar.append cvars' cvars in
            let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
            let e'               = index_exp ctxvars_all cvars_all vars fvars3 e in
              Apx.Comp.BranchSBox (loc, omega, delta', (psi1', s_var, None), e')



        | Ext.Comp.NormalPattern (m, e)  -> 
            let (m', fvars3)     = index_term cvars' bvars fvars2 m in
            let cvars_all        = CVar.append cvars' cvars in
            let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
            let fvars4 = List.append fvars3 fvars in 
            let e'               = index_exp ctxvars_all cvars_all vars fvars4 e in
              Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.NormalPattern (m', e'), None))
                
      end

(* Constraints for free bound variables *)
let fvar_cnstr : ((Int.LF.typ_free_var * Apx.LF.normal * Int.LF.cvar)  list) ref = ref [] 

let add_fvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fvarCnstr () = (fvar_cnstr := [])

(* Constraints for free metavariables and parameter variables  *)
let fcvar_cnstr : ((Apx.LF.normal * Int.LF.cvar)  list) ref = ref []

let add_fcvarCnstr  c = fcvar_cnstr := c :: !fcvar_cnstr
let reset_fcvarCnstr () = (fcvar_cnstr := [])

let rec synDom cD loc cPsi s = begin match s with
  | Apx.LF.Id ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            (Int.LF.CtxVar psi, Int.LF.Shift (Int.LF.NoCtxShift, d))

        | (None, _d) ->
            raise (Error (Some loc, UnboundIdSub))
      end

  | Apx.LF.EmptySub ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            (Int.LF.Null, Int.LF.Shift (Int.LF.CtxShift psi, d))

        | (None, d) ->
            (Int.LF.Null, Int.LF.Shift (Int.LF.NoCtxShift, d))
      end

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      begin match Context.ctxDec cPsi k with
        | Int.LF.TypDecl (x, tA) ->
            let (cPhi, s') = synDom cD loc cPsi s in
              (*  cPsi |- s <= cPhi
               *  cPsi |- tA <= type
               *  tA' = [s]^-1(tA)
               *
               * Note: We may need to check that [s]^-1(tA) actually exists.
               *
               *  Wed Jan 14 13:51:11 2009 -bp
               *)
            let ss = Substitution.LF.invert s' in 
            let tA' = pruningTyp (Some loc) cD cPsi (*?*) (Context.dctxToHat cPsi) (tA, LF.id)  (Int.LF.MShift 0, ss)  in
              (Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, tA')),
               Int.LF.Dot (Int.LF.Head(Int.LF.BVar k), s'))
(*       | _ -> raise (Violation "Undefined bound variable") *)
      end

   | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar k,j)), s) ->
      begin match Context.ctxDec cPsi k with
        | Int.LF.TypDecl (x, tB) -> (* tB = block x1:A1. ... xn:An *)
           let (cPhi, s') = synDom cD loc cPsi s in 

            let ss = Substitution.LF.invert s' in 

            let Int.LF.Sigma typRec = 
              pruningTyp (Some loc) cD cPsi (*?*) (Context.dctxToHat cPsi) (tB, LF.id) (Int.LF.MShift 0, ss)  in

            let sQ = Int.LF.getType  (Int.LF.BVar k) (typRec, LF.id) k 1 in 

              (Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, Int.LF.TClo sQ)),
               Int.LF.Dot (Int.LF.Head(Int.LF.Proj(Int.LF.BVar k, j)), s'))
         | _ -> raise (Violation "Undefined bound variable") 
      end


  | _ -> raise (Violation "Encountered non-pattern substitution")

end

(* ******************************************************************* *)
(* ELABORATION OF KINDS                                                *)
(* ******************************************************************* *)
(* elKind  cPsi k = K *)
let rec elKind  cPsi k = match k with
  | Apx.LF.Typ ->
      Int.LF.Typ

  | Apx.LF.PiKind ((Apx.LF.TypDecl (x, a),dep), k) ->
      let dep'  = match dep with Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
      let tA    = elTyp
                    PiRecon
                    
                    (*cO=*)Int.LF.Empty
                    (*cD=*)Int.LF.Empty
                    cPsi
                    a
      in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elKind  cPsi' k in
        Int.LF.PiKind ((Int.LF.TypDecl (x, tA), dep'), tK)

(* ******************************************************************* *)
(* ELABORATION OF KINDS                                                *)
(* ******************************************************************* *)
(* elTyp recT  cD cPsi a = A*)
and elTyp recT  cO cD cPsi a = match a with
  | Apx.LF.Atom (loc, a, s) ->
      begin try
        let tK = (Typ.get a).Typ.kind in
        let i  = (Typ.get a).Typ.implicit_arguments in
        let s'  = mkShift recT cPsi in 
          (* let s' = LF.id in *)
        let tS = elKSpineI recT  cO cD cPsi s i (tK, s') in
          Int.LF.Atom (Some loc, a, tS)            
      with  _ -> raise (Error (Some loc, SpineIllTyped ))
      end

  | Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a), dep), b) ->
      let dep'  = match dep with Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
      let tA    = elTyp recT  cO cD cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp recT  cO cD cPsi' b in
        Int.LF.PiTyp ((Int.LF.TypDecl (x, tA),dep'), tB)

  | Apx.LF.Sigma typRec ->
      let typRec' = elTypRec recT  cO cD cPsi typRec in
        Int.LF.Sigma typRec' 
   
       
and elTypRec recT  cO cD cPsi =
(*  let el_typ ctx = elTyp recT  cD (projectCtxIntoDctx ctx) in *)
    function
      | Apx.LF.SigmaLast a ->
          Int.LF.SigmaLast (elTyp recT  cO cD cPsi a)

      | Apx.LF.SigmaElem (name, a, typRec) ->
          let tA = elTyp recT  cO cD cPsi a in
          let cPsi' = Int.LF.DDec (cPsi, Int.LF.TypDecl (name, tA)) in
          let typRec' = elTypRec recT  cO cD cPsi' typRec in
            Int.LF.SigmaElem (name, tA, typRec')

and elTerm recT  cO cD cPsi m sA = elTermW recT  cO cD cPsi m (Whnf.whnfTyp sA)

and elTermW recT  cO cD cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (loc, x, m),  (Int.LF.PiTyp ((Int.LF.TypDecl (_x, _tA) as decl, _ ), tB), s)) ->
       (* cPsi' = cPsi, x:tA *)
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm recT  cO cD cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam (Some loc, x, tM)
  
  | (Apx.LF.Root (_loc, _h, _spine),  (Int.LF.Atom _, _s)) ->
      elTerm' recT  cO cD cPsi m  sA  
  
  | (Apx.LF.Tuple (loc, tuple),  (Int.LF.Sigma typRec, s)) -> 
      let tuple' = elTuple recT  cO cD cPsi tuple (typRec, s) in
        Int.LF.Tuple (Some loc, tuple')

  | (Apx.LF.Root (loc, Apx.LF.FMVar (x, s),  _spine),  (Int.LF.PiTyp _ as tA, _s)) ->
      let n = etaExpandFMV loc (Apx.LF.FMVar (x,s)) tA in 
        elTerm recT cO cD cPsi n sA
(*      raise (Error (Some loc, EtaExpandFMV (x, cO, cD, cPsi, sA))) *)

  | (Apx.LF.Root (loc, Apx.LF.MVar (x, s),  _spine),  (Int.LF.PiTyp _ as tA, _s)) ->
      let n = etaExpandMV loc (Apx.LF.MVar (x,s)) tA in 
        elTerm recT cO cD cPsi n sA

  | (Apx.LF.Root (loc, h, spine ), (Int.LF.PiTyp _ as tA, _s)) -> 
      let n = etaExpandApxTerm loc h spine tA in 
        elTerm recT  cO cD cPsi n sA
  
  | (Apx.LF.Lam (loc, _, _ ), _ ) ->  
      raise (Error (Some loc, IllTypedElab (cO, cD, cPsi, sA))) 

  | (Apx.LF.Tuple (loc, _ ),  _) ->
      raise (Error (Some loc, IllTypedElab (cO, cD, cPsi, sA))) 

and elTuple recT  cO cD cPsi tuple (typRec, s) =
  match (tuple, typRec) with
  | (Apx.LF.Last m,
     Int.LF.SigmaLast tA) 
    ->
      Int.LF.Last (elTerm' recT  cO cD cPsi m (tA, s))

  | (Apx.LF.Cons(m, restOfTuple),
     Int.LF.SigmaElem(_x, tA, restOfTypRec))
    ->
      let tM = elTerm recT  cO cD cPsi m (tA, s) in
      let extended_s = Int.LF.Dot (Int.LF.Obj tM, s) in
      let tuple' = elTuple recT  cO cD cPsi restOfTuple (restOfTypRec, extended_s) in
        Int.LF.Cons (tM, tuple')

  | (_, _) -> raise (Violation ("elTuple arity mismatch"))


  and instanceOfSchElem loc cO cD cPsi (tA, s) (some_part, sB) = 
    let _ = dprint (fun () -> "[instanceOfSchElem] Begin \n") in 
   (* let sArec = match Whnf.whnfTyp (tA, s) with
      | (Int.LF.Sigma tArec,s') ->  (tArec, s') 
      | (nonsigma, s')          ->  (Int.LF.SigmaLast nonsigma, s') in *)
    let _ = dprint (fun () -> ("tA =" ^ P.typToString cO cD cPsi (tA, s) ^ " \n")) in 
    let dctx        = projectCtxIntoDctx some_part in  
    let dctxSub     = ctxToSub' cD cPsi dctx in

    (* let phat        = dctxToHat cPsi in *)

    let _ =  dprint (fun () -> "***Unify.unifyTyp (" 
                        ^ "\n   cPsi = " ^ P.dctxToString cO cD cPsi
                        ^ "\n   dctx = " ^ P.dctxToString cO cD dctx  
                        ^ "\n   " ^  P.typToString cO cD cPsi (tA, s) ) in
    let _ = dprint (fun () -> "dctxSub = " ^ P.subToString cO cD cPsi dctxSub ^ "\n") in

    let _ = dprint (fun () ->  P.typToString cO cD cPsi (tA,s)) in  
    let _ = dprint (fun () ->  "== " ) in 
    let _ = dprint (fun () -> P.typToString cO cD cPsi (Int.LF.TClo sB, dctxSub) ^ "\n" )  in
    let nB  = Whnf.normTyp (Int.LF.TClo sB, dctxSub) in 
    let nA  = Whnf.normTyp (tA,s) in 
      begin
        try
          Unify.unifyTyp cD cPsi (nA, LF.id) (nB, LF.id) 
        ; dprint (fun () -> "instanceOfSchElem\n"
                            ^ "  block_part = " ^ P.typToString cO cD cPsi (Int.LF.TClo sB, dctxSub) ^ "\n"
                            ^ "  succeeded.")
        ; (Int.LF.TClo sB, dctxSub)
        with (Unify.Unify _)  ->
          (dprint (fun () -> "Type " ^ P.typToString cO cD cPsi (tA,s) ^ " doesn't unify with schema element\n");
(*          dprint (fun () ->  P.typRecToString cO cD cPsi (block_part, dctxSub)) *)
           
             raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, (nA, LF.id), (nB, LF.id)))))
          | exn -> 
              (dprint (fun () -> "[instanceOfSchElem] Non-Unify ERROR -2- "); raise exn)
      end
  
  and instanceOfSchElemProj loc cO cD cPsi (tA, s) (var, k) (Int.LF.SchElem (cPhi, trec)) = 
    let _ = dprint (fun () -> "[instanceOfSchElemProj] getType of " ^ string_of_int k ^ ". argument\n") in 
    let cPhi'  = projectCtxIntoDctx cPhi in  
    let _ = dprint (fun () -> " of " ^ P.typRecToString cO cD cPhi' (trec, LF.id)) in
    let _ = dprint (fun () -> " var = " ^ P.headToString cO cD cPsi var) in
    let sA_k (* : tclo *) = Int.LF.getType var (trec, LF.id) k 1 in  (* bp - generates  general type with some-part still intact; this tA_k is supposed to be the type of #p.1 s - hence,eventually it the some part needs to be restricted appropriately. Tue May 25 10:13:07 2010 -bp *)
    let _ = dprint (fun () -> "[instanceOfSchElemProj] retrieved the type  " ^ P.typToString cO cD cPhi' sA_k) in
    let (_tA'_k, subst) =
      instanceOfSchElem loc cO cD cPsi (tA, s) (cPhi, sA_k)
      (* tA'_k = [subst] (sA_k) = [s]tA *)
    in
      (trec, subst) 



(* Synthesize the type for a free parameter variable *)
and synSchemaElem loc recT  cO cD cPsi ((_, s) as sP) (head, k) ((Int.LF.Schema elements) as schema) =
  let self = synSchemaElem loc recT  cO cD cPsi sP (head, k) in 
  let _ = dprint (fun () -> "synSchemaElem ... head = " ^ P.headToString cO cD cPsi head ^ " Projection " ^ string_of_int k ^ "\n") in
  let _ = dprint (fun () -> "[synSchemaElem]  " ^ P.typToString cO cD cPsi sP
                    ^ "  schema= " ^ P.schemaToString schema) in
    match elements with
      | [] -> None
      | (Int.LF.SchElem (_some_part, block_part)) as elem  ::  rest  ->
          try
            let _ = dprint (fun () -> "[instanceOfSchElemProj ] ... ") in
            let (typRec, subst) = instanceOfSchElemProj loc cO cD cPsi sP (head, k) elem in 
              (* Check.LF.instanceOfSchElemProj loc cO cD cPsi sP (head, k) elem in *)
            dprint (fun () -> "synSchemaElem RESULT = "
                            ^ P.typRecToString cO cD cPsi (typRec, subst))
          ; Some (typRec, subst) (* sP *)
          with Unify.Unify _  -> self (Int.LF.Schema rest)
            | Not_found -> self (Int.LF.Schema rest) 


and elTerm' recT  cO cD cPsi r sP = match r with

  | Apx.LF.Root (loc, Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      (* let s  = mkShift recT cPsi in *)
      let s = LF.id in 
      let (tS, sQ) = elSpineI loc recT  cO cD cPsi spine i (tA, s) in
      let tR = Int.LF.Root (Some loc, Int.LF.Const c, tS)  in 
        begin try
          (Unify.unifyTyp cD cPsi sQ sP ;
           tR)
        with 
         | Unify.Unify msg ->
             ((* Printf.printf "\nUnification Error: %s\n\n" msg; *)
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
         | Unify.Error msg -> 
             (Printf.printf "\nHidden %s\n  This may indicate the following problem:\n  a contextual variable was inferred with the most general type,\n  but subsequently it must have a more restrictive type,\n  i.e., where certain bound variable dependencies cannot occur.\n\n" msg;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
         | Unify.NotInvertible -> 
            ((* Printf.printf "\nUnification Error: NotInvertible\n\n"; *)
             raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
(*         | _ ->
            (Printf.printf "Non-Unification Error (1)\n" ;
             raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
*)
        end

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      begin try 
        let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        let (tS, sQ) = elSpine loc recT  cO cD cPsi spine (tA, LF.id) in
          begin try
            (Unify.unifyTyp cD  cPsi sQ sP ;
             Int.LF.Root (Some loc, Int.LF.BVar x, tS)) 
          with Unify.Unify msg ->
            (Printf.printf "%s\n" msg;
             raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
             | _ -> (Printf.printf "Non-Unification Error (2)\n" ;
                    raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ)))) 
          end
      with _ -> raise (Error (Some loc, CompTypAnn))
        (* (Printf.printf "BVar lookup error \n" ; raise (Violation "Not Found")) *)

      end

  | Apx.LF.Root (loc, Apx.LF.FVar x, spine) as m ->
   (* This case can only happen durin PiRecon *) 
      begin match recT with 
        | PiRecon -> 
            begin try
              let Int.LF.Type tA = FVar.get x in
                (* For type reconstruction to succeed, we must have
                 *
                 *  . |- tA <= type
                 *  This will be enforced during abstraction
                 *)
              let s = mkShift recT cPsi in
              let (tS, sQ) = elSpine loc recT cO cD cPsi spine (tA, s) in
                begin try
                  (Unify.unifyTyp cD cPsi sQ sP ;
                   Int.LF.Root (Some loc, Int.LF.FVar x, tS)) 
                with Unify.Unify msg ->
                       (Printf.printf "%s\n" msg;
                        raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
                   | _ ->
                       (Printf.printf "Non-Unification Error (3)\n" ;
                        raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
                end


            with Not_found ->
              begin try
                let (_l, p_spine) = patSpine spine in
                let s = mkShift recT cPsi in              
                let (tS, tA) =  elSpineSynth recT  cD cPsi p_spine s sP in 
                  (* For type reconstruction to succeed, we must have
                   *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
                   *  This will be enforced during abstraction.
                   *)
                  FVar.add x (Int.LF.Type tA);
                  Int.LF.Root (Some loc, Int.LF.FVar x, tS)
              with NotPatSpine -> 
                (let _ = dprint (fun () -> "[elTerm'] FVar case -- Not a pattern spine...") in  
                  let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
                 let tAvar = Int.LF.TypVar (Int.LF.TInst (ref None, cPsi, Int.LF.Typ, ref [])) in  
                    add_fvarCnstr (tAvar, m, v);
                   Int.LF.Root (Some loc, Int.LF.MVar (v, LF.id), Int.LF.Nil))
                | _  ->                 
                raise (Error (Some loc, IllTypedElab (cO, cD, cPsi, sP)))
              end
            end
        | PiboxRecon -> raise (Error (Some loc, UnboundName x))
      end 
              

  | Apx.LF.Root (loc, Apx.LF.Hole, spine) ->
      begin try 
     (let (_l, pat_spine) = patSpine spine in
      let sshift = mkShift recT cPsi in
      let (tS, tA) = elSpineSynth recT  cD cPsi pat_spine sshift sP in

        begin match recT with
          | PiRecon -> 
              (* let u =  Whnf.newMVar (cPsi, tA) in 
                Int.LF.Root (Some loc, Int.LF.MVar(u, LF.id), tS) *)
              let u =  Whnf.newMVar (Int.LF.Null, tA) in 
                Int.LF.Root (Some loc, Int.LF.MVar(u, sshift), tS)
          | PiboxRecon -> 
              let u =  Whnf.newMMVar (cD, cPsi, tA) in
                Int.LF.Root (Some loc, Int.LF.MMVar(u, (Whnf.m_id, LF.id)), tS)
        end)
      with NotPatSpine ->          
           raise (Error (Some loc, NotPatternSpine))
      end
  (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) as m ->
      begin try
        let (tQ, cPhi) = FMVar.get u in
        let s'' = elSub loc recT  cO cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' --
           * this check is delayed to reconstruction *)
        let tR = Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil) in 
          begin try
            Unify.unifyTyp cD  cPsi (tQ, s'') sP ; 
            tR
          with Unify.Unify msg -> 
            (Printf.printf "%s\n" msg;
             raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), (tQ, s''), sP))))
            |_ -> (Printf.printf "Unification Error (4)\n";
             raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), (tQ, s''), sP))))

          end
      with 
        | Not_found ->
          if isPatSub s then
          (* 1) given cPsi and s synthesize the domain cPhi
           * 2) [s]^-1 ([s']tP) is the type of u
           *)
          let _ = dprint (fun () -> "Synthesize domain for meta-variable " ^ u.string_of_name ) in
          let (cPhi, s'') = synDom cD loc cPsi s in
          let ss =  Substitution.LF.invert s'' in 
          let _ = dprint (fun () -> "[synDom] Prune type " ^ P.typToString Int.LF.Empty cD cPsi sP ) in 
          let _ = dprint (fun () -> "         with respect to ss = " ^ P.subToString Int.LF.Empty cD cPhi ss ) in 
(*            begin try  *)
              let tP = pruningTyp (Some loc) cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) in
                FMVar.add u (tP, cPhi);
                Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil)
(*            with _ -> raise (Error (Some loc,  *)
          else
           if isProjPatSub s then 
             let _ = dprint (fun () -> "Synthesize domain for meta-variable " ^ u.string_of_name ) in
             let _ = dprint (fun () -> "isProjPatSub ... " ) in 
             let (flat_cPsi, conv_list) = flattenDCtx cPsi in  
             let _ = dprint (fun () -> "flattenDCtx done " ^ P.dctxToString cO cD flat_cPsi ^ "\n") in 
             let _ = dprint (fun () -> "conv_list " ^ conv_listToString conv_list ) in 
             let flat_s = flattenProjPat s conv_list in 
             let _ = dprint (fun () -> "flattenProjPat done " ) in

             let (cPhi, s'') = synDom cD loc flat_cPsi flat_s in 
             let ss =  Substitution.LF.invert s'' in  

             let tP' = strans_typ sP conv_list in 
             let _ = dprint (fun () -> "[synDom] Prune type " ^ P.typToString Int.LF.Empty cD cPsi sP ) in  
             let _ = dprint (fun () -> "[synDom] Prune flattened type " ^ P.typToString Int.LF.Empty cD cPhi (tP', LF.id) ) in  
             let _ = dprint (fun () -> "         with respect to ss = " ^ P.subToString Int.LF.Empty cD cPhi ss ) in  

             let tP = pruningTyp (Some loc) cD flat_cPsi (*?*) 
                         (Context.dctxToHat flat_cPsi) (tP', LF.id) (Int.LF.MShift 0, ss)  in 

             let sorig = elSub loc recT cO cD cPsi s cPhi in
             let _ = dprint (fun () -> "sorig = " ^ P.subToString cO cD cPsi sorig ^ "\n") in 
             let _ = dprint (fun () -> "Type of mvar " ^ u.string_of_name ^ ":" ^ 
                               P.typToString cO cD cPhi (tP, LF.id) ^ " [ " ^ 
                               P.dctxToString cO cD cPhi ^ " ] ") in
 
            FMVar.add u (tP, cPhi); 
            Int.LF.Root (Some loc, Int.LF.FMVar (u, sorig), Int.LF.Nil)

            else 
              let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
                add_fcvarCnstr (m, v);
                Int.LF.Root (Some loc, Int.LF.MVar (v, LF.id), Int.LF.Nil)

        | Violation msg  -> 
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg) ; 
            raise (Error (Some loc, CompTypAnn ))

      end



  | Apx.LF.Root (loc, Apx.LF.FPVar (p, s), spine) as m ->
      begin try
        let (tA, cPhi) = FPVar.get p in 
        let s'' = elSub loc recT  cO cD cPsi s cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
        let tR = Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), tS) in
          begin try
            Unify.unifyTyp cD cPsi sQ sP;
            tR
          with Unify.Unify msg -> 
                 (Printf.printf "%s\n" msg;
                 raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
             | _ ->
                (Printf.printf "Unification Error (5) \n";
                 raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
          end
      
      with 
        | Not_found ->
          begin match (spine, isPatSub s) with
            | (Apx.LF.Nil, true) ->
                let (cPhi, s'') = synDom cD loc cPsi s in
                let si          = Substitution.LF.invert s'' in
                let tP = pruningTyp (Some loc) cD cPsi (*?*) (Context.dctxToHat cPsi) sP 
                                (Int.LF.MShift 0, si)  in
                  FPVar.add p ((Whnf.normTyp (tP,LF.id)),  cPhi);
                  Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), Int.LF.Nil)
            
            | (Apx.LF.Nil, false) ->
                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc, Int.LF.PVar (q, LF.id), Int.LF.Nil)
            
            | (_, _) ->  raise (Error (Some loc, NotPatternSpine))

                   (* (Printf.printf "elTerm': FPVar with spine\n" ; raise NotImplemented)*)
          end
        | Violation msg  -> 
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg) ;
            raise (Error (Some loc, CompTypAnn ))
      end

  (* Reconstruct: Projection *)
  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.FPVar (p, s), k), spine) as m ->
      (* Other case where spine is not empty is not implemented -bp *)
        begin try          
          let _ = dprint (fun () -> "[Reconstruct Projection Parameter] " ^ p.string_of_name ) in 
(*          let (tA, cPhi) = FPVar.get p in *)
          let ((Int.LF.Sigma typRec) as tA, cPhi) = FPVar.get p in 
          let _ = dprint (fun () -> "      with type " ^ P.typToString cO cD cPhi (tA, LF.id) ^ "[" ^ P.dctxToString cO cD cPhi ^ "]") in 
          let s'' = elSub loc recT  cO cD cPsi s cPhi in
(*          let Int.LF.Sigma typRec = tA *)
          let sA = Int.LF.getType  (Int.LF.FPVar (p, s'')) (typRec, s'') k 1 in  
          let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (Int.LF.TClo sA, s'')  in
            begin try
              (Unify.unifyTyp cD cPsi (Int.LF.TClo sQ, s'') sP ;
               Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.FPVar (p, s''), k), tS))
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
               raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
              | _ ->               (Printf.printf "Unification Error (6)\n" ;
               raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
            end
        with Not_found ->
          begin match (isPatSub s, spine) with
            | (true, Apx.LF.Nil) ->
                let (cPhi, s'') = synDom cD loc cPsi s in
                let si          = Substitution.LF.invert s'' in
                let tP = pruningTyp (Some loc) cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, si)  in 

                let Some psi =  Context.ctxVar cPsi in
                let schema = Schema.get_schema (Context.lookupCtxVarSchema cO psi) in 
                let h = Int.LF.FPVar (p, LF.id) in
                let (typRec, s_inst) = 
                  begin match synSchemaElem loc recT  cO cD cPhi (tP, LF.id) (h, k) schema with
                  | None -> raise (Violation ("type sP = " ^ P.typToString cO cD cPhi (tP, LF.id) ^ " not in schema " ^ 
                                             P.schemaToString schema))
                  | Some (typrec, subst) -> (typrec, subst)  
                  end in       
                let tB  =  
                  begin match typRec with 
                  | Int.LF.SigmaLast tA -> 
                      (dprint (fun () -> "synType for PVar: [SigmaLast]" ^ P.typToString cO cD cPhi (tA, s_inst) ^ "\n"); tA) 
                  | typRec' -> 
                      (dprint (fun () -> "synType for PVar: [SigmaElem]" ^ P.typRecToString cO cD cPhi (typRec', s_inst) ^ "\n") ; 
                       Int.LF.Sigma typRec' )
                  end in 
                  FPVar.add p ((Whnf.normTyp (tB, s_inst)), cPhi);
                  Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.FPVar (p, s''), k),  Int.LF.Nil) 
                  
            | (false, Apx.LF.Nil) ->
                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.PVar (q, LF.id), k),  Int.LF.Nil)

            | ( _ , _ ) -> raise (Violation ("Projection on a parameter variable has a functional type"))
          end
        end

  (* Reconstruction for meta-variables  *)
  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (tN, tQ, cPhi), s'), Apx.LF.Nil) ->
      let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        begin try
          let _   = dprint (fun () -> "[elTerm] Apx-mvar: Expected type: " ^ P.typToString cO cD cPsi sP ^ "\n") in 
          let _   = dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cO cD cPsi (tQ, s'') ^ "\n") in 
          (* This case only applies to Beluga; MInst are introduced during cnormApxTerm. *)
          ( Unify.unifyTyp cD  cPsi (tQ, s'') sP ; 
            dprint (fun () -> "[elTerm] reconstruction of mvar done ");
            dprint (fun () -> "  sQ = " ^ P.typToString cO cD cPsi (tQ,s'') ^ " == " ^ P.typToString cO cD cPsi sP) ; 
            dprint (fun () -> "  tN = " ^ P.normalToString cO cD cPsi (tN, s''));
           Int.LF.Clo(tN, s''))
      with  Violation msg  -> 
        (dprint (fun () -> "[elTerm] Violation: " ^ msg) ;
         dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cO cD cPsi (tN,s''));
         raise (Error (Some loc, CompTypAnn )))
        |  Unify.Unify msg  -> 
             dprint (fun () -> "[elTerm] Unification Violation: " ^ msg) ;
             dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cO cD cPsi (tN,s''));
             dprint (fun () -> "[elTerm] Expected type: " ^ P.typToString cO cD cPsi sP);
             dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cO cD cPsi (tQ, s''));
             dprint (fun () -> "[elTerm] cD = " ^ P.mctxToString cO cD);
             raise (Error (Some loc, CompTypAnn ))
        | _ ->               (Printf.printf "Unification Error (7)\n" ;
             dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cO cD cPsi (tN,s''));
             dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cO cD cPsi (tQ, s'') ^ " does not match expected type");
(*             dprint (fun () -> "[elTerm] Expected type: " ^ P.typToString cO cD cPsi sP ^ "\n");*) 
(*             dprint (fun () -> "[elTerm] cD = " ^ P.mctxToString cO cD ^ "\n"); *)
                              raise (Error (Some loc, CompTypAnn))
                   )
      end
        
  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset u, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxMDec cD u in
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ) = elSpine loc recT  cO cD cPsi spine (tA, s'') in
        let tR = Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset u, s''), tS) in 
          begin try
            (Unify.unifyTyp cD cPsi sQ sP ; 
            tR) 
            with Unify.Unify msg ->
                   (Printf.printf "%s\n" msg;
                    raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
              | _ ->
                  (Printf.printf "Unification Error (7)\n" ;
                   raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
          end
      with Violation msg ->
        dprint (fun () -> "[elTerm] Violation: " ^ msg);
        raise (Error (Some loc, CompTypAnn))
      end

  (* Reconstruction for parameter variables *)
  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s'), spine) ->
      begin try
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
        let _ = Unify.unifyTyp cD cPsi sQ sP  in
          begin match h with 
              | Int.LF.BVar k -> 
                  begin match LF.bvarSub k s'' with 
                    | Int.LF.Head (Int.LF.BVar j) -> Int.LF.Root (Some loc, Int.LF.BVar j, tS)
                    | Int.LF.Head (Int.LF.PVar (p,r'))   -> Int.LF.Root (Some loc, Int.LF.PVar (p, LF.comp r' s''), tS)
                  end 
              | Int.LF.PVar (p, r) -> Int.LF.Root (Some loc, Int.LF.PVar (p, LF.comp r s''), tS)
            end              
            
      with _  -> 
        raise (Error (Some loc, CompTypAnn ))
        (* raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP)))*)
      end


  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p,s'), spine) ->
      begin try 
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
        let tR = Int.LF.Root (Some loc, Int.LF.PVar (Int.LF.Offset p, s''), tS) in 
          begin try
            Unify.unifyTyp cD cPsi sQ sP ; 
            tR
          with Unify.Unify msg -> 
            (Printf.printf "%s\n" msg;
             raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
          end
      with Violation msg  -> 
        dprint (fun () -> "[elTerm] Violation: " ^ msg);
        raise (Error (Some loc, CompTypAnn ))
      end



  (* Reconstruction for projections *)
  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.BVar x , k),  spine) ->
      let Int.LF.TypDecl (_, Int.LF.Sigma recA) = Context.ctxSigmaDec cPsi x in
      let sA       = Int.LF.getType (Int.LF.BVar x) (recA, LF.id) k 1 in 
      let (tS, sQ) = elSpine loc recT cO cD  cPsi spine sA in 
        begin try
          (Unify.unifyTyp cD cPsi sQ sP ;
           Int.LF.Root (Some loc, Int.LF.Proj (Int.LF.BVar x, k), tS)
          )
        with Unify.Unify msg ->
          (Printf.printf "%s\n" msg;
           raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
        end

  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset p,t), k),  spine) ->
      begin match Whnf.mctxPDec cD p with
        | (_, Int.LF.Sigma recA, cPsi') -> 
            let t' = elSub loc recT cO cD  cPsi t cPsi' in 
            let  sA = Int.LF.getType (Int.LF.PVar (Int.LF.Offset p, t')) (recA, t') k 1 in 
            let (tS, sQ) = elSpine loc recT cO cD  cPsi spine sA in 
              begin try
                (Unify.unifyTyp cD cPsi sQ sP ;
                 Int.LF.Root (Some loc, Int.LF.Proj (Int.LF.PVar (Int.LF.Offset p,t'), k), tS)
                )
              with Unify.Unify msg ->
                (Printf.printf "%s\n" msg;
                 raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
              end
        | _  -> raise (Error (Some loc, IllTypedElab (cO, cD, cPsi, sP)))

      end


  | Apx.LF.Root (loc, Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s'), k), spine) ->
      begin try
        let recA =
              match tA with
              | Int.LF.Sigma recA -> recA
              | _ -> 
                  dprint (fun () -> "Type of Parameter variable " ^ P.headToString cO cD cPhi h
                                  ^ "not a Sigma-Type, yet used with Projection; found "
                                  ^ P.typToString cO cD cPhi (tA, LF.id) ^ "\n ill-typed") ;
                  raise (Violation "Type of Parameter variable not a Sigma-Type, yet used with Projection; ill-typed")
        in 
        let s''       = elSub loc recT  cO cD cPsi s' cPhi in
        let sA        = Int.LF.getType h (recA, s'') k 1 in 
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine sA  in
        let _ = Unify.unifyTyp cD cPsi sQ sP  in
          begin match h with 
              | Int.LF.BVar y -> 
                  begin match LF.bvarSub y s'' with 
                    | Int.LF.Head (Int.LF.BVar x) -> 
                        Int.LF.Root (Some loc, Int.LF.Proj(Int.LF.BVar x, k), tS)
                    | Int.LF.Head (Int.LF.PVar (p,r'))   -> 
                        Int.LF.Root (Some loc, Int.LF.Proj(Int.LF.PVar (p, LF.comp r' s''), k), tS)
                  end 
              | Int.LF.PVar (p, r) -> 
                  Int.LF.Root (Some loc, Int.LF.Proj(Int.LF.PVar (p, LF.comp r s''), k), tS)
            end              
            
      with _   -> 
        raise (Error (Some loc, CompTypAnn ))
        (* raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP)))*)
      end

  | Apx.LF.Root (loc, Apx.LF.Proj (Apx.LF.PVar (Apx.LF.MInst _ , _), _ ), _) ->
      raise (Violation "[elTerm'] Proj (PVar (MInst _, _  ) _ , _ )")

  | Apx.LF.Root (loc, Apx.LF.Proj (Apx.LF.FMVar _, _ ), _) ->
      raise (Violation "[elTerm'] Proj (FMVar _ , _ )")

  | Apx.LF.Root (loc, Apx.LF.PVar _, _) ->
      raise (Violation "[elTerm'] PVar ")

  | Apx.LF.Root (loc, h, _s) -> 
      (dprint (fun () -> "[elTerm' **] h = " ^ what_head h ^ "\n") ;
            raise (Error (Some loc, CompTypAnn )))


and elClosedTerm' recT  cO cD cPsi r = match r with
  | Apx.LF.Root (loc, Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      (* let s  = mkShift recT cPsi in *)
      let s = LF.id in
      let (tS, sQ ) = elSpineI loc recT  cO cD cPsi spine i (tA, s)   in
        (Int.LF.Root (Some loc, Int.LF.Const c, tS), sQ)

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, LF.id) in
        (Int.LF.Root (Some loc, Int.LF.BVar x, tS), sQ)

  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset u, s), spine) ->
      begin try 
        let (_ , tA, cPhi) = Whnf.mctxMDec cD u in
        let s'' = elSub loc recT  cO cD cPsi s cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset u, s''), tS) , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (Some loc, CompTypAnn))
      end

  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root (Some loc, Int.LF.PVar (Int.LF.Offset p, s''), tS) , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (Some loc, CompTypAnn ))
      end


  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.PInst (Int.LF.PVar (p0,s0), tA, cPhi), s'), spine) -> 
      begin try 
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root(Some loc, Int.LF.PVar (p0, LF.comp s0 s''), tS)  , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (Some loc, CompTypAnn))
      end


  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (tM', tA, cPhi), s'), spine) -> 
      begin try 
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Whnf.reduce (tM', s'') tS  , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (Some loc, CompTypAnn))
      end

  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.BVar x , k),  spine) ->
      let Int.LF.TypDecl (_, Int.LF.Sigma recA) = Context.ctxSigmaDec cPsi x in
      let sA       = Int.LF.getType (Int.LF.BVar x) (recA, LF.id) k 1 in 
      let (tS, sQ) = elSpine loc recT cO cD  cPsi spine sA in 
        (Int.LF.Root (Some loc, Int.LF.Proj (Int.LF.BVar x, k), tS) , sQ)

  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset p,t), k),  spine) ->
      begin match Whnf.mctxPDec cD p with
        | (_, Int.LF.Sigma recA, cPsi') -> 
            let t' = elSub loc recT cO cD  cPsi t cPsi' in 
            let  sA = Int.LF.getType (Int.LF.PVar (Int.LF.Offset p, t')) (recA, t') k 1 in 
            let (tS, sQ) = elSpine loc recT cO cD  cPsi spine sA in 
              (Int.LF.Root (Some loc, Int.LF.Proj (Int.LF.PVar (Int.LF.Offset p,t'), k), tS) , sQ)
        | _  -> raise (Error (Some loc, CompTypAnn))
      end

  | Apx.LF.Root (loc, _ , _ ) ->
      raise (Error (Some loc, CompTypAnn ))

  | Apx.LF.Lam (loc, _, _ ) -> 
      raise (Error (Some loc, CompTypAnn ))

  | _ -> (dprint (fun () -> "[elClosedTerm] Violation?");
                raise (Error (None, CompTypAnn)))



(* elSub recT  cO cD cPsi s cPhi = s'
 *
 *)
and elSub loc recT  cO cD cPsi s cPhi =
  match (s, cPhi) with
  | (Apx.LF.EmptySub, Int.LF.Null) ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) -> Int.LF.Shift (Int.LF.CtxShift psi, d)
        | (None, d)     -> Int.LF.Shift (Int.LF.NoCtxShift, d)
      end

  | (Apx.LF.SVar (Apx.LF.Offset offset, s), Int.LF.CtxVar phi) -> 
      begin try
        match Whnf.mctxSDec cD offset with
          | (_ , Int.LF.CtxVar phi', cPhi2)  ->  
              if phi = phi' then 
                let s' = elSub loc recT  cO cD cPsi s (Int.LF.CtxVar phi) in
                  Int.LF.SVar (Int.LF.Offset offset, s')
              else raise (Error (Some loc, SubIllTyped))
      with 
          _ -> raise (Error (Some loc, SubIllTyped))
      end 


  | (Apx.LF.Id, Int.LF.CtxVar phi) ->
      begin match Context.dctxToHat (C.cnormDCtx (cPsi, C.m_id)) with
        | (Some psi, d)  ->
(*            if psi = phi then  *)
            let _ = dprint (fun () -> "[elSub] cPsi " ^ P.dctxToString cO cD cPsi ^ "\n phi = " ^ P.dctxToString cO cD cPhi ^ "\n") in
            if unify_phat (Some phi, 0) (Some psi, 0) then   
              Int.LF.Shift(Int.LF.NoCtxShift, d)
            else
              (* check for context subsumption *)
              if Check.LF.subsumes cO phi psi (* psi |- wk_sub : phi *)then
                Int.LF.Shift (Int.LF.NoCtxShift, d)
              else 
                raise (Violation ("elSub: not identity substitution between ctxvar: "
                                  ^ "`" ^ P.dctxToString cO cD cPhi ^ "' does not match `" ^ 
                                  P.dctxToString cO cD cPsi ^ "'"))
                
        | _ ->
            raise (Violation "Id must be associated with ctxvar")
      end


  | (Apx.LF.Dot (Apx.LF.Head h, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl (_, tA))) ->
      (* NOTE: if decl = x:A, and cPsi(h) = A' s.t. A =/= A'
       *       we will fail during reconstruction / type checking
       *)
      let (h', sA') = elHead loc recT  cO cD cPsi h in 
      let s' = elSub  loc recT  cO cD cPsi s cPhi' in 
      begin try 
          Unify.unifyTyp cD cPsi sA' (tA, s');
          Int.LF.Dot (Int.LF.Head h', s')
      with
        | Error (loc, msg) -> raise (Error (loc, msg))
        |  _ -> 
             raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sA', (tA, s'))))
      end


  | (Apx.LF.Dot (Apx.LF.Obj m, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl(_, tA))) ->
      let s' = elSub loc recT  cO cD cPsi s cPhi' in
      let m' = elTerm recT  cO cD cPsi m (tA, s') in
        Int.LF.Dot (Int.LF.Obj m', s')

  | (_s, cPhi) ->
      raise (Error (Some loc, IllTypedIdSub))


and elHead loc recT  cO cD cPsi = function
  | Apx.LF.BVar x ->
      let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
        (Int.LF.BVar x,  (tA' , LF.id))

  | Apx.LF.Const c ->
      let tA = (Term.get c).Term.typ in
        (Int.LF.Const c , (tA, LF.id))

  | Apx.LF.MVar (Apx.LF.Offset u, s) ->
      begin try
        let (_ , tA, cPhi) = Whnf.mctxMDec cD u in
        let s'  = elSub loc recT  cO cD cPsi s cPhi in 
          (Int.LF.MVar (Int.LF.Offset u, s') , (tA, s'))
      with Violation msg  -> 
        dprint (fun () -> "[elHead] Violation: " ^ msg);
         raise (Error (Some loc, CompTypAnn ))
      end 

  | Apx.LF.PVar (Apx.LF.Offset p, s) ->
      begin try 
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in 
        let s' = elSub loc recT  cO cD cPsi s cPhi in 
          (Int.LF.PVar (Int.LF.Offset p, s') , (tA, s'))
      with Violation msg  -> 
        dprint (fun () -> "[elHead] Violation: " ^ msg);
        raise (Error (Some loc, CompTypAnn ))
      end

  | Apx.LF.PVar (Apx.LF.PInst (Int.LF.PVar (p,r), tA, cPhi), s) -> 
      begin try
        let s' = elSub loc recT  cO cD cPsi s cPhi in 
        let r' = LF.comp r s' in 
         (Int.LF.PVar (p, r') , (tA, r')) 
      with Violation msg -> 
        dprint (fun () -> "[elHead] Violation: " ^ msg);
        raise (Error (Some loc, CompTypAnn ))
      end
      

  | Apx.LF.FVar x ->
      raise (Error (Some loc, UnboundName x))
      (* Int.LF.FVar x *)

  | Apx.LF.FMVar (u, s) ->       
      begin try 
        let (offset, (tP, cPhi)) = Whnf.mctxMVarPos cD u  in
        let s' = elSub loc recT  cO cD cPsi s cPhi in 
         (Int.LF.MVar (Int.LF.Offset offset,s'), (tP, s'))
      with Whnf.Fmvar_not_found -> 
       raise (Error (None, UnboundName u))
      end 

  | Apx.LF.FPVar (p, s) ->
      let (offset, (tA, cPhi)) = Whnf.mctxPVarPos cD p  in
      let s' = elSub loc recT  cO cD cPsi s cPhi in 
        (Int.LF.PVar (Int.LF.Offset offset, s') , (tA, s'))

  | Apx.LF.Proj (head, i) ->
      let (head', sA) = elHead loc recT  cO cD cPsi head in
      let sAi = begin match Whnf.whnfTyp sA with
                 | (Int.LF.Sigma tA'rec, s') ->
                     Int.LF.getType head' (tA'rec, s') i 1 
                 | (tA',s') -> raise (Violation ("[elHead] expected Sigma type  " 
                                                 ^ "found type " ^ P.typToString cO cD cPsi (tA', s')))
                end
      in
        (Int.LF.Proj (head', i) , sAi )

  | h -> raise (Violation (what_head h))

and elSpineI loc recT  cO cD cPsi spine i sA =
  elSpineIW loc recT  cO cD cPsi spine i (Whnf.whnfTyp sA) 

and elSpineIW loc recT  cO cD cPsi spine i sA  =
  if i = 0 then
    elSpine loc recT  cO cD cPsi spine sA 
  else
    match (sA, recT) with
      | ((Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s), PiRecon) ->
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in
          let (spine', sP) = elSpineI loc recT  cO cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            (Int.LF.App (tN, spine'), sP)

      | ((Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _), tB), s), PiboxRecon) ->
          let tN     = Whnf.etaExpandMMV (Some loc) cD cPsi (tA, s) LF.id in

          let (spine', sP) = elSpineI loc recT  cO cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            (Int.LF.App (tN, spine'), sP)

and elSpine loc recT  cO cD cPsi spine sA =
  elSpineW loc recT  cO cD cPsi spine (Whnf.whnfTyp sA)

and elSpineW loc recT  cO cD cPsi spine sA = match (spine, sA) with
  | (Apx.LF.Nil, sP) ->
      (Int.LF.Nil, sP) (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s)) ->
      let tM = elTerm recT  cO cD cPsi m (tA, s) in
      let (tS, sP) = elSpine loc recT  cO cD cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) in
        (Int.LF.App (tM, tS), sP)

  | (Apx.LF.App _, _) ->
      raise (Error (Some loc, SpineIllTyped))

(* see invariant for elSpineI *)
and elKSpineI recT  cO cD cPsi spine i sK =
  if i = 0 then
    elKSpine recT  cO cD cPsi spine sK
  else
    match (sK, recT) with
      | ((Int.LF.PiKind ((Int.LF.TypDecl (_, tA), _), tK), s), PiRecon) ->
          (* let sshift = mkShift recT cPsi in *)
          (* let tN     = Whnf.etaExpandMV Int.LF.Null (tA,s) sshift in *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in
          let spine' = elKSpineI recT  cO cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')
      | ((Int.LF.PiKind ((Int.LF.TypDecl (_, tA), _), tK), s), PiboxRecon) ->
          (* let sshift = mkShift recT cPsi in *)
          let tN     = Whnf.etaExpandMMV None cD cPsi (tA, s) LF.id in
          let spine' = elKSpineI recT  cO cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')


(* see invariant for elSpine *)
and elKSpine recT  cO cD cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (Int.LF.Typ, _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiKind ((Int.LF.TypDecl (_, tA), _), tK), s)) ->
      let tM = elTerm recT  cO cD cPsi m (tA, s) in
      let tS = elKSpine recT  cO cD cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | ( _, _) ->
      ((*Printf.printf "elKSpine: spine ill-kinded\n"; *)
      raise NotImplemented )(* TODO postpone error to reconstruction phase *)

and elSpineSynth recT  cD cPsi spine s' sP = match (spine, sP) with
  | (Apx.LF.Nil, (_tP, _s))  ->
      let ss = LF.invert s' in
      let tQ = pruningTyp None cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) in 
      (* PROBLEM: [s'][ss] [s]P is not really P; in fact [ss][s]P may not exist;
       * We use pruning to ensure that [ss][s]P does exist
       *)
        (Int.LF.Nil, tQ) 

  | (Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        (* cPsi |- tA : type
         * cPsi |- s' : cPsi'
         *)
      let ss = LF.invert s' in
      (* let tA' = Whnf.normTyp (tA, ss) in *)
      (* Is [ss]A  always guaranteed to exist? - No. Use pruning to ensure it does exist. *)
      let tA' = pruningTyp (Some loc) cD cPsi (*?*) (Context.dctxToHat cPsi)  (tA, LF.id) (Int.LF.MShift 0, ss) in 

      let _ = dprint (fun () -> "elSpineSynth: PruneTyp done\n") in 

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth recT  cD cPsi spine (Int.LF.Dot (Int.LF.Head(Int.LF.BVar x), s')) sP in
        (*  cPsi |- tS : [s', x]tB <= sP  *)
        (*  cPsi, y:A |- tB' <= type  *)
      let _ = dprint (fun () -> "elSpineSynth done \n") in 
      let tB' =  Int.LF.PiTyp ((Int.LF.TypDecl (Id.mk_name (Id.BVarName (Typ.gen_var_name tA')), tA'), 
                                Int.LF.Maybe), tB) in 

      let tN' = etaExpandHead loc (Int.LF.BVar x) tA' in 
        (Int.LF.App (tN', tS), tB')

   (* other cases impossible *)


let rec elTypDeclCtx cO cD  = function
  | Apx.LF.Empty ->
      Int.LF.Empty

  | Apx.LF.Dec (ctx, Apx.LF.TypDecl (name, typ)) ->
      let ctx'     = elTypDeclCtx cO cD ctx in
      let typDecl' = Int.LF.TypDecl (name, elTyp PiRecon cO cD (projectCtxIntoDctx ctx') typ) in
        Int.LF.Dec (ctx', typDecl')

let rec elSchElem cO (Apx.LF.SchElem (ctx, typRec)) =
   let cD = Int.LF.Empty in
   let _ = dprint (fun () -> "elTypDeclCtx \n") in 
   let el_ctx = elTypDeclCtx cO cD ctx in
   let dctx = projectCtxIntoDctx el_ctx in
   let _ = dprint (fun () -> "elSchElem cPsi = " ^ P.dctxToString Int.LF.Empty Int.LF.Empty dctx ^ "\n") in 
   let typRec' = elTypRec PiRecon cO cD dctx typRec in
     Int.LF.SchElem(el_ctx, typRec')

let rec elSchema cO (Apx.LF.Schema el_list) =
   Int.LF.Schema (List.map (elSchElem cO) el_list)


let rec elCtxVar c_var = match c_var with 
  | Apx.LF.CtxOffset offset  -> Int.LF.CtxOffset offset
  | Apx.LF.CtxName psi       -> Int.LF.CtxName psi

let rec elDCtx recT  cO cD psi = match psi with
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar (c_var) -> 
      Int.LF.CtxVar(elCtxVar c_var)

  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtx recT cO cD psi' in
      let tA   = elTyp recT cO cD cPsi a in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))

let rec elCDecl recT cO cD cdecl = match cdecl with
  | Apx.LF.MDecl (u, a, psi) ->
      let cPsi = elDCtx recT cO cD psi in
      let tA   = elTyp recT cO cD cPsi a in
        Int.LF.MDecl (u, tA, cPsi)
  | Apx.LF.PDecl (u, a, psi) ->
      let cPsi = elDCtx recT cO cD psi in
      let tA   = elTyp recT cO cD cPsi a in
        Int.LF.PDecl (u, tA, cPsi)

  | Apx.LF.SDecl (u, phi, psi) ->
      let cPsi = elDCtx recT cO cD psi in
      let cPhi = elDCtx recT cO cD phi in
        Int.LF.SDecl (u, cPhi, cPsi)

  | Apx.LF.CDecl (g, schema_cid) ->
      Int.LF.CDecl (g, schema_cid)

let rec elMCtx recT cO delta = match delta with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (delta, cdec) ->
      let cD    = elMCtx recT cO delta in
      let cdec' = elCDecl recT cO cD cdec in
        Int.LF.Dec (cD, cdec')


let rec elCCtx omega = match omega with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (omega, Apx.LF.CDecl(g,schema_cid)) ->
      let cO    = elCCtx omega in
        Int.LF.Dec (cO, Int.LF.CDecl (g, schema_cid))


(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr recT cO cD cnstr = match cnstr with
  | [] -> ()
  | ((_ , Apx.LF.Root (loc, Apx.LF.FVar x, spine), Int.LF.Inst ({contents = None} as r, cPsi, tP, _)) :: cnstrs) -> begin try
      begin match FVar.get x with
        | Int.LF.Type tA -> 
          (* For type reconstruction to succeed, we must have
           *  . |- tA <= type
           *  This will be enforced during abstraction.
           *)
            let sshift = mkShift recT cPsi in

            (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
            let (tS, sQ ) = elSpine loc recT cO cD cPsi spine (tA, sshift) in
              begin try
                (Unify.unifyTyp cD cPsi sQ (tP, LF.id) ;
                 r := Some (Int.LF.Root (Some loc, Int.LF.FVar x, tS));
                 solve_fvarCnstr recT cO cD cnstrs
                ) 
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, (tP, LF.id), sQ))))
              end
        | Int.LF.TypVar _ -> 
            raise (Error (Some loc, LeftoverConstraints x))
      end
    with _ -> raise (Error (Some loc, UnboundName x)) 
    end 


  | ((_ , Apx.LF.Root (loc, Apx.LF.FVar x, spine), Int.LF.Inst ({contents = Some tR}, cPsi, tP, _ )) :: cnstrs) ->
      begin try 
        begin match FVar.get x with
        | Int.LF.Type tA -> 
          (* For type reconstruction to succeed, we must have
           *  . |- tA <= type
           *  This will be enforced during abstraction.
           *)
            let sshift = mkShift recT cPsi in

            (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
            let (tS, sQ ) = elSpine loc recT cO cD cPsi spine (tA, sshift) in
         (* let psihat = Context.dctxToHat cPsi in             *)
              begin try 
                (Unify.unifyTyp cD cPsi sQ (tP, LF.id) ;
                 Unify.unify cD cPsi (Int.LF.Root (Some loc, Int.LF.FVar x, tS), LF.id) (tR, LF.id);
              (* r := Some (Int.LF.Root (Some loc, Int.LF.FVar x, tS)); *)
              solve_fvarCnstr recT cO cD cnstrs
                ) 
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, (tP, LF.id), sQ))))
              end


        | Int.LF.TypVar _ -> 
            raise (Error (Some loc, LeftoverConstraints x))
      end

    with _ -> raise (Error (Some loc, UnboundName x)) 
    end 


(* Solve free variable constraints *)

let rec solve_fcvarCnstr cO cD cnstr = match cnstr with
  | [] -> ()
  | ((Apx.LF.Root (loc, Apx.LF.FMVar (u,s), _nil_spine), Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let (_tP, cPhi) = FMVar.get u in
        let s'' = elSub loc PiboxRecon cO cD cPsi s cPhi in
          r := Some (Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil));
          solve_fcvarCnstr cO cD cnstrs
      with Not_found ->
        raise (Error (Some loc, LeftoverConstraints u))
      end

  | ((Apx.LF.Root (loc, Apx.LF.FPVar (x,s), spine), Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let (tA, cPhi) = FPVar.get x in
        let s'' = elSub loc PiboxRecon cO cD cPsi s cPhi in

        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let (tS, _ ) = elSpine loc PiboxRecon cO cD cPsi spine (tA, s'') in
          r := Some (Int.LF.Root (Some loc, Int.LF.FPVar (x,s''), tS));
          solve_fcvarCnstr cO cD cnstrs
      with Not_found ->
        raise (Error (Some loc, LeftoverConstraints x))
      end

let rec cnormApxTerm cO cD delta m (cD'', t) cs = match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, cnormApxTerm cO cD delta m' (cD'', t) cs)

  | Apx.LF.Root (loc, h, s) -> 
      let h' = cnormApxHead cO cD delta h (cD'', t) cs in 
      let s' = cnormApxSpine cO cD delta s (cD'', t) cs in 
        Apx.LF.Root (loc, h', s')
  | Apx.LF.Tuple (loc, tuple) -> 
      Apx.LF.Tuple(loc, cnormApxTuple cO cD delta tuple (cD'', t) cs)

and cnormApxTuple cO cD delta tuple (cD'', t) cs = match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (cnormApxTerm cO cD delta m (cD'' , t) cs)
  | Apx.LF.Cons (m, tuple) -> 
      Apx.LF.Cons (cnormApxTerm cO cD delta m (cD'' , t) cs,
                   cnormApxTuple cO cD delta tuple (cD'', t) cs)


and cnormApxHead cO cD delta h (cD'', t) cs = match h with
  | Apx.LF.MVar (Apx.LF.Offset offset, s) ->
      let l_delta = lengthApxMCtx delta in 
      let offset' = (offset - l_delta)  in 
        if offset > l_delta then 
          begin match LF.applyMSub offset  t with
            | Int.LF.MV u ->  
                Apx.LF.MVar (Apx.LF.Offset u, cnormApxSub cO cD delta s (cD'', t) cs)
            | Int.LF.MObj (_phat, tM) -> 

                let (_u, tP, cPhi) = Whnf.mctxMDec cD offset' in
                 (* Bug fix -- drop elements l_delta elements from t -bp, Aug 24, 2009
                    Given cD'' |- t : cD, l_delta 
                    produce t' s.t. cD'' |- t' : cD   and t',t_delta = t

                    Must do the same for PVARs
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 

                let t' = drop t l_delta in

                let (tP', cPhi')  = (Whnf.cnormTyp (tP, t'), Whnf.cnormDCtx (cPhi, t')) in 
                  Apx.LF.MVar (Apx.LF.MInst (tM, tP', cPhi'), 
                               cnormApxSub cO cD delta s (cD'', t) cs)
          end
        else 
          Apx.LF.MVar (Apx.LF.Offset offset, cnormApxSub cO cD delta s (cD'', t) cs)

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) -> 
      let tM' = Whnf.cnorm (tM,t) in 
      let (tP', cPhi')  = (Whnf.cnormTyp (tP, t), Whnf.cnormDCtx (cPhi, t)) in 

      let s' = cnormApxSub cO cD delta s (cD'', t) cs in  
        Apx.LF.MVar (Apx.LF.MInst (tM', tP', cPhi'), s')  

  | Apx.LF.PVar (Apx.LF.Offset offset, s) -> 
      let l_delta = lengthApxMCtx delta in 
      let offset' = (offset - l_delta)  in 
        if offset > l_delta then 
          begin match LF.applyMSub offset t with
            | Int.LF.MV offset' ->  Apx.LF.PVar (Apx.LF.Offset offset', cnormApxSub cO cD delta s (cD'', t) cs)
            | Int.LF.PObj (_phat, h) -> 
                let _ = dprint (fun () -> "[cnormApxTerm] ApplyMSub done -- resulted in PObj") in 
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                  (* Bug fix -- drop elements l_delta elements from t -bp, Aug 24, 2009
                     Given cD'' |- t : cD, l_delta 
                     produce t' s.t. cD'' |- t' : cD   and t',t_delta = t
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 

                let t' = drop t l_delta in

                  Apx.LF.PVar (Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')), 
                               cnormApxSub cO cD delta s (cD'', t) cs)
          end
        else 
          Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cO cD delta s (cD'', t) cs)


  | Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s) -> 
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in 
      let s' = cnormApxSub cO cD delta s (cD'', t) cs in 
      let h' = begin match h with 
               | Int.LF.BVar _ -> h 
               | Int.LF.PVar (Int.LF.Offset q, s1) -> 
                   begin match LF.applyMSub q t with 
                     | Int.LF.MV q' -> 
                         let s1' = Whnf.cnormSub (s1, t) in 
                           Int.LF.PVar (Int.LF.Offset q', s1') 
                     | Int.LF.PObj (_hat, Int.LF.PVar (Int.LF.Offset q', s2)) -> 
                         let s1' = Whnf.cnormSub (s1, t) in 
                           Int.LF.PVar (Int.LF.Offset q', LF.comp s1' s2) 
                   end
               end in 
        Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s')

  | Apx.LF.FMVar(u, s) -> 
      Apx.LF.FMVar(u, cnormApxSub cO cD delta s (cD'', t) cs)

  | Apx.LF.FPVar(u, s) -> 
      Apx.LF.FPVar(u, cnormApxSub cO cD delta s (cD'', t) cs)

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, s), j) -> 
      let l_delta = lengthApxMCtx delta in  
      let offset' = (offset - l_delta)  in 
      let _ = dprint (fun () -> "[cnormApxTerm] Proj (PVar _ ) . " ^ string_of_int j ^ " : offset = " ^ string_of_int offset ) in 
      let _ = dprint (fun () -> "[cnormApxTerm] Proj (PVar _ ) . " ^ string_of_int j ^ " : offset' = " ^ string_of_int offset' ) in 
      let _ = dprint (fun () -> "[cnormApxTerm] l_delta = " ^ string_of_int l_delta ) in
      let _ = dprint (fun () -> "[cnormApxTerm] t = " ^ P.msubToString cO cD'' t ^ "\n") in 
      let _ = dprint (fun () -> "[cnormApxTerm] (original) cD = " ^ P.mctxToString cO cD ^ "\n") in 
        if offset > l_delta then 
          begin match LF.applyMSub offset t with 
            | Int.LF.MV offset' ->  
                Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset offset', 
                                         cnormApxSub cO cD delta s (cD'', t) cs), 
                            j)
            | Int.LF.PObj (_phat, h) -> 
                let _ = dprint (fun () -> "[cnormApxTerm] Proj - case: ApplyMSub done -- resulted in PObj  ") in 

                let _ = dprint (fun () -> "[cnormApxTerm] offset' = " ^ string_of_int offset' ^ "\n") in
                let _ = dprint (fun () -> "[cnormApxTerm] offset = " ^ string_of_int offset ^ "\n") in
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                let _ = dprint (fun () -> "[cnormApxTerm] tP = " ^ P.typToString cO cD cPhi (tP, LF.id) ^ "\n") in
                  (* Bug fix -- drop elements l_delta elements from t -bp, Aug 24, 2009
                     Given cD'' |- t : cD, l_delta 
                     produce t' s.t. cD'' |- t' : cD   and t',t_delta = t
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 

                let t' = drop t l_delta in
                  Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')), 
                                           cnormApxSub cO cD delta s (cD'', t) cs),
                              j)

            | Int.LF.MObj (phat, tM) -> 
                (dprint (fun () -> "[cnormApxTerm] MObj :" ^ 
                           P.normalToString cO cD (Context.hatToDCtx phat) (tM, LF.id) ^ "\n") ; 
                 raise (Violation "MObj found -- expected PObj"))
          end
        else 
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cO cD delta s (cD'', t) cs), j)

  | Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) -> 
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in 
      let s' = cnormApxSub cO cD delta s (cD'', t) cs in 
      let h' = begin match h with 
               | Int.LF.BVar _ -> h 
               | Int.LF.PVar (Int.LF.Offset q, s1) -> 
                   begin match LF.applyMSub q t with 
                     | Int.LF.MV q' -> 
                         let s1' = Whnf.cnormSub (s1, t) in 
                           Int.LF.PVar (Int.LF.Offset q', s1') 
                     | Int.LF.PObj (_phat, Int.LF.PVar (p,s')) -> 
                         let s1' = Whnf.cnormSub (s1, t) in 
                           Int.LF.PVar (p, s1')
                   end 
               | Int.LF.PVar (Int.LF.PInst ({contents = _ }, _cPsi, _tA, _ ) as p ,s1) -> 
                   Int.LF.PVar (p, Whnf.cnormSub (s1, t))

               end in 
        Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s'), j)   

  | _ -> h

and cnormApxSub cO cD delta s (cD'', t) cs = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id       -> s
  | Apx.LF.Dot (Apx.LF.Head h, s) -> 
      let h' = cnormApxHead cO cD delta h (cD'', t) cs in 
      let s' = cnormApxSub cO cD delta s (cD'', t) cs in 
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) -> 
      let m' = cnormApxTerm cO cD delta m (cD'', t) cs in 
      let s' = cnormApxSub cO cD delta s (cD'', t) cs in 
        Apx.LF.Dot (Apx.LF.Obj m', s')


and cnormApxSpine cO cD delta s (cD'', t) cs = match s with 
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) -> 
      let s' = cnormApxSpine cO cD delta s (cD'', t) cs in 
      let m' = cnormApxTerm cO cD delta m (cD'', t) cs in 
        Apx.LF.App (m' , s')

let rec cnormApxTyp cO cD delta a (cD'', t) cs = match a with
  | Apx.LF.Atom (loc, c, spine) -> 
      Apx.LF.Atom (loc, c, cnormApxSpine cO cD delta spine (cD'', t) cs)

  | Apx.LF.PiTyp ((t_decl, dep), a) -> 
      let t_decl' = cnormApxTypDecl cO cD delta t_decl (cD'', t) cs in 
      let a' = cnormApxTyp cO cD delta a (cD'', t) cs in 
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = cnormApxTypRec cO cD delta typ_rec (cD'', t) cs in
        Apx.LF.Sigma typ_rec'

and cnormApxTypDecl cO cD delta t_decl cDt cs = match t_decl with
  | Apx.LF.TypDecl (x, a) -> 
      Apx.LF.TypDecl(x, cnormApxTyp cO cD delta a cDt cs)

and cnormApxTypRec cO cD delta t_rec (cD'', t) cs = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (cnormApxTyp cO cD delta a (cD'', t) cs)
  | Apx.LF.SigmaElem (x, a, t_rec) -> 
      let a' = cnormApxTyp cO cD delta a (cD'', t) cs in 
      let t_rec' = cnormApxTypRec cO cD delta t_rec (cD'', t) cs in 
        Apx.LF.SigmaElem (x, a', t_rec')

let rec cnormApxDCtx cO cD delta psi (cDt : Syntax.Int.LF.mctx * Syntax.Int.LF.msub) cs = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) -> 
      begin match Ctxsub.apply_csub (Int.LF.CtxOffset offset) cs with
        | Int.LF.CtxVar (Int.LF.CtxOffset psi0) -> Apx.LF.CtxVar (Apx.LF.CtxOffset psi0)
        | Int.LF.Null ->  (dprint (fun () -> "[cnormApxDCtx Null"); raise NotImplemented)
        | Int.LF.DDec _ -> (dprint (fun () -> "[cnormApxDCtx DDec"); raise NotImplemented)
      end
  | Apx.LF.DDec (psi, t_decl) -> 
      let psi' = cnormApxDCtx cO cD delta psi cDt cs in  
      let t_decl' = cnormApxTypDecl cO cD delta t_decl cDt cs in  
        Apx.LF.DDec (psi', t_decl')


let rec cnormApxExp cO cD delta e (cD'', t) cs = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, cnormApxExp' cO cD delta i (cD'', t) cs)
  | Apx.Comp.Fun (loc, f, e)    -> Apx.Comp.Fun (loc, f, cnormApxExp cO cD delta e (cD'', t) cs)
  | Apx.Comp.CtxFun (loc, g, e) -> Apx.Comp.CtxFun (loc, g, cnormApxExp cO cD delta e (cD'', t) (Ctxsub.cdot1 cs))
  | Apx.Comp.MLam (loc, u, e)   -> (dprint (fun () -> "cnormApxExp -- could be PLam") ; 
      Apx.Comp.MLam (loc, u, cnormApxExp cO cD (Apx.LF.Dec(delta, Apx.LF.MDeclOpt u)) e (Int.LF.Dec (cD'', Int.LF.MDeclOpt u), Whnf.mvar_dot1 t) cs) )
  | Apx.Comp.Pair (loc, e1, e2) -> 
      let e1' = cnormApxExp cO cD delta e1 (cD'', t) cs in 
      let e2' = cnormApxExp cO cD delta e2 (cD'', t) cs in 
        Apx.Comp.Pair (loc, e1', e2')
  | Apx.Comp.LetPair (loc, i, (x,y, e)) -> 
      let i' = cnormApxExp' cO cD delta i (cD'', t) cs in 
      let e' = cnormApxExp  cO cD delta e (cD'', t) cs in 
        Apx.Comp.LetPair (loc, i', (x,y, e')) 

  | Apx.Comp.Box(loc, phat, m) -> 
      let phat' = Ctxsub.ctxnorm_psihat (phat, cs) in 
      Apx.Comp.Box (loc, phat', cnormApxTerm cO cD delta m (cD'', t) cs)

  | Apx.Comp.SBox(loc, phat, s) -> 
      let phat' = Ctxsub.ctxnorm_psihat (phat, cs) in 
      Apx.Comp.SBox (loc, phat', cnormApxSub cO cD delta s (cD'', t) cs)


  | Apx.Comp.Case (loc, prag, i, branch) -> 
      Apx.Comp.Case (loc, prag, cnormApxExp' cO cD delta i (cD'', t) cs, cnormApxBranches cO cD delta branch (cD'', t) cs)

  | Apx.Comp.If(loc, i, e1, e2) -> 
      let i' =  cnormApxExp' cO cD delta i (cD'', t) cs in 
      let e1' = cnormApxExp cO cD delta e1 (cD'', t) cs in 
      let e2' = cnormApxExp cO cD delta e2 (cD'', t) cs in 
        Apx.Comp.If(loc, i', e1', e2')


and cnormApxExp' cO cD delta i cDt cs = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.Const _c -> i
  | Apx.Comp.Apply (loc, i, e) -> 
      let i' = cnormApxExp' cO cD delta i cDt cs in 
      let e' = cnormApxExp cO cD delta e cDt cs in 
        Apx.Comp.Apply (loc, i', e')
  | Apx.Comp.CtxApp (loc, i, psi) -> 
      let i' = cnormApxExp' cO cD delta i cDt cs in 
      let psi' = cnormApxDCtx cO cD delta psi cDt cs in 
        Apx.Comp.CtxApp (loc, i', psi')

  | Apx.Comp.MApp (loc, i, (phat, m)) -> 
      let i' = cnormApxExp' cO cD delta i cDt cs in 
      let m' = cnormApxTerm cO cD delta m cDt cs in
        Apx.Comp.MApp (loc, i', (phat, m'))

  | Apx.Comp.MAnnApp (loc, i, (psi, m)) -> 
      let i' = cnormApxExp' cO cD delta i cDt cs in 
      let psi' = cnormApxDCtx cO cD delta psi cDt cs in 
      let m' = cnormApxTerm cO cD delta m cDt cs in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Apx.Comp.BoxVal (loc, psi, m) -> 
      let psi' = cnormApxDCtx cO cD delta psi cDt cs in 
      let m'   = cnormApxTerm cO cD delta m cDt cs in 
        Apx.Comp.BoxVal (loc, psi', m')

  | Apx.Comp.Boolean (loc, b) -> Apx.Comp.Boolean(loc, b)
  | Apx.Comp.Equal (loc, i1, i2) -> 
    let i1' = cnormApxExp' cO cD delta i1 cDt cs in 
    let i2' = cnormApxExp' cO cD delta i2 cDt cs in 
      Apx.Comp.Equal (loc, i1', i2')


and cnormApxBranches cO cD delta branches cDt cs = match branches with
  | [] -> []
  | b::bs -> (cnormApxBranch cO cD delta b cDt cs)::(cnormApxBranches cO cD delta bs cDt cs)

and cnormApxBranch cO cD delta b (cD'', t) cs = 
  let rec mvar_dot_apx t delta = match delta with
    | Apx.LF.Empty -> t
    | Apx.LF.Dec(delta', _ ) -> 
        mvar_dot_apx (Whnf.mvar_dot1 t) delta'

  and append delta1 delta2 = match delta2 with
    | Apx.LF.Empty -> delta1

    | Apx.LF.Dec (delta2', dec) ->
      let delta1' = append delta1 delta2' in
        Apx.LF.Dec (delta1', dec)
  
  and append_mctx cD'' delta' = match delta' with
  | Apx.LF.Empty -> cD''

  | Apx.LF.Dec (delta2', Apx.LF.MDecl (x, _, _ )) ->
      let cD1'' = append_mctx cD'' delta2' in
        Int.LF.Dec (cD1'', Int.LF.MDeclOpt x) 

  | Apx.LF.Dec (delta2', Apx.LF.PDecl (x, _, _ )) ->
      let cD1 = append_mctx cD'' delta2' in
        Int.LF.Dec (cD1, Int.LF.PDeclOpt x) 
 
  in 
    match b with
      | Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.NormalPattern (m, e), Some (a, psi))) ->
          (* |omega| = k  --> shift cs by k ERROR bp *)
          let cs' = match apxget_ctxvar psi1 with None -> cs
                                                | Some _ -> Ctxsub.cdot1 cs in
          let e' = cnormApxExp cO cD (append delta delta') e (append_mctx cD'' delta',
                                                              mvar_dot_apx t delta') cs'
          in
            Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.NormalPattern (m, e'), Some (a, psi)))
              
      | Apx.Comp.BranchBox (loc, omega, delta', (psi, Apx.Comp.NormalPattern (r, e), None)) ->
          (* |omega| = k  --> shift cs by k ERROR bp *)
          let cs' = match apxget_ctxvar psi with None -> cs
                                               | Some _ -> Ctxsub.cdot1 cs in
          let e' = cnormApxExp cO cD (append delta delta') e (append_mctx cD'' delta',
                                                              mvar_dot_apx t delta') cs'
          in
            Apx.Comp.BranchBox (loc, omega, delta', (psi, Apx.Comp.NormalPattern (r, e'), None))

      | Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.EmptyPattern, typ)) ->
          (* |omega| = k  --> shift cs by k ERROR bp *)
            Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.EmptyPattern, typ))


(* ******************************************************************* *)
(* Collect FMVars and FPVars in a given LF object                      *)

let rec collectApxTerm fMVs  m = match m with
  | Apx.LF.Lam (_loc, _x, m') ->  collectApxTerm fMVs  m' 

   (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (_loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) ->
       collectApxSub (u::fMVs)  s         

  | Apx.LF.Root (_loc, h, s) -> 
      let fMVs' = collectApxHead fMVs  h in 
        collectApxSpine fMVs'  s  

  | Apx.LF.Tuple (_loc, tuple) -> 
       collectApxTuple fMVs  tuple

and collectApxTuple fMVs tuple = match tuple with
  | Apx.LF.Last m -> collectApxTerm fMVs  m
  | Apx.LF.Cons (m, tuple) -> 
      let fMVs' = collectApxTerm fMVs  m in 
        collectApxTuple fMVs' tuple

and collectApxHead fMVs h = match h with
  | Apx.LF.FPVar (p, s) -> 
      collectApxSub (p::fMVs) s 
        
  | Apx.LF.MVar (Apx.LF.Offset _offset, s) ->
      collectApxSub fMVs s 

  | Apx.LF.PVar (Apx.LF.Offset _offset, s) -> 
      collectApxSub fMVs s 

  | Apx.LF.Proj(Apx.LF.FPVar (p, s), _k) -> 
      collectApxSub (p::fMVs) s 

  | _ -> fMVs

and collectApxSub fMVs s = match s with
  | Apx.LF.EmptySub -> fMVs
  | Apx.LF.Id       -> fMVs
  | Apx.LF.Dot (Apx.LF.Head h, s) -> 
      let fMVs' = collectApxHead fMVs h in 
        collectApxSub fMVs' s  

  | Apx.LF.Dot (Apx.LF.Obj m, s) -> 
      let fMVs' = collectApxTerm fMVs m in 
        collectApxSub fMVs' s  

and collectApxSpine fMVs s = match s with 
  | Apx.LF.Nil -> fMVs
  | Apx.LF.App (m, s) -> 
      let fMVs' = collectApxSpine fMVs s in 
        collectApxTerm fMVs' m 

and collectApxTyp fMVs a = match a with 
  | Apx.LF.Atom (_ , _ , spine) -> collectApxSpine fMVs spine 
  | Apx.LF.PiTyp ((tdecl, _ ) , a) -> 
      let fMVs' = collectApxTypDecl fMVs tdecl in 
        collectApxTyp fMVs' a 
  | Apx.LF.Sigma t_rec -> collectApxTypRec fMVs t_rec

and collectApxTypRec fMVs t_rec = match t_rec with
  | Apx.LF.SigmaLast a -> collectApxTyp fMVs a
  | Apx.LF.SigmaElem (_, a, t_rec) -> 
      let fMVs' = collectApxTyp fMVs a in 
        collectApxTypRec fMVs' t_rec

and collectApxTypDecl fMVs (Apx.LF.TypDecl (_ , a))= 
  collectApxTyp fMVs a

and collectApxDCtx fMVs c_psi = match c_psi with
  | Apx.LF.Null -> fMVs
  | Apx.LF.CtxVar _ -> fMVs
  | Apx.LF.DDec (c_psi', t_decl) ->
      let fMVs' = collectApxDCtx fMVs c_psi' in
        collectApxTypDecl fMVs' t_decl
      
and collectApxMCtx fMVs c_mctx = match c_mctx with 
  | Apx.LF.Empty -> fMVs
  | Apx.LF.Dec (c_mctx', ct_decl) -> 
      let fMVs' = collectApxMCtx fMVs c_mctx' in 
        collectApxCTypDecl fMVs' ct_decl

and collectApxCTypDecl fMVs ct_decl = match ct_decl with
  | Apx.LF.MDecl ( _, a, c_psi) -> 
      let fMVs' = collectApxDCtx fMVs c_psi in 
        collectApxTyp fMVs' a

  | Apx.LF.PDecl ( _, a, c_psi) -> 
      let fMVs' = collectApxDCtx fMVs c_psi in 
        collectApxTyp fMVs' a

let rec fmvApxTerm fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param m =   match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, fmvApxTerm fMVs cO cD d_param o_param m') 

   (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) ->
      let s' = fmvApxSub fMVs cO cD d_param o_param s in 
      if List.mem u fMVs then 
          Apx.LF.Root (loc, Apx.LF.FMVar (u, s'), Apx.LF.Nil) 
      else 
        begin try 
          let _ = dprint (fun () -> "Looking up position of " ^ R.render_name u ^ "\n") in
          let (offset, (_tP, _cPhi)) = Whnf.mctxMVarPos cD u in
            Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset (offset+k), s'), Apx.LF.Nil)     
        with Whnf.Fmvar_not_found -> (dprint (fun () -> "[fmvApxTerm] UnboundName") ; raise (Error (Some loc, UnboundName u)))
        end 

  | Apx.LF.Root (loc, h, s) -> 
      let h' = fmvApxHead fMVs cO cD d_param o_param h in 
      let s' = fmvApxSpine fMVs  cO cD d_param o_param s in 
        Apx.LF.Root (loc, h', s')

  | Apx.LF.Tuple (loc, tuple) -> 
      Apx.LF.Tuple(loc, fmvApxTuple fMVs cO cD d_param o_param tuple)

and fmvApxTuple fMVs cO cD ((l_cd1, l_delta, k) as d_param)  o_param tuple = match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (fmvApxTerm fMVs cO cD d_param  o_param m)
  | Apx.LF.Cons (m, tuple) -> 
      Apx.LF.Cons (fmvApxTerm fMVs cO cD d_param  o_param m,
                   fmvApxTuple fMVs cO cD d_param o_param tuple)

and fmvApxHead fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param h = match h with
  (* free meta-variables / parameter variables *)
  | Apx.LF.FPVar (p, s) -> 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
      if List.mem p fMVs then 
        Apx.LF.FPVar (p, s')
      else 
        let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in          
          Apx.LF.PVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.FMVar (u, s) -> 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
      if List.mem u fMVs then 
        Apx.LF.FMVar (u, s')
      else 
        let (offset, (_tA, _cPhi)) = Whnf.mctxMVarPos cD u  in          
          Apx.LF.MVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.Proj (Apx.LF.FPVar (p,s), j) -> 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
        if List.mem p fMVs then 
          Apx.LF.Proj (Apx.LF.FPVar (p, s'), j)
        else 
          let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in          
            Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset (offset + k), s'), j)
 
        
  (* bound meta-variables / parameters *)
  | Apx.LF.MVar (Apx.LF.Offset offset, s) ->
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
        if offset > (l_delta+k) then 
          Apx.LF.MVar (Apx.LF.Offset (offset+ l_cd1), s')
        else 
          Apx.LF.MVar (Apx.LF.Offset offset, s')

  | Apx.LF.PVar (Apx.LF.Offset offset, s) -> 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
        if offset > (l_delta+k) then 
          Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s')
        else
          Apx.LF.PVar (Apx.LF.Offset offset, s')

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset,s), j) -> 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
        if offset > (l_delta+k) then 
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s'), j)
        else
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, s'), j)        

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) ->  
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' -> 
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in 
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta+k) in   
      let (tM',tP',cPhi') = (Whnf.cnorm (tM, r), Whnf.cnormTyp(tP, r), Whnf.cnormDCtx (cPhi, r)) in  
        Apx.LF.MVar (Apx.LF.MInst (tM',tP',cPhi') , s') 

  | Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s) -> 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' -> 
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in 
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta + k) in 
      let h'     = begin match h with
                   | Int.LF.BVar _k -> h
                   | Int.LF.PVar (Int.LF.Offset k ,s1) -> 
                       let s1' =  Whnf.cnormSub (s1, r) in 
                         begin match LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (Int.LF.Offset k' ,s1')
                               (* other cases are impossible *)
                         end 
                   end in 
        Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s')  

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) -> 
      (* let _ = Printf.printf "fmvApx PVar MInst ?\n" in  *)
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' -> 
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in 
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta + k) in 
      let h'     = begin match h with
                   | Int.LF.BVar _k -> h
                   | Int.LF.PVar (Int.LF.Offset k ,s1) -> 
                       let s1' =  Whnf.cnormSub (s1, r) in 
                         begin match LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (Int.LF.Offset k' ,s1')
                               (* other cases are impossible *)
                         end 
                   (* | Int.LF.PVar (Int.LF.PInst ({contents = Some h1} , _cPsi, _tA, _ ), s1) -> 
                       Int.LF.PVar (h1, Whnf.cnormMSub (s1, r)) *)

                   | Int.LF.PVar (Int.LF.PInst ({contents = _ }, _cPsi, _tA, _ ) as p ,s1) -> 
                       Int.LF.PVar (p, Whnf.cnormSub (s1, r))
                   end in 
        Apx.LF.Proj (Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s'), j)  

  | _ ->  h

and fmvApxSub fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param s = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id       -> s
  | Apx.LF.Dot (Apx.LF.Head h, s) -> 
      let h' = fmvApxHead fMVs cO cD d_param o_param h in 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in 
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) -> 
      let m' = fmvApxTerm fMVs cO cD d_param o_param m in 
      let s' = fmvApxSub fMVs cO cD d_param o_param s in 
        Apx.LF.Dot (Apx.LF.Obj m', s')


and fmvApxSpine fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param s = match s with 
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) -> 
      let s' = fmvApxSpine fMVs cO cD d_param o_param s in 
      let m' = fmvApxTerm fMVs cO cD d_param o_param m in 
        Apx.LF.App (m' , s')

let rec fmvApxTyp fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param a = match a with
  | Apx.LF.Atom (loc, c, spine) -> 
      Apx.LF.Atom (loc, c, fmvApxSpine fMVs cO cD d_param o_param spine)

  | Apx.LF.PiTyp ((t_decl, dep), a) -> 
      let t_decl' = fmvApxTypDecl fMVs cO cD d_param o_param t_decl in 
      let a' = fmvApxTyp fMVs cO cD d_param o_param a in 
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = fmvApxTypRec fMVs cO cD d_param o_param typ_rec in
        Apx.LF.Sigma typ_rec'

and fmvApxTypDecl fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param t_decl = match t_decl with
  | Apx.LF.TypDecl (x, a) -> 
      Apx.LF.TypDecl(x, fmvApxTyp fMVs cO cD d_param o_param a)

and fmvApxTypRec fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param t_rec = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (fmvApxTyp fMVs cO cD d_param o_param a)
  | Apx.LF.SigmaElem (x, a, t_rec) -> 
      let a' = fmvApxTyp fMVs cO cD d_param o_param a in 
      let t_rec' = fmvApxTypRec fMVs cO cD d_param o_param t_rec in 
        Apx.LF.SigmaElem (x, a', t_rec')

let rec fmvApxDCtx fMVs cO cD d_param ((l_o1, l_omega, k') as o_param) psi = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) -> 
      if offset > (l_omega + k') then
        psi
        (* Apx.LF.CtxVar(Apx.LF.CtxOffset (offset + l_o1)) *)
      else psi

  | Apx.LF.CtxVar _ -> psi 

  | Apx.LF.DDec (psi, t_decl) -> 
      let psi' = fmvApxDCtx fMVs cO cD d_param o_param psi in 
      let t_decl' = fmvApxTypDecl fMVs cO cD d_param o_param t_decl in 
        Apx.LF.DDec (psi', t_decl')

let rec fmvApxHat o_param phat = let (l_o1, l_omega, k') = o_param in
  begin match phat with
    | (Some (Int.LF.CtxOffset offset), d) -> 
        if offset > (l_omega + k') then
          phat (* (Some (Int.LF.CtxOffset (offset + l_o1)), d) *)
        else phat
    | _ -> phat
  end


let rec fmvApxExp fMVs cO cD ((l_cd1, l_delta, k) as d_param) ((l_o1, l_omega, k') as o_param) e = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, fmvApxExp' fMVs cO cD d_param o_param i)
  | Apx.Comp.Fun (loc, f, e)    -> Apx.Comp.Fun (loc, f, fmvApxExp fMVs cO cD d_param o_param e)
  | Apx.Comp.CtxFun (loc, g, e) -> Apx.Comp.CtxFun (loc, g, fmvApxExp fMVs cO cD d_param (l_o1, l_omega,k'+1) e)
  | Apx.Comp.MLam (loc, u, e)   -> Apx.Comp.MLam (loc, u, fmvApxExp fMVs cO cD (l_cd1, l_delta, (k+1)) o_param e)
  | Apx.Comp.Pair (loc, e1, e2) -> 
      let e1' = fmvApxExp fMVs cO cD d_param o_param e1 in 
      let e2' = fmvApxExp fMVs cO cD d_param o_param e2 in 
        Apx.Comp.Pair (loc, e1', e2')
  | Apx.Comp.LetPair (loc, i, (x,y, e)) -> 
      let i' = fmvApxExp' fMVs cO cD d_param o_param i in 
      let e' = fmvApxExp  fMVs cO cD d_param o_param e in 
        Apx.Comp.LetPair (loc, i', (x,y, e')) 

  | Apx.Comp.Box(loc, phat, m) -> 
      Apx.Comp.Box (loc, fmvApxHat o_param phat, fmvApxTerm fMVs cO cD d_param o_param m)

  | Apx.Comp.SBox(loc, phat, s) -> 
      Apx.Comp.SBox (loc, fmvApxHat o_param phat, fmvApxSub fMVs cO cD d_param o_param s)

  | Apx.Comp.Case (loc, prag, i, branch) -> 
      Apx.Comp.Case (loc, prag, fmvApxExp' fMVs cO cD d_param o_param i, 
                          fmvApxBranches fMVs cO cD d_param o_param branch)
  | Apx.Comp.If (loc, i, e1, e2) -> 
      let i' = fmvApxExp' fMVs cO cD d_param o_param i in 
      let e1' = fmvApxExp  fMVs cO cD d_param o_param e1 in 
      let e2' = fmvApxExp  fMVs cO cD d_param o_param e2 in 
        Apx.Comp.If (loc, i', e1', e2')


and fmvApxExp' fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param i = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.Const _c -> i
  | Apx.Comp.Apply (loc, i, e) -> 
      let i' = fmvApxExp' fMVs cO cD d_param o_param i in 
      let e' = fmvApxExp fMVs cO cD d_param o_param e in 
        Apx.Comp.Apply (loc, i', e')
  | Apx.Comp.CtxApp (loc, i, psi) -> 
      let i' = fmvApxExp' fMVs cO cD d_param o_param i in 
      let psi' = fmvApxDCtx fMVs cO cD d_param o_param psi  in 
        Apx.Comp.CtxApp (loc, i', psi')

  | Apx.Comp.MApp (loc, i, (phat, m)) -> 
      let i' = fmvApxExp' fMVs cO cD d_param o_param i in 
      let m' = fmvApxTerm fMVs cO cD d_param o_param m in
        Apx.Comp.MApp (loc, i', ((fmvApxHat o_param phat), m'))

  | Apx.Comp.MAnnApp (loc, i, (psi, m)) -> 
      let i' = fmvApxExp' fMVs cO cD d_param o_param i in 
      let psi' = fmvApxDCtx fMVs cO cD d_param o_param psi in 
      let m' = fmvApxTerm fMVs cO cD d_param o_param m in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Apx.Comp.BoxVal (loc, psi, m) -> 
      let psi' = fmvApxDCtx fMVs cO cD d_param o_param psi in 
      let m'   = fmvApxTerm fMVs cO cD d_param o_param m in 
        Apx.Comp.BoxVal (loc, psi', m')

(*  | Apx.Comp.Ann (e, tau) -> 
      let e' = fmvApxExp e t in 
      let tau' = fmvApxCTyp tau t in 
        Apx.Comp.Ann (e', tau')
    
*)

  | Apx.Comp.Boolean (loc, b) -> Apx.Comp.Boolean (loc, b)
  | Apx.Comp.Equal (loc, i1, i2) -> 
      let i1' = fmvApxExp' fMVs cO cD d_param o_param i1 in 
      let i2' = fmvApxExp' fMVs cO cD d_param o_param i2 in 
        Apx.Comp.Equal (loc, i1', i2')


and fmvApxBranches fMVs cO cD ((l_cd1, l_delta, k) as d_param) o_param branches = match branches with
  | [] -> []
  | b::bs -> (fmvApxBranch fMVs cO cD d_param o_param b)::(fmvApxBranches fMVs cO cD d_param o_param bs)

and fmvApxBranch fMVs cO cD (l_cd1, l_delta, k) o_param b = 
   match b with
      | Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.EmptyPattern, Some (a, psi))) ->
          let fMVd  = collectApxMCtx [] delta in 
          let fMVb' = fMVd in
          let fMVb1  = collectApxDCtx fMVb' psi in
          let _fMVb  = collectApxTyp fMVb1 a in
            Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.EmptyPattern, Some (a, psi)))

      | Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.EmptyPattern, None))  ->
          let fMVd  = collectApxMCtx [] delta in 
          let fMVb' = fMVd in 
          let _fMVb  = collectApxDCtx fMVb' psi in
            Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.EmptyPattern, None))

      | Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.NormalPattern (m, e), Some (a, psi))) ->
          let fMVd  = collectApxMCtx [] delta in 
          let fMVb' = collectApxTerm fMVd m in 
          let fMVb1  = collectApxDCtx fMVb' psi in
          let fMVb  = collectApxTyp fMVb1 a in
          let l    = lengthApxMCtx delta in 
          let l'    = lengthApxMCtx omega in 
          let (l_o1, l_omega, k')  = o_param in
          let o_param' = (l_o1, l_omega, k'+l') in
          let e' = fmvApxExp (fMVs@fMVb) cO cD (l_cd1, l_delta, (k+l)) o_param' e in
            Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.NormalPattern (m, e'), Some (a, psi)))
              
      | Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.NormalPattern (r, e), None))  ->
          let fMVd  = collectApxMCtx [] delta in 
          let fMVb' = collectApxTerm fMVd r in 
          let fMVb  = collectApxDCtx fMVb' psi in
          let l    = lengthApxMCtx delta in 
          let l'    = lengthApxMCtx omega in 
          let (l_o1, l_omega, k')  = o_param in
          let o_param' = (l_o1, l_omega, k'+l') in
          let e' = fmvApxExp (fMVs@fMVb) cO cD (l_cd1, l_delta, (k+l)) o_param' e in
            Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.NormalPattern (r, e'), None))


              
(* ******************************************************************* *)
(* Elaboration of computations                                         *)
(* Given a type-level constant a of type K , it will generate the most general
 * type a U1 ... Un 
 *)
let mgTyp cD cPsi a kK =
  let (flat_cPsi, conv_list) = flattenDCtx cPsi in  
  let s_proj   = gen_conv_sub conv_list in

  let rec genSpine sK = match sK with 
    | (Int.LF.Typ, _s) ->
        Int.LF.Nil

    | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA1), _ ), kK), s) ->
        let tA1' = strans_typ (tA1, s) conv_list in
        let u  = Whnf.newMMVar (cD, flat_cPsi , tA1') in
        let h  = Int.LF.MMVar (u, (Whnf.m_id, s_proj)) in 
        let tR = Int.LF.Root (None, h, Int.LF.Nil) in  (* -bp needs to be eta-expanded *)
        let _ = dprint (fun () -> "Generated meta^2-variable " ^ 
                          P.normalToString Int.LF.Empty cD cPsi (tR, LF.id)) in 
        let _ = dprint (fun () -> "of type : " ^ P.dctxToString Int.LF.Empty cD flat_cPsi ^ 
                          " |- " ^ P.typToString Int.LF.Empty cD flat_cPsi (tA1',LF.id)) in 
        let _ = dprint (fun () -> "orig type : " ^ P.dctxToString Int.LF.Empty cD cPsi ^ 
                          " |- " ^ P.typToString Int.LF.Empty cD cPsi (tA1,s)) in 
        let tS = genSpine (kK, Int.LF.Dot (Int.LF.Head h, s)) in 
        (* let tS = genSpine (kK, Int.LF.Dot (Int.LF.Obj tR , s)) in  (* -bp would not work if h is functional type *) *)
          Int.LF.App (tR, tS)

  in
    Int.LF.Atom (None, a, genSpine (kK, LF.id))

let rec genMApp loc cO cD (i, tau_t) = genMAppW loc cO cD (i, Whnf.cwhnfCTyp tau_t)

and genMAppW loc cO cD (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
      let psihat  = Context.dctxToHat cPsi in
      let cPsi' = C.cnormDCtx (cPsi, theta) in 
      let tA'   = C.cnormTyp (tA, theta) in 

      let tM'   = Whnf.etaExpandMMV (Some loc) cD  cPsi' (tA', LF.id) LF.id in
        let _   = dprint (fun () -> "[genMApp] Generated meta^2-variable " ^ 
                          P.normalToString cO cD cPsi (tM', LF.id)) in 
        let _   = dprint (fun () -> "          of type : " ^ 
                          P.dctxToString cO cD cPsi' ^ " |- " ^ 
                          P.typToString cO cD cPsi' (tA',LF.id)) in 
        genMApp loc cO cD ((Int.Comp.MApp (Some loc, i, (psihat, Int.Comp.NormObj tM'))), 
                        (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)))

  | (Int.Comp.TypCtxPi ((psi_name, schema_cid, Int.Comp.Implicit), tau), theta) -> 
      let tau'   = Whnf.cnormCTyp (tau, theta) in 
      let ctxVar = Int.LF.CtxVar (Int.LF.CInst (ref None, schema_cid, cO, cD)) in
      let tau''  = Ctxsub.csub_ctyp cD ctxVar 1 tau' in 
        genMApp loc cO cD  ((Int.Comp.CtxApp (Some loc, i, ctxVar)), (tau'', C.m_id))

  | _ -> (i, tau_t)

let rec elCompTyp cO cD tau = match tau with
  | Apx.Comp.TypBox (loc, a, psi) ->
      let cPsi = elDCtx PiboxRecon cO cD psi in
      let tA   = elTyp PiboxRecon cO cD cPsi a in
        Int.Comp.TypBox (Some loc, tA, cPsi)

  | Apx.Comp.TypSub (loc, psi, phi) -> 
      let cPsi = elDCtx PiboxRecon cO cD psi in
      let cPhi = elDCtx PiboxRecon cO cD phi in
        Int.Comp.TypSub (Some loc, cPsi, cPhi)

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCross (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypCross (tau1', tau2')

  | Apx.Comp.TypCtxPi ((x, schema_cid, apx_dep) , tau) ->
      let tau' = elCompTyp (Int.LF.Dec (cO, Int.LF.CDecl (x, schema_cid))) cD tau in
      let dep = match apx_dep with Apx.Comp.Explicit -> Int.Comp.Explicit | Apx.Comp.Implicit -> Int.Comp.Implicit in
        Int.Comp.TypCtxPi ((x, schema_cid, dep), tau')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl PiboxRecon cO cD cdecl  in
      let tau'   = elCompTyp cO (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox ((cdecl', Int.Comp.Explicit), tau')

  | Apx.Comp.TypBool -> Int.Comp.TypBool 

let rec elExp cO cD cG e theta_tau = elExpW cO cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cO cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Syn (loc, i), (tau,t)) ->
      let _ = dprint (fun () -> "[elExp] Syn") in 
      let (i1,tau1) = elExp' cO cD cG i in 
      let _ = dprint (fun () -> "[elExp] Syn done: " ^ 
                        P.compTypToString cO cD (Whnf.cnormCTyp tau1))  in 
      let (i', tau_t') = genMApp loc cO cD (i1, tau1) in 
        begin try
          dprint (fun () -> "Unifying computation-level types\n") ; 
          Unify.unifyCompTyp cD (tau, t) (tau_t');
          dprint (fun () -> "Unified computation-level types\n") ; 
          Int.Comp.Syn (Some loc, i')
        with _ -> 
          raise (Error (Some loc, CompSynMismatch (cO, cD, (tau,t), tau_t')))
        end 

  | (Apx.Comp.Fun (loc, x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
      let e' = elExp cO cD (Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo (tau1, theta)))) e (tau2, theta) in
        Int.Comp.Fun (Some loc, x, e')

  | (Apx.Comp.CtxFun (loc, psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid, Int.Comp.Explicit), tau), theta)) ->
      let e' = elExp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD cG e (tau, theta) in
        Int.Comp.CtxFun (Some loc, psi_name, e')

  | (Apx.Comp.MLam (loc, u, e) , (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let cD' = Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))) in 
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in 
      let e' = elExp cO cD' cG' e (tau, C.mvar_dot1 theta) in 
        Int.Comp.MLam (Some loc, u, e') 

  | (Apx.Comp.MLam (loc, p, e) , (Int.Comp.TypPiBox((Int.LF.PDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let cD' = Int.LF.Dec (cD, Int.LF.PDecl (p, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))) in 
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in 
      let e' = elExp cO cD' cG' e (tau, C.mvar_dot1 theta) in 
        Int.Comp.MLam (Some loc, p, e') 


  | (Apx.Comp.MLam (loc, s, e) , (Int.Comp.TypPiBox((Int.LF.SDecl(_u, cPhi, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let cD' = Int.LF.Dec (cD, Int.LF.SDecl (s, C.cnormDCtx (cPhi, theta), C.cnormDCtx (cPsi, theta))) in 
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in 
      let e' = elExp cO cD' cG' e (tau, C.mvar_dot1 theta) in 
        Int.Comp.MLam (Some loc, s, e') 



  | (e, (Int.Comp.TypCtxPi((psi_name, schema_cid, Int.Comp.Implicit), tau), theta))  ->
      let e' = elExp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD cG e (tau, theta) in
        Int.Comp.CtxFun (None, psi_name, e')

  | (e, (Int.Comp.TypPiBox((Int.LF.MDecl(u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      (* let u' = Id.mk_name (Id.MVarName (Typ.gen_mvar_name tA)) in *)
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in 
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta)))) 
                     cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (None,u , e')

  | (e, (Int.Comp.TypPiBox((Int.LF.PDecl(_u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      let u' = Id.mk_name (Id.PVarName None) in 
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in 
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.PDecl (u', C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
                     cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (None,u' , e')

  | (Apx.Comp.Pair(loc, e1, e2), (Int.Comp.TypCross (tau1, tau2), theta)) ->
      let e1' = elExp cO cD cG e1 (tau1, theta) in
      let e2' = elExp cO cD cG e2 (tau2, theta) in
        Int.Comp.Pair (Some loc, e1', e2')

  | (Apx.Comp.LetPair (loc, i, (x, y, e)), (tau, theta)) ->
      let (i', tau_theta') = elExp' cO cD cG i in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypCross (tau1, tau2), t) ->
              let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Int.Comp.TypClo (tau1, t))) in
              let cG2 = Int.LF.Dec (cG1, Int.Comp.CTypDecl (y, Int.Comp.TypClo (tau2, t))) in
              let e'  =  elExp cO cD cG2 e (tau, theta) in
                Int.Comp.LetPair (Some loc, i', (x, y, e'))

          | _ -> raise (Error (Some loc, CompMismatch (cO, cD, cG, i', Cross, tau_theta'))) 
              (* TODO postpone to reconstruction *)
        end


  | (Apx.Comp.Box (loc, psihat, tM), ((Int.Comp.TypBox (_loc, tA, cPsi), theta) as tau_theta)) ->
   (* if psihat = Context.dctxToHat cPsi then *)
      let cPsi' = C.cnormDCtx (cPsi, theta) in 
      if unify_phat psihat (Context.dctxToHat cPsi') then
        let tM' = elTerm PiboxRecon cO cD cPsi' tM (C.cnormTyp (tA, theta), LF.id) in
         
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in  
        let _        = Unify.resetGlobalCnstrs () in 
        let e =           Int.Comp.Box (Some loc, psihat, tM') in
        let _   = (dprint (fun () -> "[elExp] Box : " ^ P.expChkToString cO cD cG e ) ; 
                   dprint (fun () -> "[elExp] Box checked against "  ^ 
                             P.typToString cO cD cPsi' (C.cnormTyp (tA, theta), LF.id) ^ "[" ^ 
                             P.dctxToString cO cD cPsi' ^ "]")) in

          Int.Comp.Box (Some loc, psihat, tM')
      else 
        (* raise (Error (Some loc, CompBoxCtxMismatch (cO, cD, cPsi, (psihat, tM')))) *)
        (let (_ , k) = psihat in 
           dprint (fun () -> "cPsi = " ^ P.dctxToString cO cD cPsi  ^ "\n psihat  = " ^ string_of_int k ^ "\n") ; 
           raise (Error (Some loc, CompBoxMismatch (cO, cD, cG, tau_theta))) )


  | (Apx.Comp.SBox (loc, psihat, sigma), ((Int.Comp.TypSub (_loc, cPhi, cPsi), theta))) ->
   (* if psihat = Context.dctxToHat cPsi then *)
      if unify_phat psihat (Context.dctxToHat cPsi) then
        let sigma' = elSub loc PiboxRecon cO cD (C.cnormDCtx (cPsi, theta)) sigma (C.cnormDCtx (cPhi, theta)) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
        let _        = Unify.resetGlobalCnstrs () in 
          Int.Comp.SBox (Some loc, psihat, sigma')
      else 
        (* raise (Error (Some loc, CompBoxCtxMismatch (cO, cD, cPsi, (psihat, tM')))) *)
        (let (_ , k) = psihat in 
           dprint (fun () -> "cPsi = " ^ P.dctxToString cO cD (C.cnormDCtx (cPsi, theta))  ^ "\n psihat  = " ^ string_of_int k ^ "\n") ; 
           raise (Error (Some loc, CompSBoxMismatch (cO, cD, cG, (C.cnormDCtx (cPhi, theta)), (C.cnormDCtx (cPsi, theta)))) ))
 

  | (Apx.Comp.Case (loc, prag, i, branches), tau_theta) ->
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match (i', C.cwhnfCTyp tau_theta') with
          | (Int.Comp.Ann (Int.Comp.Box (_ , phat,tR), _ ), 
             (Int.Comp.TypBox (_, tP, cPsi) as tau', t (* m_id *))) ->
              let _ = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
              let _ = Unify.resetGlobalCnstrs () in 

              (* let _ = recTerm PiboxRecon cO cD cPsi (tR, LF.id) (tP, LF.id) in *)
              (if Whnf.closed (tR, LF.id)  then 
                 (* && Whnf.closedTyp (tP, LF.id) && Whnf.closedDCtx cPsi && Whnf.closedGCtx cG ? *)
                let branches' = List.map 
                                (function b -> 
                                   let _ = dprint (fun () -> "[elBranch - IndexObj] in context cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n") in
                                   let b = elBranch (IndexObj(phat, tR))
                                                   cO cD cG b (tP, cPsi) tau_theta in 
                                     Gensym.MVarData.reset () ; b)
                                branches in
                  Int.Comp.Case (Some loc, prag, i', branches')
              else 
                raise (Error (Some loc, ValueRestriction (cO, cD, cG, i', (tau',t))))
              )

          | (i, (Int.Comp.TypBox (_, tP, cPsi), _mid)) -> 

              (if Whnf.closedTyp (tP, LF.id) && Whnf.closedDCtx cPsi && Whnf.closedGCtx cG then 
                 let _      = dprint (fun () -> "[elExp]" 
                             ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                             ^ "Expected Pattern has type :" ^
                                        P.typToString cO cD cPsi (tP, LF.id)           
                             ^  "\n Context of expected pattern type : "
                             ^  P.dctxToString cO cD cPsi 
                             ^ "\n") in

                let internal_branches = List.map 
                                        (function b -> 
                                           let _ = dprint (fun () -> "[elBranch - DataObj] in context cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n") in
                                           let b = elBranch DataObj 
                                                         cO cD cG b (tP, cPsi) tau_theta
                                           in  Gensym.MVarData.reset () ; b) 
                                        branches in
                let internal_case_exp = Int.Comp.Case (Some loc, prag, i, internal_branches) in
(*                  Coverage.covers cO cD cG internal_branches (tP, cPsi);         moved to check.ml  -jd 2010-04-05 *)
                  internal_case_exp
                
              else 
                raise (Error (Some loc, CompScrutineeTyp (cO, cD, cG, i', (tP, LF.id), cPsi)))
              )

          | _ ->  raise (Error (Some loc, CompMismatch (cO, cD, cG, i', Box, tau_theta')))
        end
  | (Apx.Comp.If (loc, i, e1, e2), tau_theta) -> 
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match C.cwhnfCTyp tau_theta' with 
          | (Int.Comp.TypBool , _ ) -> 
              let e1' = elExp cO cD cG e1 tau_theta in 
              let e2' = elExp cO cD cG e2 tau_theta in 
                Int.Comp.If (Some loc, i', e1', e2')
          | _  -> raise (Error (Some loc, CompIfMismatch (cO, cD, cG, tau_theta')))
        end

  (* TODO postpone to reconstruction *)
  (* Error handling cases *)
  | (Apx.Comp.Fun (loc, _x, _e),  tau_theta ) -> raise (Error (Some loc, CompFunMismatch (cO, cD, cG, tau_theta)))
  | (Apx.Comp.CtxFun (loc, _psi_name, _e), tau_theta) -> raise (Error (Some loc, CompCtxFunMismatch (cO, cD, cG, tau_theta)))
  | (Apx.Comp.MLam (loc, _u, _e), tau_theta) -> raise (Error (Some loc, CompMLamMismatch (cO, cD, cG, tau_theta)))
  | (Apx.Comp.Pair(loc, _ , _ ), tau_theta) ->  raise (Error (Some loc, CompPairMismatch (cO, cD, cG, tau_theta)))
  | (Apx.Comp.Box (loc, _, _ ) , tau_theta) ->  raise (Error (Some loc, CompBoxMismatch (cO, cD, cG, tau_theta)))



and elExp' cO cD cG i = match i with
  | Apx.Comp.Var offset ->
      (Int.Comp.Var offset, (lookup cG offset, C.m_id))

  | Apx.Comp.Const prog ->
     (Int.Comp.Const prog, ((Comp.get prog).Comp.typ, C.m_id))
       

  | Apx.Comp.Apply (loc, i, e) ->
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypArr (tau2, tau), theta) ->
              let _ = dprint (fun () -> "[elExp'] Inferred type for i' = " ^ P.expSynToString cO cD cG i' 
                                ^ "\n      " ^ 
                                P.compTypToString cO cD (Whnf.cnormCTyp (Int.Comp.TypArr (tau2,tau), theta))
                                ^ "\n") in
              let _ = dprint (fun () -> "[elExp'] Check argument has type " ^ P.compTypToString cO cD (Whnf.cnormCTyp (tau2,theta))) in
              let e' = elExp cO cD cG e (tau2, theta) in
                (Int.Comp.Apply (Some loc, i', e'), (tau, theta))

          | _ -> 
              raise (Error (Some loc, CompMismatch (cO, cD, cG, i', Arrow, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.CtxApp (loc, i, cPsi) ->
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | ((Int.Comp.TypCtxPi ((_psi, _sW, _explicit ), tau), theta) as tt)->
              let cPsi'  = elDCtx PiboxRecon cO cD cPsi in
              let _ = (dprint (fun () -> "[elExp'] CtxApp : tau = " ^ 
                                 P.compTypToString cO cD (Whnf.cnormCTyp tt) ); 
                       dprint (fun () -> "[elExp'] cPsi' = " ^ P.dctxToString cO cD cPsi' )) in 
 
              let theta' = Ctxsub.csub_msub cPsi' 1 theta in
              let tau'   = Ctxsub.csub_ctyp cD cPsi' 1 tau in               

              let _ = dprint (fun () -> "[elExp'] CtxApp : [cPsi/psi]tau' = " ^ 
                                 P.compTypToString cO cD (Whnf.cnormCTyp (tau',theta')) ) in 

                (Int.Comp.CtxApp (Some loc, i', cPsi'), (tau', theta'))

          | _ -> 
              raise (Error (Some loc, CompMismatch (cO, cD, cG, i', CtxPi, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.MApp (loc, i, (psihat, m)) ->
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
              let cPsi' = C.cnormDCtx (cPsi, theta) in 
              let psihat' = Context.dctxToHat cPsi'  in
             begin try 
              let tM'    = elTerm PiboxRecon cO cD cPsi' m (C.cnormTyp (tA, theta), LF.id) in
              let theta' = Int.LF.MDot (Int.LF.MObj (psihat', tM'), theta) in
                (Int.Comp.MApp (Some loc, i', (psihat', Int.Comp.NormObj tM')), (tau, theta'))
             with Violation msg -> 
               dprint (fun () -> "[elTerm] Violation: " ^ msg);
               raise (Error (Some loc, CompTypAnn ))
             end 

            | (Int.Comp.TypPiBox ((Int.LF.PDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
              (* m = PVar or BVar of Proj *) 
              (* tM' really is a head ... if we would allow  Root (_, PVar _ , Nil) then this wouldn't be normal. *)
               begin try 
                 begin match m with 
                   | Apx.LF.Root (_, h, Apx.LF.Nil) -> 
                       let _ = dprint (fun () -> "[elExp'] Mapp case : PDecl ") in 
                       let cPsi' = C.cnormDCtx (cPsi, theta) in 
                       let (h', sB) = elHead loc PiboxRecon cO cD cPsi' h  in
                       let theta' = Int.LF.MDot (Int.LF.PObj (psihat, h'), theta) in
                       let sA' = (C.cnormTyp (tA, theta), LF.id) in 
                         begin try 
                           (Unify.unifyTyp cD cPsi' sB  sA' ;
                            dprint (fun () -> "[elExp'] unification of PDecl with inferred type done");
                          (Int.Comp.MApp (Some loc, i', (psihat, Int.Comp.NeutObj h')), (tau, theta')))
                         with Unify.Unify msg ->
                           (Printf.printf "%s\n" msg;
                            raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi', sA', sB))))
                         end 
                   | _ -> 
                       (dprint (fun () -> "[elTerm] Violation: Not a head");
                        raise (Error (Some loc, CompTypAnn)))
                 end  
               with Violation msg -> 
                 dprint (fun () -> "[elTerm] Violation: " ^ msg);
                 raise (Error (Some loc, CompTypAnn))
               end 


          | _ ->
              raise (Error (Some loc, CompMismatch (cO, cD, cG, i', PiBox, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end



  | Apx.Comp.MAnnApp (loc, i, (psi, m)) ->
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
              let cPsi    = C.cnormDCtx (cPsi, theta) in
             begin try 
               let cPsi' = elDCtx PiboxRecon cO cD psi in
               let _     = Unify.unifyDCtx cO cD cPsi cPsi' in 
               let psihat' = Context.dctxToHat cPsi'  in
              let tM'    = elTerm PiboxRecon cO cD cPsi' m (C.cnormTyp (tA, theta), LF.id) in
              let theta' = Int.LF.MDot (Int.LF.MObj (psihat', tM'), theta) in
                (Int.Comp.MApp (Some loc, i', (psihat', Int.Comp.NormObj tM')), (tau, theta'))
             with Violation msg -> 
               dprint (fun () -> "[elTerm] Violation: " ^ msg);
               raise (Error (Some loc, CompTypAnn ))
             end 
          | _ ->
              raise (Error (Some loc, CompMismatch (cO, cD, cG, i', PiBox, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end



  | Apx.Comp.BoxVal (loc, psi, r) ->
      let _ = dprint (fun () -> "[elExp'] BoxVal dctx ") in 
      let cPsi     = elDCtx PiboxRecon cO cD psi in
      let _ = dprint (fun () -> "[elExp'] BoxVal dctx done: " ^ P.dctxToString cO cD cPsi ) in 
      let (tR, sP) = elClosedTerm' PiboxRecon cO cD cPsi r in
      let _ = dprint (fun () -> "[elExp'] BoxVal tR done ") in 
      (* let sP    = synTerm PiboxRecon cO cD cPsi (tR, LF.id) in *)
      let phat     = Context.dctxToHat cPsi in
      let tau      = Int.Comp.TypBox (None, Int.LF.TClo sP, cPsi) in
        (Int.Comp.Ann (Int.Comp.Box (Some loc, phat, tR), tau), (tau, C.m_id))

  | Apx.Comp.Ann (e, tau) ->
      let tau' = elCompTyp cO cD tau in
      let e'   = elExp cO cD cG e (tau', C.m_id) in
        (Int.Comp.Ann (e', tau'), (tau', C.m_id))


  | Apx.Comp.Equal (loc, i1, i2) -> 
      let _ = dprint (fun () -> "[elExp'] Equal ... ") in 
      let (i1', ttau1) = genMApp loc cO cD (elExp' cO cD cG i1) in 
      let (i2', ttau2) = genMApp loc cO cD (elExp' cO cD cG i2) in 
       if Whnf.convCTyp ttau1 ttau2 then  
         (Int.Comp.Equal (Some loc, i1', i2'), (Int.Comp.TypBool , C.m_id))
       else 
         raise (Error(Some loc, CompEqMismatch (cO, cD, ttau1, ttau2 )))


  | Apx.Comp.Boolean (_ , b)  -> (Int.Comp.Boolean b, (Int.Comp.TypBool, C.m_id))

and recPattern cO cD cPsi omega delta psi m tPopt = 
  let cO1     = elCCtx omega in 
  let cD'     = elMCtx  PiboxRecon cO1 delta in
  let cPsi'   = elDCtx  PiboxRecon cO1 cD' psi in
  let l = Context.length cD' in 

  let _ = dprint (fun () -> "[recPattern] cPsi' = " ^ P.dctxToString cO1 cD' cPsi' ) in
  let _ = dprint (fun () -> "[recPattern] cPsi = " ^ P.dctxToString cO cD cPsi ) in

  let cvar1Opt = Context.ctxVar cPsi' in 
  let (cO_ext,k) = begin match cvar1Opt with 
                   | None -> (cO, 0)
                   | Some (Int.LF.CtxOffset _ ) -> 
                       begin match cO1 with
                         | Int.LF.Dec(Int.LF.Empty, cdecl) -> (Int.LF.Dec(cO, cdecl) , 1)
 
                         | _ -> (Int.LF.Dec(cO, Int.LF.CDeclOpt (Id.mk_name (Id.NoName))), 1)
                             (* can this case ever happen? Thu Sep  2 12:57:46 2010 -bp *)
                       end
                   | Some (Int.LF.CtxName psi_name ) -> (Int.LF.Dec(cO, Int.LF.CDeclOpt psi_name) , 1)
                  end in

  let cs     = Ctxsub.id_csub cO_ext in 
  let cPsi0  = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx (cPsi,Int.LF.MShift l), Int.LF.CShift k) in 
  let _ = dprint (fun () -> "unifyDCtx : cPsi0 = " ^ P.dctxToString cO_ext Int.LF.Empty cPsi0 ^ 
                    " \n   cPsi' = " ^ P.dctxToString cO_ext Int.LF.Empty cPsi' ^ "\n") in 
  let (cO', cs) = unifyDCtx cPsi0 cPsi' (cs, cO_ext) in 
  let _ = dprint (fun () -> "domain : cO_ext = " ^ P.octxToString cO_ext) in 
  (* let _ = dprint (fun () -> "cs = " ^ P.csubToString cO' cs ) in  *)
  let _ = dprint (fun () -> "range : cO'= " ^ P.octxToString cO') in 

  let l_cO1  = Context.length cO1 in 
  let l_cO'  = Context.length cO' in 
  let cD1_joint = Context.append cD cD' in                   (*         cD'  = cD, cD1     *)

  let (cs', cs1) = begin match (cvar1Opt, cs) with 
              | (None, _ ) -> (cs , Int.LF.CShift 0)
              | (Some _ , Int.LF.CDot (c_psi , cs') ) -> (cs'  , Int.LF.CDot(c_psi, Int.LF.CShift l_cO'))
            end  in

  let _ = dprint (fun () -> "cs' = " ^ P.csubToString cO' cD1_joint cs' ) in 
  let _ = dprint (fun () -> "cs1 = " ^ P.csubToString cO' cD1_joint cs1 ) in 

  let cPsi'  = Ctxsub.ctxnorm_dctx (cPsi', cs1) in 
  let cD'    = Ctxsub.ctxnorm_mctx (cD', cs1) in 

  let _ = (dprint (fun () -> "[recPattern] cO'= " ^ P.octxToString cO');
           dprint (fun () -> "[recPattern] " ^ P.mctxToString cO' cD' ^ " [ " ^ P.dctxToString cO' cD' cPsi' ^ "]")) in


  let tP'     = begin match tPopt with 
                  | FullTyp  a    -> 
                      let tP' = elTyp PiboxRecon cO' cD' cPsi' a  in 
                        (* recTyp PiboxRecon cO cD' cPsi' (tP', LF.id) ;*) tP'
                  | PartialTyp a  -> 
                      let _ = dprint (fun () -> "[mgTyp] Generate mg type in context " ^ 
                                        P.dctxToString cO' cD' cPsi' ) in
                      mgTyp cD' cPsi' a (Typ.get a).Typ.kind   
                end in

  let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of type  " ^ 
                               P.typToString cO cD' cPsi' (tP', LF.id)) in
  let tR = elTerm' PiboxRecon cO' cD' cPsi' m (tP', LF.id) in    

  let _  = solve_fcvarCnstr cO' cD' !fcvar_cnstr in 
  let _  = reset_fcvarCnstr () in 
  let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
  let _        = Unify.resetGlobalCnstrs () in 

  let _   = dprint (fun () -> "recPattern: Elaborated pattern...\n" ^ P.mctxToString cO' cD' ^ "  ;   " ^
                      P.dctxToString cO' cD' cPsi' ^ "\n   |-\n    "  ^ P.normalToString cO' cD' cPsi' (tR, LF.id) ^ 
                      "\n has type " ^ P.typToString  cO' cD' cPsi' (tP', LF.id) ^ "\n") in
 
  let phat = Context.dctxToHat cPsi' in 

  let (cD1', cPsi1', (_phat, tR1'), tP1', cs, cs') =  Abstract.abstrPattern cD' cPsi' (phat, tR) tP' (cs, cs') in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.octxToString cO' ^ " ; \n" ^
                          P.mctxToString cO' cD1' ^ "  ;   " ^ P.dctxToString cO' cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.normalToString cO' cD1' cPsi1' (tR1', LF.id) ^ "\n has type \n cO' = " ^
                          P.octxToString cO' ^ " |- \n" ^
                          P.typToString cO' cD1' cPsi1'  (tP1', LF.id) ^ "\n cs = " ^ 
                          P.csubToString cO' cD1_joint cs ^ " : " ^ P.octxToString cO_ext ^ 
                          "\n cs' = " ^ P.csubToString cO' cD1_joint cs' ^ " : " ^ P.octxToString cO ^  "\n") in   
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in  
    ((n,k), (l_cO', l_cO1), cO', cD1', cPsi1', Some tR1', tP1', cs, cs')


and recEmptyPattern cO cD cPsi omega delta psi tPopt = 
  let cO1     = elCCtx omega in 
  let cD'     = elMCtx  PiboxRecon cO1 delta in
  let cPsi'   = elDCtx  PiboxRecon cO1 cD' psi in
  let l = Context.length cD' in 

  let _ = dprint (fun () -> "[recPattern] cPsi' = " ^ P.dctxToString cO1 cD' cPsi' ) in

  let cvar1Opt = Context.ctxVar cPsi' in 
  let cO_ext = begin match cvar1Opt with 
                   | None -> cO
                   | Some (Int.LF.CtxOffset _ ) -> 
                       begin match cO1 with
                         | Int.LF.Dec(Int.LF.Empty, cdecl) -> Int.LF.Dec(cO, cdecl)
                         | _ -> Int.LF.Dec(cO, Int.LF.CDeclOpt (Id.mk_name (Id.NoName)))
                       end
                   | Some (Int.LF.CtxName psi_name ) -> Int.LF.Dec(cO, Int.LF.CDeclOpt psi_name)
                  end in
  let cs     = Ctxsub.id_csub cO_ext in 
  let cPsi0  = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx (cPsi,Int.LF.MShift l), Int.LF.CShift 1) in 
  let _ = dprint (fun () -> "unifyDCtx : cPsi0 = " ^ P.dctxToString cO_ext Int.LF.Empty cPsi0 ^ 
                    " \n   cPsi' = " ^ P.dctxToString cO_ext Int.LF.Empty cPsi' ^ "\n") in 
  let (cO', cs) = unifyDCtx cPsi0 cPsi' (cs, cO_ext) in 
  let _ = dprint (fun () -> "domain : cO_ext = " ^ P.octxToString cO_ext) in 
  (* let _ = dprint (fun () -> "cs = " ^ P.csubToString cO' cs ) in  *)
  let _ = dprint (fun () -> "range : cO'= " ^ P.octxToString cO') in 

  let l_cO1  = Context.length cO1 in 
  let l_cO'  = Context.length cO' in 
  let cD1_joint = Context.append cD cD' in                   (*         cD'  = cD, cD1     *)

  let (cs', cs1) = begin match (cvar1Opt, cs) with 
              | (None, _ ) -> (cs , Int.LF.CShift 0)
              | (Some _ , Int.LF.CDot (c_psi , cs') ) -> (cs'  , Int.LF.CDot(c_psi, Int.LF.CShift l_cO'))
            end  in

  let _ = dprint (fun () -> "cs' = " ^ P.csubToString cO' cD1_joint cs' ) in 
  let _ = dprint (fun () -> "cs1 = " ^ P.csubToString cO' cD1_joint cs1 ) in 

  let cPsi'  = Ctxsub.ctxnorm_dctx (cPsi', cs1) in 
  let cD'    = Ctxsub.ctxnorm_mctx (cD', cs1) in 

  let _ = (dprint (fun () -> "[recPattern] cO'= " ^ P.octxToString cO');
           dprint (fun () -> "[recPattern] " ^ P.mctxToString cO' cD' ^ " [ " ^ P.dctxToString cO' cD' cPsi' ^ "]")) in


  let tP'     = begin match tPopt with 
                  | FullTyp  a    -> 
                      let tP' = elTyp PiboxRecon cO' cD' cPsi' a  in 
                        (* recTyp PiboxRecon cO cD' cPsi' (tP', LF.id) ;*) tP'
                  | PartialTyp a  -> 
                      let _ = dprint (fun () -> "[mgTyp] Generate mg type in context " ^ 
                                        P.dctxToString cO' cD' cPsi' ) in
                      mgTyp cD' cPsi' a (Typ.get a).Typ.kind   
                end in

  let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of type  " ^ 
                               P.typToString cO cD' cPsi' (tP', LF.id)) in

  let _  = solve_fcvarCnstr cO' cD' !fcvar_cnstr in 
  let _  = reset_fcvarCnstr () in 
  let _  = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
  let _  = Unify.resetGlobalCnstrs () in 

  let (cD1', cPsi1', tP1', cs, cs') =  (cD', cPsi', tP', cs, cs') in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.octxToString cO' ^ " ; \n" ^
                          P.mctxToString cO' cD1' ^ "  ;   " ^ P.dctxToString cO' cD1' cPsi1' ^ "\n   |-\n    "  ^
                          "\n cs = " ^ 
                          P.csubToString cO' cD1_joint cs ^ " : " ^ P.octxToString cO_ext ^ 
                          "\n cs' = " ^ P.csubToString cO' cD1_joint cs' ^ " : " ^ P.octxToString cO ^  "\n") in   
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in  
    ((n,k), (l_cO', l_cO1), cO', cD1', cPsi1', None, tP1', cs, cs')

and synRefine loc cO' caseT (cD, cD1) pattern1 (cPsi, tP) (cPsi1, tP1) =
  begin try 
    let cD'    = Context.append cD cD1 in                   (*         cD'  = cD, cD1     *)
    let _      = dprint (fun () -> "[synRefine] cD' = " ^ P.mctxToString cO' cD') in 
    let t      = mctxToMSub cD'  in                         (*         .  |- t   <= cD'   *) 
    let _      = dprint (fun () -> "[synRefine] mctxToMSub .  |- t <= cD' " ^ 
                             P.msubToString cO'  Int.LF.Empty (Whnf.cnormMSub t)) in 
    let n      = Context.length cD1 in 
    let m      = Context.length cD in 
    
    let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
      (* cD, cD1 |- t1 <= cD1 *)
    let mt1    = Whnf.mcomp t1 t in                          (*         .  |- mt1 <= cD1   *)
    
    let cPsi'  = Whnf.cnormDCtx (cPsi, t) in                 (*         .  |- cPsi' ctx    *)
    
    let _  = begin match (caseT, pattern1) with
               | (_, None) -> ()
               | (IndexObj (_phat, tR'), Some tR1) -> 
                   begin try 
                     (dprint (fun () -> "Pattern matching on index object...");
                      Unify.unify Int.LF.Empty cPsi' (C.cnorm (tR',  t),  LF.id) 
                                                     (C.cnorm (tR1, mt1), LF.id))
                   with Unify.Unify msg -> 
                     (dprint (fun () -> "Unify ERROR: " ^ msg);
                      raise (Violation "Pattern matching on index argument failed"))
                   end
               | (DataObj, _) -> ()
             end
    in
    
    let cPsi'  = Whnf.cnormDCtx (cPsi, t) (* t *) in        (* cO' ;     .  |- cPsi' ctx    *)
    let cPsi1' = Whnf.cnormDCtx (cPsi1, mt1) in             (* cO' ;     .  |- cPsi1 ctx    *)
    let tP'    = Whnf.cnormTyp (tP, t) (* t *) in           (* cO' ; . ; cPsi'  |- tP'  <= type *) 
    let tP1'   = Whnf.cnormTyp (tP1, mt1) in                (* cO' ; . ; cPsi1' |- tP1' <= type *)
        
      (* Since |cO1| = 1, we have  cO, c01 |- cPsi'^1 ctx    *)

    let _  = begin try 
          Unify.unifyDCtx cO' (Int.LF.Empty) cPsi' cPsi1' ;
          Unify.unifyTyp  cO' cPsi' (tP', LF.id) (tP1', LF.id); 
          dprint (fun () -> "Unify successful: \n" ^  "  Inferred pattern type: "
                    ^  P.dctxToString cO' Int.LF.Empty cPsi1' ^ "    |-    "
                    ^ P.typToString cO' Int.LF.Empty cPsi1' (tP1', LF.id)
                    ^ "\n  Expected pattern type: "
                    ^ P.dctxToString cO' Int.LF.Empty  cPsi1' ^ "    |-    "
                    ^ P.typToString cO' Int.LF.Empty cPsi1' (tP', LF.id))           
        with Unify.Unify msg ->
           (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n" ^  "  Inferred pattern type: "
                   ^  P.dctxToString cO' Int.LF.Empty cPsi1' ^ "    |-    "
                   ^ P.typToString cO' Int.LF.Empty cPsi1' (tP1', LF.id)
                   ^ "\n  Expected pattern type: "
                   ^ P.dctxToString cO' Int.LF.Empty cPsi' ^ "    |-    "
                   ^ P.typToString cO' Int.LF.Empty cPsi' (tP', LF.id))
             ; 
            raise (Error (loc, CompPattMismatch ((cO', cD1, cPsi1, pattern1, (tP1, LF.id)), 
                                              (cO', cD, cPsi, (tP, LF.id)))))
           )
        end
    in 
    let _ = dprnt "AbstractMSub..." in 
      (* cD1' |- t' <= cD' *)
    let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub t) in 

      (* let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub (Whnf.mcomp t mt1)) in  *)

    let rec drop t l_delta1 = match (l_delta1, t) with
        | (0, t) -> t
        | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 
        
    let t0   = drop t' n in  (* cD1' |- t0 <= cD *)
    let cPsi1_new = Whnf.cnormDCtx (cPsi1, Whnf.mcomp t1 t') in 
        (* cD1' |- cPsi1_new ctx *)
    let outputPattern = match pattern1 with
                   | Some tR1 -> Some (Whnf.cnorm (tR1, Whnf.mcomp t1 t'))
                   | None -> None in
        (* cD1' ; cPsi1_new |- tR1 <= tP1' *)
    let _ = dprint (fun () -> "synRefine [Show OCtx] cO' = " ^ P.octxToString cO' ) in 
    let _ = dprint (fun () -> "synRefine [Substitution] t': " ^ P.mctxToString cO' cD1' ^ 
                        "\n|-\n" ^ P.msubToString cO' cD1' t' ^ "\n <= " ^ P.mctxToString cO' cD' ^ "\n") in 
      (t0, t', cD1', cPsi1_new, outputPattern)
  with exn -> raise exn (* raise (Error (loc, ConstraintsLeft))*)
  end



and synRefineSubPattern loc cO' sigma1' (cD, cPsi, cPhi) (cD1, cPsi1', cPhi1') = 
  begin try 
    let cD'    = Context.append cD cD1 in                   (*         cD'  = cD, cD1     *)
    let t      = mctxToMSub cD'  in                         (*         .  |- t   <= cD'   *) 
    let n      = Context.length cD1 in 
    let m      = Context.length cD in 
    let mt     = Whnf.mcomp (Int.LF.MShift n) t in         
      (* cD, cD1 |- MShift n <= cD  
         .       |- t        <= cD, cD1
         .       |- mt       <= cD

       *)
    let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
      (* cD, cD1 |- t1 <= cD1 *)
    let mt1    = Whnf.mcomp t1 t in                          (*         .  |- mt1 <= cD1   *)

    let mt'    = Whnf.mcomp mt (Int.LF.MShift n) in          (*       cD1  |- mt' <= cD    *)
      (* let phat   = Context.dctxToHat cPsi' in *)

    let mt''   = Whnf.mcomp mt' mt1 in                       (*         .  |- mt'' <=  cD  *)

    let cPsi'  = Whnf.cnormDCtx (cPsi, mt'') (* mt *) in    (* cO ;     .  |- cPsi' ctx    *)
    let cPsi1' = Whnf.cnormDCtx (cPsi1', mt1) in             (* cO1;     .  |- cPsi1 ctx    *)

    let cPhi'  = Whnf.cnormDCtx (cPhi, mt'') (* mt *) in    (* cO ;     .  |- cPsi' ctx    *)
    let cPhi1' = Whnf.cnormDCtx (cPhi1', mt1) in             (* cO1;     .  |- cPsi1 ctx    *)
        
      (* Since |cO1| = 1, we have  cO, c01 |- cPsi'^1 ctx    *)

    let _  = begin try 
          Unify.unifyDCtx cO' (Int.LF.Empty) cPsi'  cPsi1' ;
          Unify.unifyDCtx  cO' (Int.LF.Empty) cPhi' cPhi1' ; 
          dprint (fun () -> "Unify successful: \n" ^  "Inferred pattern type: "
                    ^ P.dctxToString cO' Int.LF.Empty cPsi1' ^ "[ "
                    ^ P.dctxToString cO' Int.LF.Empty cPhi1' ^ "]" 
                    ^ "\nExpected pattern type: "
                    ^ P.dctxToString cO' Int.LF.Empty cPsi' ^ "["
                    ^ P.dctxToString cO' Int.LF.Empty cPhi')           
        with Unify.Unify msg ->
           (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n" ^  "Inferred pattern type: "
                    ^ P.dctxToString cO' Int.LF.Empty cPsi1' ^ "[ "
                    ^ P.dctxToString cO' Int.LF.Empty cPhi1' ^ "]" 
                   ^ "\nExpected pattern type: "
                    ^ P.dctxToString cO' Int.LF.Empty cPsi' ^ "["
                    ^ P.dctxToString cO' Int.LF.Empty cPhi')                      
             ; 
            raise (Error (loc, CompSubPattMismatch ((cO', cD1, cPsi1', sigma1', cPhi1'), 
                                              (cO', cD, cPsi, cPhi))))
           )
        end 
    in 
    let _ = dprint (fun () -> "AbstractMSub ..") in 
      (* cD1' |- t' <= cD' *)
    let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub t)in 

      (* let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub (Whnf.mcomp t mt1)) in  *)

    let rec drop t l_delta1 = match (l_delta1, t) with
        | (0, t) -> t
        | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 
        
    let t0   = drop t' n in  (* cD1' |- t0 <= cD *)
    let cPsi1_new = Whnf.cnormDCtx (cPsi1', Whnf.mcomp t1 t') in 
        (* cD1' |- cPsi1_new ctx *)
    let sigma' = Whnf.cnormSub (sigma1', Whnf.mcomp t1 t') in 
        (* cD1' ; cPsi1_new |- tR1 <= tP1' *)
    let _ = dprint (fun () -> "synRefine [Show OCtx] cO' = " ^ P.octxToString cO' ) in 
    let _ = dprint (fun () -> "synRefine [Substitution] t': " ^ P.mctxToString cO' cD1' ^ 
                        "\n|-\n" ^ P.msubToString cO' cD1' t' ^ "\n <= " ^ P.mctxToString cO' cD' ^ "\n") in 
      (t0, t', cD1', cPsi1_new, sigma')
  with exn -> raise exn (* raise (Error (loc, ConstraintsLeft))*)
  end





and elBranch caseTyp cO cD cG branch (Int.LF.Atom(_, a, _) as tP , cPsi) (tau, theta) = match branch with
  | Apx.Comp.BranchBox (loc, omega, delta, (psi, pattern, tAopt)) ->
      let typAnn = begin match tAopt with 
                     | None -> PartialTyp a
                     | Some (at, _psi) ->  FullTyp at
                   end in
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern ... ") in
      let _ = dprint (fun () -> "context cPsi = " ^ P.dctxToString cO cD cPsi ^ "...\n") in
      (* ***************  RECONSTRUCT PATTERN BEGIN *************** *)
      let (((l_cd1', l_delta), (l_cO', l_omega),
           cO', cD1', cPsi1', pattern', tP1', cs1, cs'),  e) =
              match pattern with
                | Apx.Comp.EmptyPattern -> (recEmptyPattern cO cD cPsi omega delta psi typAnn, None)
                | Apx.Comp.NormalPattern (m, e) -> (recPattern cO cD cPsi omega delta psi m typAnn, Some e) in 
 
      let cD         = Ctxsub.ctxnorm_mctx (cD, cs')   in  
      
      (* ***************  RECONSTRUCT PATTERN DONE  *************** *)    
      let (cPsi, tP) =  (Whnf.cnormDCtx (cPsi, Int.LF.MShift l_cd1') , Whnf.cnormTyp (tP, Int.LF.MShift l_cd1')) in 
      let (cPsi, tP)   =  (Ctxsub.ctxnorm_dctx (cPsi, cs'), Ctxsub.ctxnorm_typ (tP, cs')) in 
      (* NOW: cO'; cD , cD1 |- cPsi  and    cD, cD1' ; cPsi |- tP   *)
      (*      cO';  cD1 ; cPsi1' |- tM1' <= tP1'                    *)
      (* ***************                            *************** *)
      let caseT'  = begin match caseTyp with
                      | IndexObj (phat, tR') -> 
                          IndexObj (phat, Ctxsub.ctxnorm (Whnf.cnorm (tR', Int.LF.MShift l_cd1'), cs'))
                      | DataObj -> DataObj
                    end in
      
      (* *************** Synthesize Refinement Substitution *************************)
      let (t', t1, cD1'', cPsi1'', tR1') = 
        synRefine (Some loc) cO' caseT' (cD, cD1') pattern' (cPsi, tP) (cPsi1', tP1') in  
      (*   cD1''|-  t' : cD   and   cD1'' ; [t']cPsi |- tR1 <= [t']tP  
           cD1''|- t1  : cD, cD1'
      *)
      let (cs1, cs') = (Whnf.cnormCSub (cs1, t1) , Whnf.cnormCSub (cs', t1) ) in 
      (* *************** Synthesize Refinement Substitution *************************)
      (* Note: e is in the scope of cD, cD0; however, cD1' = cD1, cD0 !!   *)
      (*       e is in the scope of cO_ext *)
      let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
      let l_o1     = l_cO' - l_omega  in   (* l_cd1 is the length of cD1 *) 
      let cD'      = Context.append cD cD1' in
        match e with
          | None ->
              let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                                       "\n |- \n " ^ P.msubToString cO cD1'' t' ^ 
                                       " \n <= " ^ P.mctxToString cO cD) in
              let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                                       "\n |- \n " ^ P.msubToString cO cD1'' t1 ^ 
                                       " = t1") in
              let _ = (dprint (fun () -> "cs = " ^ P.csubToString cO' cD1'' cs') ; 
                       dprint (fun () -> "tau' = " ^ P.compTypToString cO cD (Whnf.cnormCTyp (tau, theta))) ; 
                       dprint (fun () -> "tau' = " ^ P.compTypToString cO' cD1''
                                 (Ctxsub.ctxnorm_ctyp (
                                    Whnf.cnormCTyp(
                                      (Whnf.cnormCTyp (Whnf.cnormCTyp (tau, theta),  (Int.LF.MShift l_cd1')) , 
                                                          t1)) , 
                                                cs'                
                                                               ))) ; 
                       dprint (fun () -> "t'   = " ^ P.msubToString cO' cD1'' t' )) in

              let _       = FMVar.clear () in
              let _       = FPVar.clear () in   
                  Int.Comp.BranchBox (cO', cD1'', (cPsi1'', Int.Comp.EmptyPattern, t', cs'))

          | Some e ->
              let e1       = fmvApxExp [] cO' cD' (l_cd1, l_delta, 0) (l_o1, l_omega, 0) e in

              let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                                       "\n |- \n " ^ P.msubToString cO cD1'' t' ^ 
                                       " \n <= " ^ P.mctxToString cO cD ^ "\n") in
              let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                                       "\n |- \n " ^ P.msubToString cO cD1'' t1 ^ 
                                       " = t1\n") in

              let e'      =  cnormApxExp cO' cD' Apx.LF.Empty e1  (cD1'', t1) cs1 in  
              (* Note: e' is in the scope of cD1''  *)
              let cG'     = Ctxsub.ctxnorm_gctx (Whnf.cnormCtx (cG, t'), cs') in 

              let _ = (dprint (fun () -> "cs = " ^ P.csubToString cO' cD1'' cs') ; 
                       dprint (fun () -> "tau' = " ^ P.compTypToString cO cD (Whnf.cnormCTyp (tau, theta))) ; 
                       dprint (fun () -> "tau' = " ^ P.compTypToString cO' cD1''
                                 (Ctxsub.ctxnorm_ctyp (
                                    Whnf.cnormCTyp(
                                      (Whnf.cnormCTyp (Whnf.cnormCTyp (tau, theta),  (Int.LF.MShift l_cd1')) , 
                                                          t1)) , 
                                                cs'                
                                                               ))) ; 
                       dprint (fun () -> "t'   = " ^ P.msubToString cO' cD1'' t' )) in

              let tau'    = Ctxsub.ctxnorm_ctyp (Whnf.cnormCTyp (tau, Whnf.mcomp theta t'), cs') in

        (*      let cG'     = Whnf.cnormCtx (Ctxsub.ctxnorm_gctx (cG, cs'), t') in 
              let tau'    = Ctxsub.ctxnorm_ctyp (tau, cs') in
              let ttau'   = (tau', Whnf.mcomp theta t') in   *)
              let _       = dprint (fun () -> "[elBranch] Elaborate branch \n" ^
                                     P.mctxToString cO' cD1'' ^ "  ;  " ^
                                     P.gctxToString cO' cD1'' cG' ^ "\n      |-\n" ^
                                     "against type " ^ P.compTypToString cO' cD1'' tau' ^ "\n") in
        (*                             "against type " ^ P.compTypToString cO' cD1'' (C.cnormCTyp ttau') ^ "\n") *)
              (* let eE'      = elExp cO' cD1'' cG'  e' ttau' in  *)
              let eE'      = elExp cO' cD1'' cG'  e' (tau', Whnf.m_id) in  
              let _       = FMVar.clear () in
              let _       = FPVar.clear () in
              let Some tR1' = tR1' in
                  Int.Comp.BranchBox (cO', cD1'', (cPsi1'', Int.Comp.NormalPattern(tR1', eE'), t', cs'))

(* ------------------------------------------------------------------- *)

open Printf

let recSgnDecl d = 
    reset_fvarCnstr ();
    FMVar.clear ();
    FPVar.clear ();
    match d with
    | Ext.Sgn.Typ (_, a, extK)   ->
        let _        = dprint (fun () -> "\nIndexing type constant " ^ a.string_of_name) in
        let fvars    = [] in 
        let (apxK, _ ) = index_kind (CVar.create ()) (BVar.create ()) fvars extK in
        let _        = FVar.clear () in

        let _        = dprint (fun () -> "\nElaborating type constant " ^ a.string_of_name) in

        let tK       = Monitor.timer ("Type Elaboration", 
                                      fun () -> (let tK = elKind Int.LF.Null apxK in
                                                   solve_fvarCnstr PiRecon (*cO=*)Int.LF.Empty Int.LF.Empty !fvar_cnstr;
                                                   tK )) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 

        (* let _        = dprint (fun () -> "\nReconstructing type constant " ^ a.string_of_name) in
           let _        = Monitor.timer ("Type Reconstruction", 
                                      fun () -> recKind Int.LF.Empty Int.LF.Null (tK, LF.id) ) in *)
        let (tK', i) = Monitor.timer ("Type Abstraction",  
                                      fun () -> Abstract.abstrKind tK) in

        let _        = reset_fvarCnstr () in          
        let _        = Unify.resetGlobalCnstrs () in 

        let _        = dprint (fun () ->  a.string_of_name ^ " : " ^  (P.kindToString Int.LF.Null (tK', LF.id))) in  

        let _        = Monitor.timer ("Type Check", 
                                      fun () -> Check.LF.checkKind Int.LF.Empty Int.LF.Empty Int.LF.Null tK') in

        let _        = dprint (fun () ->  "\nDOUBLE CHECK for type constant " ^a.string_of_name ^
                                          " successful!") in
        let _a'       = Typ.add (Typ.mk_entry a tK' i) in
          (* Int.Sgn.Typ (a', tK') *) ()


    | Ext.Sgn.Const (loc, c, extT) ->
        let fvars    = [] in 
        let (apxT, _ ) = index_typ (CVar.create ()) (BVar.create ()) fvars extT in
        let rec yankType = function
                           | Apx.LF.Atom(_loc, a, _spine) -> a
                           | Apx.LF.PiTyp ((_, _), t) -> yankType t in
        let constructedType = yankType apxT in
        let _          = dprint (fun () -> "Reconstructing term constant " ^ c.string_of_name) in

        let _        = FVar.clear () in
        let cO       = Int.LF.Empty in
        let tA       = Monitor.timer ("Constant Elaboration",
                                      fun () -> (let tA = elTyp PiRecon cO Int.LF.Empty Int.LF.Null apxT in
                                                   solve_fvarCnstr PiRecon cO Int.LF.Empty !fvar_cnstr;
                                                   tA)) in
        let cD       = Int.LF.Empty in


        let _        = dprint (fun () -> "\nElaboration of constant " ^ c.string_of_name ^ " : " ^
                                         P.typToString cO cD Int.LF.Null (tA, LF.id)) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
        (* let _        = Monitor.timer ("Constant Reconstruction", 
                                      fun () -> recTyp PiRecon cO cD Int.LF.Null (tA, LF.id)) in 

        let _        = dprint (fun () -> "\nReconstruction (without abstraction) of constant " ^ 
                                 c.string_of_name ^ " : " ^ 
                                 P.typToString cO cD Int.LF.Null (tA, LF.id)) in *)

        let (tA', i) = Monitor.timer ("Constant Abstraction", 
                                      fun () -> Abstract.abstrTyp tA) in

        let _        = reset_fvarCnstr () in
        let _        = Unify.resetGlobalCnstrs () in 
        let _        = dprint (fun () -> "\nReconstruction (with abstraction) of constant: " ^
                                 c.string_of_name ^ " : " ^
                                 (P.typToString cO cD Int.LF.Null (tA', LF.id)) ^ "\n\n") in

        let _        = Monitor.timer ("Constant Check", 
                                      fun () -> Check.LF.checkTyp Int.LF.Empty Int.LF.Empty Int.LF.Null (tA', LF.id)) in
        let _c'       = Term.add (Some loc) constructedType (Term.mk_entry c tA' i) in
        (* let _        = Printf.printf "%s : %s .\n" (c.string_of_name) (P.typToString cO cD  Int.LF.Null (tA', LF.id)) in *)
          (* Int.Sgn.Const (c', tA') *)
          ()       

    | Ext.Sgn.Schema (_, g, schema) ->
        (* let _       = Printf.printf "\n Indexing schema  %s  \n" g.string_of_name  (P.fmt_ppr_lf_schema  in   *)
        let apx_schema = index_schema schema in
        let _        = dprint (fun () -> "\nReconstructing schema " ^ g.string_of_name ^ "\n") in
        let cO       = Int.LF.Empty in
        let _        = FVar.clear () in
        let sW       = elSchema cO apx_schema in
        let _        = dprint (fun () -> "\nElaborating schema " ^ g.string_of_name ) in 
        (* let _        = dprint (fun () -> " \n = " ^   (P.schemaToString sW) ^ "\n\n") in  *)

        let _        = solve_fvarCnstr PiRecon (*cO=*)Int.LF.Empty Int.LF.Empty !fvar_cnstr in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 

        let _        = reset_fvarCnstr () in
        let _        = Unify.resetGlobalCnstrs () in 

        (* let _        = recSchemaWf sW in *)
        let sW'      = Abstract.abstrSchema sW in 
        let _        = Check.LF.checkSchemaWf sW' in
        let _        = dprint (fun () -> "\nTYPE CHECK for schema " ^ g.string_of_name ^ " successful" )  in
        let _g'      = Schema.add (Schema.mk_entry g sW') in
        let _        = Format.printf "\nschema %s = @[%a@];@."
                                     (g.string_of_name)
                                     (P.fmt_ppr_lf_schema Pretty.std_lvl) sW' in
          (* Int.Sgn.Schema (g', sW) *) ()

    | Ext.Sgn.Val (loc, x, None, i) -> 
          let fvars = [] in 
          let apx_i   = index_exp' (CVar.create ()) (CVar.create ()) (Var.create ()) fvars i in
          let cO      = Int.LF.Empty in
          let cD      = Int.LF.Empty in
          let cG      = Int.LF.Empty in 
          let (i', (tau, theta)) = Monitor.timer ("Function Elaboration", fun () -> elExp' cO cD cG apx_i ) in
          let _       = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _       = Unify.resetGlobalCnstrs () in 
          let tau'    = Whnf.cnormCTyp (tau, theta) in 
          let i'      = Whnf.cnormExp' (i', Whnf.m_id) in 
          let _       = dprint (fun () ->  "\n [AFTER Reconstruction] let " ^ x.string_of_name ^
                               "\n   : " ^ P.compTypToString cO cD tau' ^ 
                                "\n  =  " ^ 
                                P.expSynToString cO cD cG i' ^ "\n") in

          let i''    = Monitor.timer ("Function Abstraction", fun () -> 
                                        Abstract.abstrExp (Int.Comp.Syn (Some loc, i'))) in
          let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cO cD  cG i'' (tau', C.m_id)) in

          let v  =   Opsem.eval i''  in 
          let _       = Printf.printf  "\n\nlet %s : %s = %s  \n ===>  %s \n"
                  (R.render_name x)
                  (P.compTypToString cO cD tau') 
                  (P.expChkToString cO cD cG i'') 
                  (P.expChkToString cO cD cG v) in
          let _x = Comp.add (Comp.mk_entry x tau' 0 v []) in 
            ()


    | Ext.Sgn.Val (loc, x, Some tau, i) -> 
          let fvars = [] in 
          let apx_tau = index_comptyp (CVar.create ()) (CVar.create ()) fvars tau in
          let cO      = Int.LF.Empty in
          let cD      = Int.LF.Empty in
          let cG      = Int.LF.Empty in 
          let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> elCompTyp cO cD apx_tau)  in
          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _        = Unify.resetGlobalCnstrs () in 
          let (tau', _imp) = Monitor.timer ("Function Type Abstraction", fun () -> Abstract.abstrCompTyp tau') in
          let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cO cD tau') in

          let apx_i   = index_exp' (CVar.create ()) (CVar.create ()) (Var.create ()) fvars i in

          let i'      = Monitor.timer ("Function Elaboration", fun () -> elExp cO cD cG (Apx.Comp.Syn(loc, apx_i)) (tau', C.m_id)) in
          let _       = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _       = Unify.resetGlobalCnstrs () in 

          let _       = dprint (fun () ->  "\n [AFTER Reconstruction] let " ^ x.string_of_name ^
                               "\n   : " ^ P.compTypToString cO cD tau' ^ 
                                "\n  =  " ^ 
                                P.expChkToString cO cD cG i' ^ "\n") in

          let i''     = Monitor.timer ("Function Abstraction", fun () -> Abstract.abstrExp i') in
          let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cO cD  cG i'' (tau', C.m_id)) in

          let v  =   Opsem.eval i''  in
          let _       = Printf.printf  "\nlet %s : %s = %s\n===>  %s\n"
                                       (R.render_name x)
                                       (P.compTypToString cO cD tau') 
                                       (P.expChkToString cO cD cG i'') 
                                       (P.expChkToString cO cD cG v) in
          let _x = Comp.add (Comp.mk_entry x tau' 0 v []) in 
            ()


    | Ext.Sgn.Rec (_, recFuns) ->
        (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in   *)
        let cD      = Int.LF.Empty in
        let cO      = Int.LF.Empty in

        let rec preprocess l = match l with 
          | [] -> (Int.LF.Empty, Var.create (), [])
          | Ext.Comp.RecFun (f, tau, _e) :: lf -> 
          let fvars = [] in 
          let apx_tau = index_comptyp (CVar.create ()) (CVar.create ()) fvars tau in
          let _       = dprint (fun () ->  "Reconstructing function " ^  f.string_of_name ^ " \n") in
          let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> elCompTyp cO cD apx_tau)  in
          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _        = Unify.resetGlobalCnstrs () in 
          (* Are some FMVars delayed since we can't infer their type? - Not associated with pattsub *)
          let _        = dprint (fun () ->  "Elaboration of function type " ^ f.string_of_name ^ 
                                   " \n : " ^  (P.compTypToString cO cD tau') ^ " \n\n" )   in   

          (* let _       = Monitor.timer ("Function Type Reconstruction", fun () -> recCompTyp cO cD tau') in *)
          let (tau', _i) = Monitor.timer ("Function Type Abstraction", fun () -> Abstract.abstrCompTyp tau') in
          let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cO cD tau') in
          let _       = dprint (fun () -> "Checked computation type " ^ (P.compTypToString cO cD tau') ^ " successfully\n\n")  in
          let _       = FMVar.clear () in
          let _       = FPVar.clear () in

          let (cG, vars, n_list) = preprocess lf in 
            (* check that names are unique ? *)
            (Int.LF.Dec(cG, Int.Comp.CTypDecl (f, tau')) , Var.extend  vars (Var.mk_entry f), f::n_list )

        in

        let (cG , vars', n_list ) = preprocess recFuns in 

        let reconFun f e = 
          let fvars = [] in 
          let apx_e   = index_exp (CVar.create ()) (CVar.create ()) vars' fvars e in
          let _       = dprint (fun () -> "\n  Indexing  exp done \n") in
          let tau'    = lookupFun cG f in 
          let e'      = Monitor.timer ("Function Elaboration", fun () -> elExp cO cD cG apx_e (tau', C.m_id)) in

          let _       = dprint (fun () ->  "\n Elaboration of function " ^ f.string_of_name ^
                                  "\n   type: " ^ P.compTypToString cO cD tau' ^ 
                                  "\n   result:  " ^ 
                                  P.expChkToString cO cD cG e' ^ "\n") in

          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _        = Unify.resetGlobalCnstrs () in 

          (* let e_r     = Monitor.timer ("Function Reconstruction", fun () -> check  cO cD cG e' (tau', C.m_id)) in  *)

          let _       = dprint (fun () ->  "\n [AFTER reconstruction] Function " ^ f.string_of_name ^
                               "\n   type: " ^ P.compTypToString cO cD tau' ^ 
                                "\n   result:  " ^ 
                                P.expChkToString cO cD cG e' ^ "\n") in

          let e_r'    = Monitor.timer ("Function Abstraction", fun () -> Abstract.abstrExp e' ) in

          let e_r'    = Whnf.cnormExp (e_r', Whnf.m_id) in  

          let _       = Monitor.timer ("Function Check", fun () -> 
                                         Check.Comp.check cO cD  cG e_r' (tau', C.m_id)                                   
                                      ) in
             (e_r' , tau')
        in 

        let rec reconRecFun recFuns = match recFuns with
          | [] -> ()
          | Ext.Comp.RecFun (f, _tau, e) :: lf -> 
              let (e_r' , tau') = reconFun f e in 
              let _       = Printf.printf  "and %s : %s =\n %s\n"
              (R.render_name f)
              (P.compTypToString cO cD tau') 
              (P.expChkToString cO cD cG e_r')
              (* (P.expChkToString cO cD cG (Whnf.cnormExp (e_r', C.m_id)) ) *) in 

              let _       = dprint (fun () ->  "DOUBLE CHECK of function " ^    f.string_of_name ^  " successful!\n\n" ) in

              let _f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' n_list)   in
               reconRecFun lf
              
        in 
          begin match recFuns with
            | Ext.Comp.RecFun (f, _tau, e) :: lf -> 
                let (e_r' , tau') = reconFun f e in 
                  Format.printf "\nrec %s :@[<2>@ %a@] = @.@[<2>%a@]@.\n"
                    (R.render_name f)
                    (P.fmt_ppr_cmp_typ cO cD Pretty.std_lvl) (Whnf.normCTyp tau')
                    (P.fmt_ppr_cmp_exp_chk cO cD cG Pretty.std_lvl) (Whnf.cnormExp (e_r', Whnf.m_id));

                let _       = dprint (fun () ->  "DOUBLE CHECK of function " ^    f.string_of_name ^  " successful!\n" ) in

                let _f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' n_list)   in
                  reconRecFun lf 
            | _ -> raise (Violation "No recursive function defined")
          end


    | Ext.Sgn.Pragma(loc, Ext.LF.NamePrag (typ_name, m_name, v_name)) ->
        begin try 
          begin match v_name with
            | None ->
                let _cid_tp = Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name)) None in
                  (* Int.Sgn.Pragma(Int.LF.NamePrag(cid_tp)) *) ()
            | Some x ->
                let _cid_tp = Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name))
                  (Some (Gensym.VarData.name_gensym x)) in
                  (* Int.Sgn.Pragma(Int.LF.NamePrag(cid_tp)) *) ()
          end
        with _ -> raise (Error  (Some loc, UnboundName typ_name)) 
        end 


let rec recSgnDecls = function

  | [] -> ()

  | Ext.Sgn.Pragma(_, Ext.LF.NotPrag) :: not'd_decl :: rest ->
      (*   let internal_syntax_pragma = Int.Sgn.Pragma(Int.LF.NotPrag) in *)
      let not'd_decl_succeeds = 
        begin try
          (let _ = recSgnDecl not'd_decl in
             true)
        with
            _ -> (print_string ("Reconstruction fails for %not'd declaration\n");
                  false)
        end
      in
        if not'd_decl_succeeds then
          raise (Violation ("UNSOUND: reconstruction succeeded for %not'd declaration"))
        else recSgnDecls rest

  | [Ext.Sgn.Pragma(_, Ext.LF.NotPrag)] ->  (* %not declaration with nothing following *)
      ()

  | decl :: rest ->
      recSgnDecl decl;
      recSgnDecls rest

(**

   @author Marie-Andree B.Langlois
*)

module Loc = Syntax.Loc
let out_channel = open_out "reconstruct.out";

exception Error of string

let printLocation loc = Parser.Grammar.Loc.print Format.std_formatter loc
(* create terminals and then check if a symbol was declared terminal *)

(*let regexp terminals = list of strings (not sure if necessary) *)

(* terminal list -> string list *)
let rec makeTerminals lt =
  match lt with
    | [] -> []
    | h :: t -> let Terminal(_, t1) = h in t1 :: (makeTerminals t)

(* string -> string list -> bool *)
let rec checkString s lt = 
  match lt with 
    | [] -> false
    | h :: t -> if h = s then true else checkString s t

let checkNil lt = 
  match lt with 
    | [] -> true
    | h :: t -> false

let rec printL l =
  match l with 
    | [ ] -> ( )
    | h::t -> output_string out_channel h; output_string out_channel "print list \n"; printL t

type bind = Paire of alternative * variable list

and variable = Var of Loc.t * string

let rec findBind a lv ac =
  match a with
    | AltAtomic(l1,t1,a1) -> (begin match a1 with
                                | None -> raise (Error ("This alternative needs a variable binding."))
                                | Some(a2) -> if checkString t1 lv then findBind a2 lv (Var(l1,t1)::ac) else raise (Error ("Did you forget to declare **** as a variable.")) (** throw var name*)
                              end )
    | AltBin(l1, a) -> Paire(AltBin(l1, a), ac)
    | _ -> raise (Error ("Syntax error in alternative."))

let rec altList l ty lty lt lv la =
  match la with
    | [] -> raise (Error ("Can't have empty list here according to parser."))
    | h::[] -> alts l ty lty lt lv h
    | h::t -> Ext.LF.ArrTyp(l, alts l ty lty lt lv h, altList l ty lty lt lv t)

(* this is for any alternative *)
(* Loc.t -> string -> string list -> terminal list -> alternative list -> Ext.LF.typ *)
and alts l ty lty lt lv a = 
  match a with
    | AltAtomic(l1, t1, a1) -> if (checkString t1 lty ) then
                                  (* this is a type is theres is an alternative after it just skip to next*)
                                  ( begin match a1 with
                                      | None -> Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil)
                                      | Some(a2) -> output_string out_channel "AltAtomic typ \n"; alts l1 ty lty lt lv a2 
                                    end )
                                  else(* if (checkString t1 lt) then *)
                                  ( begin match a1 with
                                      | None -> Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil)
                                      | Some(a2) -> Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), alts l1 ty lty lt lv a2)
                                    end ) 
                                 (* else raise (Error ("Alternatives must be only types or terminals"))*)

    | AltLam(l1, AName(t1), a1) -> output_string out_channel "alts AltLam \n"; (** record this name somewhere *)
                                        (begin match a1 with
                                           | None -> raise (Error ("Must indicate variable binding in this alternative"))
                                           | Some(a2) ->  let Paire(a3, lv1) = findBind a2 lv [] in alts l1 ty lty lt lv a3
                                        end) 
    | AltFn(l1, Typ(l2, t1), t_or_l, a1) -> (begin match t_or_l with
                                                  | Ty(Typ(l3, t2)) -> (begin match a1 with 
                                                                          | None -> Ext.LF.Atom(l1, Id.mk_name(Id.SomeString t2),Ext.LF.Nil)
                                                                          | Some(a2) -> Ext.LF.ArrTyp(l, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString t2),Ext.LF.Nil), alts l1 ty lty lt lv a2)  
                                                                       end)
                                                  | La(la2) -> (begin match a1 with 
                                                                  | None -> Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), altList l1 ty lty lt lv la2)
                                                                  | Some(a2) -> Ext.LF.ArrTyp(l,alts l1 ty lty lt lv a2, altList l1 ty lty lt lv la2)  
                                                                end)
                                               end )

   (* | AltPar ->  Ext.LF.Atom(l, Id.mk_name (Id.SomeString ty),Ext.LF.Nil) *)

    | AltBin(l1, a) -> output_string out_channel "AltBin\n"; alts (** *) l1 ty lty lt lv a

    | AltOft(l1, a1, a2) -> alts l1 ty lty lt lv a2 
    | _ -> raise (Error ("Unvalid alternative/Not implemented yet"))

(* this is for the first element at the begginig of an alternative *)
(* Loc.t -> string -> terminal list alternative list -> Ext.Sgn.decl list *)
let rec sgnAlts l ty lty lt lv la = 
  match la with
    | [] -> []
    | AltAtomic(l1, t1, a1)::t -> output_string out_channel "sgn AltAtomic \n";
                                  if (checkString t1 lty ) then
                                  (* skip to next and dont care about this type, we are at the beggining of the alternative so there cant be only this atom*)
                                  ( begin match a1 with
                                      | None -> raise (Error ("Illegal alternative"))
                                      | Some(a2) -> output_string out_channel "sgn AltAtomic typ\n"; Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), alts l1 ty lty lt lv a2)::sgnAlts l ty lty lt lv t 
                                    end )
                                  else if (checkString t1 lt) then 
                                  ( begin match a1 with
                                      | None -> Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Atom(l, Id.mk_name (Id.SomeString ty),Ext.LF.Nil))::sgnAlts l ty lty lt lv t
                                      | Some(a2) -> output_string out_channel "sgn altAtomic terminal \n"; 
                                                    Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.ArrTyp(l,
                                                    Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil), alts l1 ty lty lt lv a2))::sgnAlts l ty lty lt lv t 
                                    end )
                                   else ( begin match a1 with
                                      | None -> (*Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Atom(l, Id.mk_name (Id.SomeString ty),Ext.LF.Nil))::*)sgnAlts l ty lty lt (lv@[t1]) t
                                      | Some(a2) -> raise (Error ("An Alternative must start with a terminal or declare a variable, maybe you forgot to declare **** terminal")) (** *)
                                    end )

    | AltLam(l1, AName(t1), a1)::t -> output_string out_channel "AltLam print list of variables\n"; printL lv; if checkString t1 lt 
                                      then
                                      (begin match a1 with
                                           | None -> raise (Error ("Must indicate variable binding in this alternative"))
                                           | Some(a2) ->  let Paire(a3, lv1) = findBind a2 lv [] in Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), alts l1 ty lty lt lv a3)::sgnAlts l ty lty lt lv t
                                        end) (* make sure you dont need lv1*)
                                      else raise (Error ("***** was not declared terminal")) (** get it to print t1 *)
                                      
(** You must deal with a1 *)
    | AltFn(l1, Typ(l2, t1), Ty(Typ(l3, t2)), a1)::t ->  Ext.Sgn.Const(l, Id.mk_name (Id.SomeString ty), 
                                                 Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), 
                                                 Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t2),Ext.LF.Nil)))::sgnAlts l ty lty lt lv t 
    | AltLet(l1, a1, a2, a3)::t -> output_string out_channel "sgn AltLet \n"; 
                                      (begin match a3 with
                                           | AltFn(_) -> Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString "letv"), Ext.LF.ArrTyp(l, Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil), 
                                                         alts l1 ty lty lt lv a3))::sgnAlts l ty lty lt lv t
                                           | _ -> raise (Error ("Unvalid alternative"))
                                        end)

    | AltPar::t ->  sgnAlts l ty lty lt lv t
    | _ -> raise (Error ("Unvalid start of alternative"))

(* string list -> string list -> production list -> Ext.Sgn.decl list, first list types second terminals *)
let rec sgnTypes lt lty lp =
  match lp with
    | [] -> []
    | Production(l1, Typ(l2, t1), la)::t -> [Ext.Sgn.Typ(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Typ(l1))]@ sgnAlts l2 t1 lty lt [] la @ sgnTypes lt lty t

(* Loc.t -> string -> judge list -> string list -> Ext.Sgn.decl list *)
let rec typ_or_sym l js ltyp =
  match js with
    | [] -> output_string out_channel "typ or sym [] \n"; Ext.LF.Typ(l) 
    | h::t -> let Judge(l1,s1) = h in if (checkString s1 ltyp ) then (output_string out_channel "typ or sym then \n"; 
                                   Ext.LF.ArrKind(l, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s1),Ext.LF.Nil), typ_or_sym l1 t ltyp) )
                                   else (output_string out_channel "typ or sym else \n"; typ_or_sym l1 t ltyp)

(* checks the judgement if its not a type its a symbol indicating the syntax of the judgement *)
(* judge list -> string list -> string list *)
let rec typ_or_sym_list lj ltyp = 
  match lj with
    | [] -> output_string out_channel "typ or sym list [] \n"; []
    | h::t -> let Judge(l1,s1) = h in if (checkString s1 ltyp ) then (output_string out_channel s1; output_string out_channel "check string then \n"; 
              typ_or_sym_list t ltyp) else (output_string out_channel s1; output_string out_channel "check string else \n"; s1 :: typ_or_sym_list t ltyp  )

(* Loc.t -> jName -> jSyntax -> string list -> (string list , Ext.Sgn.decl list) *)
let sgnJudge l jn js ltyp =
   let JName(j) = jn in let JSyntax(l, a, lj) = js in ( typ_or_sym_list lj ltyp, Ext.Sgn.Typ(l,Id.mk_name (Id.SomeString j), typ_or_sym l lj ltyp))

(* Loc.t -> string list -> var_alternative -> Ext.LF.spine *)
let rec valtsPar l a lsym =
  match a with 
    | VAltAtomic(l, s, ao) -> (begin match ao with 
                                 | None -> output_string out_channel "valtsPar none \n";
                                           Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil)

                                 | Some(a) -> output_string out_channel "valts some then \n";  
                                              Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), valts l lsym a) 

                              end)

    | _ -> raise (Error ("Not implemented yet (in valtsPar).")) 

(* Loc.t -> string list -> var_alternative -> Ext.LF.spine *)
and valts l lsym va =
  match va with 
    | VAltAtomic(l, s, ao) -> (begin match ao with 
                                 | None -> if checkString s lsym 
                                           then (output_string out_channel s; output_string out_channel "valts none then \n"; Ext.LF.Nil ) 
                                           else (output_string out_channel s; output_string out_channel " valts none else \n";
                                                   Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), Ext.LF.Nil) )

                                 | Some(a) -> if checkString s lsym 
                                              then (output_string out_channel s; output_string out_channel "valts some then \n"; valts l lsym a) 
                                              else (output_string out_channel s; output_string out_channel " valts some else \n";
                                                   Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), valts l lsym a) )

                              end)

    | VAltPar(l, a, ao) -> (begin match ao with 
                                 | None -> output_string out_channel " valts altpar none \n";
                                                   Ext.LF.App(l, valtsPar l a lsym, Ext.LF.Nil) 

                                 | Some(b) -> output_string out_channel " valts altpar some \n";
                                                   Ext.LF.App(l, valtsPar l a lsym, valts l lsym b) 

                              end)

    | _ -> raise (Error ("Not implemented yet (in valts).")) 

(* string list -> rule list -> Ext.Sgn.decl list *)
let rec judges jn lsym lr = 
   match lr with
    | [] -> []
    | h::t -> let Rule(l1, a, RName(s), Premisse(l2, b, c, va)) = h in let JName(s1) = jn in
              begin match a with
                | [] -> let JName(s) = jn in output_string out_channel "judges \n";  
                        [Ext.Sgn.Const(l1, Id.mk_name(Id.SomeString s), Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s1), valts l2 lsym va))] @ judges jn lsym t
                | h1::t1 -> let Premisse(l3, b1, c1, va1) = h1 in
                            [Ext.Sgn.Const(l1, Id.mk_name(Id.SomeString s), Ext.LF.ArrTyp(l1, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s1), valts l3 lsym va1), 
                                                                            Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s1), valts l2 lsym va)))] @ judges jn lsym t
              end


(* string list -> string list -> Ext.Sgn.decl list, first list terminals secong types *)
let rec recSectionDecl lt ltyp ls = 
  match ls with 
    | [] -> []
    | h::t -> begin match h with
                | Grammar (_, lp) -> output_string out_channel "Grammar decl \n"; (sgnTypes lt ltyp [lp] @ recSectionDecl lt ltyp t )
                | Judgement(l, jn, js, a, lr) -> (*output_string out_channel "Judgement \n"; output_string out_channel "print list in judgement \n";printL ltyp; 
                                                 let (l1, sgnj) = sgnJudge l jn js ltyp in output_string out_channel "Print list of symbol: \n"; printL l1;
                                                                                           [sgnj] @ judges jn l1 lr @ recSectionDecl lt ltyp t*) [] (** *)
                | Theorems _ -> output_string out_channel "Theorems \n"; []
              end

(* section list -> string list *)
let rec recSectionDeclGram l ls =
  match ls with
    | [] -> []
    | Grammar (_, Production(l1, Typ(l2, t1), la)):: t -> output_string out_channel t1; output_string out_channel " gram decl \n"; t1 :: recSectionDeclGram l t 
    | Judgement _ ::t -> recSectionDeclGram l t
    | Terminals_decl _:: t -> (*printLocation l; *)raise (Error ("Should only have one declaration of terminals"))
    | Theorems _ :: t-> recSectionDeclGram l t

(* string list -> string list -> Syntax.section list -> Syntax.Ext.Sgn.decl list *)
let sectionDecls ls = 
  match ls with
    | Terminals_decl(l,lt):: t -> let lt1 = makeTerminals lt in let ltyp = recSectionDeclGram l t in output_string out_channel "Section Decls \n"; 
                                  printL ltyp; recSectionDecl lt1 ltyp t
    | _ -> raise (Error ("No terminal declaration or grammar at the beginnig of file"))
