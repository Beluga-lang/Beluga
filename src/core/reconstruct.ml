(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

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

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [4])

exception NotImplemented
exception Error of Syntax.Loc.t option * error
exception Violation of string
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




let rec unify_phat psihat ctx_var = 
  match ctx_var with
    | (Some (Int.LF.CInst ({contents = None} as cref, _, _, _ )), d) -> 
        begin match psihat with 
          | ((Some (c_var)) , d') -> 
              if d = d' then
                (cref := Some (Int.LF.CtxVar (c_var))  ; true)
              else 
                (dprint (fun () -> "[unify_phat] unify ctx_var with a full context ") ; 
                 raise NotImplemented)
          | (None , d') -> 
              if d = d' then 
                (cref := Some (Int.LF.Null) ; true)
              else 
                (dprint (fun () -> "[unify_phat] unify ctx_var with a full context ") ; 
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


let rec ctxShift cPsi = begin match cPsi with
  | Int.LF.Null              -> Int.LF.Shift (Int.LF.NoCtxShift , 0 )
  | Int.LF.CtxVar psi        -> Int.LF.Shift (Int.LF.CtxShift psi, 0)
  | Int.LF.DDec   (cPsi, _x) -> 
      match  ctxShift cPsi with
          Int.LF.Shift (cshift, n)  -> Int.LF.Shift (cshift, n+1)
  end


  (* ctxToSub' cPhi cPsi = s 

     if x1:A1, ... xn:An = cPsi
     then D = u1:A1[cPhi], ... un:An[cPhi]

     s.t. D; cPhi |- u1[id]/x1 ... un[id]/xn : cPsi
  *)
  let rec ctxToSub' cD cPhi cPsi = match cPsi with
    | Int.LF.Null -> LF.id
    | Int.LF.DDec (cPsi', Int.LF.TypDecl (_, tA)) ->
        let s = ((ctxToSub' cD cPhi cPsi') : Int.LF.sub) in
          (* For the moment, assume tA atomic. *)
          (* lower tA? *)
          (* A = A_1 -> ... -> A_n -> P

             create cPhi = A_1, ..., A_n
             \x_1. ... \x_n. u[id]
             u::P[cPhi]

             already done in reconstruct.ml
             let (_, d) = Context.dctxToHat cPsi in
             let tN     = etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift d) in
             in elSpineIW
          *)
        (* let (_, phat') = Context.dctxToHat cPsi' in*)
        (* let u     = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in *)

        (* let u     = Whnf.etaExpandMV Null (tA, s) LF.id in *)
          (* let u = Whnf.newMVar (Null ,  TClo( tA, s)) in *)
        let u     = Whnf.etaExpandMMV None cD cPhi (tA, LF.comp s (ctxShift cPhi)) LF.id in 
        let front = (Int.LF.Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : Int.LF.front) in
          Int.LF.Dot (front, LF.comp s LF.shift)



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
  let _ = dprint (fun () -> "check pat spine") in
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
    patSpine' [] spine

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

(* We cannot handle this at the moment; to infer the type of 
   FMVars which are associated with projections and impose a restriction;
   the issues arises in pruning the type of FMVars where the most general
   type is generated as a id sub from a context containing blocks to another
   one containing blocks; instead we would need to create FMVars as
   going from a flattened block context to its block equivalent, and
   unroll the id substitution to b.1 b.2 b.3 etc instead of b
     
    | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar _k,_j)), s) ->
      isPatSub s
*)
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

let rec mctxToMSub cD = match cD with
  | Int.LF.Empty -> C.m_id
  | Int.LF.Dec (cD', Int.LF.MDecl(_, tA, cPsi)) ->
      let t     = mctxToMSub cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi,t) in
      let tA'   = Whnf.cnormTyp (tA, t) in
      let u     = Whnf.newMVar (cPsi', tA') in
      let phat  = Context.dctxToHat cPsi' in
        Int.LF.MDot (Int.LF.MObj (phat, Int.LF.Root (None, Int.LF.MVar (u, LF.id), Int.LF.Nil)) , t)

  | Int.LF.Dec(cD', Int.LF.PDecl(_, tA, cPsi)) ->
      let t    = mctxToMSub cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi, t) in
      let p    = Whnf.newPVar (cPsi', Whnf.cnormTyp (tA, t)) in
      let phat = Context.dctxToHat cPsi' in
        Int.LF.MDot (Int.LF.PObj (phat, Int.LF.PVar (p, LF.id)) , t)


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

let rec lookup cG k = match (cG, k) with
  | (Int.LF.Dec(_cG', Int.Comp.CTypDecl (_, tau)), 1) ->   tau
  | (Int.LF.Dec( cG', Int.Comp.CTypDecl (_, _tau)), k) ->
      lookup cG' (k-1)

(* -------------------------------------------------------------*)
(* PHASE 0 : Indexing
 *
 * index_term names ext_m = (m, fvars)
 *
 * Translates an object ext_m in external syntax
 * into an object m in approximate internal syntax.
 *
 * ASSUMPTION:
 *
 *    ext_m is in beta normal form
 *        m is in beta normal form, i.e.
 *
 *)


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
      raise (Violation "index_of for a free variable does not exist – should be impossible\n")  
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

(* Order of psihat ? -bp
   It's not clear how to know that the last name is a bound variable
   or if it is a name of a context variable...
*)
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
        let _ = dprint (fun () -> "Indexing TypSub – turning TypBox into TypSub") in
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

  | Ext.Comp.Case (loc, i, branches) ->
      let i' = index_exp' ctx_vars cvars vars fvars i in
      let branches' = List.map (function b -> index_branch ctx_vars cvars vars fvars b) branches in
        Apx.Comp.Case (loc, i', branches')


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
  | (Ext.Comp.BranchBox(loc,  delta, (psi1, m, Some (a, psi)), e)) ->
    let empty_fvars = [] in 
    let _ = dprint (fun () -> "index_branch") in 
    (* this trick of getting the context variable occurring in a pattern
       doesn't work anymore in the presence of substitution patterns and 
       substitution variables; substitution variables may have type h[h']
       where h' may occur in psi1 but h doesn't occur anywhere... *)
    let ctx_vars' = begin match get_ctxvar psi1 with 
                     | None -> CVar.create () 
                     | Some psi_name -> CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) 
                    end in


    let (omega, delta', ctx_vars', cvars', fvars1)  = 
      index_mctx ctx_vars' ctx_vars' empty_fvars delta in
    let (psi1', bvars, fvars2)   = index_dctx ctx_vars' cvars' (BVar.create ()) fvars1 psi1 in 
    let (m', fvars3)             = index_term cvars' bvars fvars2 m in
    let (psi', _bvars, fvars4)   = index_dctx ctx_vars' cvars' (BVar.create ()) fvars3 psi in
    (* _bvars = bvars *)
    let (a', fvars5)             = index_typ cvars' bvars fvars4 a in

    let cvars_all        = CVar.append cvars' cvars in
    let ctxvars_all      = CVar.append ctx_vars' ctx_vars in

    let fvars6 = List.append fvars5 fvars in 
    let e'               = index_exp ctxvars_all cvars_all vars fvars6 e in

      Apx.Comp.BranchBox (loc, omega, delta', (psi1', m', Some (a', psi')), e')

  | (Ext.Comp.BranchBox(loc, delta, (psi, m, None), e)) ->
    let empty_fvars = [] in 
    let ctx_vars' = begin match get_ctxvar psi with 
                     | None -> CVar.create () 
                     | Some psi_name -> CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) 
                    end in

    let (omega, delta', ctx_vars', cvars', fvars1)  = 
      index_mctx ctx_vars' (CVar.create()) empty_fvars delta in
    let (psi1', bvars, fvars2)    = index_dctx ctx_vars' cvars' (BVar.create ()) fvars1 psi in

      begin match m with 
        | Ext.LF.Root(_, Ext.LF.SVar (loc, s, sigma), Ext.LF.Nil) -> 
            let (s_var, fvars3) = begin try
                          let offset = CVar.index_of_name cvars' s in
                          let (sigma' , fvars') = index_sub cvars' bvars fvars2 sigma in
                            (Apx.LF.SVar (Apx.LF.Offset offset, sigma') , fvars')
                        with Not_found ->
                          let _ = dprint (fun () -> "SVar Not_found " ^ R.render_name s) in
                          let (sigma', fvars')     = index_sub cvars bvars fvars sigma in
                            (Apx.LF.FSVar (s, sigma') , FSV s :: fvars' )
                        end in 

            let cvars_all        = CVar.append cvars' cvars in
            let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
            let e'               = index_exp ctxvars_all cvars_all vars fvars3 e in
              Apx.Comp.BranchSBox (loc, omega, delta', (psi1', s_var, None), e')



        | _             -> 
            let (m', fvars3)     = index_term cvars' bvars fvars2 m in
            let cvars_all        = CVar.append cvars' cvars in
            let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
            let fvars4 = List.append fvars3 fvars in 
            let e'               = index_exp ctxvars_all cvars_all vars fvars4 e in
              Apx.Comp.BranchBox (loc, omega, delta', (psi1', m', None), e')
                
      end


(* ******************************************************************* *)
(* PHASE 1 : Elaboration and Reconstruction (one pass)                 *)
(*  elTerm recT cO cD cPsi m sA = M
 *
 *  Pre-condition:
 *
 *  U = FV(m) (FV(a), FV(k) resp.)
 *  O = meta-variables in M (A, K, resp.)
 *
 * Invariant:
 *  If   O1 ; U1 ; (cD ; cPsi) |- m <- [s]A /_r (O2, U2) M 
 *      and there exists a modal substitution r
 *      s.t. O2 |- r <= O1
 *  then
 *
 *     elTerm cO cD cPsi m sA succeeds and
 *
 *     O2 ; [|r|]U2 ; ([|r|]cD ; [|r|]cPsi) |- M <= [|r|][s]A
 *
 * Post-condition:
 *
 *   O2 |- U2 fvar_ctx    and   . |-{U2} O2 mvar_ctx 
 *   (circular dependency between O2 and U2)
 *
 *   O2 s.t. O2 |-{U2} r <= O1 , and
 *
 * In the implementation:
 *   - meta-variables in O1 and O2 are handled destructively, and O1 and O2 resp characterize the state of memory.
 *   - r is not explicit but implicit since we  update all meta-variables in O1 destructively
 *   - U1 and U2 are the fvar_ctx; they are handled globally and hence are not carried explicitely as an argument
 *     to elTerm 
 *   - may raise Error, if no modal substitution r exists.
 *
 * Similar invariants and pre- and post-conditions for:
 *
 *  elKind cD cPsi k = K'
 *  elTyp  cD cPsi a = A'
 *)

(* ******************************************************************* *)
(* Free variable constraints:
 *
 * fvar_cnstr  C := . | Root (FVar X, tS) & C
 *
 * The constraints are generated when encountering
 * a free variable X whose type is yet unknown and has a
 * non-pattern spine tS. This means we cannot easily infer
 * the type of the free variable X.
 *)


(* Constraints for free bound variables *)
let fvar_cnstr : ((Int.LF.typ_free_var * Apx.LF.normal * Int.LF.cvar)  list) ref = ref [] 

let add_fvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fvarCnstr () = (fvar_cnstr := [])

(* Constraints for free metavariables and parameter variables  *)
let fcvar_cnstr : ((Apx.LF.normal * Int.LF.cvar)  list) ref = ref []

let add_fcvarCnstr  c = fcvar_cnstr := c :: !fcvar_cnstr
let reset_fcvarCnstr () = (fcvar_cnstr := [])

(* ******************************************************************* *)

(* synDom cPsi s = (cPhi , s')
 *
 * If s is a pattern substitution in approximate syntax
 *    cPsi is the range of the pattern substitution
 *
 * then
 *     s' the pattern substitution in internal syntax
 *     corresponding to s and
 *
 *     cPsi |- s' <= cPhi
 *)
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
            let tA' = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) (tA, LF.id) 
                                     (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in
              (Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, tA')),
               Int.LF.Dot (Int.LF.Head(Int.LF.BVar k), s'))
(*         | _ -> raise (Violation "Undefined bound variable\n") *)
      end

   | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar k,j)), s) ->
      begin match Context.ctxDec cPsi k with
        | Int.LF.TypDecl (x, tB) -> (* tB = block x1:A1. ... xn:An *)
           let (cPhi, s') = synDom cD loc cPsi s in 
              (*  cPsi |- s <= cPhi
               *  cPsi |- tA <= type
               *  tA' = [s]^-1(tA)
               *
               * Note: We may need to check that [s]^-1(tA) actually exists; 
               * Wed Jan 14 13:51:11 2009 -bp
               *)
            let ss = Substitution.LF.invert s' in 

            let Int.LF.Sigma typRec = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) (tB, LF.id) 
                                     (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in

            let sQ = Int.LF.getType  (Int.LF.BVar k) (typRec, LF.id) k 1 in 

              (Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, Int.LF.TClo sQ)),
               Int.LF.Dot (Int.LF.Head(Int.LF.Proj(Int.LF.BVar k, j)), s'))
         | _ -> raise (Violation "Undefined bound variable\n") 
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
(* elTyp recT  cD cPsi a = A
 *
 * Pre-condition:
 *     U = set of free variables
 *     O = set of meta-variables (references subject to instantiation)
 *
 * if cD ; cPsi |- a <= type and a is in beta normal form
 *   
 * then
 *        [|r|]cD ;  [|r|]cPsi   |- A <= type 
 * and A is in beta-eta normal form.
 *
 * Effect:
 *     U' = FV(A)  where U' is an extension of U s.t. [|r|]U,U0 = U'
 *     O' = FMV(A) where O' |-{U'} r <= O
 *)
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


(* elTerm recT  cD cPsi m sA = M
 * elTerm recT  cD cPsi m sA = M  where sA = (A,s) is in whnf
 *                              m is in beta normal form.
 * Pre-condition:
 *     U = set of free variables   O |- U fvar_ctx
 *     O = set of meta-variables (references subject to instantiation)
 *                                 . |-{U} O mvar_ctx
 * if cD ; cPsi |- M <= [s]A'
 *
 *    cD |- cPsi ctx
 *    cD ; cPsi  |- s <= cPsi'
 *    cD ; cPsi' |- A <= type 
 *
 * then
 *    [|r|]cD ; [|r|]cPsi |- M <= [|r|]A 
 *
 * and M is in beta-eta normal form, i.e.
 *   all free variables are eta-expanded.
 *
 * Effect:
 *     U' = FV(A)  where U' is an extension of U s.t. [|r|]U,U0 = U'
 *     O' = FMV(A) where O' |-{U'} r <= O
 *)
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

  | (Apx.LF.Root (loc, Apx.LF.FMVar (x, _),  _spine),  (Int.LF.PiTyp _ , _s)) ->
      raise (Error (Some loc, EtaExpandFMV (x, cO, cD, cPsi, sA)))


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


  and instanceOfSchElem cO cD cPsi (tA, s) (Int.LF.SchElem (some_part, block_part)) = 
    let _ = dprint (fun () -> "instanceOfSchElem ... \n") in 
    let sArec = match Whnf.whnfTyp (tA, s) with
      | (Int.LF.Sigma tArec,s') ->  (tArec, s') 
      | (nonsigma, s')          ->  (Int.LF.SigmaLast nonsigma, s') in
    let _ = dprint (fun () -> ("tA =" ^ P.typToString cO cD cPsi (tA, s) ^ " \n")) in 
    let dctx        = projectCtxIntoDctx some_part in     
    let dctxSub     = ctxToSub' cD cPsi dctx in

    (* let phat        = dctxToHat cPsi in *)

    let _ =  dprint (fun () -> "***Unify.unifyTypRec (" 
                        ^ "\n   cPsi = " ^ P.dctxToString cO cD cPsi
                        ^ "\n   dctx = " ^ P.dctxToString cO cD dctx  
                        ^ "\n   " ^  P.typToString cO cD cPsi (tA, s) ) in
    let _ = dprint (fun () -> "dctxSub = " ^ P.subToString cO cD cPsi dctxSub ^ "\n") in
      (* P.typRecToString cO cD cPsi sArec  *)
(*    let _ = dprint (fun () -> 
                         "\n== " ^ P.typRecToString cO cD cPsi (block_part, dctxSub) ) in  *)
    let _ = dprint (fun () ->  "== " ) in 
    (* let _ = dprint (fun () -> P.typRecToString cO cD cPsi (block_part, dctxSub) )  in*)
      begin
        try
          Unify.unifyTypRec cD cPsi sArec (block_part, dctxSub) 
        ; dprint (fun () -> "instanceOfSchElem\n"
                            ^ "  block_part = " ^ P.typRecToString cO cD cPsi (block_part, dctxSub) ^ "\n"
                            ^ "  succeeded.")
        ; (block_part, dctxSub)
        with (Unify.Unify _) as exn ->
          (dprint (fun () -> "Type " ^ P.typRecToString cO cD cPsi sArec ^ " doesn't unify with schema element\n");
(*          dprint (fun () ->  P.typRecToString cO cD cPsi (block_part, dctxSub) *)
          raise exn )
          | exn -> 
              (dprint (fun () -> " -2- "); raise exn)
      end
  
  and instanceOfSchElemProj cO cD cPsi (tA, s) (var, k) (Int.LF.SchElem (cPhi, trec)) = 
    let _ = dprint (fun () -> "instanceOfSchElemProj ... getType " ^ string_of_int k ) in 
    let _ = dprint (fun () -> " of " ^ P.typRecToString cO cD cPsi (trec, LF.id)) in
    let tA_k (* : tclo *) = Int.LF.getType var (trec, LF.id) k 1 in
    let _ = dprint (fun () -> "instanceOfSchElemProj ... ") in
    let (_tA'_k, subst) =
      instanceOfSchElem cO cD cPsi (tA, s) (Int.LF.SchElem (cPhi, Int.LF.SigmaLast (Int.LF.TClo tA_k)))
      (* tA'_k = [subst] (tA_k) = [s]tA *)
    in
      (trec, subst) 



(* Synthesize the type for a free parameter variable *)
and synSchemaElem recT  cO cD cPsi ((_, s) as sP) (head, k) ((Int.LF.Schema elements) as schema) =
  let self = synSchemaElem recT  cO cD cPsi sP (head, k) in 
  let _ = dprint (fun () -> "synSchemaElem ... head = " ^ P.headToString cO cD cPsi head ^ " Projection " ^ string_of_int k ^ "\n") in
  let _ = dprint (fun () -> "synSchemaElem ... " ^ P.typToString cO cD cPsi sP
                    ^ "  schema= " ^ P.schemaToString schema) in
    match elements with
      | [] -> None
      | (Int.LF.SchElem (_some_part, block_part)) as elem  ::  rest  ->
          try
            let _ = dprint (fun () -> "[instanceOfSchElemProj ] ... ") in
            let (typRec, subst) = instanceOfSchElemProj cO cD cPsi sP (head, k) elem in 
              (* Check.LF.instanceOfSchElemProj cO cD cPsi sP (head, k) elem in *)
            dprint (fun () -> "synSchemaElem RESULT = "
                            ^ P.typRecToString cO cD cPsi (typRec, subst))
          ; Some (typRec, subst) (* sP *)
          with Unify.Unify _  -> self (Int.LF.Schema rest)
            | Not_found -> self (Int.LF.Schema rest) 
(*
and lookupCtxVar cO ctx_var = match cO with
  | Int.LF.Empty -> raise (Violation ("Context variable not found"))
  | Int.LF.Dec (cO, Int.LF.CDecl (psi, schemaName)) -> 
      begin match ctx_var with 
      | Int.LF.CtxName phi when psi = phi -> (psi, schemaName)
      | (Int.LF.CtxName _phi) as ctx_var  -> lookupCtxVar cO ctx_var
      | Int.LF.CtxOffset 1                -> (psi, schemaName)
      | Int.LF.CtxOffset n                -> lookupCtxVar cO (Int.LF.CtxOffset (n - 1))
      end 
*)
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
              (Printf.printf "%s\n" msg;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
              | Unify.Error msg -> 
                  (Printf.printf "Hidden %s \n This may indicates the following problem: \n a contextual variable was inferred with the most general type\n however subsequently, it is required to have a more restrictive type, \ni.e., where certain bound variable dependencies cannot occur.\n\n " msg;
                   raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
              | _ -> (Printf.printf "Non-Unification Error (1) \n" ;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
        end

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      begin try 
        let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, LF.id) in
          begin try
            (Unify.unifyTyp cD  cPsi sQ sP ;
             Int.LF.Root (Some loc, Int.LF.BVar x, tS)) 
          with Unify.Unify msg ->
            (Printf.printf "%s\n" msg;
             raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
             | _ -> (Printf.printf "Non-Unification Error (2) \n" ;
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
              let (tS, sQ ) = elSpine loc recT cO cD cPsi spine (tA, s) in
                begin try
                  (Unify.unifyTyp cD cPsi sQ sP ;
                   Int.LF.Root (Some loc, Int.LF.FVar x, tS)) 
                with Unify.Unify msg ->
                  (Printf.printf "%s\n" msg;
                   raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
                  | _ ->                   (Printf.printf "Non-Unification Error (3)  \n" ;
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
                (let _ = dprint (fun () -> "[elTerm'] FVar case – Not a pattern spine ...") in  
                  let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
                 let tAvar = Int.LF.TypVar (Int.LF.TInst (ref None, cPsi, Int.LF.Typ, ref [])) in  
                    add_fvarCnstr (tAvar, m, v);
                   Int.LF.Root (Some loc, Int.LF.MVar (v, LF.id), Int.LF.Nil))
              end
            end
        | PiboxRecon -> raise (Error (Some loc, UnboundName x))
      end 
              

  | Apx.LF.Root (loc, Apx.LF.Hole, spine) ->
      begin try 
      (let (_l, pat_spine) = patSpine spine in
      let sshift = mkShift recT cPsi in
      let (tS, tA) = elSpineSynth recT  cD cPsi pat_spine sshift sP in
        (* For Beluga type reconstruction to succeed, we must have
         *  cPsi |- tA <= type  and cPsi |- tS : tA <= [s]tP
         *  This will be enforced during abstraction.
         *)
        (* For LF type reconstruction to succeed, we must have
         *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
         *  This will be enforced during abstraction.
         *)
        (* Potentially need to handle eta-expansion -bp *)
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
          (* For type reconstruction to succeed, we must have
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
           * meta-variables in cD. This will be enforced during abstraction *)
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
          let tP = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in
         (* let tP = Int.LF.TClo (Int.LF.TClo sP, Substitution.LF.invert s'') in *)
            (* For type reconstruction to succeed, we must have
             * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
             * This will be enforced during abstraction.
             *)
            FMVar.add u (tP, cPhi);
            Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil)
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

             let tP = Unify.pruneTyp cD flat_cPsi (*?*) 
                         (Context.dctxToHat flat_cPsi) (tP', LF.id) (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in 

             let sorig = elSub loc recT cO cD cPsi s cPhi in
             let _ = dprint (fun () -> "sorig = " ^ P.subToString cO cD cPsi sorig ^ "\n") in 
            (* For type reconstruction to succeed, we must have
             * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
             * This will be enforced during abstraction.
             *)
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
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
            raise (Error (Some loc, CompTypAnn ))

      end



  | Apx.LF.Root (loc, Apx.LF.FPVar (p, s), spine) as m ->
      begin try
        let (tA, cPhi) = FPVar.get p in
          (* For type reconstruction to succeed, we must have
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
           * meta-variables in cD. This will be enforced during abstraction *)
          
        let s'' = elSub loc recT  cO cD cPsi s cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
        let tR = Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), tS) in
          begin try
            Unify.unifyTyp cD cPsi sQ sP ; 
            tR
          with Unify.Unify msg -> 
            (Printf.printf "%s\n" msg;
             raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
            | _ ->             (Printf.printf "Unification Error (5) \n";
             raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
          end
      
      with 
        | Not_found ->
          begin match (spine, isPatSub s) with
            | (Apx.LF.Nil, true) ->
                (* 1) given cPsi and s, synthesize the domain cPhi
                 * 2) [s]^-1 ([s']tP) is the type of u
                 *)
                (* Need to check that the inferred type for p is indeed in cPsi's schema -bp *)
                let (cPhi, s'') = synDom cD loc cPsi s in
                let si          = Substitution.LF.invert s'' in
                let tP = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) sP 
                                (Int.LF.MShift 0, si) (Unify.MVarRef (ref None)) in
                (* let tP          = Whnf.normTyp (Int.LF.TClo sP, si) in*)
                  (* For type reconstruction to succeed, we must have
                   * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
                   * This will be enforced during abstraction.
                   *)
                  FPVar.add p (tP, cPhi);
                  Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), Int.LF.Nil)
            
            | (Apx.LF.Nil, false) ->
                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc, Int.LF.PVar (q, LF.id), Int.LF.Nil)
            
            | (_, _) ->  raise (Error (Some loc, NotPatternSpine))

                   (* (Printf.printf "elTerm': FPVar with spine\n" ; raise NotImplemented)*)
          end
        | Violation msg  -> 
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
            raise (Error (Some loc, CompTypAnn ))
      end

  (* Reconstruct: Projection *)
  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.FPVar (p, s), k), spine) as m ->
      (* Other case where spine is not empty is not implemented -bp *)
        begin try          
          let (Int.LF.Sigma typRec, cPhi) = FPVar.get p in
          let s'' = elSub loc recT  cO cD cPsi s cPhi in
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
                let Some psi =  Context.ctxVar cPsi in
                let schema = Schema.get_schema (Check.LF.lookupCtxVarSchema cO psi) in 
                let h = Int.LF.FPVar (p, s'') in
                let (typRec, s_inst) = 
                  begin match synSchemaElem recT  cO cD cPsi sP (h, k) schema with
                  | None -> raise (Violation ("type sP = " ^ P.typToString cO cD cPsi sP ^ " not in schema " ^ 
                                             P.schemaToString schema))
                  | Some (typrec, subst) -> (typrec, subst) 
                  end in       
                let tB  = 
                  begin match typRec with
                  | Int.LF.SigmaLast tA -> 
                      (dprint (fun () -> "synType for PVar: [SigmaLast]" ^ P.typToString cO cD cPsi (tA, s_inst) ^ "\n"); tA)
                  | typRec' -> 
                      (dprint (fun () -> "synType for PVar: [SigmaElem]" ^ P.typRecToString cO cD cPsi (typRec', s_inst) ^ "\n") ; 
                       Int.LF.Sigma typRec' )
                  end in

                (* tB = Sigma x1:A1 ... xn:An.A(n+1) 
                   and [s_inst][proj_1 h/x_1 ... proj_(k-1) h/x_(k-1)] A_k = sP
                *)
                let tB' = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) (tB, s_inst)
                                        (Int.LF.MShift 0, si) (Unify.MVarRef (ref None)) in 

                 (* r is a pruning substitution s.t. [si]([|r|]tB) = tB' and 
                    where     cPhi |- si <= cPsi
                 *)
                  FPVar.add p (tB', cPhi);
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
          let _   = dprint (fun () -> "[elTerm] Apx-mvar : Expected type: " ^ P.typToString cO cD cPsi sP ^ "\n") in 
          let _   = dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cO cD cPsi (tQ, s'') ^ "\n") in 
          (* This case only applies to Beluga; MInst are introduced during cnormApxTerm. *)
          ( Unify.unifyTyp cD  cPsi (tQ, s'') sP ; 
            dprint (fun () -> "[elTerm] reconstruction of mvar done ");
            dprint (fun () -> " sQ = " ^ P.typToString cO cD cPsi (tQ,s'') ^ " == " ^ P.typToString cO cD cPsi sP) ; 
            dprint (fun () -> "tN = " ^ P.normalToString cO cD cPsi (tN, s''));
           Int.LF.Clo(tN, s''))
      with  Violation msg  -> 
        (dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
         dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cO cD cPsi (tN,s'') ^ "\n");
         raise (Error (Some loc, CompTypAnn )))
        |  Unify.Unify msg  -> 
             dprint (fun () -> "[elTerm] Unification Violation: " ^ msg ^ "\n") ; 
             dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cO cD cPsi (tN,s'') ^ "\n");
             dprint (fun () -> "[elTerm] Expected type: " ^ P.typToString cO cD cPsi sP ^ "\n");
             dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cO cD cPsi (tQ, s'') ^ "\n");
             dprint (fun () -> "[elTerm] cD = " ^ P.mctxToString cO cD ^ "\n");
             raise (Error (Some loc, CompTypAnn ))
        | _ ->               (Printf.printf "Unification Error (7)\n" ;
             dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cO cD cPsi (tN,s'') ^ "\n");
             dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cO cD cPsi (tQ, s'') ^ " does not match expected type \n");
(*             dprint (fun () -> "[elTerm] Expected type: " ^ P.typToString cO cD cPsi sP ^ "\n");*) 
(*             dprint (fun () -> "[elTerm] cD = " ^ P.mctxToString cO cD ^ "\n"); *)
                              raise (Error (Some loc, CompTypAnn ))
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
              | _ ->               (Printf.printf "Unification Error (7)\n" ;
              raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
          end
      with  Violation msg  -> 
        dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
        raise (Error (Some loc, CompTypAnn ))
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
        dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
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
        let recA      = match tA with Int.LF.Sigma recA -> recA | _ -> 
          dprint (fun () -> "Type of Parameter variable " ^ P.headToString cO cD cPhi h ^ "not a Sigma-Type – yet used with Projection; Found " ^ P.typToString cO cD cPhi (tA, LF.id) ^ "\n illtyped\n") ;  raise (Violation "Type of Parameter variable not a Sigma-Type – yet used with Projection; illtyped\n") in 
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
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end

  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root (Some loc, Int.LF.PVar (Int.LF.Offset p, s''), tS) , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end


  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.PInst (Int.LF.PVar (p0,s0), tA, cPhi), s'), spine) -> 
      begin try 
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root(Some loc, Int.LF.PVar (p0, LF.comp s0 s''), tS)  , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end


  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (tM', tA, cPhi), s'), spine) -> 
      begin try 
        let s'' = elSub loc recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Whnf.reduce (tM', s'') tS  , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
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

  | _ -> (dprint (fun () -> "[elClosedTerm] Violation ? ") ; 
                raise (Error (None, CompTypAnn )))



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
          _ -> raise (Error (Some loc, SubIllTyped ))
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
        (
          Unify.unifyTyp cD cPsi sA' (tA, s');
          Int.LF.Dot (Int.LF.Head h', s'))
      with 
        | Error (loc, msg) -> raise (Error (loc, msg))
        |  _ -> 
           raise (Error (Some loc , TypMismatchElab (cO, cD, cPsi, sA', (tA, s'))))
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
        dprint (fun () -> "[elHead] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end 

  | Apx.LF.PVar (Apx.LF.Offset p, s) ->
      begin try 
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in 
        let s' = elSub loc recT  cO cD cPsi s cPhi in 
          (Int.LF.PVar (Int.LF.Offset p, s') , (tA, s'))
      with Violation msg  -> 
        dprint (fun () -> "[elHead] Violation: " ^ msg ^ "\n") ; 
        raise (Error (Some loc, CompTypAnn ))
      end

  | Apx.LF.PVar (Apx.LF.PInst (Int.LF.PVar (p,r), tA, cPhi), s) -> 
      begin try
        let s' = elSub loc recT  cO cD cPsi s cPhi in 
        let r' = LF.comp r s' in 
         (Int.LF.PVar (p, r') , (tA, r')) 
      with Violation msg -> 
        dprint (fun () -> "[elHead] Violation: " ^ msg ^ "\n") ; 
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

  | h -> raise (Violation (what_head h ))

(* elSpineI  recT  cO cD cPsi spine i sA  = (S : sP)
 * elSpineIW recT  cO cD cPsi spine i sA  = (S : sP)
 *
 *   where sA = (A,s) and sP = (P,s')
 *     and sA and sP in whnf
 *
 * Pre-condition:
 *   U = free variables
 *   O = meta-variables for implicit arguments
 *
 * Invariant:
 *
 * If O1 ; U1 ; (cD ; cPsi) |- spine <= [s]A  /_r (O2 ; U2) S
 * then
 *    O2 ; U2 ; [|r|](cD ; cPsi) |- S <= [|r|]([s]A) : [|r|]([s']P)
 *
 *
 * Post-condition:
 *     U2 = FV(A)  where U2 is an extension of U1 s.t. [|r|]U1,U0 = U2
 *     O2 = FMV(A) where O2 |-{U2} r <= O1

 *   U2 = extension of U1 containing all free variables of S
 *   O2 = extension of O1 containing i new meta-variables
 *            for implicit arguments
 *
 *   S is in beta-eta-normalform
 *
 * Comment: elSpineI will insert new meta-variables (as references)
 *   for omitted implicit type arguments; 
 *)
and elSpineI loc recT  cO cD cPsi spine i sA =
  elSpineIW loc recT  cO cD cPsi spine i (Whnf.whnfTyp sA) 

and elSpineIW loc recT  cO cD cPsi spine i sA  =
  if i = 0 then
    elSpine loc recT  cO cD cPsi spine sA 
  else
    match (sA, recT) with
      | ((Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s), PiRecon) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           *
           * tN = u[s']  and u::A'[.]
           *
           * s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
           *   and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)
           *)
          (* let (_, d) = Context.dctxToHat cPsi in
          let tN     = Whnf.etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift(Int.LF.NoCtxShift, d)) in   *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in
          let (spine', sP) = elSpineI loc recT  cO cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            (Int.LF.App (tN, spine'), sP)

      | ((Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _), tB), s), PiboxRecon) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           *
           * tN = u[s']  and u::P[Psi, x1:A1,....xn:An]  and A = Pi x1:A1 ... Pi xn:An.P
           *
           * s.t.  cPsi |- \x1...\xn. u[id] => [id]A  where cPsi |- id : cPsi
           *)
          let tN     = Whnf.etaExpandMMV (Some loc) cD cPsi (tA, s) LF.id in

          let (spine', sP) = elSpineI loc recT  cO cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            (Int.LF.App (tN, spine'), sP)

      (* other cases impossible by (soundness?) of abstraction *)

(* elSpine loc recT  cO cD cPsi spine sA = S
 * elSpineW cD cPsi spine sA  = S
 *   where sA = (A,s) and sA in whnf
 *
 * Pre-condition:
 *   U = free variables
 *   O = meta-variables for implicit arguments
 *
 * Invariant:
 *
 * If O ; U ; cPsi |- spine <- [s]A  (approx)
 * then
 *    O' ; U' ; cPsi |- S <- [s]A  (pre-dependent)
 *
 *
 * Post-condition:
 *   U' = extension of U containing all free variables of S
 *   O' = extension of O containing new meta-variables of S
 *)
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

(* elSpineSynth cD cPsi p_spine s' = (S, A')
 *
 * Pre-condition:
 *   U = free variables
 *   O = meta-variables for implicit arguments
 *
 * Invariant:
 *
 * If O ; U ; (cD ; cPsi) |- spine < [s]P
 *    and spine is a pattern spine
 *
 *            cD ; cPsi |- s' <= .      |cPsi| = d  and s' = ^d
 *
 *
 *            cD ; cPsi |- s   <= cPsi'
 *            Cd ;   .  |- ss' <= cPsi
 *
 * then O ; U ; (cD ; cPsi) |- S : [s']A' < [s]P
 *
 * Post-condition:
 *   U = containing all free variables of S (unchanged)
 *   O = containing new meta-variables of S (unchanged)
 *)
and elSpineSynth recT  cD cPsi spine s' sP = match (spine, sP) with
  | (Apx.LF.Nil, (_tP, _s))  ->
      let ss = LF.invert s' in
      let tQ = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in 
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
      let tA' = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi)  (tA, LF.id) (Int.LF.MShift 0, ss)
                                     (Unify.MVarRef (ref None)) in 

      let _ = dprint (fun () -> "elSpineSynth: PruneTyp done\n") in 

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth recT  cD cPsi spine (Int.LF.Dot (Int.LF.Head(Int.LF.BVar x), s')) sP in
        (*  cPsi |- tS : [s', x]tB <= sP  *)
        (*  cPsi, y:A |- tB' <= type  *)
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




(* ******************************************************************* *)
(* Shift mvars in approximate expression by k *)
(* Apply modal substitution t to approximate term
   where cD1 contains all the free modal variables in m 

   cnormApxExp e t cs = e' 

   if  cD1''      |- t <= cD @ delta  and  
       cD @ delta |- e <= apx_exp     
   the cD1''  |- |[t]|e <= apx_exp
       
*)

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
                 (* Bug fix – drop elements l_delta elements from t -bp, Aug 24, 2009
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
                let _ = dprint (fun () -> "[cnormApxTerm] ApplyMSub done – resulted in PObj  ") in 
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                  (* Bug fix – drop elements l_delta elements from t -bp, Aug 24, 2009
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
                let _ = dprint (fun () -> "[cnormApxTerm] Proj - case: ApplyMSub done – resulted in PObj  ") in 

                let _ = dprint (fun () -> "[cnormApxTerm] offset' = " ^ string_of_int offset' ^ "\n") in
                let _ = dprint (fun () -> "[cnormApxTerm] offset = " ^ string_of_int offset ^ "\n") in
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                let _ = dprint (fun () -> "[cnormApxTerm] tP = " ^ P.typToString cO cD cPhi (tP, LF.id) ^ "\n") in
                  (* Bug fix – drop elements l_delta elements from t -bp, Aug 24, 2009
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
                 raise (Violation "MObj found – expected PObj"))
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
        | _ -> (dprint (fun () -> "[cnormApxDCtx" ) ; raise NotImplemented)
      end
  | Apx.LF.DDec (psi, t_decl) -> 
      let psi' = cnormApxDCtx cO cD delta psi cDt cs in  
      let t_decl' = cnormApxTypDecl cO cD delta t_decl cDt cs in  
        Apx.LF.DDec (psi', t_decl')


let rec cnormApxExp cO cD delta e (cD'', t) cs = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, cnormApxExp' cO cD delta i (cD'', t) cs)
  | Apx.Comp.Fun (loc, f, e)    -> Apx.Comp.Fun (loc, f, cnormApxExp cO cD delta e (cD'', t) cs)
  | Apx.Comp.CtxFun (loc, g, e) -> Apx.Comp.CtxFun (loc, g, cnormApxExp cO cD delta e (cD'', t) (Ctxsub.cdot1 cs))
  | Apx.Comp.MLam (loc, u, e)   -> (dprint (fun () -> "cnormApxExp – could be PLam") ; 
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


  | Apx.Comp.Case (loc, i, branch) -> 
      Apx.Comp.Case (loc, cnormApxExp' cO cD delta i (cD'', t) cs, cnormApxBranches cO cD delta branch (cD'', t) cs)

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

(*  | Apx.Comp.Ann (e, tau) -> 
      let e' = cnormApxExp e cDt in 
      let tau' = cnormApxCTyp tau cDt in 
        Apx.Comp.Ann (e', tau')
    
*)

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
    (match b with
      | Apx.Comp.BranchBox (loc, omega, delta', (psi1 , m, Some (a, psi)), e) ->
          (* |omega| = k  –> shift cs by k ERROR bp *)
          let cs' = (match (apxget_ctxvar psi1 ) with | None -> cs | Some _ -> Ctxsub.cdot1 cs) in 
            Apx.Comp.BranchBox (loc, omega, delta', (psi1, m, Some (a, psi)),
                                cnormApxExp cO cD (append delta delta') e ((append_mctx cD'' delta'), (mvar_dot_apx t delta')) cs')
              
      | (Apx.Comp.BranchBox (loc, omega, delta', (psi, r, None), e))  ->        
          (* |omega| = k  –> shift cs by k ERROR bp *)
          let cs' = (match (apxget_ctxvar psi) with None -> cs | Some _ -> Ctxsub.cdot1 cs) in 
            Apx.Comp.BranchBox (loc, omega, delta', (psi, r, None),
                                cnormApxExp cO cD (append delta delta') e ((append_mctx cD'' delta'), mvar_dot_apx t delta') cs'))
              
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


(* Replace FMVars with appropriate de Bruijn index  
 * If a FMVar (of FPVar) occurs in fMVs do not replace it
 * since it is bound in some inner branch of a case-expression
 *
 *)
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


  (* approx. terms may already contain valid LF objects due to 
     applying the refinement substitution eagerly to the body of
     case-expressions 
     Mon Sep  7 14:08:00 2009 -bp  
  *)

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) ->  
      let s' = fmvApxSub fMVs cO cD d_param o_param s in
        (* mvar_dot t cD = t' 

           if cD1 |- t <= cD2 
           then cD1, cD |- t <= cD2, cD
        *)
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' -> 
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in 
      (* cD',cD0 ; cPhi |- tM <= tP   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0  
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
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
      (* cD',cD0 ; cPhi |- h => tA   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0  
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
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
      (* cD',cD0 ; cPhi |- h => tA   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0  
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
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

  | Apx.Comp.Case (loc, i, branch) -> 
      Apx.Comp.Case (loc, fmvApxExp' fMVs cO cD d_param o_param i, 
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
  (match b with
      | Apx.Comp.BranchBox (loc, omega, delta, (psi1, m, Some (a, psi)), e) ->
          let fMVd  = collectApxMCtx [] delta in 
          let fMVb' = collectApxTerm fMVd m in 
          let fMVb1  = collectApxDCtx fMVb' psi in
          let fMVb  = collectApxTyp fMVb1 a in
          let l    = lengthApxMCtx delta in 
          let l'    = lengthApxMCtx omega in 
          let (l_o1, l_omega, k')  = o_param in
          let o_param' = (l_o1, l_omega, k'+l') in
            Apx.Comp.BranchBox (loc, omega, delta, (psi1, m, Some (a, psi)),
                                fmvApxExp (fMVs@fMVb) cO cD (l_cd1, l_delta, (k+l)) o_param' e)
              
      | (Apx.Comp.BranchBox (loc, omega, delta, (psi, r, None), e))  ->
          let fMVd  = collectApxMCtx [] delta in 
          let fMVb' = collectApxTerm fMVd r in 
          let fMVb  = collectApxDCtx fMVb' psi in
          let l    = lengthApxMCtx delta in 
          let l'    = lengthApxMCtx omega in 
          let (l_o1, l_omega, k')  = o_param in
          let o_param' = (l_o1, l_omega, k'+l') in

            Apx.Comp.BranchBox (loc, omega, delta, (psi, r, None),
                                fmvApxExp (fMVs@fMVb) cO cD (l_cd1, l_delta, (k+l)) o_param' e))
              
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

(*    | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA1), _ ), kK), s) ->
        let u  = Whnf.newMMVar (cD, cPsi , Int.LF.TClo (tA1,s)) in
        let h  = Int.LF.MMVar (u, (Whnf.m_id, LF.id)) in 
        let tR = Int.LF.Root (None, h, Int.LF.Nil) in  (* -bp needs to be eta-expanded *)
        let _ = dprint (fun () -> "Generated meta²-variable " ^ 
                          P.normalToString Int.LF.Empty cD cPsi (tR, LF.id)) in 
        let _ = dprint (fun () -> "of type : " ^ P.dctxToString Int.LF.Empty cD cPsi ^ 
                          " |- " ^ P.typToString Int.LF.Empty cD cPsi (tA1,s)) in 
        let tS = genSpine (kK, Int.LF.Dot (Int.LF.Head h, s)) in 
        (* let tS = genSpine (kK, Int.LF.Dot (Int.LF.Obj tR , s)) in  (* -bp would not work if h is functional type *) *)
          Int.LF.App (tR, tS)
*)
    | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA1), _ ), kK), s) ->
        let tA1' = strans_typ (tA1, s) conv_list in
        let u  = Whnf.newMMVar (cD, flat_cPsi , tA1') in
        let h  = Int.LF.MMVar (u, (Whnf.m_id, s_proj)) in 
        let tR = Int.LF.Root (None, h, Int.LF.Nil) in  (* -bp needs to be eta-expanded *)
        let _ = dprint (fun () -> "Generated meta²-variable " ^ 
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
        let _   = dprint (fun () -> "[genMApp] Generated meta²-variable " ^ 
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

  | _ ->  (i, tau_t)

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

  | (e, (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      let u' = Id.mk_name Id.NoName in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in 
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u', C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
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
 

  | (Apx.Comp.Case (loc, i, branches), tau_theta) ->
      let (i', tau_theta') = genMApp loc cO cD (elExp' cO cD cG i) in
        begin match (i', C.cwhnfCTyp tau_theta') with
          | (Int.Comp.Ann (Int.Comp.Box (_ , phat,tR), _ ), 
             (Int.Comp.TypBox (_, tP, cPsi) as tau', t (* m_id *))) ->
              let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
              let _        = Unify.resetGlobalCnstrs () in 

              (* let _ = recTerm PiboxRecon cO cD cPsi (tR, LF.id) (tP, LF.id) in *)
              (if Whnf.closed (tR, LF.id)  then 
                 (* && Whnf.closedTyp (tP, LF.id) && Whnf.closedDCtx cPsi && Whnf.closedGCtx cG ? *)
                let branches' = List.map (function b -> 
                                            elBranch (IndexObj(phat, tR))
                                              cO cD cG b (tP, cPsi) tau_theta) branches in
                  Int.Comp.Case (Some loc, i', branches')
              else 
                raise (Error (Some loc, ValueRestriction (cO, cD, cG, i', (tau',t))))
              )

          | (i, (Int.Comp.TypBox (_, tP, cPsi), _mid)) -> 
              (if Whnf.closedTyp (tP, LF.id) && Whnf.closedDCtx cPsi && Whnf.closedGCtx cG then 
                 let _      = dprint (fun () -> "[elExp]" 
                             ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                             ^  "Context of expected pattern type : "
                             ^  P.dctxToString cO cD cPsi 
                             ^ "\n") in

                let branches' = List.map (function b ->  elBranch DataObj cO cD cG b (tP, cPsi) tau_theta )  branches in
                  Int.Comp.Case (Some loc, i, branches') 
                
              else 
                raise (Error (Some loc, CompScrutineeTyp (cO, cD, cG, i', (tP, LF.id), cPsi)))
              )

(*          | (i, (Int.Comp.TypSub (_, cPsi, cPhi), _mid)) -> 
              let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
              let _        = Unify.resetGlobalCnstrs () in 
                
                (if Whnf.closedDCtx cPhi && Whnf.closedDCtx cPsi && Whnf.closedGCtx cG then 
                   let _      = dprint (fun () -> "[elExp] " 
                                          ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                                          ^  "Context of expected pattern type :" 
                                          ^  P.dctxToString cO cD cPsi  ^ "[" 
                                          ^  P.dctxToString cO cD cPhi ^ "]" 
                                          ^ "\n") in

                let branches' = List.map (function b ->  elSBranch cO cD cG b (cPsi, cPhi) tau_theta )  branches in
                  Int.Comp.Case (Some loc, i, branches') 
                
              else 
                raise (Error (Some loc, CompScrutineeSubTyp (cO, cD, cG, i', cPsi, cPhi)))
              )
*)


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
               dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
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
                       (dprint (fun () -> "[elTerm] Violation: Not a head  \n") ; 
                        raise (Error (Some loc, CompTypAnn )))
                 end  
               with Violation msg -> 
                 dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
                 raise (Error (Some loc, CompTypAnn ))
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
               dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
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



(* We don't check that each box-expression has approximately
 *  the same type as the expression we analyze.
 *
 * TODO double check -bp
 *)
(* NOTE: Any context variable occurring in delta, psihat, a, psi is bound
 *  in cO !  So delta (and cD' and cD) do not contain it!
 *)

and recPattern cO cD cPsi omega delta psi m tPopt = 
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

  let _ = dprint (fun () -> ("[recPattern] Reconstruction of pattern ... type = " ^ 
                               P.typToString cO cD' cPsi' (tP', LF.id) ^ "\n")) in
  let tR = elTerm' PiboxRecon cO' cD' cPsi' m (tP', LF.id) in    

  let _  = solve_fcvarCnstr cO' cD' !fcvar_cnstr in 
  let _  = reset_fcvarCnstr () in 
  let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
  let _        = Unify.resetGlobalCnstrs () in 

  let _   = dprint (fun () -> "recPattern: Elaborated pattern ...\n" ^ P.mctxToString cO' cD' ^ "  ;   " ^
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
    ((n,k), (l_cO', l_cO1), cO', cD1', cPsi1', tR1', tP1', cs, cs')



(* and recSubPattern loc cO (cPsi, cPhi) delta psi sigma  phi = 
  let cD'     = elMCtx  PiboxRecon cO delta in
  let cPsi'   = elDCtx  PiboxRecon cO cD' psi in
  let cPhi'   = elDCtx  PiboxRecon cO cD' phi in
  let cvar1Opt = Context.ctxVar cPsi' in 
  let cO_ext = begin match cvar1Opt with 
                 | None -> cO
                 | Some (Int.LF.CtxOffset _ )      -> Int.LF.Dec(cO, Int.LF.CDeclOpt (Id.mk_name Id.NoName))
                 | Some (Int.LF.CtxName psi_name ) -> Int.LF.Dec(cO, Int.LF.CDeclOpt psi_name)
               end in
  let cs     = Ctxsub.id_csub cO_ext in 
  let cPsi0  = Ctxsub.ctxnorm_dctx (cPsi, Int.LF.CShift 1) in 
  let cPhi0  = Ctxsub.ctxnorm_dctx (cPhi, Int.LF.CShift 1) in 
  let (cO', cs) = unifyDCtx cPsi0 cPsi' (cs, cO_ext) in 
  let (cO', cs) = unifyDCtx cPhi0 cPhi' (cs, cO_ext) in 
  let _ = dprint (fun () -> "cO_ext = " ^ P.octxToString cO_ext) in 
  let _ = dprint (fun () -> "cs = " ^ P.csubToString cO' cs ) in 
  let _ = dprint (fun () -> "cO'= " ^ P.octxToString cO') in 

  let cs' = begin match (cvar1Opt, cs) with 
              | (None, _ ) -> cs 
              | (Some _ , Int.LF.CDot (_ , cs') ) -> cs'  
            end  in

  let _ = dprint (fun () -> "cs' = " ^ P.csubToString cO' cs' ) in 

  let cPsi'  = Ctxsub.ctxnorm_dctx (cPsi', cs) in 
  let cD'    = Ctxsub.ctxnorm_mctx (cD', cs) in 

  let _ = dprint (fun () -> ("[recPattern] Reconstruction of sub pattern ... range = " ^ 
                               P.dctxToString cO cD' cPsi' ^ "\n")) in

  let sigma' = elSub loc PiboxRecon cO' cD' cPsi' sigma cPhi' in     

  let _  = solve_fcvarCnstr cO' cD' !fcvar_cnstr in 
  let _  = reset_fcvarCnstr () in 
  let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
  let _        = Unify.resetGlobalCnstrs () in 

  let _   = dprint (fun () -> "recPattern: Elaborated Sub-pattern ...\n" ^ P.mctxToString cO' cD' ^ "  ;   " ^
                      P.dctxToString cO' cD' cPsi' ^ "\n   |-\n    "  ^ P.subToString cO' cD' cPsi' sigma' ^ 
                      "\n    : " ^ P.dctxToString  cO' cD' cPhi' ^ "\n") in
 
  let (cD1', cPsi1', sigma1', cPhi1') =  Abstract.abstrSubPattern cD' cPsi' sigma' cPhi' in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.octxToString cO' ^ " ; \n" ^
                          P.mctxToString cO' cD1' ^ "  ;   " ^ P.dctxToString cO' cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.subToString cO' cD1' cPsi1' sigma1' ^ "\n has type " ^
                          P.dctxToString cO' cD1' cPhi1'  ^ "\n cs = " ^ 
                          P.csubToString cO' cs ^ " : " ^ P.octxToString cO_ext ^ 
                          "\n cs' = " ^ P.csubToString cO' cs' ^ " : " ^ P.octxToString cO ^  "\n") in   
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in  
    ((n,k), cO', cD1', cPsi1', sigma1', cPhi1', cs, cs')

*)

(* synRefine cO caseT (cD, cD1) tR1 (cPsi, tP) (cPsi1, tP1) = (t, cD1', cO', cs)

   if  cO ; cD, cD1 ; cPsi  |- tP  <= type
       cO ; cD1; cPsi1 |- tP1 <= type
       cO ; cD, cD1 ; cPsi  |- tR1 <= tP      
     
   then
       cD1' |- t <= cD, cD1    and        

       cD1' |- |[t]|(|[r]|cPsi)  =   |[t]|(|[r1]|cPsi1) 
       cD1' ; |[t]|(|[r]|cPsi) |- |[t]|(|[r]|cP)  =   |[t]|(|[r1]|tP1) 

*)

and synRefine loc cO' caseT (cD, cD1) tR1 (cPsi, tP) (cPsi1, tP1) =
  begin try 
    let cD'    = Context.append cD cD1 in                   (*         cD'  = cD, cD1     *)
    let _      = dprint (fun () -> "[synRefine] cD' = " ^ P.mctxToString cO' cD' ^ "\n") in 
    let t      = mctxToMSub cD'  in                         (*         .  |- t   <= cD'   *) 
    let _      = dprint (fun () -> "[synRefine] mctxToMSub .  |- t <= cD' " ^ 
                             P.msubToString cO'  Int.LF.Empty (Whnf.cnormMSub t) ^ "\n") in 
    let n      = Context.length cD1 in 
    let m      = Context.length cD in 

    let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
      (* cD, cD1 |- t1 <= cD1 *)
    let mt1    = Whnf.mcomp t1 t in                          (*         .  |- mt1 <= cD1   *)

    let cPsi'  = Whnf.cnormDCtx (cPsi, t) in                 (*         .  |- cPsi' ctx    *)
    
    let _  = begin match caseT with
               | IndexObj (_phat, tR') -> 
                   begin try 
                     (dprint (fun () -> "Pattern matching on index object ...");
                      Unify.unify Int.LF.Empty cPsi'(C.cnorm (tR',  t),  LF.id) 
                                                    (C.cnorm (tR1, mt1), LF.id))
                   with Unify.Unify msg -> 
                     (dprint (fun () -> "Unify ERROR: " ^  msg  ^ "\n") ; 
                      raise (Violation "Pattern matching on index argument failed"))
                   end
               | DataObj -> ()
              end  in
    

    let cPsi'  = Whnf.cnormDCtx (cPsi, t) (* t *) in        (* cO' ;     .  |- cPsi' ctx    *)
    let cPsi1' = Whnf.cnormDCtx (cPsi1, mt1) in             (* cO' ;     .  |- cPsi1 ctx    *)
    let tP'    = Whnf.cnormTyp (tP, t) (* t *) in           (* cO' ; . ; cPsi'  |- tP'  <= type *) 
    let tP1'   = Whnf.cnormTyp (tP1, mt1) in                (* cO' ; . ; cPsi1' |- tP1' <= type *)
        
      (* Since |cO1| = 1, we have  cO, c01 |- cPsi'^1 ctx    *)

    let _  = begin try 
          Unify.unifyDCtx cO' (Int.LF.Empty) cPsi'  cPsi1' ;
          Unify.unifyTyp  cO' cPsi' (tP', LF.id) (tP1', LF.id); 
          dprint (fun () -> "Unify successful: \n" ^  "Inferred pattern type: "
                    ^  P.dctxToString cO' Int.LF.Empty cPsi1' ^ "    |-    "
                    ^ P.typToString cO' Int.LF.Empty cPsi1' (tP1', LF.id)
                    ^ "\nExpected pattern type: "
                    ^ P.dctxToString cO' Int.LF.Empty  cPsi1' ^ "     |-    "
                    ^ P.typToString cO' Int.LF.Empty cPsi1' (tP', LF.id))           
        with Unify.Unify msg ->
           (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n" ^  "Inferred pattern type: "
                   ^  P.dctxToString cO' Int.LF.Empty cPsi1' ^ "    |-    "
                   ^ P.typToString cO' Int.LF.Empty cPsi1' (tP1', LF.id)
                   ^ "\nExpected pattern type: "
                   ^ P.dctxToString cO' Int.LF.Empty cPsi' ^ "     |-    "
                   ^ P.typToString cO' Int.LF.Empty cPsi' (tP', LF.id))
             ; 
            raise (Error (loc, CompPattMismatch ((cO', cD1, cPsi1, tR1, (tP1, LF.id)), 
                                              (cO', cD, cPsi, (tP, LF.id)))))
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
    let cPsi1_new = Whnf.cnormDCtx (cPsi1, Whnf.mcomp t1 t') in 
        (* cD1' |- cPsi1_new ctx *)
    let tR1' = Whnf.cnorm (tR1, Whnf.mcomp t1 t') in 
        (* cD1' ; cPsi1_new |- tR1 <= tP1' *)
    let _ = dprint (fun () -> "synRefine [Show OCtx] cO' = " ^ P.octxToString cO' ) in 
    let _ = dprint (fun () -> "synRefine [Substitution] t': " ^ P.mctxToString cO' cD1' ^ 
                        "\n|-\n" ^ P.msubToString cO' cD1' t' ^ "\n <= " ^ P.mctxToString cO' cD' ^ "\n") in 
      (t0, t', cD1', cPsi1_new, tR1')
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
  | Apx.Comp.BranchBox (loc, omega, delta, (psi, m, tAopt), e) ->
      let typAnn = begin match tAopt with 
                     | None -> PartialTyp a
                     | Some (at, _psi) ->  FullTyp at
                   end in
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern ... ") in
      (* ***************  RECONSTRUCT PATTERN BEGIN *************** *)
      let ((l_cd1', l_delta), (l_cO', l_omega),
           cO', cD1', cPsi1', tM1', tP1', cs1, cs') = recPattern cO cD cPsi omega delta psi m typAnn in 

      (*  cO' ; [cs']cD, cD1' |- cs' <= cO
          cO' ; [cs']cD, cD1' |- cs1 <= cO1

          |cD1'| = l_cd1'
      *)
      (* Make sure that cO' |- cD *)
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
      let (t', t1, cD1'',cPsi1'', tR1') = 
        synRefine (Some loc) cO' caseT' (cD, cD1') tM1' (cPsi, tP) (cPsi1', tP1') in  
      (*   cD1''|-  t' : cD   and   cD1'' ; [t']cPsi |- tR1 <= [t']tP  
           cD1''|- t1  : cD, cD1'
      *)
      let (cs1, cs') = (Whnf.cnormCSub (cs1, t1) , Whnf.cnormCSub (cs', t1) ) in 
      (* *************** Synthesize Refinement Substitution *************************)
      (* Note: e is in the scope of cD, cD0 ; however, cD1' = cD1, cD0 !!   *)
      (*       e is in the scope of cO_ext *)
      let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
      let l_o1     = l_cO' - l_omega  in   (* l_cd1 is the length of cD1 *) 
      let cD'      = Context.append cD cD1' in  

      let e1       = fmvApxExp [] cO' cD' (l_cd1, l_delta, 0) (l_o1, l_omega, 0) e in   

      let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                               "\n |- \n " ^ P.msubToString cO cD1'' t' ^ 
                               " \n <= " ^ P.mctxToString cO cD ^ "\n") in 
      let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                               "\n |- \n " ^ P.msubToString cO cD1'' t1 ^ 
                               " = t1 \n") in 

      (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0 
          then cD, cD1' |- e1 apx_exp
      *)
      (* if   cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
         then cD1'' |- e' apx_exp
      *)
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
          Int.Comp.BranchBox (cO', cD1'', (cPsi1'', tR1', t', cs'), eE')

(* Before context matching ... *)

(*        if psi_hat = psi1_hat then *)
(*           Int.Comp.BranchBox (cO', cD1'', (cPsi1'', tR1', t', cs'), eE')*)
(*        else 
          raise (Error (Some loc, CompPattMismatch ((cO, cD1'', cPsi1'', tR1', (tP1', LF.id)), 
                                                    (cO, cD, cPsi, (tP, LF.id))))) 
*)           


(* and elSBranch cO cD cG branch (cPhi , cPsi) (tau, theta) = match branch with 
  | Apx.Comp.BranchSBox (loc, omega, delta, (psi, sigma, Some phi), e) -> 
      let psi_hat = Context.dctxToHat cPsi in 

      let _ = dprint (fun () -> "[elBranch] Reconstruction of sub-pattern ... ") in

      let ((l_cd1', l_delta), 
           cO', cD1', cPsi1', sigma', cPhi1', cs1, cs') = recSubPattern loc cO (cPsi, cPhi) delta psi sigma phi in 

      let psi1_hat = Context.dctxToHat cPsi1' in 
 
      let (cD, cPsi, cPhi) = (Ctxsub.ctxnorm_mctx (cD, cs'),  
                              Ctxsub.ctxnorm_dctx (cPsi, cs'), Ctxsub.ctxnorm_dctx (cPhi, cs')) in 

      let _ = dprint (fun () -> "[elBranch]" ^ "Context cD  = " ^ P.mctxToString cO' cD ^ "\n") in
      let _ = dprint (fun () -> "[elBranch]" ^ "Context cD1'  = " ^ P.mctxToString cO' cD1' ^ "\n") in
      let _ = dprint (fun () -> "cPsi' = " ^ P.dctxToString cO' cD cPsi ) in  
      let _ = dprint (fun () -> "cPsi1' = " ^ P.dctxToString cO' cD1' cPsi1' ) in

      let sigma1'    = Ctxsub.ctxnorm_sub (sigma', cs1) in 

      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern done") in
      let _ = dprint (fun () -> "[elBranch]" ^ "Context cD  = " ^ P.mctxToString cO' cD ^ "\n"
                           ^  "Context of expected pattern type : " ^  P.dctxToString cO' cD cPsi ^ "\n") in

      let (t', t1, cD1'',cPsi1'', sigma1') = 
        synRefineSubPattern (Some loc) cO'  sigma1' (cD, cPsi, cPhi) (cD1', cPsi1', cPhi1') in  
      (*   cD1''|-  t' : cD   and   cD1'' ; [t']cPsi |- tR <= [t']tP  
           cD1''|- t1  : cD, cD1'
      *)

      (* Note: e is in the scope of cD, cD0 ; however, cD1' = cD1, cD0 !!   *)
      (*       e is in the scope of cO_ext *)
      let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
      let cD'      = Context.append cD cD1' in  

      let o_param  = (0, 0, 0) in 
      let e1       = fmvApxExp [] cO' cD' (l_cd1, l_delta, 0) o_param e in   

      let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                               "\n |- \n " ^ P.msubToString cO cD1'' t' ^ 
                               " \n <= " ^ P.mctxToString cO cD ^ "\n") in 
      let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO' cD1'' ^ 
                               "\n |- \n " ^ P.msubToString cO cD1'' t1 ^ 
                               " = t1 \n") in 

      (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0 
          then cD, cD1' |- e1 apx_exp
      *)
      (* if cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
         the cD1'' |- e' apx_exp
      *)
      let e'      =  cnormApxExp cO' cD' Apx.LF.Empty e1  (cD1'', t1) cs1 in  
      (* Note: e' is in the scope of cD1''  *)
      let cG'     = Whnf.cnormCtx (cG,  t') in 
      let ttau'   = (tau, Whnf.mcomp theta t') in 
      let _       = dprint (fun () -> "[elBranch] Elaborate branch \n" ^
                             P.mctxToString cO' cD1'' ^ "  ;  " ^
                             P.gctxToString cO' cD1'' cG' ^ "\n      |-\n" ^
                             "against type " ^ P.compTypToString cO' cD1'' (C.cnormCTyp ttau') ^ "\n") in


      let eE'      = elExp cO' cD1'' cG'  e' ttau' in
      let _       = FMVar.clear () in
      let _       = FPVar.clear () in
       
        if psi_hat = psi1_hat then
          Int.Comp.BranchSBox (cO', cD1'', (cPsi1'', sigma1', t', cs'), eE')
        else 
          raise (Error (Some loc, CompSubPattMismatch ((cO, cD1'', cPsi1'', sigma1', cPhi1'), 
                                                    (cO, cD, cPsi, cPhi)))) 

  (*    raise (Violation "not implemented sbranch") *)
*)
(*
(* ******************************************************************* *)
(* check cO cD cG e (tau, theta) = ()
 *
 * Invariant:
 *
 * If  cO ; cD ; cG |- e wf-exp
 * and cO ; cD |- theta <= cD'
 * and cO ; cD'|- tau <= c_typ
 * returns ()
 * if  cO ; cD ; cG |- e <= [|t|]tau
 *
 * otherwise exception Error is raised
 *)

*)
(* ------------------------------------------------------------------- *)
let recSgnDecl d = 
    let _       = reset_fvarCnstr () in 
    let _       = FMVar.clear () in
    let _       = FPVar.clear () in
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


  | Ext.Sgn.Const (_, c, extT) ->
      let fvars    = [] in 
      let (apxT, _ ) = index_typ (CVar.create ()) (BVar.create ()) fvars extT in
      let _          = dprint (fun () -> "\nReconstructing term constant " ^ c.string_of_name ^ "\n") in
    
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

      let _c'       = Term.add (Term.mk_entry c tA' i) in
      (* let _        = Printf.printf "\n %s : %s ." (c.string_of_name) (P.typToString cO cD  Int.LF.Null (tA', LF.id)) in *)
        (* Int.Sgn.Const (c', tA') *) 
        ()       

  | Ext.Sgn.Schema (_, g, schema) ->
      (* let _       = Printf.printf "\n Indexing schema  %s  \n" g.string_of_name  (P.fmt_ppr_lf_schema  in   *)
      let apx_schema = index_schema schema in
      let _        = dprint (fun () -> "\nReconstructing schema " ^  g.string_of_name ^ "\n") in
      let cO        = Int.LF.Empty in
      let _        = FVar.clear () in
      let sW         = elSchema cO apx_schema in
      let _        = dprint (fun () -> "\nElaboration of schema " ^ g.string_of_name ) in 
      (* let _        = dprint (fun () -> " \n = " ^   (P.schemaToString sW) ^ "\n\n") in  *)

      let _        = solve_fvarCnstr PiRecon (*cO=*)Int.LF.Empty Int.LF.Empty !fvar_cnstr in
      let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 

      let _        = reset_fvarCnstr () in
      let _        = Unify.resetGlobalCnstrs () in 

      (* let _          = recSchemaWf sW in *)
      let sW'        = Abstract.abstrSchema sW in 
      let _          = Check.LF.checkSchemaWf sW' in
      let _        = dprint (fun () -> "\nTYPE CHECK for schema " ^ g.string_of_name ^ " successful\n" )  in
      let _g'         = Schema.add (Schema.mk_entry g sW') in
      let _        = Printf.printf "\nschema %s = %s.\n" (g.string_of_name) (P.schemaToString sW') in 
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

        let i''    = Monitor.timer ("Function Abstraction", fun () -> Abstract.abstrExp i') in
        let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cO cD  cG i'' (tau', C.m_id)) in

        let v  =   Opsem.eval i''  in 
        let _       = Printf.printf  "\n\nlet %s : %s = %s  \n ===>  %s \n"
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
          
        let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cO cD  cG e_r' (tau', C.m_id)) in
           (e_r' , tau')
      in 

      let rec reconRecFun recFuns = match recFuns with
        | [] -> ()
        | Ext.Comp.RecFun (f, _tau, e) :: lf -> 
            let (e_r' , tau') = reconFun f e in 
            let _       = Printf.printf  "and %s : %s = \n %s \n"
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
              let _       = Printf.printf  "\n\nrec %s : %s =\n %s \n"
                (R.render_name f)
                (P.compTypToString cO cD tau') 
                (P.expChkToString cO cD cG e_r')
                (* (P.expChkToString cO cD cG (Whnf.cnormExp (e_r', C.m_id))) *) in 
              
              let _       = dprint (fun () ->  "DOUBLE CHECK of function " ^    f.string_of_name ^  " successful!\n\n" ) in
                
              let _f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' n_list)   in
                reconRecFun lf 
          | _ -> raise (Violation "No recursive function defined\n")
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
            _ -> (print_string ("Reconstruction fails for %not'd declaration\n"); false)
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



