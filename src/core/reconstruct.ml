(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

(* TODO
 *
 * - Extension to deal with schemas
 * - Checking Schemas
 *
 * - Extension to handle sigma-types
 *    -> need to change data-type definition for typ_rec
 *
 * - Cycle detection?
 * - Code walk for reconstruction
 *)

open Store
open Store.Cid
open Syntax
open Substitution
open Error
open Id

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

let rec what_head = function
  | Apx.LF.BVar _ -> "BVar"
  | Apx.LF.Const _ -> "Const"
  | Apx.LF.MVar _ -> "MVar"
  | Apx.LF.PVar _ -> "PVar"
  | Apx.LF.Proj (head, k) -> "Proj " ^ what_head head ^ "." ^ string_of_int k
  | Apx.LF.FVar _ -> "FVar"
  | Apx.LF.FMVar _ -> "FMVar"
  | Apx.LF.FPVar _ -> "FPVar"
  | Apx.LF.CoFPVar _ -> "CoFPVar"
  | Apx.LF.CoPVar _ -> "CoPVar"

exception Violation of string

type reconType = PiboxRecon | PiRecon

type caseType  = IndexObj of Int.LF.psi_hat * Int.LF.normal | DataObj

type typAnn    = FullTyp of Apx.LF.typ | PartialTyp of cid_typ

type free_cvars = 
    FMV of Id.name | FPV of Id.name


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
        let u     = Whnf.etaExpandMMV cD cPhi (tA, LF.comp s (ctxShift cPhi)) LF.id in 
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

  | Apx.LF.CoId _ -> true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar _k), s) ->
      isPatSub s

  | Apx.LF.Dot (Apx.LF.Head _, _s) -> false

  | Apx.LF.Dot (Apx.LF.Obj  _, _s) -> false

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
        (Apx.LF.FVar n , fvars)
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

  | Ext.LF.CoPVar (loc, co_name, p_name, k, sigma) -> 
      let cid_co = try Coercion.index_of_name co_name 
                   with Not_found ->  raise (Error (Some loc, UnboundCoName co_name))   in
        begin match index_head cvars bvars fvars (Ext.LF.PVar (loc, p_name, sigma)) with
          | (Apx.LF.FPVar (p,s), fvars') -> (Apx.LF.CoFPVar (cid_co, p, k, s) , fvars')
          | (Apx.LF.PVar (p, s), fvars') -> (Apx.LF.CoPVar (cid_co, p, k, s) , fvars')
        end
        
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
  | Ext.LF.CoId (loc, co_name) -> 
      let cid_co = begin try 
                     Coercion.index_of_name co_name 
                   with Not_found -> 
                     raise (Error (Some loc, UnboundCoName co_name))
                   end 
      in
        (Apx.LF.CoId (loc, cid_co) , fvars)

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
  | Ext.LF.CoCtx (loc, co_name, psi_name) -> 
      let offset = begin try
                     CVar.index_of_name ctx_vars psi_name 
                  with Not_found ->
                    raise (Error (Some loc, UnboundCtxName psi_name)) 
                   end in
      let cid_co = begin try 
                     Coercion.index_of_name co_name 
                   with Not_found -> 
                     raise (Error (Some loc, UnboundCoName co_name))
                   end in
          (Apx.LF.CtxVar (Apx.LF.CoCtx (cid_co, Apx.LF.CtxOffset offset)) , bvars, fvars)
        (* (Apx.LF.CtxVar (Apx.LF.CtxName psi_name) , bvars) *)


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
    | Ext.LF.VarName x :: psihat ->
        let bvars' = BVar.extend bvars (BVar.mk_entry x) in
        let (l, bvars'') = index_hat bvars' psihat in
          (l + 1, bvars'')
    | _ ->  raise (Violation "Context Coercion must be applied to context variable which must occur at the beginning.\n")
  in
    begin match explicit_psihat with
      | [] -> ((None, 0), bv)
      | Ext.LF.VarName x :: psihat ->
          begin try
            let ctx_var = CVar.index_of_name ctx_vars x in
            let (d, bvars) = index_hat bv psihat in
              ((Some (Int.LF.CtxOffset ctx_var), d) , bvars)
          with Not_found ->
            let (d, bvars ) = index_hat bv explicit_psihat in
              ((None, d) , bvars)
          end

      | Ext.LF.CoName (co, psi) :: psihat ->
          begin try
            let ctx_var = CVar.index_of_name ctx_vars psi in
            let cid_co  = Coercion.index_of_name co in 
            let (d, bvars) = index_hat bv psihat in
              ((Some (Int.LF.CoCtx(cid_co, Int.LF.CtxOffset (ctx_var))), d) , bvars)
          with Not_found ->
            raise (Violation "Context Coercion Error -- either coercion was not found or coercion was not applied to context variable\n")
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
        (Apx.LF.MDecl (u, a', psi'), cvars', fvars'')

  | Ext.LF.PDecl (_, p, a, psi) ->
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
      let (a', fvars')           = index_typ  cvars bvars' fvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry p) in
        (Apx.LF.PDecl (p, a', psi') , cvars', fvars')


let rec index_mctx ctx_vars cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty , cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (delta', cvars', fvars') = index_mctx ctx_vars cvars fvars delta in
      let (cdec', cvars'', fvars'') = index_cdecl ctx_vars cvars' fvars' cdec in
        (Apx.LF.Dec (delta', cdec'), cvars'', fvars'')


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


let rec index_coe c_list = match c_list with
  | [] -> []
  | Ext.LF.CoBranch (typ_ctx, trec1, trec2_opt)  :: c_list' -> 
    let cvars = CVar.create () in
    let bvars = BVar.create () in
    let fvars = [] in 
    let (typ_ctx', bvars', _ ) = index_ctx cvars bvars fvars typ_ctx in
    let (typ_rec1', _ )        = index_typrec cvars bvars' fvars trec1 in
    let typ_rec2'_opt          = 
      match trec2_opt with 
          None -> None 
        | Some trec2 -> 
            let (trec2', _ ) = index_typrec cvars bvars' fvars trec2 in 
              Some trec2' in
    let c_list'            = index_coe c_list' in
       Apx.LF.CoBranch (typ_ctx', typ_rec1', typ_rec2'_opt) :: c_list'


(* Translation of external computations into approximate computations *)
let rec index_comptyp ctx_vars cvars  fvars = 

  function
  | Ext.Comp.TypBox (loc, a, psi)    ->
      let (psi', bvars', _ ) = index_dctx ctx_vars cvars (BVar.create ()) fvars psi in
      let (a', _ )           = index_typ cvars bvars' fvars a   in
        Apx.Comp.TypBox (loc, a', psi')

  | Ext.Comp.TypArr (_loc, tau, tau') ->
      Apx.Comp.TypArr (index_comptyp ctx_vars cvars fvars tau, 
                       index_comptyp ctx_vars cvars fvars tau')

  | Ext.Comp.TypCross (_loc, tau, tau') ->
      Apx.Comp.TypCross (index_comptyp ctx_vars cvars fvars tau, 
                         index_comptyp ctx_vars cvars fvars tau')

  | Ext.Comp.TypPiBox (_loc, cdecl, tau)    ->
      let (cdecl', cvars', _) = index_cdecl ctx_vars cvars fvars cdecl in
        Apx.Comp.TypPiBox (cdecl', index_comptyp ctx_vars cvars' fvars tau)

  | Ext.Comp.TypCtxPi (loc, (ctx_name, schema_name), tau)    ->
    begin try 
      let ctx_vars'        = CVar.extend ctx_vars (CVar.mk_entry ctx_name) in
      let schema_cid       = Schema.index_of_name schema_name in
        (* if exception Not_found is raised, it means schema_name does not exist *)
        Apx.Comp.TypCtxPi ((ctx_name, schema_cid), index_comptyp ctx_vars' cvars fvars tau)
    with 
        Not_found -> raise (Error (Some loc, UnboundCtxSchemaName schema_name))
    end


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

  | Ext.Comp.Box (loc, psihat, m) ->
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let (m', _ ) = index_term cvars bvars fvars m in 
        Apx.Comp.Box (loc, psihat', m')

  | Ext.Comp.Case (loc, i, branches) ->
      let i' = index_exp' ctx_vars cvars vars fvars i in
      let branches' = List.map (function b -> index_branch ctx_vars cvars vars fvars b) branches in
        Apx.Comp.Case (loc, i', branches')

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

  | Ext.Comp.BoxVal (loc, psi, m) ->
      let (psi', bvars, _ ) = index_dctx ctx_vars cvars  (BVar.create ()) fvars psi in
      let (m', _ ) = index_term cvars bvars fvars m in 
        Apx.Comp.BoxVal (loc, psi', m')

  | Ext.Comp.Ann (_loc, e, tau) ->
      Apx.Comp.Ann (index_exp  ctx_vars cvars vars fvars e,
                         index_comptyp ctx_vars cvars fvars tau)


and index_branch ctx_vars cvars vars fvars branch = match branch with
  | (Ext.Comp.BranchBox(loc, delta, (psi1, m, Some (a, psi)), e)) ->
    let empty_fvars = [] in 
    let (delta', cvars', fvars1)  = index_mctx ctx_vars (CVar.create()) empty_fvars delta in
(*    let (psihat', bvars) = index_psihat ctx_vars psihat in  *)
    let (psi1', bvars, fvars2)   = index_dctx ctx_vars cvars' (BVar.create ()) fvars1 psi1 in
    let (m', fvars3)             = index_term cvars' bvars fvars2 m in
    let (psi', _bvars, fvars4)   = index_dctx ctx_vars cvars' (BVar.create ()) fvars3 psi in
    (* _bvars = bvars *)
    let (a', fvars5)             = index_typ cvars' bvars fvars4 a in
    let cvars_all        = CVar.append cvars' cvars in
    let fvars6 = List.append fvars5 fvars in 
    let e'               = index_exp ctx_vars cvars_all vars fvars6 e in
      Apx.Comp.BranchBox (loc, delta', (psi1', m', Some (a', psi')), e')


  | (Ext.Comp.BranchBox(loc, delta, (psi, m, None), e)) ->
    let empty_fvars = [] in 
    let (delta', cvars', fvars1)  = index_mctx ctx_vars (CVar.create()) empty_fvars delta in
      (* let (psihat', bvars) = index_psihat ctx_vars psihat in *)
    let (psi1', bvars, fvars2)    = index_dctx ctx_vars cvars' (BVar.create ()) fvars1 psi in
    let (m', fvars3)              = index_term cvars' bvars fvars2 m in
    let cvars_all        = CVar.append cvars' cvars in
    let fvars4 = List.append fvars3 fvars in 
    let e'               = index_exp ctx_vars cvars_all vars fvars4 e in
        Apx.Comp.BranchBox (loc, delta', (psi1', m', None), e')



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

  | Apx.LF.CoId(loc, co_cid) -> 
      begin match Context.dctxToHat cPsi with
        | (Some (Int.LF.CoCtx (co_cid', psi)), d) ->
             if co_cid = co_cid' then 
               (Int.LF.CtxVar psi,  Int.LF.CoShift (Int.LF.Coe co_cid, Int.LF.NoCtxShift, d))
             else 
               raise (Error (Some loc, CoercionMismatch (co_cid, co_cid')))
        | (_ , d) ->
             raise (Error (Some loc, IllTypedCoIdSub))
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
            let tA' = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) (tA, LF.id) (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in
              ((* Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, Int.LF.TClo(tA, Substitution.LF.invert s'))), *)
                Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, tA')),
               Int.LF.Dot (Int.LF.Head(Int.LF.BVar k), s'))
(*         | _ -> raise (Violation "Undefined bound variable\n") *)
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
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let s'  = mkShift recT cPsi in 
(* let s' = LF.id in *)
      let tS = elKSpineI recT  cO cD cPsi s i (tK, s') in
        Int.LF.Atom (Some loc, a, tS)

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
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
        end

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, LF.id) in
        begin try
          (Unify.unifyTyp cD  cPsi sQ sP ;
           Int.LF.Root (Some loc, Int.LF.BVar x, tS)) 
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
              raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
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
                (let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
                 let tAvar = Int.LF.TypVar (Int.LF.TInst (ref None, cPsi, Int.LF.Typ, ref [])) in 
                    add_fvarCnstr (tAvar, m, v);
                   Int.LF.Root (Some loc, Int.LF.MVar (v, LF.id), Int.LF.Nil))
              end
            end
        | PiboxRecon -> raise (Error (Some loc, UnboundName x))
      end 
              

  | Apx.LF.Root (loc, Apx.LF.Hole, spine) ->
      begin try 
      let (_l, pat_spine) = patSpine spine in
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
            end
      with NotPatSpine -> 
          (Printf.printf "elTerm' encountered hole with non-pattern spine\n";
           raise NotImplemented)
      end
  (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) as m ->
      begin try
        let (tQ, cPhi) = FMVar.get u in
          (* For type reconstruction to succeed, we must have
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
           * meta-variables in cD. This will be enforced during abstraction *)
        let s'' = elSub recT  cO cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' --
           * this check is delayed to reconstruction *)
        let tR = Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil) in 
          begin try
            Unify.unifyTyp cD  cPsi (tQ, s'') sP ; 
            tR
          with Unify.Unify msg -> 
            (Printf.printf "%s\n" msg;
             raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), (tQ, s''), sP))))
          end
      with 
        | Not_found ->
          if isPatSub s then
          (* 1) given cPsi and s synthesize the domain cPhi
           * 2) [s]^-1 ([s']tP) is the type of u
           *)
          
          let (cPhi, s'') = synDom cD loc cPsi s in
          let ss =  Substitution.LF.invert s'' in 
          let tP = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) (Unify.MVarRef (ref None)) in
         (* let tP = Int.LF.TClo (Int.LF.TClo sP, Substitution.LF.invert s'') in *)
            (* For type reconstruction to succeed, we must have
             * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
             * This will be enforced during abstraction.
             *)
            FMVar.add u (tP, cPhi);
            Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil)
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
          
        let s'' = elSub recT  cO cD cPsi s cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
        let tR = Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), tS) in
          begin try
            Unify.unifyTyp cD cPsi sQ sP ; 
            tR
          with Unify.Unify msg -> 
            (Printf.printf "%s\n" msg;
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
            
            | (_, _) -> ((*Printf.printf "elTerm': FPVar with spine\n" ;*) raise NotImplemented)
          end
        | Violation msg  -> 
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
            raise (Error (Some loc, CompTypAnn ))
      end

  (* Reconstruct: Projection *)
  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.FPVar (p, s), k),  Apx.LF.Nil) as m ->
      (* Other case where spine is not empty is not implemented -bp *)
        begin try          
          let (Int.LF.Sigma typRec, cPhi) = FPVar.get p in
          let s'' = elSub recT  cO cD cPsi s cPhi in
          let sQ = Int.LF.getType  (Int.LF.FPVar (p, s'')) (typRec, s'') k 1 in 
            begin try
              (Unify.unifyTyp cD cPsi (Int.LF.TClo sQ, s'') sP ;
               Int.LF.Root (Some loc,  Int.LF.FPVar (p, s''),  Int.LF.Nil))
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
               raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
            end
        with Not_found ->
          begin match isPatSub s with
            | true ->
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
                  
            | false ->
                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.PVar (q, LF.id), k),  Int.LF.Nil)
          end
        end


  (* Context coercion on a free parameter variable *)
  | Apx.LF.Root (loc,  Apx.LF.CoFPVar(co_cid, p, k, s),  Apx.LF.Nil) ->
      (* Other case where spine is not empty is not implemented -bp *)
        begin try          
          let (tA, cPhi) = FPVar.get p in
          let typRec = match tA with Int.LF.Sigma typRec -> typRec | _ -> Int.LF.SigmaLast tA in 
          (* cD ; cPhi |- typRec               *)
          let sB = match Ctxsub.coeTypRec (Coercion.get_coercion co_cid) cD (cPhi, (typRec, LF.id)) with
              (Int.LF.SigmaLast nonsigma, s) -> (nonsigma, s)
            | (tBrec, s) -> (Int.LF.Sigma tBrec, s)
          in 
          let cPhi' = Ctxsub.applyCtxCoe co_cid cD cPhi in 
          let tB'   = Ctxsub.coerceTyp (Int.LF.Coe co_cid) sB in
            (* cPsi |- tB but we need however cPhi |- [s]trec2 ! *)
            (* NOTE in general: We need to find a substitution s' s.t. cPhi |- s' <= cPsi 
               and eventually return [s']([s]tB)
               This here assumes that the coercion is a one-to-one mapping, and hence
               s' is Shift 0.
        *)  
          let s'' = elSub recT  cO cD cPsi s cPhi' in     
          let sQ = match tB' with 
                    Int.LF.Sigma tBrec -> Int.LF.getType  (Int.LF.FPVar (p, s'')) (tBrec, s'') k 1 
                  | _ -> (tB', LF.id) in  
            begin try
              (Unify.unifyTyp cD cPsi sQ sP ; 
               Int.LF.Root (Some loc,  Int.LF.CoFPVar (co_cid, p, k, s''),  Int.LF.Nil))
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
               raise (Error (Some loc, TypMismatchElab (cO, cD, cPsi, sP, sQ))))
            end
        with Not_found ->
          begin match isPatSub s with
            | true ->
                let (cPhi, s'') = synDom cD loc cPsi s in
                let si          = Substitution.LF.invert s'' in
                let Some psi =  Context.ctxVar cPsi in

                let schema_cid = Schema.get_schema (Check.LF.lookupCtxVarSchema cO psi) in 
                let h = Int.LF.FPVar (p, s'') in
                let (tB, s_inst) = 
                  (* Find element some cPhi tB  in schema_cid where
                        tB = Sigma x1:A1 ... xn:An.A(n+1) 
                     s.t. there exists a substitution s_inst for the variables in cPhi s.t.

                   and [s_inst][proj_1 h/x_1 ... proj_(k-1) h/x_(k-1)] A_k = sP

                  *)
                  begin match synSchemaElem recT  cO cD cPsi sP (h, k) schema_cid with
                  | None -> raise (Violation ("type sP not in psi's schema")) 
                  | Some (Int.LF.SigmaLast tA, subst) -> (tA, subst) 
                  | Some (typRec', subs) -> (Int.LF.Sigma typRec', subs)
                  end in       
                (* coerceType co_cid tB_invcoe = (tB, s_inst) *)

                let tB' = Unify.pruneTyp cD cPsi (*?*) (Context.dctxToHat cPsi) (tB, s_inst)
                                        (Int.LF.MShift 0, si) (Unify.MVarRef (ref None)) in 

                 (* r is a pruning substitution s.t. [si]([|r|]tB) = tB' and 
                    where     cPhi |- si <= cPsi
                 *)

                let tB_invcoe =  Ctxsub.coerceTyp (Int.LF.InvCoe co_cid) (tB', LF.id) in
                let cPhi_invcoe  = Ctxsub.applyInvCtxCoe co_cid cD cPhi in 

                  FPVar.add p (tB_invcoe, cPhi_invcoe);
                  Int.LF.Root (Some loc,  Int.LF.CoFPVar (co_cid, p, k, s''),  Int.LF.Nil) 
                  
            | false ->
                raise (Violation "Delaying coerced parameter variables not implemented ")
(*                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.PVar (q, LF.id), k),  Int.LF.Nil)*)
          end
        end

  (* Reconstruction for meta-variables  *)
  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (tN, tQ, cPhi), s'), Apx.LF.Nil) ->
      let s'' = elSub recT  cO cD cPsi s' cPhi in
        begin try
          (* This case only applies to Beluga; MInst are introduced during cnormApxTerm. *)
          ( Unify.unifyTyp cD  cPsi (tQ, s'') sP ; 
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
      end
        
  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset u, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxMDec cD u in
        let s'' = elSub recT  cO cD cPsi s' cPhi in
        let (tS, sQ) = elSpine loc recT  cO cD cPsi spine (tA, s'') in
        let tR = Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset u, s''), tS) in 
          begin try
            (Unify.unifyTyp cD cPsi sQ sP ; 
            tR) 
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
              raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP))))
          end
      with  Violation msg  -> 
        dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
        raise (Error (Some loc, CompTypAnn ))
      end

  (* Reconstruction for parameter variables *)
  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s'), spine) ->
      begin try
        let s'' = elSub recT  cO cD cPsi s' cPhi in
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
            
      with Violation msg  -> 
        dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
        raise (Error (Some loc, CompTypAnn ))
        (* raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP)))*)
      end


  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p,s'), spine) ->
      begin try 
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub recT  cO cD cPsi s' cPhi in
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
            let t' = elSub recT cO cD  cPsi t cPsi' in 
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


  | Apx.LF.Root (loc, Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, Int.LF.Sigma recA, cPhi), s'), k), spine) ->
      begin try
        let s''       = elSub recT  cO cD cPsi s' cPhi in
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
            
      with Violation msg  -> 
        dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
        raise (Error (Some loc, CompTypAnn ))
        (* raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP)))*)
      end


  (* Reconstruction of coerced parameter variables *)
  | Apx.LF.Root (loc, Apx.LF.CoPVar (co_cid, Apx.LF.PInst (h, tA, cPhi), j, s'), spine) ->
      begin try
        let cPhi' = Ctxsub.applyCtxCoe co_cid cD cPhi in 
        let s'' = elSub recT  cO cD cPsi s' cPhi' in

        let typRec = match tA with Int.LF.Sigma typRec -> typRec
                            | _ -> Int.LF.SigmaLast tA in 
          (* cD ; cPhi |- typRec               *)
        let sB = match Ctxsub.coeTypRec (Coercion.get_coercion co_cid) cD (cPhi, (typRec, LF.id)) with
                     (Int.LF.SigmaLast nonsigma, s) -> (nonsigma, s)
                   | (tBrec, s) -> (Int.LF.Sigma tBrec, s)
          in 

        let _ = dprint (fun () -> "[elTerm'] h = " ^ P.headToString cO cD cPhi h ^ "\n") in 
        let _ = dprint (fun () -> "[elTerm'] s'' = " ^ P.subToString cO cD cPsi s''  ^ "\n") in 
        let _ = dprint (fun () -> "[elTerm' CoPVar PInst ] j = " ^ string_of_int j ^ "\n") in 
        let h' = match h with 
                   Int.LF.PVar (Int.LF.Offset q, r) -> 
                     (* Int.LF.PVar (Int.LF.Offset q, LF.comp r s'') *)
                     Int.LF.PVar (Int.LF.Offset q, LF.comp (Ctxsub.coerceSub (Int.LF.Coe co_cid) r) s'')
                 | _ -> raise (Violation "[elTerm'] CoPVar (PInst BVar _ )") in

        let tB'   = Ctxsub.coerceTyp (Int.LF.Coe co_cid) sB in 
        let sB_j  = match tB' with Int.LF.Sigma tBrec -> Int.LF.getType h' (tBrec, s'') j 1 
                                 | _ -> (tB', s'') in
                 

        (* let sA  =  match tA with Int.LF.Sigma tArec -> Int.LF.getType h (tArec, s'') j 1 
                               | tA -> (tA, s'') in *)
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine sB_j  in
        let _ = Unify.unifyTyp cD cPsi sQ sP  in
          begin match h with 
            (*  | Int.LF.BVar k -> 
                  begin match LF.bvarSub k s'' with 
                    | Int.LF.Head (Int.LF.BVar x) -> 
                        if j = 0 then 
                          Int.LF.Root (Some loc, Int.LF.BVar x, tS)
                        else 
                          Int.LF.Root (Some loc, Int.LF.Proj(Int.LF.BVar x, j), tS)
                    | Int.LF.Head (Int.LF.PVar (p,r'))   -> 
                        Int.LF.Root (Some loc, Int.LF.CoPVar (co_cid, p, j, LF.comp r' s''), tS)
                  end *)
              | Int.LF.PVar (p, r) -> 
                  let _ = dprint (fun () -> "[elTerm' (2)] j = " ^ string_of_int j ^ "\n") in 
                  Int.LF.Root (Some loc, Int.LF.CoPVar (co_cid, p, j, LF.comp r s''), tS)
              | _ -> raise (Violation "[elTerm'] CoPVar (PInst BVar _ )") 
            end              
            
      with Violation msg  -> 
        dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
        raise (Error (Some loc, CompTypAnn ))
        (* raise (Error (Some loc, TypMismatch (cO, cD, cPsi, (tR, LF.id), sQ, sP)))*)
      end


  | Apx.LF.Root (loc, Apx.LF.CoPVar (co_cid, Apx.LF.Offset p,j, s'), spine) ->
      begin try 
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let _ = dprint (fun () -> "[elTerm' CoPVar Offset] j = " ^ string_of_int j ^ "\n") in 
        let cPhi' = Ctxsub.applyCtxCoe co_cid cD cPhi in 
        let s'' = elSub recT  cO cD cPsi s' cPhi' in

        let typRec = match tA with Int.LF.Sigma typRec -> typRec
                            | _ -> Int.LF.SigmaLast tA in 
          (* cD ; cPhi |- typRec               *)
        let sB = match Ctxsub.coeTypRec (Coercion.get_coercion co_cid) cD (cPhi, (typRec, LF.id)) with
                     (Int.LF.SigmaLast nonsigma, s) -> (nonsigma, s)
                   | (tBrec, s) -> (Int.LF.Sigma tBrec, s)
          in 

        let h = Int.LF.PVar (Int.LF.Offset p, s'') in 

        let tB'   = Ctxsub.coerceTyp (Int.LF.Coe co_cid) sB in
        let sB_j  = match tB' with Int.LF.Sigma tBrec -> Int.LF.getType h (tBrec, s'') j 1 
                                 | _ -> (tB', s'') in
                 


        let (tS, sQ) = elSpine loc recT  cO cD cPsi spine sB_j  in
        let tR = Int.LF.Root (Some loc, Int.LF.CoPVar (co_cid, Int.LF.Offset p, j, s''), tS) in 
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

  | Apx.LF.Root (loc, Apx.LF.CoPVar _, _) ->
      raise (Violation "[elTerm'] CoPVar ")

  | Apx.LF.Root (loc, Apx.LF.CoFPVar _, _) ->
      raise (Violation "[elTerm'] CoFPVar ")
  | Apx.LF.Root (loc, Apx.LF.Proj _, _) ->
      raise (Violation "[elTerm'] Proj ")

  | Apx.LF.Root (loc, Apx.LF.PVar _, _) ->
      raise (Violation "[elTerm'] PVar ")

  | Apx.LF.Root (loc, h, _s) -> 
      (dprint (fun () -> "[elTerm'] h = " ^ what_head h ^ "\n") ;
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
        let s'' = elSub recT  cO cD cPsi s cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset u, s''), tS) , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end

  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Int.LF.Root (Some loc, Int.LF.PVar (Int.LF.Offset p, s''), tS) , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end
  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (tM', tA, cPhi), s'), spine) -> 
      begin try 
        let s'' = elSub recT  cO cD cPsi s' cPhi in
        let (tS, sQ ) = elSpine loc recT  cO cD cPsi spine (tA, s'')  in
          (Whnf.reduce (tM', s'') tS  , sQ)
      with Violation msg  -> 
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg ^ "\n") ; 
         raise (Error (Some loc, CompTypAnn ))
      end

  | Apx.LF.Root (loc, _ , _ ) ->
      raise (Error (Some loc, CompTypAnn ))

  | Apx.LF.Lam (loc, _, _ ) -> 
      raise (Error (Some loc, CompTypAnn ))


(* elSub recT  cO cD cPsi s cPhi = s'
 *
 *)
and elSub recT  cO cD cPsi s cPhi =
  match (s, cPhi) with
  | (Apx.LF.EmptySub, Int.LF.Null) ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) -> Int.LF.Shift (Int.LF.CtxShift psi, d)
        | (None, d)     -> Int.LF.Shift (Int.LF.NoCtxShift, d)
      end

  | (Apx.LF.CoId (loc, coe_cid), Int.LF.CtxVar phi) ->
      begin match Context.dctxToHat cPsi with
        | (Some (Int.LF.CoCtx(coe_cid', psi)), d) ->
             if coe_cid = coe_cid'  then 
               (* check coercions maps phi to psi *)
               (*               let schema2 = Context.lookupSchema cO c2 in *)
               let Int.LF.CoTyp(_a_schema, b_schema) = Coercion.get_coercionTyp coe_cid in 
               (* let schema = Check.LF.synCtxSchema cO phi in 
               let _ = (print_string ("[SynCtxSchema] schema = " ^ R.render_cid_schema schema ^ " of phi = " ^ P.dctxToString cO cD cPhi ^ "\n") ; flush_all ()) in
               let _ = (print_string ("coercion :  " ^ R.render_cid_schema a_schema ^ " –> " ^ R.render_cid_schema b_schema ^ "\n") ; flush_all ()) in
               let _ = (print_string ("[checkCoercion] psi = " ^ P.dctxToString cO cD cPsi  ^ " : " ^ R.render_cid_schema a_schema ^  "\n") ; flush_all ()) in *)
                 (if Check.LF.checkCoercion cO (psi, b_schema) phi  then                    
                   Int.LF.CoShift(Int.LF.Coe coe_cid, Int.LF.NoCtxShift, d)
                 else 
               raise (Violation ("elSub: Cannot coerce " ^ P.dctxToString cO cD cPhi ^ 
                                   " \n to " ^ P.dctxToString cO cD cPsi ^ "\n")))
             else 
               raise (Violation ("elSub: coe_Id must be associated with same coercion on ctxvar: \n" ^ 
                                   "Found context coercion " ^ R.render_cid_coercion coe_cid ^ 
                                   "\nExpected: " ^ R.render_cid_coercion coe_cid' ^ "\n"))
        | (None, _ ) -> 
               raise (Violation ("elSub: coe_Id must be associated with same coercion on ctxvar: \n" ^ 
                                   "Found countext" ^ P.dctxToString cO cD cPsi ^ " \n and coercion " ^
                                   R.render_cid_coercion coe_cid ^ "\n")) 
      end

  | (Apx.LF.Id, Int.LF.CtxVar phi) ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            if psi = phi then
              Int.LF.Shift(Int.LF.NoCtxShift, d)
            else
              raise (Violation ("elSub: Id must be associated with same ctxvar: "
                                ^ "`" ^ P.dctxToString cO cD cPhi ^ "' does not match `" ^ 
                                P.dctxToString cO cD cPsi ^ "'"))
                
        | _ ->
            raise (Violation "Id must be associated with ctxvar")
      end


  | (Apx.LF.Dot (Apx.LF.Head h, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl (_, tA))) ->
      (* NOTE: if decl = x:A, and cPsi(h) = A' s.t. A =/= A'
       *       we will fail during reconstruction / type checking
       *)
      let h' = elHead recT  cO cD cPsi h in 
      let s' = elSub recT  cO cD cPsi s cPhi' in 
      let sA' =   begin match h' with
        | Int.LF.BVar x -> 
            let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
              (tA' , LF.id)
        | Int.LF.Proj (Int.LF.BVar x, projIndex) -> 
            let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
             begin match Whnf.whnfTyp (tA', LF.id) with
                | (Int.LF.Sigma tA'rec, s') ->
                    Int.LF.getType (Int.LF.BVar x) (tA'rec, s') projIndex 1 
                | (tA',s') -> raise (Violation ("[elSub] expected Sigma type  " 
                                                ^ "found type " ^ P.typToString cO cD cPsi (tA', s')))
             end

      end       
      in 
        (
          Unify.unifyTyp cD cPsi sA' (tA, s');
          Int.LF.Dot (Int.LF.Head h', s'))

  | (Apx.LF.Dot (Apx.LF.Obj m, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl(_, tA))) ->
      let s' = elSub recT  cO cD cPsi s cPhi' in
      let m' = elTerm recT  cO cD cPsi m (tA, s') in
        Int.LF.Dot (Int.LF.Obj m', s')


  | (_s, cPhi) ->

        let rec p_sub s = match s with Apx.LF.EmptySub -> " . "  
          | Apx.LF.Id -> " id " | 
          Apx.LF.Dot(Apx.LF.Head h , s') -> ("Dot "^ what_head h) ^ p_sub s'| _ -> " _ " in 
      let s_string = p_sub s in

      raise (Violation ("elSub: substitution is ill-typed : range " ^ 
                          P.dctxToString cO cD cPsi ^ "\n domain " ^ P.dctxToString cO cD cPhi ^ "\n" ^  
                       "s = " ^ s_string ^ "\n"))


and elHead recT  cO cD cPsi = function
  | Apx.LF.BVar x ->
      Int.LF.BVar x

  | Apx.LF.Const c ->
      Int.LF.Const c

  | Apx.LF.MVar (Apx.LF.Offset u, s) ->
      let (_ , _tA, cPhi) = Whnf.mctxMDec cD u in
        Int.LF.MVar (Int.LF.Offset u, elSub recT  cO cD cPsi s cPhi)

  | Apx.LF.PVar (Apx.LF.Offset p, s) ->
      let (_, _tA, cPhi) = Whnf.mctxPDec cD p in
        Int.LF.PVar (Int.LF.Offset p, elSub recT  cO cD cPsi s cPhi)

  | Apx.LF.FVar x ->
      Int.LF.FVar x

  | Apx.LF.FMVar (u, s) ->      
      begin try 
        let (offset, (_tP, cPhi)) = Whnf.mctxMVarPos cD u  in
        Int.LF.MVar (Int.LF.Offset offset, elSub recT  cO cD cPsi s cPhi)
      with Whnf.Fmvar_not_found -> 
       raise (Error (None, UnboundName u))
      end 


  | Apx.LF.FPVar (p, s) ->
      let (offset, (_tA, cPhi)) = Whnf.mctxPVarPos cD p  in
        Int.LF.PVar (Int.LF.Offset offset, elSub recT  cO cD cPsi s cPhi)

  | Apx.LF.Proj (head, i) ->
      let head' = elHead recT  cO cD cPsi head in
        Int.LF.Proj (head', i)


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
          let tN     = Whnf.etaExpandMMV cD cPsi (tA, s) LF.id in

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
          let tN     = Whnf.etaExpandMMV cD cPsi (tA, s) LF.id in
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
      ((*.printf "elKSpine: spine ill-kinded\n";*)
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

let rec elCoercion c_list  = match c_list with
  | [] -> []
  | Apx.LF.CoBranch (typ_ctx, trec1, trec2_opt) :: c_list' -> 
    let cO = Int.LF.Empty in
    let cD = Int.LF.Empty in

   let el_ctx = elTypDeclCtx cO cD typ_ctx in
   let dctx = projectCtxIntoDctx el_ctx in

   let trec1' = elTypRec PiRecon cO cD dctx trec1 in
   let trec2'_opt = match trec2_opt with None -> None | Some trec2 -> Some (elTypRec PiRecon cO cD dctx trec2) in
   let c_list' = elCoercion c_list' in 
     Int.LF.CoBranch (el_ctx, trec1', trec2'_opt) :: c_list'

let rec elCtxVar c_var = match c_var with 
  | Apx.LF.CtxOffset offset  -> Int.LF.CtxOffset offset
  | Apx.LF.CtxName psi       -> Int.LF.CtxName psi
  | Apx.LF.CoCtx (co, c_var) -> Int.LF.CoCtx (co, elCtxVar c_var)


let rec elDCtx recT  cO cD psi = match psi with
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar (c_var) -> Int.LF.CtxVar(elCtxVar c_var)

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


let rec elMCtx recT cO delta = match delta with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (delta, cdec) ->
      let cD    = elMCtx recT cO delta in
      let cdec' = elCDecl recT cO cD cdec in
        Int.LF.Dec (cD, cdec')


(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr recT cO cD cnstr = match cnstr with
  | [] -> ()
  | ((_ , Apx.LF.Root (loc, Apx.LF.FVar x, spine), Int.LF.Inst ({contents = None} as r, cPsi, tP, _)) :: cnstrs) ->
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
            raise (Error (None, LeftoverConstraints x))
      end


  | ((_ , Apx.LF.Root (loc, Apx.LF.FVar x, spine), Int.LF.Inst ({contents = Some tR}, cPsi, tP, _ )) :: cnstrs) ->
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
            raise (Error (None, LeftoverConstraints x))
      end



(* Solve free variable constraints *)

let rec solve_fcvarCnstr cO cD cnstr = match cnstr with
  | [] -> ()
  | ((Apx.LF.Root (loc, Apx.LF.FMVar (u,s), _nil_spine), Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let (_tP, cPhi) = FMVar.get u in
        let s'' = elSub PiboxRecon cO cD cPsi s cPhi in
          r := Some (Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil));
          solve_fcvarCnstr cO cD cnstrs
      with Not_found ->
        raise (Error (None, LeftoverConstraints u))
      end

  | ((Apx.LF.Root (loc, Apx.LF.FPVar (x,s), spine), Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let (tA, cPhi) = FPVar.get x in
        let s'' = elSub PiboxRecon cO cD cPsi s cPhi in

        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let (tS, _ ) = elSpine loc PiboxRecon cO cD cPsi spine (tA, s'') in
          r := Some (Int.LF.Root (Some loc, Int.LF.FPVar (x,s''), tS));
          solve_fcvarCnstr cO cD cnstrs
      with Not_found ->
        raise (Error (None, LeftoverConstraints x))
      end




(* ******************************************************************* *)
(* Shift mvars in approximate expression by k *)
(* Apply modal substitution t to approximate term
   where cD1 contains all the free modal variables in m 

   cnormApxExp e t = e' 

   if  cD1''      |- t <= cD @ delta  and  
       cD @ delta |- e <= apx_exp     
   the cD1''  |- |[t]|e <= apx_exp
       
*)

let rec cnormApxTerm cO cD delta m (cD'', t) = match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, cnormApxTerm cO cD delta m' (cD'', t) )

  | Apx.LF.Root (loc, h, s) -> 
      let h' = cnormApxHead cO cD delta h (cD'', t) in 
      let s' = cnormApxSpine cO cD delta s (cD'', t) in 
        Apx.LF.Root (loc, h', s')
  | Apx.LF.Tuple (loc, tuple) -> 
      Apx.LF.Tuple(loc, cnormApxTuple cO cD delta tuple (cD'', t))

and cnormApxTuple cO cD delta tuple (cD'', t) = match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (cnormApxTerm cO cD delta m (cD'' , t))
  | Apx.LF.Cons (m, tuple) -> 
      Apx.LF.Cons (cnormApxTerm cO cD delta m (cD'' , t),
                   cnormApxTuple cO cD delta tuple (cD'', t))


and cnormApxHead cO cD delta h (cD'', t) = match h with
  | Apx.LF.MVar (Apx.LF.Offset offset, s) ->
      let l_delta = lengthApxMCtx delta in 
      let offset' = (offset - l_delta)  in 
        if offset > l_delta then 
          begin match LF.applyMSub offset  t with
            | Int.LF.MV u ->  
                Apx.LF.MVar (Apx.LF.Offset u, cnormApxSub cO cD delta s (cD'', t))
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
                               cnormApxSub cO cD delta s (cD'', t))
          end
        else 
          Apx.LF.MVar (Apx.LF.Offset offset, cnormApxSub cO cD delta s (cD'', t))

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) -> 
      let tM' = Whnf.cnorm (tM,t) in 
      let (tP', cPhi')  = (Whnf.cnormTyp (tP, t), Whnf.cnormDCtx (cPhi, t)) in 

      let s' = cnormApxSub cO cD delta s (cD'', t) in  
        Apx.LF.MVar (Apx.LF.MInst (tM', tP', cPhi'), s')  

  | Apx.LF.PVar (Apx.LF.Offset offset, s) -> 
      let l_delta = lengthApxMCtx delta in 
      let offset' = (offset - l_delta)  in 
        if offset > l_delta then 
          begin match LF.applyMSub offset t with
            | Int.LF.MV offset' ->  Apx.LF.PVar (Apx.LF.Offset offset', cnormApxSub cO cD delta s (cD'', t))
            | Int.LF.PObj (_phat, h) -> 
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
                               cnormApxSub cO cD delta s (cD'', t))
          end
        else 
          Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cO cD delta s (cD'', t))


  | Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s) -> 
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in 
      let s' = cnormApxSub cO cD delta s (cD'', t) in 
      let h' = begin match h with 
               | Int.LF.BVar _ -> h 
               | Int.LF.PVar (Int.LF.Offset q, s1) -> 
                   let Int.LF.MV q' = LF.applyMSub q t in 
                   let s1' = Whnf.cnormSub (s1, t) in 
                     Int.LF.PVar (Int.LF.Offset q', s1') 
               end in 
        Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s')

  | Apx.LF.FMVar(u, s) -> 
      Apx.LF.FMVar(u, cnormApxSub cO cD delta s (cD'', t))

  | Apx.LF.FPVar(u, s) -> 
      Apx.LF.FPVar(u, cnormApxSub cO cD delta s (cD'', t))

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, s), j) -> 
      let l_delta = lengthApxMCtx delta in  
      let offset' = (offset - l_delta)  in 
        if offset > l_delta then 
          begin match LF.applyMSub offset t with
            | Int.LF.MV offset' ->  
                Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset offset', 
                                         cnormApxSub cO cD delta s (cD'', t)), 
                            j)
            | Int.LF.PObj (_phat, h) -> 
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                  (* Bug fix – drop elements l_delta elements from t -bp, Aug 24, 2009
                     Given cD'' |- t : cD, l_delta 
                     produce t' s.t. cD'' |- t' : cD   and t',t_delta = t
                     
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 

                let t' = drop t l_delta in
                  Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')), 
                                           cnormApxSub cO cD delta s (cD'', t)),
                              j) 
          end
        else 
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cO cD delta s (cD'', t)), j)

  | Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) -> 
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in 
      let s' = cnormApxSub cO cD delta s (cD'', t) in 
      let h' = begin match h with 
               | Int.LF.BVar _ -> h 
               | Int.LF.PVar (Int.LF.Offset q, s1) -> 
                   let Int.LF.MV q' = LF.applyMSub q t in 
                   let s1' = Whnf.cnormSub (s1, t) in 
                     Int.LF.PVar (Int.LF.Offset q', s1') 
               end in 
        Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s'), j)
        

  | Apx.LF.CoPVar (co_cid, Apx.LF.PInst (h, tA, cPhi), j, s) -> 
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in 
      let _ = dprint (fun () -> "cnormApxHead (CoPVar PInst ) : j = " ^ string_of_int j ^ "\n") in
      let s' = cnormApxSub cO cD delta s (cD'', t) in 
      let h' = begin match h with 
               | Int.LF.BVar _ -> h 
               | Int.LF.PVar (Int.LF.Offset q, s1) -> 
                   let Int.LF.MV q' = LF.applyMSub q t in 
                   let s1' = Whnf.cnormSub (s1, t) in 
                     Int.LF.PVar (Int.LF.Offset q', s1') 
               end in 
        Apx.LF.CoPVar (co_cid, Apx.LF.PInst (h', tA', cPhi'), j , s')      

  | Apx.LF.CoPVar (co_cid, Apx.LF.Offset offset, j, s) -> 
      let _ = dprint (fun () -> "cnormApxHead (CoPVar Offset) : j = " ^ string_of_int j ^ "\n") in
      let l_delta = lengthApxMCtx delta in  
      let offset' = (offset - l_delta)  in 
        if offset > l_delta then 
          begin match LF.applyMSub offset t with
            | Int.LF.MV offset' ->  
                Apx.LF.CoPVar (co_cid, Apx.LF.Offset offset', j,
                               cnormApxSub cO cD delta s (cD'', t)) 

            | Int.LF.PObj (_phat, h) -> 
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                  (* Bug fix – drop elements l_delta elements from t -bp, Aug 24, 2009
                     Given cD'' |- t : cD, l_delta 
                     produce t' s.t. cD'' |- t' : cD   and t',t_delta = t
                     
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 

                let t' = drop t l_delta in
                  Apx.LF.CoPVar (co_cid, Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')), j, 
                                           cnormApxSub cO cD delta s (cD'', t))

          end
        else 
          Apx.LF.CoPVar (co_cid, Apx.LF.Offset offset, j, cnormApxSub cO cD delta s (cD'', t))


  | _ -> h

and cnormApxSub cO cD delta s (cD'', t) = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id       -> s
  | Apx.LF.CoId _   -> s
  | Apx.LF.Dot (Apx.LF.Head h, s) -> 
      let h' = cnormApxHead cO cD delta h (cD'', t) in 
      let s' = cnormApxSub cO cD delta s (cD'', t) in 
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) -> 
      let m' = cnormApxTerm cO cD delta m (cD'', t) in 
      let s' = cnormApxSub cO cD delta s (cD'', t) in 
        Apx.LF.Dot (Apx.LF.Obj m', s')


and cnormApxSpine cO cD delta s (cD'', t) = match s with 
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) -> 
      let s' = cnormApxSpine cO cD delta s (cD'', t) in 
      let m' = cnormApxTerm cO cD delta m (cD'', t) in 
        Apx.LF.App (m' , s')

let rec cnormApxTyp cO cD delta a (cD'', t) = match a with
  | Apx.LF.Atom (loc, c, spine) -> 
      Apx.LF.Atom (loc, c, cnormApxSpine cO cD delta spine (cD'', t))

  | Apx.LF.PiTyp ((t_decl, dep), a) -> 
      let t_decl' = cnormApxTypDecl cO cD delta t_decl (cD'', t) in 
      let a' = cnormApxTyp cO cD delta a (cD'', t) in 
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = cnormApxTypRec cO cD delta typ_rec (cD'', t) in
        Apx.LF.Sigma typ_rec'

and cnormApxTypDecl cO cD delta t_decl cDt = match t_decl with
  | Apx.LF.TypDecl (x, a) -> 
      Apx.LF.TypDecl(x, cnormApxTyp cO cD delta a cDt)

and cnormApxTypRec cO cD delta t_rec (cD'', t) = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (cnormApxTyp cO cD delta a (cD'', t))
  | Apx.LF.SigmaElem (x, a, t_rec) -> 
      let a' = cnormApxTyp cO cD delta a (cD'', t) in 
      let t_rec' = cnormApxTypRec cO cD delta t_rec (cD'', t) in 
        Apx.LF.SigmaElem (x, a', t_rec')

let rec cnormApxDCtx cO cD delta psi (cDt : Syntax.Int.LF.mctx * Syntax.Int.LF.msub) = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar _ -> psi 
  | Apx.LF.DDec (psi, t_decl) -> 
      let psi' = cnormApxDCtx cO cD delta psi cDt in  
      let t_decl' = cnormApxTypDecl cO cD delta t_decl cDt in  
        Apx.LF.DDec (psi', t_decl')


let rec cnormApxExp cO cD delta e (cD'', t) = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, cnormApxExp' cO cD delta i (cD'', t))
  | Apx.Comp.Fun (loc, f, e)    -> Apx.Comp.Fun (loc, f, cnormApxExp cO cD delta e (cD'', t))
  | Apx.Comp.CtxFun (loc, g, e) -> Apx.Comp.CtxFun (loc, g, cnormApxExp cO cD delta e (cD'', t))
  | Apx.Comp.MLam (loc, u, e)   -> Apx.Comp.MLam (loc, u, cnormApxExp cO cD delta e (cD'', Whnf.mvar_dot1 t))
  | Apx.Comp.Pair (loc, e1, e2) -> 
      let e1' = cnormApxExp cO cD delta e1 (cD'', t) in 
      let e2' = cnormApxExp cO cD delta e2 (cD'', t) in 
        Apx.Comp.Pair (loc, e1', e2')
  | Apx.Comp.LetPair (loc, i, (x,y, e)) -> 
      let i' = cnormApxExp' cO cD delta i (cD'', t) in 
      let e' = cnormApxExp  cO cD delta e (cD'', t) in 
        Apx.Comp.LetPair (loc, i', (x,y, e')) 

  | Apx.Comp.Box(loc, phat, m) -> 
      Apx.Comp.Box (loc, phat, cnormApxTerm cO cD delta m (cD'', t))
  | Apx.Comp.Case (loc, i, branch) -> 
      Apx.Comp.Case (loc, cnormApxExp' cO cD delta i (cD'', t), cnormApxBranches cO cD delta branch (cD'', t))

and cnormApxExp' cO cD delta i cDt = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.Const _c -> i
  | Apx.Comp.Apply (loc, i, e) -> 
      let i' = cnormApxExp' cO cD delta i cDt in 
      let e' = cnormApxExp cO cD delta e cDt in 
        Apx.Comp.Apply (loc, i', e')
  | Apx.Comp.CtxApp (loc, i, psi) -> 
      let i' = cnormApxExp' cO cD delta i cDt in 
      let psi' = cnormApxDCtx cO cD delta psi cDt in 
        Apx.Comp.CtxApp (loc, i', psi')

  | Apx.Comp.MApp (loc, i, (phat, m)) -> 
      let i' = cnormApxExp' cO cD delta i cDt in 
      let m' = cnormApxTerm cO cD delta m cDt in
        Apx.Comp.MApp (loc, i', (phat, m'))

  | Apx.Comp.BoxVal (loc, psi, m) -> 
      let psi' = cnormApxDCtx cO cD delta psi cDt in 
      let m'   = cnormApxTerm cO cD delta m cDt in 
        Apx.Comp.BoxVal (loc, psi', m')

(*  | Apx.Comp.Ann (e, tau) -> 
      let e' = cnormApxExp e cDt in 
      let tau' = cnormApxCTyp tau cDt in 
        Apx.Comp.Ann (e', tau')
    
*)


and cnormApxBranches cO cD delta branches cDt = match branches with
  | [] -> []
  | b::bs -> (cnormApxBranch cO cD delta b cDt)::(cnormApxBranches cO cD delta bs cDt)

and cnormApxBranch cO cD delta b (cD'', t) = 
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
      | Apx.Comp.BranchBox (loc, delta', (psi1, m, Some (a, psi)), e) ->
            Apx.Comp.BranchBox (loc, delta', (psi1, m, Some (a, psi)),
                                cnormApxExp cO cD (append delta delta') e ((append_mctx cD'' delta'), (mvar_dot_apx t delta')))
              
      | (Apx.Comp.BranchBox (loc, delta', (psi, r, None), e))  ->
            Apx.Comp.BranchBox (loc, delta', (psi, r, None),
                                cnormApxExp cO cD (append delta delta') e ((append_mctx cD'' delta'), mvar_dot_apx t delta')))
              
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
  | Apx.LF.CoId _   -> fMVs
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
      


(* Replace FMVars with appropriate de Bruijn index  
 * If a FMVar (of FPVar) occurs in fMVs do not replace it
 * since it is bound in some inner branch of a case-expression
 *
 *)
let rec fmvApxTerm fMVs cO cD l_cd1 l_delta k m =   match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, fmvApxTerm fMVs cO cD l_cd1 l_delta k m') 

   (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) ->
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in 
      if List.mem u fMVs then 
          Apx.LF.Root (loc, Apx.LF.FMVar (u, s'), Apx.LF.Nil) 
      else 
        begin try 
          let (offset, (_tP, _cPhi)) = Whnf.mctxMVarPos cD u in
            Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset (offset+k), s'), Apx.LF.Nil)     
        with Whnf.Fmvar_not_found -> (dprint (fun () -> "[fmvApxTerm] UnboundName") ; raise (Error (Some loc, UnboundName u)))
        end 

  | Apx.LF.Root (loc, h, s) -> 
      let h' = fmvApxHead fMVs cO cD l_cd1 l_delta k h in 
      let s' = fmvApxSpine fMVs  cO cD l_cd1 l_delta k s in 
        Apx.LF.Root (loc, h', s')

  | Apx.LF.Tuple (loc, tuple) -> 
      Apx.LF.Tuple(loc, fmvApxTuple fMVs cO cD l_cd1 l_delta k tuple)

and fmvApxTuple fMVs cO cD l_cd1 l_delta k tuple = match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (fmvApxTerm fMVs cO cD l_cd1 l_delta k m)
  | Apx.LF.Cons (m, tuple) -> 
      Apx.LF.Cons (fmvApxTerm fMVs cO cD l_cd1 l_delta k m,
                   fmvApxTuple fMVs cO cD l_cd1 l_delta k tuple)

and fmvApxHead fMVs cO cD l_cd1 l_delta k h = match h with
  (* free meta-variables / parameter variables *)
  | Apx.LF.FPVar (p, s) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
      if List.mem p fMVs then 
        Apx.LF.FPVar (p, s')
      else 
        let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in          
          Apx.LF.PVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.FMVar (u, s) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
      if List.mem u fMVs then 
        Apx.LF.FMVar (u, s')
      else 
        let (offset, (_tA, _cPhi)) = Whnf.mctxMVarPos cD u  in          
          Apx.LF.MVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.Proj (Apx.LF.FPVar (p,s), j) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
        if List.mem p fMVs then 
          Apx.LF.Proj (Apx.LF.FPVar (p, s'), j)
        else 
          let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in          
            Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset (offset + k), s'), j)
 
  | Apx.LF.CoFPVar(co_cid, p,j,s) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
      let _ = dprint (fun () -> "fmvApxHead (CoFPVar ) : j = " ^ string_of_int j ^ "\n") in
        if List.mem p fMVs then 
          Apx.LF.CoFPVar (co_cid, p, j, s')
        else 
          let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in          
            Apx.LF.CoPVar(co_cid, Apx.LF.Offset (offset + k), j, s')
        
  (* bound meta-variables / parameters *)
  | Apx.LF.MVar (Apx.LF.Offset offset, s) ->
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
        if offset > (l_delta+k) then 
          Apx.LF.MVar (Apx.LF.Offset (offset+ l_cd1), s')
        else 
          Apx.LF.MVar (Apx.LF.Offset offset, s')

  | Apx.LF.PVar (Apx.LF.Offset offset, s) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
        if offset > (l_delta+k) then 
          Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s')
        else
          Apx.LF.PVar (Apx.LF.Offset offset, s')

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset,s), j) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
        if offset > (l_delta+k) then 
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s'), j)
        else
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, s'), j)        

  | Apx.LF.CoPVar(co_cid, Apx.LF.Offset offset,j,s) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
        if offset > (l_delta+k) then 
          Apx.LF.CoPVar (co_cid, Apx.LF.Offset (offset + l_cd1), j,  s')
        else
          Apx.LF.CoPVar (co_cid, Apx.LF.Offset offset, j, s')

  (* approx. terms may already contain valid LF objects due to 
     applying the refinement substitution eagerly to the body of
     case-expressions 
     Mon Sep  7 14:08:00 2009 -bp  
  *)

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) ->  
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
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
      let _ = Printf.printf "fmvApx PVar MInst ?\n" in 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
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
      let _ = Printf.printf "fmvApx PVar MInst ?\n" in 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
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
        Apx.LF.Proj (Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s'), j)  

    | Apx.LF.CoPVar (co_cid, Apx.LF.PInst (h, tA, cPhi), j,  s) -> 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in
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
        Apx.LF.CoPVar (co_cid, Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), j, s')  
  | _ ->  h

and fmvApxSub fMVs cO cD l_cd1 l_delta k s = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id       -> s
  | Apx.LF.CoId _   -> s
  | Apx.LF.Dot (Apx.LF.Head h, s) -> 
      let h' = fmvApxHead fMVs cO cD l_cd1 l_delta k h in 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in 
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) -> 
      let m' = fmvApxTerm fMVs cO cD l_cd1 l_delta k m in 
      let s' = fmvApxSub fMVs cO cD l_cd1 l_delta k s in 
        Apx.LF.Dot (Apx.LF.Obj m', s')


and fmvApxSpine fMVs cO cD l_cd1 l_delta k s = match s with 
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) -> 
      let s' = fmvApxSpine fMVs cO cD l_cd1 l_delta k s in 
      let m' = fmvApxTerm fMVs cO cD l_cd1 l_delta k m in 
        Apx.LF.App (m' , s')

let rec fmvApxTyp fMVs cO cD l_cd1 l_delta k a = match a with
  | Apx.LF.Atom (loc, c, spine) -> 
      Apx.LF.Atom (loc, c, fmvApxSpine fMVs cO cD l_cd1 l_delta k spine)

  | Apx.LF.PiTyp ((t_decl, dep), a) -> 
      let t_decl' = fmvApxTypDecl fMVs cO cD l_cd1 l_delta k t_decl in 
      let a' = fmvApxTyp fMVs cO cD l_cd1 l_delta k a in 
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = fmvApxTypRec fMVs cO cD l_cd1 l_delta k typ_rec in
        Apx.LF.Sigma typ_rec'

and fmvApxTypDecl fMVs cO cD l_cd1 l_delta k t_decl = match t_decl with
  | Apx.LF.TypDecl (x, a) -> 
      Apx.LF.TypDecl(x, fmvApxTyp fMVs cO cD l_cd1 l_delta k a)

and fmvApxTypRec fMVs cO cD l_cd1 l_delta k t_rec = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (fmvApxTyp fMVs cO cD l_cd1 l_delta k a)
  | Apx.LF.SigmaElem (x, a, t_rec) -> 
      let a' = fmvApxTyp fMVs cO cD l_cd1 l_delta k a in 
      let t_rec' = fmvApxTypRec fMVs cO cD l_cd1 l_delta k t_rec in 
        Apx.LF.SigmaElem (x, a', t_rec')

let rec fmvApxDCtx fMVs cO cD l_cd1 l_delta k psi = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar _ -> psi 
  | Apx.LF.DDec (psi, t_decl) -> 
      let psi' = fmvApxDCtx fMVs cO cD l_cd1 l_delta k psi in 
      let t_decl' = fmvApxTypDecl fMVs cO cD l_cd1 l_delta k t_decl in 
        Apx.LF.DDec (psi', t_decl')


let rec fmvApxExp fMVs cO cD l_cd1 l_delta k e = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, fmvApxExp' fMVs cO cD l_cd1 l_delta k i)
  | Apx.Comp.Fun (loc, f, e)    -> Apx.Comp.Fun (loc, f, fmvApxExp fMVs cO cD l_cd1 l_delta k e)
  | Apx.Comp.CtxFun (loc, g, e) -> Apx.Comp.CtxFun (loc, g, fmvApxExp fMVs cO cD l_cd1 l_delta k e)
  | Apx.Comp.MLam (loc, u, e)   -> Apx.Comp.MLam (loc, u, fmvApxExp fMVs cO cD l_cd1 l_delta k e)
  | Apx.Comp.Pair (loc, e1, e2) -> 
      let e1' = fmvApxExp fMVs cO cD l_cd1 l_delta k e1 in 
      let e2' = fmvApxExp fMVs cO cD l_cd1 l_delta k e2 in 
        Apx.Comp.Pair (loc, e1', e2')
  | Apx.Comp.LetPair (loc, i, (x,y, e)) -> 
      let i' = fmvApxExp' fMVs cO cD l_cd1 l_delta k i in 
      let e' = fmvApxExp  fMVs cO cD l_cd1 l_delta k e in 
        Apx.Comp.LetPair (loc, i', (x,y, e')) 

  | Apx.Comp.Box(loc, phat, m) -> 
      Apx.Comp.Box (loc, phat, fmvApxTerm fMVs cO cD l_cd1 l_delta k m)
  | Apx.Comp.Case (loc, i, branch) -> 
      Apx.Comp.Case (loc, fmvApxExp' fMVs cO cD l_cd1 l_delta k i, fmvApxBranches fMVs cO cD l_cd1 l_delta k branch)

and fmvApxExp' fMVs cO cD l_cd1 l_delta k i = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.Const _c -> i
  | Apx.Comp.Apply (loc, i, e) -> 
      let i' = fmvApxExp' fMVs cO cD l_cd1 l_delta k i in 
      let e' = fmvApxExp fMVs cO cD l_cd1 l_delta k e in 
        Apx.Comp.Apply (loc, i', e')
  | Apx.Comp.CtxApp (loc, i, psi) -> 
      let i' = fmvApxExp' fMVs cO cD l_cd1 l_delta k i in 
      let psi' = fmvApxDCtx fMVs cO cD l_cd1 l_delta k psi  in 
        Apx.Comp.CtxApp (loc, i', psi')

  | Apx.Comp.MApp (loc, i, (phat, m)) -> 
      let i' = fmvApxExp' fMVs cO cD l_cd1 l_delta k i in 
      let m' = fmvApxTerm fMVs cO cD l_cd1 l_delta k m in
        Apx.Comp.MApp (loc, i', (phat, m'))

  | Apx.Comp.BoxVal (loc, psi, m) -> 
      let psi' = fmvApxDCtx fMVs cO cD l_cd1 l_delta k psi in 
      let m'   = fmvApxTerm fMVs cO cD l_cd1 l_delta k m in 
        Apx.Comp.BoxVal (loc, psi', m')

(*  | Apx.Comp.Ann (e, tau) -> 
      let e' = fmvApxExp e t in 
      let tau' = fmvApxCTyp tau t in 
        Apx.Comp.Ann (e', tau')
    
*)


and fmvApxBranches fMVs cO cD l_cd1 l_delta k branches = match branches with
  | [] -> []
  | b::bs -> (fmvApxBranch fMVs cO cD l_cd1 l_delta k b)::(fmvApxBranches fMVs cO cD l_cd1 l_delta k bs)

and fmvApxBranch fMVs cO cD l_cd1 l_delta k b = 
  (match b with
      | Apx.Comp.BranchBox (loc, delta, (psi1, m, Some (a, psi)), e) ->
          let fMVb' = collectApxTerm [] m in 
          let fMVb1  = collectApxDCtx fMVb' psi in
          let fMVb  = collectApxTyp fMVb1 a in
          let l    = lengthApxMCtx delta in 
            Apx.Comp.BranchBox (loc, delta, (psi1, m, Some (a, psi)),
                                fmvApxExp (fMVs@fMVb) cO cD l_cd1 l_delta (k+l) e)
              
      | (Apx.Comp.BranchBox (loc, delta, (psi, r, None), e))  ->
          let fMVb' = collectApxTerm [] r in 
          let fMVb  = collectApxDCtx fMVb' psi in
          let l    = lengthApxMCtx delta in 
            Apx.Comp.BranchBox (loc, delta, (psi, r, None),
                                fmvApxExp (fMVs@fMVb) cO cD l_cd1 l_delta (k+l) e))
              
(* ******************************************************************* *)
(* Elaboration of computations                                         *)
(* Given a type-level constant a of type K , it will generate the most general
 * type a U1 ... Un 
 *)
let mgTyp cD cPsi a kK =
  let rec genSpine sK = match sK with
    | (Int.LF.Typ, _s) ->
        Int.LF.Nil

    | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA1), _ ), kK), s) ->
        let u  = Whnf.newMMVar (cD, cPsi , Int.LF.TClo (tA1,s)) in
        let h  = Int.LF.MMVar (u, (Whnf.m_id, LF.id)) in 
        let tR = Int.LF.Root (None, h, Int.LF.Nil) in
        (* let tS = genSpine (kK, Int.LF.Dot (Int.LF.Head h, s)) in *)
        let tS = genSpine (kK, Int.LF.Dot (Int.LF.Obj tR , s)) in
          Int.LF.App (tR, tS)
  in
    Int.LF.Atom (None, a, genSpine (kK, LF.id))

let rec genMApp cD (i, tau_t) = genMAppW cD (i, Whnf.cwhnfCTyp tau_t)

and genMAppW cD (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
      let psihat  = Context.dctxToHat cPsi in
      let tM'     = Whnf.etaExpandMMV cD (C.cnormDCtx (cPsi, theta))  (C.cnormTyp (tA, theta), LF.id) LF.id in
        genMApp cD ((Int.Comp.MApp (None, i, (psihat, tM'))), (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)))

  | _ -> (i, tau_t)

let rec elCompTyp cO cD tau = match tau with
  | Apx.Comp.TypBox (loc, a, psi) ->
      let cPsi = elDCtx PiboxRecon cO cD psi in
      let tA   = elTyp PiboxRecon cO cD cPsi a in
        Int.Comp.TypBox (Some loc, tA, cPsi)

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCross (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypCross (tau1', tau2')

  | Apx.Comp.TypCtxPi ((x, schema_cid) , tau) ->
      let tau' = elCompTyp (Int.LF.Dec (cO, Int.LF.CDecl (x, schema_cid))) cD tau in
        Int.Comp.TypCtxPi ((x, schema_cid), tau')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl PiboxRecon cO cD cdecl  in
      let tau'   = elCompTyp cO (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox ((cdecl', Int.Comp.Explicit), tau')

let rec elExp cO cD cG e theta_tau = elExpW cO cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cO cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Syn (loc, i), (tau,t)) ->
      let (i', tau_t') = genMApp cD (elExp' cO cD cG i) in
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

  | (Apx.Comp.CtxFun (loc, psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid), tau), theta)) ->
      let e' = elExp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD cG e (tau, theta) in
        Int.Comp.CtxFun (Some loc, psi_name, e')

  | (Apx.Comp.MLam (loc, u, e) , (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
                     cG e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (Some loc, u, e')

  | (e, (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      let u' = Id.mk_name Id.NoName in
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u', C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
                     cG e (tau, C.mvar_dot1 theta) in
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


  | (Apx.Comp.Box (loc, psihat, tM), (Int.Comp.TypBox (_loc, tA, cPsi), theta)) ->
      let tM' = elTerm PiboxRecon cO cD (C.cnormDCtx (cPsi, theta)) tM (C.cnormTyp (tA, theta), LF.id) in
      let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
      let _        = Unify.resetGlobalCnstrs () in 
        Int.Comp.Box (Some loc, psihat, tM')

  | (Apx.Comp.Case (loc, i, branches), tau_theta) ->
      let (i', tau_theta') = genMApp cD (elExp' cO cD cG i) in
      (* let (i', tau_theta')   = syn cO cD cG i' in *)
        begin match (i', C.cwhnfCTyp tau_theta') with
          | (Int.Comp.Ann (Int.Comp.Box (_ , phat,tR), _ ), 
             (Int.Comp.TypBox (_, tP, cPsi) as tau', t (* m_id *))) ->
              let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
              let _        = Unify.resetGlobalCnstrs () in 

              (* let _ = recTerm PiboxRecon cO cD cPsi (tR, LF.id) (tP, LF.id) in *)
              (if Whnf.closed (tR, LF.id) then 
                let branches' = List.map (function b -> 
                                            elBranch (IndexObj(phat, tR))
                                              cO cD cG b (tP, cPsi) tau_theta) branches in
                  Int.Comp.Case (Some loc, i', branches')
              else 
                raise (Error (Some loc, ValueRestriction (cO, cD, cG, i', (tau',t))))
              )

          | (i, (Int.Comp.TypBox (_, tP, cPsi), _mid)) -> 
              (if Whnf.closedTyp (tP, LF.id) && Whnf.closedDCtx cPsi then 
                 let _      = dprint (fun () -> "[elExp]" 
                             ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                             ^  "Context of expected pattern type : "
                             ^  P.dctxToString cO cD cPsi 
                             ^ "\n") in

                let branches' = List.map (function b -> 
                                            elBranch DataObj
                                              cO cD cG b (tP, cPsi) tau_theta) branches in
                  Int.Comp.Case (Some loc, i, branches')
              else 
                raise (Error (Some loc, CompScrutineeTyp (cO, cD, cG, i', (tP, LF.id), cPsi)))
              )

          | _ -> raise (Error (Some loc, CompMismatch (cO, cD, cG, i', Box, tau_theta'))) 
              (* TODO postpone to reconstruction *)
        end
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
      let (i', tau_theta') = genMApp cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypArr (tau2, tau), theta) ->
              let e' = elExp cO cD cG e (tau2, theta) in
                (Int.Comp.Apply (Some loc, i', e'), (tau, theta))

          | _ -> 
              raise (Error (None, CompMismatch (cO, cD, cG, i', Arrow, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.CtxApp (loc, i, cPsi) ->
      let (i', tau_theta') = genMApp cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypCtxPi ((_psi, _sW), tau), theta) ->
              let cPsi'  = elDCtx PiboxRecon cO cD cPsi in
              let theta' = Ctxsub.csub_msub cPsi' 1 theta in
              let tau'   = Ctxsub.csub_ctyp cD cPsi' 1 tau in
                (Int.Comp.CtxApp (Some loc, i', cPsi'), (tau', theta'))

          | _ -> 
              raise (Error (None, CompMismatch (cO, cD, cG, i', CtxPi, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.MApp (loc, i, (psihat, m)) ->
      let (i', tau_theta') = genMApp cD (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
             begin try 
              let tM'    = elTerm PiboxRecon cO cD (C.cnormDCtx (cPsi, theta)) m (C.cnormTyp (tA, theta), LF.id) in
              let theta' = Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta) in
                (Int.Comp.MApp (Some loc, i', (psihat, tM')), (tau, theta'))
             with Violation msg -> 
               dprint (fun () -> "[elTerm] Violation: " ^ msg ^ "\n") ; 
               raise (Error (Some loc, CompTypAnn ))
             end 

          | _ ->
              raise (Error (None, CompMismatch (cO, cD, cG, i', PiBox, tau_theta'))) 
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.BoxVal (loc, psi, r) ->
      let cPsi   = elDCtx PiboxRecon cO cD psi in
      let (tR, sP)     = elClosedTerm' PiboxRecon cO cD cPsi r in
      (* let sP     = synTerm PiboxRecon cO cD cPsi (tR, LF.id) in *)
      let phat   = Context.dctxToHat cPsi in
      let tau    = Int.Comp.TypBox (None, Int.LF.TClo sP, cPsi) in
        (Int.Comp.Ann (Int.Comp.Box (Some loc, phat, tR), tau), (tau, C.m_id))

  | Apx.Comp.Ann (e, tau) ->
      let tau' = elCompTyp cO cD tau in
      let e'   = elExp cO cD cG e (tau', C.m_id) in
        (Int.Comp.Ann (e', tau'), (tau', C.m_id))


(* We don't check that each box-expression has approximately
 *  the same type as the expression we analyze.
 *
 * TODO double check -bp
 *)
(* NOTE: Any context variable occurring in delta, psihat, a, psi is bound
 *  in cO !  So delta (and cD' and cD) do not contain it!
 *)

and recPattern cO delta psi m tPopt = 
  let cD'     = elMCtx  PiboxRecon cO delta in
  (* let  _      = recMCtx PiboxRecon cO cD' in *)
  let cPsi'   = elDCtx  PiboxRecon cO cD' psi in
  (* let  _      = recDCtx PiboxRecon cO cD' cPsi' in  *)
 (* TODO:
    - Check that psi = psi1;
      if they are not equal, then we would need to fail here.
    - recDCtx against context schema to ensure that cPsi' is a 
      valid data-context ?
 -bp *)

  let tP'     = begin match tPopt with 
                  | FullTyp  a    -> 
                      let tP' = elTyp PiboxRecon cO cD' cPsi' a  in 
                        (* recTyp PiboxRecon cO cD' cPsi' (tP', LF.id) ;*) tP'
                  | PartialTyp a  -> 
                      mgTyp cD' cPsi' a (Typ.get a).Typ.kind   
                end in

  let _ = dprint (fun () -> ("[recPattern] Reconstruction of pattern ... type = " ^ P.typToString cO cD' cPsi' (tP', LF.id) ^ "\n")) in
  let tR = elTerm' PiboxRecon cO cD' cPsi' m (tP', LF.id) in    

  let _  = solve_fcvarCnstr cO cD' !fcvar_cnstr in 
  let _  = reset_fcvarCnstr () in 
  let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
  let _        = Unify.resetGlobalCnstrs () in 

  let _   = dprint (fun () -> "recPattern: Elaborated pattern ...\n" ^
                      P.mctxToString cO cD' ^ "  ;   " ^
                      P.dctxToString cO cD' cPsi' ^ "\n   |-\n    "  ^
                      P.normalToString cO cD' cPsi' (tR, LF.id) ^ "\n has type " ^
                      P.typToString  cO cD' cPsi' (tP', LF.id) ^ "\n") in

 
  (* Uncommenting this next line leads to error in cut-elim.bel -bp *)
  (* let _     = recTerm PiboxRecon cO cD' cPsi' (tR, LF.id) (tP', LF.id) in  *)

    let _   = dprint (fun () -> "recPattern: Syn pattern done ...\n" ) in 
 
  let phat = Context.dctxToHat cPsi' in 

  let (cD1', cPsi1', (_phat, tR1'), tP1') =  Abstract.abstrPattern cD' cPsi' (phat, tR) tP' in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.mctxToString cO cD1' ^ "  ;   " ^
                          P.dctxToString cO cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.normalToString cO cD1' cPsi1' (tR1', LF.id) ^ "\n has type " ^
                          P.typToString cO cD1' cPsi1'  (tP1', LF.id) ^ "\n") in
    
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in 
    ((n,k), cD1', cPsi1', tR1', tP1')

(*
(* synRefine cO caseT tR1 (cD, cPsi, tP) (cD1, cPsi1, tP1) = (t, cD1')

   if  cO ; cD ; cPsi  |- tP  <= type
       cO ; cD1; cPsi1 |- tP1 <= type
      
       and let r =  MShift n
       cO ; cD, cD1    |- r  <= cD (where n = |cD1| ) 
       and let r1 = mctx_dot (MShift m) cD1
       cO ; cD, cD1    |- r1  <= cD1  (where m = |cD| )
     
   then
       cD1' |- t <= cD, cD1    and        

       cD1' |- |[t]|(|[r]|cPsi)  =   |[t]|(|[r1]|cPsi1) 
       cD1' ; |[t]|(|[r]|cPsi) |- |[t]|(|[r]|cP)  =   |[t]|(|[r1]|tP1) 

*)

and synRefine loc cO caseT tR1 (cD, cPsi, tP) (cD1, cPsi1, tP1) =
      let cD'    = Context.append cD cD1 in                   (*         cD'  = cD, cD1     *)
      let _      = dprint (fun () -> "[synRefine] cD' = " ^ P.mctxToString cO cD' ^ "\n") in 
      let t      = mctxToMSub cD'  in                         (*         .  |- t   <= cD'   *) 
      let _      = dprint (fun () -> "[synRefine] mctxToMSub cD' = t = " ^ 
                             P.msubToString cO  Int.LF.Empty (Whnf.cnormMSub t) ^ "\n") in 
      let n      = Context.length cD1 in 
      let m      = Context.length cD in 
      let mt     = Whnf.mcomp (Int.LF.MShift n) t in         
      (* cD, cD1 |- MShift n <= cD  
         .       |- t        <= cD, cD1
         .       |- mt       <= cD
       *)
      let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
      (* cD, cD1 |- t1 <= cD1 *)
      let mt1    = Whnf.mcomp t1 t in
                                                              (*         .  |- mt1 <= cD1   *)

      let cPsi'  = Whnf.cnormDCtx (cPsi, mt) in              (*         .  |- cPsi' ctx    *)
      let cPsi1' = Whnf.cnormDCtx (cPsi1, mt1) in             (*         .  |- cPsi1 ctx    *)
      let tP'    = Whnf.cnormTyp (tP, mt) in                 (* . ; cPsi'  |- tP'  <= type *)
      let tP1'   = Whnf.cnormTyp (tP1, mt1) in                (* . ; cPsi1' |- tP1' <= type *)

      let phat   = Context.dctxToHat cPsi' in 

      let _      = dprint (fun () -> "SynRefine [BEFORE Unify]:\n\n"
                             ^ "Contexts cD1  = " ^ P.mctxToString cO cD1 ^ "\n"
                             ^  "Context of inferred pattern type : "
                             ^  P.dctxToString cO cD1 cPsi1
                             ^ "  \n\n" 
                             ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                             ^  "Context of expected pattern type : "
                             ^  P.dctxToString cO cD cPsi 
                             ^ "\n") in

      let _      = dprint (fun () -> "SynRefine [BEFORE Unify shifted to cD']:\n\n"
                             ^  "Context of Inferred pattern type : cD' |- "
                             ^  P.dctxToString cO cD' (Whnf.cnormDCtx (cPsi1, t1))
                             ^ "\n\nContext Expected pattern type: cD' |-"
                             ^ P.dctxToString cO cD' (Whnf.cnormDCtx (cPsi, Int.LF.MShift n))
                          ) in 



      let _      = dprint (fun () -> "SynRefine [BEFORE Unify instantiated with MVars]:\n\n"
                             ^  "Context of Inferred pattern type : . |- "
                             ^  P.dctxToString cO Int.LF.Empty (Whnf.cnormDCtx(Whnf.cnormDCtx (cPsi1, t1), t))
                             ^ "\n\nContext Expected pattern type: cD' |-"
                             ^ P.dctxToString cO Int.LF.Empty (Whnf.cnormDCtx(Whnf.cnormDCtx (cPsi, mt), t))
                          ) in 



      let _      = dprint (fun () -> "SynRefine [BEFORE Unify instantiated with MVars]:\n\n"
                             ^  "Context of Inferred pattern type : . |- "
                             ^  P.dctxToString cO Int.LF.Empty cPsi1'
                             ^ "\n\nContext Expected pattern type: cD' |-"
                             ^ P.dctxToString cO Int.LF.Empty cPsi'
                          ) in 


      let _      = dprint (fun () -> "synRefine ...\n") in 

      let _  = begin match caseT with
               | IndexObj (_phat, tR') -> 
                   begin try Unify.unify cD1 phat (C.cnorm (tR', Whnf.mcomp mt (Int.LF.MShift n)), LF.id) 
                                                    (tR1, LF.id) 
                   with Unify.Unify msg -> 
                     (dprint (fun () -> "Unify ERROR: " ^  msg  ^ "\n") ; 
                      raise (Violation "Pattern matching on index argument failed"))
                   end
               | DataObj -> ()
              end  in
        
      let _    = begin try 
        Unify.unifyDCtx Int.LF.Empty cPsi' cPsi1' ;
        Unify.unifyTyp  Int.LF.Empty phat (tP', LF.id) (tP1', LF.id);
        dprint (fun () -> "Unify successful: \n"
                   ^  "Inferred pattern type: "
                   ^  P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "    |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi1' (tP1', LF.id)
                                  ^ "\nExpected pattern type: "
                                  ^ P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "     |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi' (tP', LF.id))

      with Unify.Unify msg ->
        (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n"
                   ^  "Inferred pattern type: "
                   ^  P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "    |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi1' (tP1', LF.id)
                                  ^ "\nExpected pattern type: "
                                  ^ P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "     |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi' (tP', LF.id))
                       ; 
         raise (Error (loc, CompPattMismatch ((cO, cD1, cPsi1, tR1, (tP1, LF.id)), 
                                                (cO, cD, cPsi, (tP, LF.id))))))
                   end 
      in 
      (* cD1' |- t' <= cD' *)
      let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub t) in 
      let _ = dprint (fun () -> "synRefine [Substitution (BEFORE ABSTRACTION)]:\n " ^  
                        P.msubToString cO Int.LF.Empty (Whnf.cnormMSub t) ^ "\n <= " ^ P.mctxToString cO cD' ^ "\n") in 
      let _ = dprint (fun () -> "synRefine [Substitution]: " ^ P.mctxToString cO cD1' ^ 
                        "\n|-\n" ^ P.msubToString cO cD1' t' ^ "\n <= " ^ P.mctxToString cO cD' ^ "\n") in 
        (t', cD1')
*)
(*
and elBranch caseTyp cO cD cG branch (Int.LF.Atom(_, a, _) as tP , cPsi) (tau, theta) = match branch with
  | Apx.Comp.BranchBox (loc, delta, (psi, m, tAopt), e) ->

      let typAnn = begin match tAopt with 
                     | None -> PartialTyp a
                     | Some (at, _psi) ->  FullTyp at
                   end in

      let ((l_cd1', l_delta), cD1', cPsi1', tM1', tP1') = recPattern cO delta psi m typAnn in 
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern done") in
      let _      = dprint (fun () -> "[elBranch]" 
                             ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                             ^  "Context of expected pattern type : "
                             ^  P.dctxToString cO cD cPsi 
                             ^ "\n") in

      let (t', cD1'') = synRefine (Some loc) cO caseTyp tM1' (cD, cPsi, tP) (cD1', cPsi1', tP1') in  

      (* Note: e is in the scope of cD, cD1' ; however, cD1' = cD1, cD0 !!   *)

      let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
      let cD'      = Context.append cD cD1' in  

      let e1       = fmvApxExp [] cO cD' l_cd1 l_delta  0 e in   

      let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO cD1'' ^ 
                               "\n |- \n " ^ P.msubToString cO cD1'' t' ^ 
                               " \n <= " ^ P.mctxToString cO cD' ^ "\n") in 
      (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0 
          then cD, cD1' |- e1 apx_exp
      *)
      (* if cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
         the cD1'' |- e' apx_exp
      *)
      let e'      =  cnormApxExp cO cD' Apx.LF.Empty e1  (cD1'', t') in  
      (* Note: e' is in the scope of cD1''  *)

      let t'' = Whnf.mcomp (Int.LF.MShift l_cd1') t' in  
      (*  cD, cD1' |- MShift l_cd1'  <= cD    where l_cd1' = |cD1'| and
       *  cD1''    |- t'  <= cD, cD1'
       * 
       *  cD1''    |- t''   <= cD  
       *)
      let cG'     = Whnf.cnormCtx (cG,  t'') in 
      let ttau'   = (tau, Whnf.mcomp theta t'') in 

      let _       = dprint (fun () -> "[elBranch] Elaborate branch" ^
                             P.mctxToString cO cD1'' ^ "  ;  " ^
                             P.gctxToString cO cD1'' cG' ^ "\n      |-\n" ^
                             "against type" ^ P.compTypToString cO cD1'' (C.cnormCTyp ttau') ^ "\n") in

      let eE'      = elExp cO cD1'' cG'  e' ttau' in
      let _       = FMVar.clear () in
      let _       = FPVar.clear () in

      let _       = dprint (fun () -> "elBranch: Elaborated branch" ^
                             P.mctxToString cO cD1'' ^ "  ;  " ^
                             P.gctxToString cO cD1'' cG' ^ "\n      |-\n" ^
                             P.expChkToString cO cD1'' cG' eE' ^ "\n") in

        Int.Comp.BranchBox (cD1', (cPsi1', tM1', (t', cD1'')), eE')

*)

(* synRefine cO caseT tR1 (cD, cPsi, tP) (cD1, cPsi1, tP1) = (t, cD1')

   if  cO ; cD ; cPsi  |- tP  <= type
       cO ; cD1; cPsi1 |- tP1 <= type
      
       and let r =  MShift n
       cO ; cD, cD1    |- r  <= cD (where n = |cD1| ) 
       and let r1 = mctx_dot (MShift m) cD1
       cO ; cD, cD1    |- r1  <= cD1  (where m = |cD| )
     
   then
       cD1' |- t <= cD, cD1    and        

       cD1' |- |[t]|(|[r]|cPsi)  =   |[t]|(|[r1]|cPsi1) 
       cD1' ; |[t]|(|[r]|cPsi) |- |[t]|(|[r]|cP)  =   |[t]|(|[r1]|tP1) 

*)

and synRefine loc cO caseT tR1 (cD, cPsi, tP) (cD1, cPsi1, tP1) =
      let cD'    = Context.append cD cD1 in                   (*         cD'  = cD, cD1     *)
      let _      = dprint (fun () -> "[synRefine] cD' = " ^ P.mctxToString cO cD' ^ "\n") in 
      let t      = mctxToMSub cD'  in                         (*         .  |- t   <= cD'   *) 
      let _      = dprint (fun () -> "[synRefine] mctxToMSub cD' = t = " ^ 
                             P.msubToString cO  Int.LF.Empty (Whnf.cnormMSub t) ^ "\n") in 
      let n      = Context.length cD1 in 
      let m      = Context.length cD in 
      let mt     = Whnf.mcomp (Int.LF.MShift n) t in         
      (* cD, cD1 |- MShift n <= cD  
         .       |- t        <= cD, cD1
         .       |- mt       <= cD
       *)
      let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
      (* cD, cD1 |- t1 <= cD1 *)
      let mt1    = Whnf.mcomp t1 t in
                                                              (*         .  |- mt1 <= cD1   *)

      let cPsi'  = Whnf.cnormDCtx (cPsi, mt) in              (*         .  |- cPsi' ctx    *)
      let cPsi1' = Whnf.cnormDCtx (cPsi1, mt1) in             (*         .  |- cPsi1 ctx    *)
      let tP'    = Whnf.cnormTyp (tP, mt) in                 (* . ; cPsi'  |- tP'  <= type *)
      let tP1'   = Whnf.cnormTyp (tP1, mt1) in                (* . ; cPsi1' |- tP1' <= type *)

      (* let phat   = Context.dctxToHat cPsi' in *)

      let _  = begin match caseT with
               | IndexObj (_phat, tR') -> 
                   begin try Unify.unify cD1 cPsi' (C.cnorm (tR', Whnf.mcomp mt (Int.LF.MShift n)), LF.id) 
                                                    (tR1, LF.id) 
                   with Unify.Unify msg -> 
                     (dprint (fun () -> "Unify ERROR: " ^  msg  ^ "\n") ; 
                      raise (Violation "Pattern matching on index argument failed"))
                   end
               | DataObj -> ()
              end  in
        
      let _    = begin try 
        Unify.unifyDCtx Int.LF.Empty cPsi' cPsi1' ;
        Unify.unifyTyp  Int.LF.Empty cPsi' (tP', LF.id) (tP1', LF.id);
        dprint (fun () -> "Unify successful: \n"
                   ^  "Inferred pattern type: "
                   ^  P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "    |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi1' (tP1', LF.id)
                                  ^ "\nExpected pattern type: "
                                  ^ P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "     |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi' (tP', LF.id))

      with Unify.Unify msg ->
        (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n"
                   ^  "Inferred pattern type: "
                   ^  P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "    |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi1' (tP1', LF.id)
                                  ^ "\nExpected pattern type: "
                                  ^ P.dctxToString cO Int.LF.Empty cPsi'
                                  ^ "     |-    "
                                  ^ P.typToString cO Int.LF.Empty cPsi' (tP', LF.id))
                       ; 
         raise (Error (loc, CompPattMismatch ((cO, cD1, cPsi1, tR1, (tP1, LF.id)), 
                                                (cO, cD, cPsi, (tP, LF.id))))))
                   end 
      in 
      (* cD1' |- t' <= cD' *)
      let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub t) in 
      let rec drop t l_delta1 = match (l_delta1, t) with
        | (0, t) -> t
        | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in 
        
      let t0   = drop t' n in  (* cD1' |- t0 <= cD *)
      let tR1' = Whnf.cnorm (tR1, Whnf.mcomp t1 t') in 
        (* cD1' ; cPsi1' |- tR1 <= tP1' *)
      let _ = dprint (fun () -> "synRefine [Substitution (BEFORE ABSTRACTION)]:\n " ^  
                        P.msubToString cO Int.LF.Empty (Whnf.cnormMSub t) ^ "\n <= " ^ P.mctxToString cO cD' ^ "\n") in 
      let _ = dprint (fun () -> "synRefine [Substitution]: " ^ P.mctxToString cO cD1' ^ 
                        "\n|-\n" ^ P.msubToString cO cD1' t' ^ "\n <= " ^ P.mctxToString cO cD' ^ "\n") in 
        (t0, t', cD1', tR1')

and elBranch caseTyp cO cD cG branch (Int.LF.Atom(_, a, _) as tP , cPsi) (tau, theta) = match branch with
  | Apx.Comp.BranchBox (loc, delta, (psi, m, tAopt), e) ->

      let typAnn = begin match tAopt with 
                     | None -> PartialTyp a
                     | Some (at, _psi) ->  FullTyp at
                   end in
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern ... ") in
      let ((l_cd1', l_delta), cD1', cPsi1', tM1', tP1') = recPattern cO delta psi m typAnn in 
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern done") in
      let _      = dprint (fun () -> "[elBranch]" 
                             ^ "Contexts cD  = " ^ P.mctxToString cO cD ^ "\n"
                             ^  "Context of expected pattern type : "
                             ^  P.dctxToString cO cD cPsi 
                             ^ "\n") in

      let (t', t1, cD1'', tR1') = synRefine (Some loc) cO caseTyp tM1' (cD, cPsi, tP) (cD1', cPsi1', tP1') in  
      (*   cD1''|-  t' : cD   and   cD1'' ; [t']cPsi |- tR <= [t']tP  
           cD1''|- t1  : cD, cD1'
      *)

      (* Note: e is in the scope of cD, cD0 ; however, cD1' = cD1, cD0 !!   *)

      let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
      let cD'      = Context.append cD cD1' in  

      let e1       = fmvApxExp [] cO cD' l_cd1 l_delta  0 e in   

      let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cO cD1'' ^ 
                               "\n |- \n " ^ P.msubToString cO cD1'' t' ^ 
                               " \n <= " ^ P.mctxToString cO cD ^ "\n") in 
      (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0 
          then cD, cD1' |- e1 apx_exp
      *)
      (* if cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
         the cD1'' |- e' apx_exp
      *)
      let e'      =  cnormApxExp cO cD' Apx.LF.Empty e1  (cD1'', t1) in  
      (* Note: e' is in the scope of cD1''  *)

      let cG'     = Whnf.cnormCtx (cG,  t') in 
      let ttau'   = (tau, Whnf.mcomp theta t') in 

      let _       = dprint (fun () -> "[elBranch] Elaborate branch \n" ^
                             P.mctxToString cO cD1'' ^ "  ;  " ^
                             P.gctxToString cO cD1'' cG' ^ "\n      |-\n" ^
                             "against type " ^ P.compTypToString cO cD1'' (C.cnormCTyp ttau') ^ "\n") in

      let eE'      = elExp cO cD1'' cG'  e' ttau' in
      let _       = FMVar.clear () in
      let _       = FPVar.clear () in

      let phat    = Context.dctxToHat cPsi1' in 
      let _       = dprint (fun () -> "elBranch: Elaborated branch" ^
                             P.mctxToString cO cD1'' ^ "  ;  " ^
                             P.gctxToString cO cD1'' cG' ^ "\n      |-\n" ^
                             P.expChkToString cO cD1'' cG' eE' ^ "\n") in

        Int.Comp.BranchBox (cD1'', (phat, tR1', t'), eE')

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


  | Ext.Sgn.Coercion (_ , co, Ext.LF.CoTyp(actx, bctx), c_body) -> 
      let c_body'  = index_coe c_body in
      let c_body'' = elCoercion c_body' in 
      let (a_schema, b_schema)    = (Schema.index_of_name actx, Schema.index_of_name bctx)  in
      (* let _        = recCoercion c_body'' (a_schema, b_schema) in  *)
      (* May need to add abstraction over reconstructed c_body'' *)
      let _        = Coercion.add (Coercion.mk_entry co (Int.LF.CoTyp(a_schema, b_schema)) 
                                                         c_body'') in 
      (Printf.printf "\ncoercion %s : %s -> %s =\n %s\n" 
         (co.string_of_name) (actx.string_of_name) (bctx.string_of_name)
         (P.coercionToString c_body'') ;
      ())


  | Ext.Sgn.Val (_, x, i) -> ()

  | Ext.Sgn.Rec (_, recFuns) ->
      (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in   *)
      let cD      = Int.LF.Empty in
      let cO      = Int.LF.Empty in

      let rec preprocess l = match l with 
        | [] -> (Int.LF.Empty, Var.create ())
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

        let (cG, vars) = preprocess lf in 
          (* check that names are unique ? *)
          (Int.LF.Dec(cG, Int.Comp.CTypDecl (f, tau')) , Var.extend  vars (Var.mk_entry f))

      in

      let (cG , vars') = preprocess recFuns in 
    
      let reconFun f e = 
        let fvars = [] in 
        let apx_e   = index_exp (CVar.create ()) (CVar.create ()) vars' fvars e in
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

            let _f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' )   in
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
                
              let _f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' )   in
                reconRecFun lf 
          | _ -> raise (Violation "No recursive function defined\n")
        end

        (* Int.Sgn.Rec (f', tau',  e_r' ) *)


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

