(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**

   @author Brigitte Pientka

*)

(* Context substitution  *)

open Context
open Syntax.Int.LF
open Syntax.Int
open Substitution
open Store.Cid
open Error

exception Error of Syntax.Loc.t option * error
exception Violation of string

module Comp = Syntax.Int.Comp

module Unify = Unify.EmptyTrail

  (* ctxToSub cPsi:
   *
   * generates, based on cPsi, a substitution suitable for unification
   *
   * Currently broken: assumes all types in cPsi are atomic
   *)
  let rec ctxToSub cPsi = match cPsi with
    | Null -> LF.id
    | DDec (cPsi', TypDecl (_, tA)) ->
        let s = ((ctxToSub cPsi') : sub) in
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
        let (_, phat') = dctxToHat cPsi' in
        let u     = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in
          (* let u = newMVar (Null ,  TClo( tA, s)) in *)
        let front = (Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : front) in
          Dot (front, LF.comp s LF.shift)



(* ************************************************* *)
(* Context substitutions                             *)
(* ************************************************* *)

let rec csub_typ cPsi k tA = match tA with 
  | Atom (loc, a, tS) -> 
      Atom (loc, a, csub_spine cPsi k tS)

  | PiTyp ((TypDecl (x, tA), dep), tB) -> 
      PiTyp ((TypDecl (x, csub_typ cPsi k tA), dep),
                csub_typ cPsi k tB)

  | TClo (tA, s) -> 
     TClo (csub_typ cPsi k tA, csub_sub cPsi k s)

  | Sigma trec -> Sigma (csub_trec cPsi k trec)


and csub_trec cPsi k trec = match trec with 
  | SigmaLast tA -> SigmaLast (csub_typ cPsi k tA)
  | SigmaElem (x, tA, trec) -> 
      let tA' = csub_typ cPsi k tA in 
      let trec' = csub_trec cPsi k trec in 
       SigmaElem (x, tA', trec')

and csub_norm cPsi k tM = match tM with
  | Lam (loc, x, tN)  -> Lam (loc, x, csub_norm cPsi k tN)

  | Root (loc, h, tS) ->
      Root (loc, csub_head cPsi k h, csub_spine cPsi k tS)

  | Clo (tN, s) -> 
      Clo (csub_norm cPsi k tN, csub_sub cPsi k s)

and csub_head cPsi k h = match h with
(*  | MMVar (u, (t,s)) -> MMVar(u, (csub_msub k t, csub_sub cPsi k s)) *)
  | MVar (u, s)  -> MVar(u, csub_sub cPsi k s)
  | PVar (p, s)  -> PVar(p, csub_sub cPsi k s)
  | _            -> h

and csub_spine cPsi k tS = match tS with
  | Nil -> Nil
  | App(tM, tS) -> 
      App (csub_norm cPsi k tM, csub_spine cPsi k tS)
  | SClo (tS, s) -> 
      SClo (csub_spine cPsi k tS, csub_sub cPsi k s)

(* csub_sub cPsi phi s = s' 

*)
and csub_sub cPsi phi (* k *) s = match s with
  | Shift (NoCtxShift, _k) -> s

  | Shift (CtxShift (CtxOffset psi), k) -> 
      if psi = phi then 
        begin match Context.dctxToHat cPsi with
          | (Some ctx_v, d) -> 
              Shift (CtxShift ctx_v, k + d)

          | (None, d) ->
              Shift (NoCtxShift, k + d)
        end

      else 
        Shift (CtxShift (CtxOffset psi), k)

  | Shift (NegCtxShift (CtxOffset psi), k) -> 
      if psi = phi then 
        let rec undef_sub d s = 
          if d = 0 then s 
          else undef_sub (d-1) (Dot(Undef, s)) 
        in 
          begin match Context.dctxToHat cPsi with
          | (Some ctx_v, d) -> 
          (* Psi |- s : psi  and psi not in Psi and |Psi| = k 
           * Psi |- Shift(negCtxShift(phi), k) . Undef ....  : phi, Phi 
           *)                      
              undef_sub d (Shift (NegCtxShift ctx_v, k))

          | (None, d) -> undef_sub d (Shift (NoCtxShift, k))

          end
              
      else 

        Shift(NegCtxShift (CtxOffset psi), k)

  | Dot (ft, s) -> 
      Dot (csub_front cPsi phi ft, csub_sub cPsi phi s)

and csub_front cPsi k ft = match ft with
  | Head h -> Head (csub_head cPsi k h)
  | Obj tN -> Obj (csub_norm cPsi k tN)
  | Undef  -> Undef
 
let rec csub_ctyp cD cPsi k tau = match tau with
  | Syntax.Int.Comp.TypBox (loc, tA, cPhi) -> 
      Syntax.Int.Comp.TypBox (loc, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi)

  | Syntax.Int.Comp.TypArr (tau1, tau2) -> 
      Syntax.Int.Comp.TypArr (csub_ctyp cD cPsi k tau1, csub_ctyp cD cPsi k tau2)

  | Syntax.Int.Comp.TypCross (tau1, tau2) -> 
      Syntax.Int.Comp.TypCross (csub_ctyp cD cPsi k tau1, csub_ctyp cD cPsi k tau2)

  | Syntax.Int.Comp.TypCtxPi (psi_decl, tau) -> 
      Syntax.Int.Comp.TypCtxPi (psi_decl, csub_ctyp cD cPsi (k + 1) tau)

  | Syntax.Int.Comp.TypPiBox ((MDecl (u, tA, cPhi), dep), tau) -> 
      let mdecl = MDecl (u, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi) in 
      Syntax.Int.Comp.TypPiBox ((mdecl, dep),
                     csub_ctyp (Dec(cD, mdecl)) (Whnf.cnormDCtx (cPsi, MShift 1)) k tau)

  | Syntax.Int.Comp.TypClo (tau, theta) -> 
      Syntax.Int.Comp.TypClo (csub_ctyp cD cPsi k tau, csub_msub cPsi k theta)

and csub_psihat cPsi k (ctxvar, offset) = match ctxvar with 
  | None -> (None, offset)
  | Some (CtxOffset psi) -> 
      if k = psi then 
        let (psivar, psi_offset) = dctxToHat cPsi in 
          (psivar, (psi_offset + offset))
       else (ctxvar, offset)


and csub_dctx cD cPsi k cPhi =  
  let rec csub_dctx' cPhi = match cPhi with 
    | Null -> (Null, false)
    | CtxVar (CtxOffset offset) ->         
        if k = offset then 
          (cPsi, true) else (cPhi, false)

    | DDec (cPhi, TypDecl (x, tA)) ->   
        let (cPhi', b) = csub_dctx' cPhi in 
        if b then       
          (* cPhi |- tA type     phi', cPhi' |- s : phi, cPhi *)
          let tA' = csub_typ cPsi k tA in 
          (DDec (cPhi', TypDecl(x, tA')), b)
        else 
          (DDec(cPhi', TypDecl (x, tA)), b)
  in 
  let(cPhi', _ ) = csub_dctx' cPhi in 
    cPhi'

and csub_mctx cPsi k cD = match cD with
  | Empty -> Empty
  | Dec(cD', MDecl(n, tA, cPhi)) -> 
      let cD''   = csub_mctx cPsi k cD'  in 
      let tA' = csub_typ cPsi k tA in 
      let cPhi' = csub_dctx cD'' cPsi k cPhi in 
        Dec(cD'', MDecl(n, tA', cPhi'))
  | Dec(cD', PDecl(n, tA, cPhi)) -> 
      let cD''   = csub_mctx cPsi k cD'  in 
      let tA' = csub_typ cPsi k tA in 
      let cPhi' = csub_dctx cD'' cPsi k cPhi in 
        Dec(cD'', PDecl(n, tA', cPhi'))
  | Dec(cD', MDeclOpt n) ->
      let cD''   = csub_mctx cPsi k cD'  in 
        Dec(cD'', MDeclOpt n)
  | Dec(cD', PDeclOpt n) ->
      let cD''   = csub_mctx cPsi k cD'  in 
        Dec(cD'',PDeclOpt n)


and csub_msub cPsi k theta = match theta with 
  | MShift n -> MShift n
  | MDot (MObj (phihat , tM), theta) -> 
      MDot (MObj (csub_psihat cPsi k phihat , tM), 
                 csub_msub cPsi k theta)

  | MDot (PObj (phihat , h), theta) -> 
      MDot (PObj (csub_psihat cPsi k phihat , h), 
                 csub_msub cPsi k theta)

  | MDot (ft, theta) -> 
      MDot (ft, csub_msub cPsi k theta)
      


let rec csub_exp_chk cPsi k e' = 
  match e' with 
  | Comp.Syn (loc, i) -> 
      Comp.Syn(loc, csub_exp_syn cPsi k i)
  | Comp.Rec (loc, n, e) -> 
      Comp.Rec(loc, n, csub_exp_chk cPsi k e)
  | Comp.Fun (loc, n, e) -> 
      Comp.Fun(loc, n, csub_exp_chk cPsi k e)
  | Comp.CtxFun (loc, n, e) -> 
      Comp.CtxFun(loc, n, csub_exp_chk cPsi (k+1) e)
  | Comp.MLam (loc, u, e) -> 
      Comp.MLam(loc, u, csub_exp_chk cPsi k e)
  | Comp.Pair (loc, e1, e2) -> 
      let e1' = csub_exp_chk cPsi k e1 in 
      let e2' = csub_exp_chk cPsi k e2 in 
        Comp.Pair (loc, e1', e2')

  | Comp.LetPair (loc, i, (x,y,e)) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let e1 = csub_exp_chk cPsi k e in 
        Comp.LetPair (loc, i1, (x,y,e1))

  | Comp.Box (loc, phat, tM) -> 
      let phat' = csub_psihat cPsi k phat in 
      let tM'   = csub_norm cPsi k tM in 
        Comp.Box (loc, phat', tM')

  | Comp.Case (loc, i, branches) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let branches' = List.map (fun b -> csub_branch cPsi k b) branches in 
        Comp.Case (loc, i1, branches')

and csub_exp_syn cPsi k i' = match i' with
  | Comp.Const _c -> i'
  | Comp.Var _    -> i'
  | Comp.Apply (loc, i, e) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let e1 = csub_exp_chk cPsi k e in 
        Comp.Apply (loc, i1, e1)
  | Comp.CtxApp (loc, i, cPhi) -> 
      let cPhi' = csub_dctx Empty (*dummy *) cPsi k cPhi in 
      let i1    = csub_exp_syn cPsi k i in 
        Comp.CtxApp (loc, i1, cPhi')

  | Comp.MApp (loc, i, (phat, tM)) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let tM' = csub_norm cPsi k tM  in
      let phat' = csub_psihat cPsi k phat in 
        Comp.MApp (loc, i1, (phat', tM'))

  | Comp.Ann (e, tau) -> 
      let e' = csub_exp_chk cPsi k e in 
      let tau' = csub_ctyp Empty (*dummy *) cPsi k tau in 
        Comp.Ann (e', tau')
        

and csub_branch cPsi k branch = match branch with 
  | Comp.BranchBox (cD, (cPhi, tM, ms), e) -> 
      let cPhi' = csub_dctx Empty (*dummy *) cPsi k cPhi in 
      let tM'   = csub_norm cPsi k tM in 
      let ms'   = csub_msub cPsi k ms in 
      let e'    = csub_exp_chk cPsi k e in 
      let cD'   = csub_mctx cPsi k cD in 
        Comp.BranchBox (cD', (cPhi', tM', ms'), e')



