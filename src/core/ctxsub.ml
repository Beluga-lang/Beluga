(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

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
open Id

module P = Pretty.Int.DefaultPrinter

let rec subToString = function
  | Shift(CtxShift _, n) -> "Shift(CtxShift _, " ^ string_of_int n ^ ")"
  | Shift(NoCtxShift, n) -> "Shift(NoCtxShift, " ^ string_of_int n ^ ")"
  | Shift(NegCtxShift _, n) -> "Shift(NegCtxShift _, " ^ string_of_int n ^ ")"
  | SVar _ -> "SVar(_,_)"
  | FSVar _ -> "FSVar(_,_)"
  | Dot(front, s) -> "Dot(" ^ frontToString front ^ ", " ^ subToString s ^ ")"

and frontToString = function
  | Head h -> "Head _"
  | Obj tM -> "Obj _"
  | Undef -> "Undef"

module Comp = Syntax.Int.Comp

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [12])

(* broken
  (* ctxToSub cPsi:
   *
   * generates, based on cPsi, a substitution suitable for unification
   * s.t. if . ; . |- cPsi dctx then  cO ; . ;  cPhi |- s : cPsi
   * 
   * Assumes all types in cPsi are atomic -bp
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
*)

(* ***************************************************)
(* Ctx normalization                                 *)
(* ***************************************************)


let rec ccomp cs1 cs2 = match (cs1, cs2) with
  | (CShift 0, cs) -> cs
  | (cs, CShift 0) -> cs
  | (CShift n, CShift m) -> CShift (n+m)
  | (CShift n, CDot (_ft, cs)) ->
        ccomp (CShift (n - 1)) cs

  | (CDot (cPsi, cs1'), cs2') -> 
      CDot (ctxnorm_dctx (cPsi, cs2'),  ccomp cs1' cs2')

and cdot1 cs = match cs with
  | CShift 0 -> cs
  | cs -> CDot ( CtxVar (CtxOffset 1), ccomp cs (CShift 1))

and apply_csub cvar cs = match (cvar, cs) with 
  | ((CtxOffset offset), cs) ->   
      let rec apply offset cs = begin match (offset, cs) with
        | (n, CShift k)         -> CtxVar (CtxOffset (n + k))
        | (1, CDot (cPsi, cs')) -> cPsi
        | (n, CDot (_ , cs'))   -> apply (n-1) cs' 
      end
      in 
        apply offset cs

  | (CInst (_, {contents =  Some cPhi }, _schema, _octx, _mctx), cs) -> 
      ctxnorm_dctx (cPhi, cs)
  | (CInst (_, {contents = None}, _ , _, _ ) , cs) -> CtxVar (cvar )



and ctxnorm (tM, cs) = match tM with
  | Lam (loc,y,tN) -> Lam (loc, y, ctxnorm (tN, cs))
  | Tuple (loc, tuple) -> Tuple (loc, ctxnorm_tuple (tuple, cs)) 
  | Clo (tN, s) -> Clo (ctxnorm (tN, cs), ctxnorm_sub (s, cs))
  | Root( loc, h, tS) -> 
      Root (loc, ctxnorm_head (h, cs), ctxnorm_spine (tS, cs))

and ctxnorm_tuple (tuple, t) = match tuple with
  | Last tM -> Last (ctxnorm (tM, t))
  | Cons (tM, rest) ->
      let tM' = ctxnorm (tM, t) in
      let rest' = ctxnorm_tuple (rest, t) in
        Cons (tM', rest')


and ctxnorm_head (h,cs) = match h with
  | FMVar (u, s) -> FMVar (u, ctxnorm_sub (s, cs))
  | FPVar (u, s) -> FPVar (u, ctxnorm_sub (s, cs))
  | MVar (u, s) -> MVar (u, ctxnorm_sub (s, cs))
  | PVar (p, s) -> PVar (p, ctxnorm_sub (s, cs))
  | MMVar (MInst(n, ({contents = None} as u), cD, cPsi, tA, cnstr), (t,s)) -> 
      (* cnstr must be empty *)
      MMVar (MInst (n, u,ctxnorm_mctx (cD, cs), ctxnorm_dctx (cPsi, cs), ctxnorm_typ (tA, cs), cnstr)
               , (ctxnorm_msub (t,cs) , ctxnorm_sub (s,cs)))

(*  | MMVar (u, (t,s)) -> MMVar (u, (ctxnorm_msub (t,cs) , ctxnorm_sub (s,cs))) *)
  | Proj(PVar (p,s), k) -> 
      Proj(PVar (p, ctxnorm_sub (s, cs)), k)
  | Proj(FPVar (p,s), k) -> 
      Proj(FPVar (p, ctxnorm_sub (s, cs)), k)
  | _ -> h 

and ctxnorm_spine (tS, cs) = match tS with
  | Nil -> Nil
  | App (tN, tS) -> App (ctxnorm (tN, cs) , ctxnorm_spine (tS, cs))
  | SClo (tS, s) -> SClo (ctxnorm_spine (tS, cs), ctxnorm_sub (s, cs))

and ctxnorm_sub (s, cs) = match s with
  | Shift (NoCtxShift, _k) -> s
  | Shift (CtxShift (CInst (_n, {contents =  Some cPhi }, _schema, _octx, _mctx)), k) -> 
      begin match Context.dctxToHat cPhi with
        | (None, l) -> Shift (NoCtxShift, k+l)
        | (Some psi, l) -> Shift (CtxShift psi, k+l)
      end 

  | Shift (CtxShift ctxvar, k) -> 
      begin match apply_csub ctxvar cs with
        | CtxVar cvar -> Shift (CtxShift cvar, k)
        | Null        -> Shift (NoCtxShift, k)
        | DDec _ as cPsi -> 
            begin match Context.dctxToHat cPsi with
              | (Some ctx_v, d) -> 
                  Shift (CtxShift ctx_v, k + d)
                    
              | (None, d) ->
                  Shift (NoCtxShift, k + d)
            end
      end

  | Shift (NegCtxShift (CInst (_n, {contents =  Some cPhi }, _schema, _octx, _mctx)), k) -> 
      let rec undef_sub d s = 
        if d = 0 then s 
        else undef_sub (d-1) (Dot(Undef, s)) 
      in 

      begin match Context.dctxToHat cPhi with
        | (None, d)     -> undef_sub d (Shift (NoCtxShift, k))
     
        | (Some psi, d) -> undef_sub d (Shift (NegCtxShift psi, k))
      end 

  | Shift (NegCtxShift ctxvar, k) -> 
      begin match apply_csub ctxvar cs with
        | CtxVar cvar -> Shift (NegCtxShift cvar, k)
        | Null        -> Shift (NoCtxShift, k)
        | DDec _ as cPsi -> 
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

      end

  | Dot (ft, s) -> Dot (ctxnorm_ft (ft, cs) , ctxnorm_sub (s, cs))

and ctxnorm_ft (ft, cs) = match ft with 
  | Head h  -> Head (ctxnorm_head (h, cs))
  | Obj tN  -> Obj (ctxnorm (tN, cs))
  | Undef   -> Undef


and ctxnorm_msub (ms, cs) = match ms with
  | MShift k -> MShift k
  | MDot (mf, ms') -> 
      MDot (ctxnorm_mft (mf,cs)  ,  ctxnorm_msub (ms', cs))

and ctxnorm_mft (mf, cs) = match mf with
  | MObj (phat, tM) -> MObj (ctxnorm_psihat (phat,cs), ctxnorm (tM,cs))
  | PObj (phat, h)  -> PObj (ctxnorm_psihat (phat,cs), ctxnorm_head (h ,cs))
  | _ -> mf


and ctxnorm_typ (tA, cs) = match tA with
  | Atom (loc, a, tS) -> Atom (loc, a, ctxnorm_spine (tS, cs))
  | PiTyp ((TypDecl (x, tA), dep), tB) -> 
      PiTyp ((TypDecl (x, ctxnorm_typ (tA, cs)), dep), ctxnorm_typ (tB, cs))
  | TClo (tA, s) -> 
      TClo (ctxnorm_typ (tA, cs), ctxnorm_sub (s, cs))
  | Sigma trec -> 
      Sigma (ctxnorm_trec (trec, cs))

and ctxnorm_trec (trec, cs) = match trec with
  | SigmaLast tA -> SigmaLast (ctxnorm_typ (tA, cs))
  | SigmaElem (x, tA, trec) -> 
      SigmaElem (x, ctxnorm_typ (tA, cs), ctxnorm_trec (trec, cs))


and ctxnorm_dctx (cPsi, cs) = match cPsi with 
  | Null -> Null
  | DDec (cPsi', TypDecl (x, tA)) -> 
      DDec (ctxnorm_dctx (cPsi', cs), TypDecl (x, ctxnorm_typ (tA, cs)))
  | CtxVar (CInst (_n, {contents =  Some cPhi }, _schema, _octx, _mctx)) -> 
      ctxnorm_dctx (cPhi, cs)
  | CtxVar ctxvar -> begin match apply_csub ctxvar cs with
      | CtxVar cvar -> CtxVar cvar
      | Null        -> Null 
      | DDec _ as cPhi -> 
          cPhi
    end

and ctxnorm_psihat (phat, cs) = match phat with
  | (None , _ ) -> phat
  | (Some (CInst (_n, {contents =  Some cPhi }, _schema, _octx, _mctx)), k) -> 
      (match Context.dctxToHat cPhi with 
        | (None, l) -> (None, l+k)
        | (Some cvar, l) -> 
            begin match Context.dctxToHat (apply_csub cvar cs) with
              | (None, i) -> (None, l+k+i)
              | (Some cvar', i) -> (Some cvar', l+i+k)
            end        )


  | (Some cvar, k) -> 
      begin match Context.dctxToHat (apply_csub cvar cs) with
        | (None, i) -> (None, k+i)
        | (Some cvar', i) -> (Some cvar', i+k)
      end

(* The function below only works, if cs is a renaming substitution;
   if cs contains itself proper context with dependently typed declarations
   which make sense in cD itself, then we need to appropriately shift them 
- bp
*)

and ctxnorm_mctx (cD, cs) = match cD with
  | Empty -> Empty
  | Dec(cD', cdec) -> 
      Dec (ctxnorm_mctx (cD', cs), ctxnorm_cdec (cdec, cs))

and ctxnorm_cdec (cdec, cs) = match cdec with
  | MDecl (u, tA, cPsi) -> 
      MDecl(u, ctxnorm_typ (tA, cs), ctxnorm_dctx (cPsi, cs))
  | PDecl (u, tA, cPsi) -> 
      PDecl(u, ctxnorm_typ (tA, cs), ctxnorm_dctx (cPsi, cs))
  | MDeclOpt _ -> cdec
  | PDeclOpt _ -> cdec





(* would still require that cD is ordered in
   such a way that MVars with empty context are first.

and ctxnorm_mctx' (cD, cs) k = match cD with
  | Empty -> Empty
  | Dec(cD', cdec) -> 
      Dec (ctxnorm_mctx' (cD', cs) (k+1), ctxnorm_cdec' (cdec, cs) (k+1))

and ctxnorm_cdec' (cdec, cs) ms = match cdec with
  | MDecl (u, tA, cPsi) -> 
      MDecl(u, ctxnorm_typ (tA, cnorm (cs, MShift -k)), ctxnorm_dctx' (cPsi, (cnorm (cs, MShift -1)))
  | PDecl (u, tA, cPsi) -> 
      PDecl(u, ctxnorm_typ (tA, cs), ctxnorm_dctx' (cPsi, cs))
  | MDeclOpt _ -> cdec
  | PDeclOpt _ -> cdec

*)

let rec ctxnorm_ctyp (cT, cs) = match cT with
  | Comp.TypBool -> Comp.TypBool
  | Comp.TypBox (loc, tA, cPsi) -> 
     Comp.TypBox (loc, ctxnorm_typ (tA, cs), ctxnorm_dctx (cPsi, cs))
  | Comp.TypArr (cT1, cT2) -> 
      Comp.TypArr (ctxnorm_ctyp (cT1, cs), ctxnorm_ctyp (cT2, cs))
  | Comp.TypCross (cT1, cT2) -> 
      Comp.TypCross (ctxnorm_ctyp (cT1, cs), ctxnorm_ctyp (cT2, cs))
  | Comp.TypPiBox ((cdecl, dep), cT) -> 
      Comp.TypPiBox ((ctxnorm_cdec (cdecl, cs), dep), 
                     ctxnorm_ctyp (cT, cs))
  | Comp.TypCtxPi (ctx_dec, cT) -> 
     Comp.TypCtxPi (ctx_dec, ctxnorm_ctyp (cT, cdot1 cs))
  | Comp.TypClo (cT, t) -> 
      Comp.TypClo (ctxnorm_ctyp (cT, cs), ctxnorm_msub (t, cs))



let rec ctxnorm_gctx (cG, cs) = match cG with
  | Empty -> Empty
  | Dec(cG, Comp.CTypDecl (x, cT)) -> 
      Dec(ctxnorm_gctx (cG, cs), Comp.CTypDecl (x, ctxnorm_ctyp (cT, cs)))


let rec ctxnorm_csub cs = match cs with
  | CShift k -> CShift k
  | CDot (cPsi, cs) -> 
      CDot (ctxnorm_dctx (cPsi, CShift 0), ctxnorm_csub cs)


let rec lookupSchemaOpt cO psi_offset = match (cO, psi_offset) with
  | (Dec (_cO, CDecl (_, cid_schema, _)), 1) -> Some (cid_schema)
  | (Dec (cO, _) , i) -> 
      lookupSchemaOpt cO (i-1)
  | _ -> None



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
        (if psi < phi then 
           Shift (CtxShift (CtxOffset psi), k)
         else 
            Shift (CtxShift (CtxOffset (psi-1)), k)) 


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
        (if psi < phi then Shift(NegCtxShift (CtxOffset psi), k)
         else Shift(NegCtxShift (CtxOffset (psi-1)), k)
        )
  | Shift (CtxShift _ , k) -> s
  | Shift (NegCtxShift _ , k) -> s
  | Dot (ft, s) -> 
      Dot (csub_front cPsi phi ft, csub_sub cPsi phi s)

and csub_front cPsi k ft = match ft with
  | Head h -> Head (csub_head cPsi k h)
  | Obj tN -> Obj (csub_norm cPsi k tN)
  | Undef  -> Undef


(*

  x,y,z  |-  f(x,z) = y    instantiate y = 2 

   x,z   | x, f(x,z), z    lower all indices > 2 namely 3 by 1.


*)



let rec csub_meta_obj cD cPsi k mO = match mO with 
  | Syntax.Int.Comp.MetaCtx (loc, cPhi) -> 
      let cPhi' = csub_dctx cD cPsi k cPhi in 
        Syntax.Int.Comp.MetaCtx (loc, cPhi')
  | Syntax.Int.Comp.MetaObj (loc, phat, tM) -> 
      let phat' = csub_psihat cPsi k phat in 
      let tM'   = csub_norm cPsi k tM in 
        Syntax.Int.Comp.MetaObj (loc, phat', tM') 


and csub_meta_spine cD cPsi k mS = match mS with 
  | Syntax.Int.Comp.MetaNil -> Syntax.Int.Comp.MetaNil
  | Syntax.Int.Comp.MetaApp (mO, mS) -> 
      let mO' = csub_meta_obj cD cPsi k mO in 
      let mS' = csub_meta_spine cD cPsi k mS in 
        Syntax.Int.Comp.MetaApp (mO', mS')

and csub_ckind cD cPsi k cK = begin match cK with 
  | Syntax.Int.Comp.Ctype _ -> cK
  | Syntax.Int.Comp.PiKind (loc, (cdecl, dep), cK') -> 
      begin match cdecl with 
        | Syntax.Int.LF.CDecl _ -> 
            let cK' = csub_ckind cD (ctxnorm_dctx (cPsi, CShift 1)) (k+1) cK' in 
              Syntax.Int.Comp.PiKind (loc, (cdecl, dep), cK')
        | Syntax.Int.LF.MDecl (u, tA, cPhi) -> 
            let mdecl = MDecl (u, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi) in 
            let cK'    = csub_ckind (Dec(cD, mdecl)) (Whnf.cnormDCtx (cPsi, MShift 1)) k cK' in 
              Syntax.Int.Comp.PiKind (loc, (mdecl, dep), cK')
        | Syntax.Int.LF.PDecl (u, tA, cPhi) -> 
            let pdecl = PDecl (u, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi) in 
            let cK'    = csub_ckind (Dec(cD, pdecl)) (Whnf.cnormDCtx (cPsi, MShift 1)) k cK' in 
              Syntax.Int.Comp.PiKind (loc, (pdecl, dep), cK')
      end
end 

and csub_ctyp cD cPsi k tau = match tau with
  | Syntax.Int.Comp.TypBase (loc, c, mS) -> 
      let mS' = csub_meta_spine cD cPsi k mS in 
        Syntax.Int.Comp.TypBase (loc, c, mS')

  | Syntax.Int.Comp.TypBool ->
      Syntax.Int.Comp.TypBool 

  | Syntax.Int.Comp.TypBox (loc, tA, cPhi) -> 
      Syntax.Int.Comp.TypBox (loc, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi)

  | Syntax.Int.Comp.TypArr (tau1, tau2) -> 
      Syntax.Int.Comp.TypArr (csub_ctyp cD cPsi k tau1, csub_ctyp cD cPsi k tau2)

  | Syntax.Int.Comp.TypCross (tau1, tau2) -> 
      Syntax.Int.Comp.TypCross (csub_ctyp cD cPsi k tau1, csub_ctyp cD cPsi k tau2)

  | Syntax.Int.Comp.TypCtxPi (psi_decl, tau) -> 
      Syntax.Int.Comp.TypCtxPi (psi_decl, csub_ctyp cD (ctxnorm_dctx (cPsi, CShift 1)) (k+1) tau)

  | Syntax.Int.Comp.TypPiBox ((MDecl (u, tA, cPhi), dep), tau) -> 
      let mdecl = MDecl (u, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi) in 
      Syntax.Int.Comp.TypPiBox ((mdecl, dep),
                     csub_ctyp (Dec(cD, mdecl)) (Whnf.cnormDCtx (cPsi, MShift 1)) k tau)

  | Syntax.Int.Comp.TypPiBox ((PDecl (u, tA, cPhi), dep), tau) -> 
      let pdecl = PDecl (u, csub_typ cPsi k tA, csub_dctx cD cPsi k cPhi) in 
      Syntax.Int.Comp.TypPiBox ((pdecl, dep),
                     csub_ctyp (Dec(cD, pdecl)) (Whnf.cnormDCtx (cPsi, MShift 1)) k tau)

  | Syntax.Int.Comp.TypPiBox ((SDecl (u, cPhi0, cPhi1), dep), tau) -> 
      let sdecl = SDecl (u, csub_dctx cD cPsi k cPhi0, csub_dctx cD cPsi k cPhi1) in 
      Syntax.Int.Comp.TypPiBox ((sdecl, dep),
                     csub_ctyp (Dec(cD, sdecl)) (Whnf.cnormDCtx (cPsi, MShift 1)) k tau)


  | Syntax.Int.Comp.TypClo (tau, theta) -> 
      Syntax.Int.Comp.TypClo (csub_ctyp cD cPsi k tau, csub_msub cPsi k theta)

and csub_psihat cPsi phi (ctxvar, offset) = match ctxvar with 
  | None -> (None, offset)
  | Some (CtxOffset psi) -> 
      if phi = psi then 
        let (psivar, psi_offset) = dctxToHat cPsi in 
          (psivar, (psi_offset + offset))
       else (ctxvar, offset)


and csub_dctx cD cPsi k cPhi =  
  let rec csub_dctx' cPhi = match cPhi with 
    | Null -> (Null, false)
    | CtxVar (CtxOffset offset') ->         
        if offset' = k then 
          (cPsi, true) else 
            (if offset' < k then 
               (dprint (fun () -> "[csub_dctx] 0" ); 
               (CtxVar (CtxOffset offset'), false))
             else 
               (dprint (fun () -> "[csub_dctx] 1") ; (CtxVar (CtxOffset (offset' - 1)), false)))

    | CtxVar (CInst (_n, {contents =  Some cPhi }, _schema, _octx, _mctx)) ->         
        csub_dctx' cPhi

    | CtxVar (CInst (_n, {contents =  None }, _schema, _octx, _mctx)) ->         
        (cPhi , false)

    | DDec (cPhi, TypDecl (x, tA)) ->   
        let (cPhi', b) = csub_dctx' cPhi in 
        if b then       
          (* cPhi |- tA type     phi', cPhi' |- s : phi, cPhi *)
          let tA' = csub_typ cPsi k tA in 
          (DDec (cPhi', TypDecl(x, tA')), b)
        else 
          let _ = dprint (fun () -> "[csub_dctx] 2") in 
          let tA' = csub_typ cPsi k tA in 
            (DDec(cPhi', TypDecl (x, tA')), b)
(*            (DDec(cPhi', TypDecl (x, tA)), b) *)

    | DDec (cPhi, TypDeclOpt x) ->   
        let (cPhi', b) = csub_dctx' cPhi in 
          (DDec (cPhi', TypDeclOpt x), b)
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
      Comp.CtxFun(loc, n, csub_exp_chk (ctxnorm_dctx (cPsi, CShift 0)) (k+1) e)
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

  | Comp.Let (loc, i, (x,e)) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let e1 = csub_exp_chk cPsi k e in 
        Comp.Let (loc, i1, (x,e1))

  | Comp.Box (loc, phat, tM) -> 
      let phat' = csub_psihat cPsi k phat in 
      let tM'   = csub_norm cPsi k tM in 
        Comp.Box (loc, phat', tM')

  | Comp.If (loc, i, e1, e2) -> 
      let i' = csub_exp_syn cPsi k i in 
      let e1' = csub_exp_chk cPsi k e1 in 
      let e2' = csub_exp_chk cPsi k e2 in 
       Comp.If (loc, i', e1', e2')

  | Comp.Case (loc, prag, i, branches) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let branches' = List.map (fun b -> csub_branch cPsi k b) branches in 
        Comp.Case (loc, prag, i1, branches')

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

  | Comp.MApp (loc, i, (phat, Comp.NormObj tM)) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let tM' = csub_norm cPsi k tM  in
      let phat' = csub_psihat cPsi k phat in 
        Comp.MApp (loc, i1, (phat', Comp.NormObj tM'))

  | Comp.MApp (loc, i, (phat, Comp.NeutObj h)) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let h' = csub_head cPsi k h  in
      let phat' = csub_psihat cPsi k phat in 
        Comp.MApp (loc, i1, (phat', Comp.NeutObj h'))

  | Comp.MApp (loc, i, (phat, Comp.SubstObj s)) -> 
      let i1 = csub_exp_syn cPsi k i in 
      let s' = csub_sub cPsi k s  in
      let phat' = csub_psihat cPsi k phat in 
        Comp.MApp (loc, i1, (phat', Comp.SubstObj s'))

  | Comp.Ann (e, tau) -> 
      let e' = csub_exp_chk cPsi k e in 
      let tau' = csub_ctyp Empty (*dummy *) cPsi k tau in 
        Comp.Ann (e', tau')

  | Comp.Equal (loc, i1, i2) -> 
      let i1' = csub_exp_syn cPsi k i1 in 
      let i2' = csub_exp_syn cPsi k i2 in 
        Comp.Equal (loc, i1', i2')

  | Comp.Boolean b -> Comp.Boolean b

and csub_branch cPsi k branch = match branch with 
  | Comp.BranchBox (cO, cD, (cPhi, Comp.NormalPattern(pattern, e), ms, cs)) -> 
    (* currently we ignore the extra binding of context variables
       Feb 17 2010 - bp *)
      let cPhi' = csub_dctx Empty (*dummy *) cPsi k cPhi in  
      let pattern' = csub_norm cPsi k pattern in
      let ms'   = csub_msub cPsi k ms in 
      let e'    = csub_exp_chk cPsi k e in 
      let cD'   = csub_mctx cPsi k cD in 
        Comp.BranchBox (cO, cD', (cPhi', Comp.NormalPattern(pattern', e'), ms', cs))

  | Comp.BranchBox (cO, cD, (cPhi, Comp.EmptyPattern, ms, cs)) -> 
    (* currently we ignore the extra binding of context variables
       Feb 17 2010 - bp *)
      let cPhi' = csub_dctx Empty (*dummy *) cPsi k cPhi in  
      let ms'   = csub_msub cPsi k ms in 
      let cD'   = csub_mctx cPsi k cD in 
        Comp.BranchBox (cO, cD', (cPhi', Comp.EmptyPattern, ms', cs))




(* Normalizing terms and types with csub, i.e. a substitution for context variables *)



let id_csub cO = 
  let rec gen_id cO k = match cO with
  | Empty -> CShift k 
  | Dec (cO', CDecl(_psi, _sW, _)) -> 
      CDot(CtxVar (CtxOffset (k+1)), gen_id cO' (k+1) )
  | Dec (cO', CDeclOpt _ ) -> 
      CDot(CtxVar (CtxOffset (k+1)), gen_id cO' (k+1) )
  in 
    gen_id cO 0


(* instantiate  2 with 3    1/1  2/2  3/3  
       1/1   3/2  3/3   but we just eliminated the first declaration so
           1/1  2/2   i.e. lower all indices >=2 by 1.
                 |cO| = 2  ---> |cO'| = 1 *)
(* instantiate  2 with 1    1/1  1/2 *)
let rec inst_csub cPsi2 offset' csub cO = 
  let rec update_octx cO1 offset sW = 
    begin match (cO1, offset) with
      | (Dec (cO', CDeclOpt psi_name ), 1) ->      
           Dec(cO', CDecl (psi_name, sW, Maybe ))
      | (Dec (cO', cdec), k) -> 
          Dec(update_octx cO' (k-1) sW, cdec)  
    end
  in
  let check_schema_known cPsi2 cO = 
    begin match Context.ctxVar cPsi2 with
      | Some (CtxOffset psi2_offset) -> 
        begin match lookupSchemaOpt cO psi2_offset with 
            None   -> 
              let Some sW = lookupSchemaOpt cO offset' in 
                update_octx cO psi2_offset sW
          | Some _ -> cO
        end 

      | None ->
          cO
          (* raise (Violation "Encountered context variable, but it stands for the empty context") *)
    end
  in
  let rec decrement_csub cs  = 
      begin match cs with
        | CShift k -> CShift (k-1)
        | CDot (cPsi, cs) -> CDot (ctxnorm_dctx (cPsi, CShift(-1)), decrement_csub cs)
      end
  in
  let rec inst cvar_replaced offset csub cO' = 
    match (offset, csub, cO') with 
      | (1,  CDot(_ , cs),  Dec(cO', _ ) ) -> 
          (* cO |-  cPsi2      and   cO_new |- cs : cO' *)
          (*  lower all indices > offset' in Psi2 by k *) 
  (*          let cPsi2' = ctxnorm_dctx (cPsi2, CShift(-1)) in  *)
          let cPsi2' = match Context.dctxToHat cPsi2  with 
                     | (Some (CtxOffset k) , _ ) -> 
                         if cvar_replaced < k then ctxnorm_dctx (cPsi2, CShift(-1))
                         else cPsi2
                     | _ -> cPsi2
          in
          let cs'    = decrement_csub cs in 
            (cO', CDot (cPsi2', cs'))   

(*
      | (n, CDot(_, cs),  Empty) -> inst cvar_replaced n cs cO'
      | (1, CShift _,  Empty) -> (Empty, csub)
*)

      | (n,  CDot(ft, cs),  Dec(cO', ((CDecl _ ) as dec))) -> 
          let (cO', cs') = inst cvar_replaced (n-1) cs cO' in 
            (Dec(cO', dec), CDot(ft, cs'))
  in 
  let cO' = check_schema_known cPsi2 cO in 
     inst offset' offset' csub cO'




(*
Not needed for now?  Also broken in the case of branches
Wed Feb 17 16:35:22 2010 -bp 
*)
let rec ctxnorm_exp_chk (e', cs) = 
  match e' with 
  | Comp.Syn (loc, i) -> 
      Comp.Syn(loc, ctxnorm_exp_syn (i, cs))
  | Comp.Rec (loc, n, e) -> 
      Comp.Rec(loc, n, ctxnorm_exp_chk (e,cs))
  | Comp.Fun (loc, n, e) -> 
      Comp.Fun(loc, n, ctxnorm_exp_chk (e, cs))
  | Comp.CtxFun (loc, n, e) -> 
      Comp.CtxFun(loc, n, ctxnorm_exp_chk (e, cdot1 cs))
  | Comp.MLam (loc, u, e) -> 
      Comp.MLam(loc, u, ctxnorm_exp_chk (e, cs))
  | Comp.Pair (loc, e1, e2) -> 
      let e1' = ctxnorm_exp_chk (e1,cs) in 
      let e2' = ctxnorm_exp_chk (e2, cs) in 
        Comp.Pair (loc, e1', e2')

  | Comp.LetPair (loc, i, (x,y,e)) -> 
      let i1 = ctxnorm_exp_syn (i, cs) in 
      let e1 = ctxnorm_exp_chk (e, cs) in 
        Comp.LetPair (loc, i1, (x,y,e1))

  | Comp.Box (loc, phat, tM) -> 
      let phat' = ctxnorm_psihat (phat, cs) in 
      let tM'   = ctxnorm (tM, cs) in 
        Comp.Box (loc, phat', tM')

  | Comp.Case (loc, prag, i, branches) -> 
      let i1 = ctxnorm_exp_syn (i,cs) in 
      let branches' = List.map (fun b -> ctxnorm_branch (b,cs)) branches in 
        Comp.Case (loc, prag, i1, branches')

and ctxnorm_exp_syn (i',cs) = match i' with
  | Comp.Const _c -> i'
  | Comp.Var _    -> i'
  | Comp.Apply (loc, i, e) -> 
      let i1 = ctxnorm_exp_syn (i,cs) in 
      let e1 = ctxnorm_exp_chk (e,cs) in 
        Comp.Apply (loc, i1, e1)
  | Comp.CtxApp (loc, i, cPhi) -> 
      let cPhi' = ctxnorm_dctx (cPhi, cs) in 
      let i1    = ctxnorm_exp_syn (i, cs) in 
        Comp.CtxApp (loc, i1, cPhi')

  | Comp.MApp (loc, i, (phat, Comp.NormObj tM)) -> 
      let i1 = ctxnorm_exp_syn (i,cs) in 
      let tM' = ctxnorm (tM, cs)  in
      let phat' = ctxnorm_psihat (phat, cs) in 
        Comp.MApp (loc, i1, (phat', Comp.NormObj tM'))

  | Comp.Ann (e, tau) -> 
      let e' = ctxnorm_exp_chk (e, cs) in 
      let tau' = ctxnorm_ctyp (tau, cs) in 
        Comp.Ann (e', tau')
        
and ctxnorm_branch (branch,cs') = match branch with  
  | Comp.BranchBox (cO, cD, (cPhi, pattern, ms, cs)) ->  
    (* technically, we need to unify cs and cs' 
       Feb 17 2010 - bp *) 
        Comp.BranchBox (cO, cD, (cPhi, pattern, ms, cs))

let rec ctxShift cPsi = match cPsi with
  | Null              -> Shift (NoCtxShift , 0 )
  | CtxVar psi        -> Shift (CtxShift psi, 0)
  | DDec   (cPsi, _x) -> 
      let Shift(cshift, n) = ctxShift cPsi in
        Shift (cshift, n+1)

(* ctxToSub_mclosed cD psi cPsi = (cD', s)

   if x1:A1, ... xn:An = cPsi  and 
       . ; cD |- cPsi dctx
       

      cD, cD_ext ; psi  |-  s : cPsi
   then 

   s.t. cD, cD_ext; psi |- u1[id]/x1 ... un[id]/xn : cPsi
    and where cD_ext = u1:A1[psi], ... un:An[psi]

if  ctxToSub_mclosed  cD psi cPsi = (cD',s) then    
   cD' ; psi |- s : cPsi

*)
let rec ctxToSub_mclosed cD psi cPsi = 
  let rec toSub cPsi =  match cPsi with
    | Null ->
      (* Substitution.LF.id  --changed 2010-07-26*)
      (cD, ctxShift psi, 0)
            
    | DDec (cPsi', TypDecl (_, (Atom _  as tA))) ->
        Debug.indent 2;
      let (cD', s, k) = toSub cPsi' in  (* cD' ; psi |- s : cPsi' *)
        Debug.outdent 2;
        dprint (fun () -> "s = " ^ subToString s);
        (* For the moment, assume tA atomic. *)

      let u     = Root(Syntax.Loc.ghost, MVar(Offset 1,  Substitution.LF.id), Nil) in 

        (* cD' ; psi |- s : cPsi' *)
        (* cD' ; psi |- u[id] : [s]tA *)

      let tA'   = TClo(tA, s) in 
      (* cD', u: _   ; psi |- s : cPsi', x:tA *)
      let s' = Whnf.cnormSub (s, MShift 1) in 
      let result = Dot(Obj u, s') in

      let u_name = Id.mk_name (Id.MVarName (Typ.gen_mvar_name tA')) in 
        (* dprint (fun () -> "[ctxToSub_mclosed] result = " ^ subToString result); *)
        (Dec (cD', MDecl(u_name , tA', Whnf.cnormDCtx (psi, MShift k))), result, k+1)
  in
    toSub cPsi





(* ctxToSub' cD cPhi cPsi = s 

   if x1:A1, ... xn:An = cPsi
      . ; . |- cPsi dctx
      cD    |- cPhi dctx
    
   then D = u1:A1[cD ; cPhi], ... un:An[cD ; cPhi]

   s.t. D; cPhi |- u1[m_id ; id]/x1 ... un[m_id]/xn : cPsi

   and  cD ; cPhi |- s : cPsi

*)
let rec ctxToSub' cD cPhi cPsi = match cPsi with
  | Null ->
      (* Substitution.LF.id  --changed 2010-07-26*)
      ctxShift cPhi

  | DDec (cPsi', TypDecl (n, tA)) ->
      Debug.indent 2;
      let s = ((ctxToSub' cD cPhi cPsi') : sub) in
      (* cD ; cPhi |- s : cPsi' *)
         Debug.outdent 2;
      dprint (fun () -> "s = " ^ subToString s);
        (* For the moment, assume tA atomic. *)
        (* lower tA? *)
        (* A = A_1 -> ... -> A_n -> P

           create cPhi = A_1, ..., A_n
           \x_1. ... \x_n. u[id]
           u::P[cPhi]

           already done in reconstruct.ml
           let (_, d) = dctxToHat cPsi in
           let tN     = etaExpandMV Null (tA, s) (Shift d) in
           in elSpineIW
        *)
      (* let (_, phat') = dctxToHat cPsi' in*)
      (* let u     = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in *)
      (* let u     = Whnf.etaExpandMV Null (tA, s) LF.id in *)
        (* let u = Whnf.newMVar (Null ,  TClo(tA, s)) in *)
(* following 3 lines removed, 2010-07-26
      let composition = Substitution.LF.comp s (ctxShift cPhi) in
      dprint (fun () -> "composition = " ^ subToString composition);
      let u     = Whnf.etaExpandMMV None cD cPhi (tA, composition) Substitution.LF.id in 
*)
      let u     = Whnf.etaExpandMMV Syntax.Loc.ghost cD cPhi (tA, s) n Substitution.LF.id in 
      let front = (Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : front) in
      (* cD ; cPhi |- s : cPsi' *)
      (* cD ; cPhi |- u[id] : [s]tA *)
      (* cD ; cPhi |- Dot(s, Obj u) : cPsi', x:tA *)
      (* let shifted = Substitution.LF.comp s Substitution.LF.shift in*)
      (* dprint (fun () -> "shifted = " ^ subToString shifted);*)
      let result = Dot(front, s) in
      dprint (fun () -> "result = " ^ subToString result);
        result


let rec mctxToMSub cD = match cD with
  | Empty -> Whnf.m_id
  | Dec (cD', MDecl(n, tA, cPsi)) ->
      let t     = mctxToMSub cD' in
      let _ = dprint (fun () -> "[mctxToMSub] cD' = " ^ P.mctxToString cD') in
      let _     = dprint (fun () -> "[mctxToMSub] t = " ^ P.msubToString Empty t) in 
      let cPsi' = Whnf.cnormDCtx (cPsi,t) in
      let tA'   = Whnf.cnormTyp (tA, t) in
      let u     = Whnf.newMVar (Some n) (cPsi', tA') in
      let phat  = Context.dctxToHat cPsi' in
        MDot (MObj (phat, Root (Syntax.Loc.ghost, MVar (u, Substitution.LF.id), Nil)) , t)

  | Dec(cD', PDecl(n, tA, cPsi)) ->
      let t    = mctxToMSub cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi, t) in
      let p    = Whnf.newPVar (Some n) (cPsi', Whnf.cnormTyp (tA, t)) in
      let phat = dctxToHat cPsi' in
        MDot (PObj (phat, PVar (p, Substitution.LF.id)) , t)

  | Dec (cD', CDecl(n, sW, _)) -> 
      let t = mctxToMSub cD' in 
      let cvar = Whnf.newCVar (Some n) sW in 
        MDot (CObj (CtxVar cvar), t)




let rec mctxToMMSub cD0 cD = match cD with
  | Empty -> MShift (Context.length cD0)   
  | Dec (cD', MDecl(n, tA, cPsi)) ->
      let t     = mctxToMMSub cD0 cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi,t) in
      let tA'   = Whnf.cnormTyp (tA, t) in
      let u     = Whnf.newMMVar (Some n) (cD0, cPsi', tA') in
      let phat  = Context.dctxToHat cPsi' in
        MDot (MObj (phat, Root (Syntax.Loc.ghost, MMVar (u, (Whnf.m_id, Substitution.LF.id)), Nil)) , t)

  | Dec(cD', PDecl(n, tA, cPsi)) ->
     (* This is somewhat a hack...  *)
      let t    = mctxToMSub cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi, t) in
      let p    = Whnf.newPVar (Some n) (cPsi', Whnf.cnormTyp (tA, t)) in
      let phat = dctxToHat cPsi' in
        MDot (PObj (phat, PVar (p, Substitution.LF.id)) , t)

  | Dec (cD', CDecl (n, sW, _ )) -> 
     (* This is somewhat a hack...  *)
      let _     = dprint (fun () -> "[mctxToString] CDecl " ^ n.string_of_name) in 
      let t = mctxToMMSub cD0 cD' in 
      let _     = dprint (fun () -> "[mctxToString] CDecl continued " ^ n.string_of_name) in 
      let cvar = Whnf.newCVar (Some n) sW in 
        MDot (CObj (CtxVar cvar), t)




let rec cctxToCSub cO cD = match cO with
  | Empty -> CShift 0
  | Dec (cO, CDecl (psi, schema, _)) -> 
      let ctxVar = CtxVar (CInst (psi, ref None, schema, cO, cD)) in
      let cs = cctxToCSub cO cD  in 
        CDot (ctxVar, cs)



(* The following functions are from an attempt to improve printing of meta-variables;
   the idea was to check if the result of applying a substitution produced an "equivalent"
   context, and if so, to use the original names.  -jd 2010-07 *)
let rec isomorphic cD1 cD2 = match (cD1, cD2) with
  | (Empty, Empty) -> true
  | (Empty, _) -> false
  | (_, Empty) -> false
  | (Dec(cD1', dec1),  Dec(cD2', dec2)) ->
       isomorphic cD1' cD2' && isomorphic_ctyp_decl dec1 dec2

and isomorphic_ctyp_decl dec1 dec2 = match (dec1, dec2) with
  | (MDecl(_, tA1, dctx1),  MDecl(_, tA2, dctx2)) -> isomorphic_typ tA1 tA2 && isomorphic_dctx dctx1 dctx2
  | (PDecl(_, tA1, dctx1),  PDecl(_, tA2, dctx2)) -> isomorphic_typ tA1 tA2 && isomorphic_dctx dctx1 dctx2
  | (SDecl(_, dctx1A, dctx1B),  SDecl(_, dctx2A, dctx2B)) -> isomorphic_dctx dctx1A dctx2A && isomorphic_dctx dctx2A dctx2B
  | (CDecl _, CDecl _) -> false  (* unsupported *)
  | (MDeclOpt _, MDeclOpt _) -> true
  | (PDeclOpt _, PDeclOpt _) -> true
  | (CDeclOpt _, CDeclOpt _) -> false  (* unsupported *)
  | (_, _) -> false
      
and isomorphic_dctx dctx1 dctx2 = (dctx1 = dctx2) (* match (dctx1, dctx2) with *)

and isomorphic_typ tA1 tA2 = (tA1 = tA2)
;; (* ocaml is unhappy without the ;; *)
