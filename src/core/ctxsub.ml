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
  in
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
  | CoShift (_co_cid , NoCtxShift, _k) -> s

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
      let mdecl = MDecl (u, tA, csub_dctx cD cPsi k cPhi) in 
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

  | Some (CoCtx (co_cid, phi)) -> 
      let rec subst phi = match phi with
	| CtxOffset psi -> 
	    if k = psi then 
	      let (psivar, psi_offset) = dctxToHat cPsi in 
		(psivar, psi_offset + offset)
	    else 
	      (ctxvar, offset)
	| CoCtx (co_cid', phi') -> 
	    (* This again assumes we preserve the length of the context
	       by applying the coercion *)
	    let (phi1_opt, offset1) = subst phi' in 
	      match phi1_opt with
		  None -> (None, offset1)
		| Some phi1 -> 
		    (Some (CoCtx (co_cid', phi1)), offset1)
      in 
      let (psivar_opt, offset) = subst phi in 
	match psivar_opt with
	    None -> (None, offset)
	  | Some psivar -> 
	      (Some (CoCtx(co_cid, psivar)), offset)
(* ******************************************************************** *)
(* Shift term (type etc.) to the new context                            *)
(* coerceTerm co_cid cPsi (tM, s) = sN where co_cid(cPsi) |- sN *)
(*  

*)
and coerceTerm co_cid sM = coerceTermW co_cid (Whnf.whnf sM)
and coerceTermW co_cid sM = match sM with
  | (Lam (loc, x, tM), s) -> 
      Lam(loc, x, coerceTerm co_cid (tM, LF.dot1 s))
  | (Root (loc, h, tS), s (* id *)) -> 
      Root (loc, (coerceHead co_cid  h), coerceSpine co_cid  (tS, s))
  | (Tuple (loc, tuple), s) -> 
      Tuple (loc, coerceTuple co_cid (tuple, s))

and coerceTuple co_cid (tuple, s) = match tuple with
  | Last tM -> Last (coerceTerm co_cid (tM, s))
  | Cons (tM, rest) ->
      let tM' = coerceTerm co_cid (tM,s) in
      let rest' = coerceTuple co_cid (rest,s) in
        Cons (tM', rest')

and coerceHead co_cid h = match h with 
  | MVar (cvar, s')  -> 
      MVar(cvar, coerceSub co_cid s') 
  | PVar (cvar, s')  -> 
      PVar (cvar, coerceSub co_cid s')
  | MMVar (u, (t, s)) -> 
      MMVar (u, (t, coerceSub co_cid s))
  | _ -> h

and coerceSub co_cid s = match s with
  | Dot(Head h, s') -> 
      Dot(Head (coerceHead co_cid h), coerceSub co_cid s')
	
  | Dot (Block (h,i), s) -> 
      Dot(Block (coerceHead co_cid h,i),  coerceSub co_cid s)

  | Dot (Obj tM, s) -> 
      Dot (Obj (coerceTerm co_cid (tM, LF.id)), coerceSub co_cid s)

  | Shift (psi, n) -> CoShift(co_cid, psi, n)
  (* | CoShift (Coe co_cid', psi, n) -> CoShift (Coe co_cid, CoCtx (co_cid', psi), n)*)
  (* Fri Sep  4 11:34:16 2009 -bp Not handled yet; seems to indicate
     we need CoCtx (InvCoe(co_cid), psi) *)
  (* | CoShift (InvCoe co_cid', psi, n) -> CoShift (Coe co_cid, CoCtx(co_cid', psi), n)*)

and coerceSpine co_cid sS = match sS with
  | (Nil, s) -> Nil
  | (App (tM, tS), s) -> 
      App (coerceTerm co_cid (tM, s), coerceSpine co_cid (tS, s))
  | (SClo (tS, s), s') -> 
      coerceSpine co_cid (tS, LF.comp s s')

and coerceTypRec co_cid sArec = match sArec with
  | (SigmaLast tA, s) -> SigmaLast (coerceTyp co_cid (tA, s))
  | (SigmaElem (x, tA, recA), s) -> 
      SigmaElem (x, coerceTyp co_cid (tA, s), coerceTypRec co_cid (recA, LF.dot1 s))

and coerceTyp  co_cid  sA = coerceTypW co_cid (Whnf.whnfTyp sA) 
and coerceTypW co_cid  sA = match sA with 
  | (Atom(loc, a, tS)  ,s) -> Atom (loc, a, coerceSpine co_cid (tS, s))
  | (PiTyp ((TypDecl(x, tA),dep), tB), s) -> 
      PiTyp((TypDecl(x, coerceTyp co_cid (tA, s)), dep), coerceTyp co_cid (tB, LF.dot1 s))
  | (Sigma recA, s) -> 
      Sigma (coerceTypRec co_cid (recA, s))


(* ******************************************************************** *)
(* coeTypRec coe_list cD (cPsi, sArec) = srec 

   let coe_list is a list of coercion branches i, s.t.
     some Phi_i. trecA_i ==> trecBopt_i  
      
   If cD ; cPsi |- sArec and 
      there exists a coercion branch
      some Phi. trecA ==> trecBopt   
    
     s.t. there exists a substitution ms for the variables in Phi 
     and |[ms]|trecA = sArec

   then |[ms]|trecBopt   and cD ; cPsi |- |[ms]|trecBopt

*)
and coeTypRec coe_list cD (cPsi, sArec)  = match coe_list with 
  | [] -> raise (Violation "No coercion defined to given type")
  | (CoBranch (some_part, trec1, trec2opt)::c_list) -> 
       let dctx  = projectCtxIntoDctx some_part in
       let s     = ctxToSub dctx in
       let phat  = dctxToHat cPsi in
         begin try 
           Unify.matchTypRec cD phat sArec (trec1, s);
           begin match trec2opt with
	       Some trec2 -> (trec2, s) 
           (* cPsi |- [s]trec2   *) 
           (* NOTE in general: We need to find a substitution s' s.t. cPhi |- s' <= cPsi 
              and eventually return [s']([s]trec2)
              This here assumes that the coercion is a one-to-one mapping.
           *)
	     | None -> raise (Violation "Coercion drops elements – not implemented")
	   end 
         with _ -> coeTypRec c_list cD (cPsi, sArec)
         end


(* applyCtxCoe coe_list cPsi = cPsi' 

  if coe_list is the list of coercions defined for co_cid 
      and co_cid maps contexts of schema W1 to schema W2,

  and cO ; cD |- cPsi : W1
  then
      cO ; cD |- cPsi' : W2     

*)
and applyCtxCoe co_cid cD cPsi = match cPsi with
    Null -> Null
  | CtxVar psi -> CtxVar (CoCtx (co_cid, psi))
  | DDec (cPsi', TypDecl (n, tA)) -> 
      let sArec = match Whnf.whnfTyp (tA, LF.id) with
        | (Sigma tArec,s') -> 
            (tArec, s') 
        | (nonsigma, s') -> 
            (SigmaLast nonsigma, s') in
      let sB = match coeTypRec (Coercion.get_coercion co_cid) cD (cPsi, sArec) with
          (SigmaLast nonsigma, s) -> (nonsigma, s)
        | (tBrec, s) -> (Sigma tBrec, s)
      in 
      let tB' = coerceTyp (Coe co_cid) sB in
        (* cPsi |- tB but we need however cPhi |- [s]trec2 ! *)
        (* NOTE in general: We need to find a substitution s' s.t. cPhi |- s' <= cPsi 
              and eventually return [s']([s]tB)
              This here assumes that the coercion is a one-to-one mapping, and hence
              s' is Shift 0.
        *)  
      let cPhi = applyCtxCoe co_cid cD cPsi' in 
        DDec (cPhi, TypDecl (n, tB'))


(* invcoeTypRec coe_list cD (cPsi, sArec) = srec 

   let coe_list is a list of coercion branches i, s.t.
     some Phi_i. trecA_i ==> trecBopt_i  
      
   If cD ; cPsi |- sArec and 
      there exists a coercion branch
      some Phi. trecA ==> trecBopt   
    
     s.t. there exists a substitution ms for the variables in Phi 
     and |[ms]|trecBopt = sArec

   then |[ms]|trecA   and cD ; cPsi |- |[ms]|trecA

*)
and invcoeTypRec coe_list cD (cPsi, sArec)  = match coe_list with 
  | [] -> raise (Violation "No coercion defined to given type")
  | (CoBranch (some_part, trec1, Some trec2)::c_list) -> 
       let dctx  = projectCtxIntoDctx some_part in
       let s     = ctxToSub dctx in
       let phat  = dctxToHat cPsi in
         begin try 
           Unify.matchTypRec cD phat sArec (trec2, s);
           (trec1, s)
         with _ -> invcoeTypRec c_list cD (cPsi, sArec)
         end
 | (CoBranch (_ , _ , None)::c_list) -> 
     (Printf.printf "\nCoercion drops elements – coercion branch not invertible\n" ; 
      invcoeTypRec c_list cD (cPsi, sArec))



(* applyInvCtxCoe coe_list cPsi = cPsi' 

  if coe_list is the list of coercions defined for co_cid 
      and co_cid maps contexts of schema W1 to schema W2,

  and cO ; cD |- cPsi : W2
  then
      cO ; cD |- cPsi' : W1     

*)
and applyInvCtxCoe co_cid cD cPsi = match cPsi with
    Null -> Null
  | CtxVar (CoCtx (co_cid', psi)) when co_cid = co_cid' -> CtxVar psi 
  | DDec (cPsi', TypDecl (n, tA)) -> 
      let sArec = match Whnf.whnfTyp (tA, LF.id) with
        | (Sigma tArec,s') -> 
            (tArec, s') 
        | (nonsigma, s') -> 
            (SigmaLast nonsigma, s') in
      let sB = match invcoeTypRec (Coercion.get_coercion co_cid) cD (cPsi, sArec) with
          (SigmaLast nonsigma, s) -> (nonsigma, s)
        | (tBrec, s) -> (Sigma tBrec, s)
      in 
      let tB' = coerceTyp (InvCoe co_cid) sB in
        (* cPsi |- tB but we need however cPhi |- [s]trec2 ! *)
        (* NOTE in general: We need to find a substitution s' s.t. cPhi |- s' <= cPsi 
              and eventually return [s']([s]tB)
              This here assumes that the coercion is a one-to-one mapping, and hence
              s' is Shift 0.
        *)  
      let cPhi = applyInvCtxCoe co_cid cD cPsi' in 
        DDec (cPhi, TypDecl (n, tB'))


and csub_ctxCoe co_cid cD (phi,k) cPsi = match phi with
  | CtxOffset offset -> 
      if k = offset then 
        ((applyCtxCoe co_cid cD cPsi), true) 
      else (CtxVar phi, false)
  | CoCtx (co_cid', phi') -> 
      let (cPsi', flag) = csub_ctxCoe co_cid' cD (phi',k) cPsi in 
	if flag then 
	  ((applyCtxCoe co_cid cD cPsi') , true)
	else
	  (cPsi', false)

and csub_dctx cD cPsi k cPhi = 
  let rec csub_dctx' cPhi = match cPhi with 
    | Null -> (Null, false)
    | CtxVar (phi) -> 
        let rec check_ctx_var phi = match phi with
          | CtxOffset offset -> 
              if k = offset then 
                (cPsi, true) else (CtxVar phi, false)
          | CoCtx (co_cid , phi') -> 
	      csub_ctxCoe co_cid cD (phi',k) cPsi 
        in 
          check_ctx_var phi 

    

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
      
