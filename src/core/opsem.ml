(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

open Store
open Store.Cid
open Syntax
open Syntax.Int.Comp
open Substitution
open Id

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail 
module C     = Whnf
module I     = Syntax.Int



module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer
module RR = Pretty.Int.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [4])

exception NotImplemented
exception Error of Syntax.Loc.t option * Error.error
exception Violation  of string
exception BranchMismatch


let rec length_env env = begin match env with
  | Empty -> 0
  | Cons(_ , env') -> length_env env' + 1
end

let rec lookupValue x env = begin match (x, env) with
  | (1, Cons (v, env'))  -> v 
  | (n, Cons (_ , env')) -> lookupValue (n-1) env'
  (* otherwise undefined *)
end 



(* ******************************************************************************* *)
(* Substitution for computation-level bound variables

   If D ; G |- e <= tau   and   . |- theta <= D   and   . |- eta <= [|theta|]G 
   then     [eta][|theta|]e

  Code below is broken ... 

let rec subst_chk offset e eta = match e with 
  | Syn (loc, i)         -> Syn(loc, subst_syn offset i eta)
  | Fun (loc, f, e)      -> Fun (loc, f, subst_chk (offset+1) e eta)
  | CtxFun (loc, psi, e) -> CtxFun (loc, psi, subst_chk offset e eta)
  | Pair (loc, e1, e2)   -> 
     Pair(loc, subst_chk offset e1 eta, subst_chk offset e2 eta)
  | LetPair (loc, i, (x,y, e)) -> 
      LetPair(loc, subst_syn offset i eta, 
              (x,y, subst_chk (offset+2) e eta))
  | Box(_loc, _phat, _tM) -> e 
  | SBox _ -> e 
  | Case (loc, i, branches) -> 
      Case (loc, subst_syn offset i eta, subst_branches offest branches eta)

and subst_syn offset i eta = match i with 
  | Var x -> 
  | Const c -> Const c
  | Apply (loc, i, e) -> 
      Apply (loc, subst_syn offset i eta, subst_chk offset e eta)
  | MApp (loc, i, (phat,tM)) -> 
      MApp (loc, subst_syn offset i eta, (phat, tM))
  | CtxApp (loc, i, cPsi) -> 
      CtxApp (loc, subst_syn offset i eta, cPsi)
  | Ann (e, tau) -> Ann (subst_chk offset e eta, tau)


and subst_branch offset branch eta = match branch with
  | BranchBox (cD, pattern, e) -> 
      BranchBox (cD, pattern, subst_chk offset e eta)

and subst_branches offset branches eta = 
  List.map (fun b -> subst_branch offset b eta) branches
*)


(* ******************************************************************************* *)

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



(* eval e (theta, eta) = v 

where  cD ; cG |- e <= wf_exp
       .       |- theta <= cD
       .  ; .  |- eta   <= [|theta|]cG

*)


let rec eval_syn i theta_eta = 
  let (theta, eta ) = theta_eta in
  let _ = dprint (fun () -> "\n[eval_syn] with  theta = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) in
    match i with  
  | Const cid -> 
      let e = (Comp.get cid).Comp.prog in 
      eval_chk  e (theta, Cons(RecValue ((cid, e), theta, eta) ,eta))

  | Var x     -> 
      let _ = dprint (fun () -> "[eval_syn] Looking up " ^ string_of_int x ^ " in environment") in 
	begin match lookupValue x eta with	   
	  | RecValue ((cid,e'), theta', eta') as w -> 
	      dprint (fun () -> "[eval_syn] Var case : Lookup found RecValue\n");
	      dprint (fun () -> "\n[eval_syn] with  theta' = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta'));
	      eval_chk e' (theta',Cons(w, eta'))
	  | v -> v
	end 

  | Apply (_ , i', e') -> 
      let w2 = eval_chk e' theta_eta in 
      let _ = dprint (fun () -> "[eval_syn] Apply argument evaluated ") in 
      let _ = dprint (fun () -> "[eval_syn] Extended environment: |env| =  " ^ 
				string_of_int (length_env eta))    in 
      let _ = dprint (fun () -> "\n[eval_syn] with  theta = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) in
	begin match eval_syn i' theta_eta with
	  | FunValue ((_loc, _x , e'), theta1, eta1) -> 
	      let _ = dprint (fun () -> "[eval_syn] Extended environment: |env1| =  " ^ 
				string_of_int (length_env eta1)) in 
	      let _ = dprint (fun () -> "[eval_syn] Extended environment: |env1'| =  " ^ 
				string_of_int (length_env (Cons(w2,eta1)))   ) in 
      let _ = dprint (fun () -> "\n[eval_syn] with  theta1 = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta1)) in
	      eval_chk e' (theta1, Cons(w2,eta1))
	  | _ -> raise (Violation "Expected FunValue")
	end
  | MApp (_, i', (phat, tM)) -> 
      begin match eval_syn i' theta_eta with
	| MLamValue ((_loc, _u, e'), theta1, eta1) -> 
            eval_chk e' (I.LF.MDot(I.LF.MObj(phat, Whnf.cnorm (tM, theta)), theta1), eta1)
	| _ -> raise (Violation "Expected MLamValue")
      end

  | CtxApp (_, i', cPsi) -> 
      begin match eval_syn i' theta_eta with
	| CtxValue ((_loc, _psi, e'), theta1, eta1) -> 
	    let _ = dprint (fun () -> "CtxApp BEFORE substitution cPsi") in 
	    let e1 = Ctxsub.csub_exp_chk (Whnf.cnormDCtx (cPsi,theta)) 1 e' in 
	    let _ = dprint (fun () -> "CtxApp AFTER substitution cPsi") in 
	    eval_chk e1 (theta1,eta1)
	| _ -> raise (Violation "Expected CtxValue")
      end 

  | Ann (e, _tau) -> 
      eval_chk e theta_eta

    

and eval_chk e theta_eta =  
  let (theta,eta) = theta_eta in 
    match e with
      | Syn(_, i) -> eval_syn i theta_eta
(*      | Rec (loc, n, e') -> 
	  let w = RecValue ((loc, n, e'), theta, eta) in  
	  let _ = dprint (fun () -> "[eval_chk] rec-case -1- |env| = " ^ string_of_int (length_env eta) ^ "\n") in 
	  let eta' = Cons(w, eta) in 
	  let _ = dprint (fun () -> "[eval_chk] rec-case -2- |env| = " ^ string_of_int (length_env eta') ^ "\n") in 
	    eval_chk e' (theta, Cons(w, eta))*) 
      | MLam(loc, n, e') -> 
	  MLamValue ((loc, n ,e'), theta, eta) 
      | CtxFun (loc, n, e') -> 
	  CtxValue ((loc,n,e'), theta, eta)
      | Fun(loc, n, e') -> 
	  FunValue ((loc, n, e'), theta, eta)
      | Box(_loc, phat, tM) -> 
	  BoxValue (phat, C.cnorm (tM, theta))
      | Case(_, i, branches) ->  
	(match eval_syn i theta_eta with
	  | BoxValue (phat, tM) -> 	  
	      let _ = dprint (fun () -> "[eval_syn] Evaluated scrutinee ...") in 
	      eval_branches (phat,tM) (branches, theta_eta)
	  | _ -> raise (Violation "Expected BoxValue for case"))

      | Value v -> v

and eval_branches (phat,tM) (branches, theta_eta) = match branches with 
  | [] -> raise (Violation "Missing branch - Non-exhaustive pattern match") 
  | b::branches -> 
	let (theta, _ ) = theta_eta in 
      begin try 
	 dprint (fun () -> "\n[eval_branches] try branch with  theta = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) ;  
	eval_branch (phat,tM) b  theta_eta
      with BranchMismatch -> 
	(dprint (fun () -> "[eval_branches] Try next branch ...");
	 dprint (fun () -> "\n[eval_branches] with  theta = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) ; 
	eval_branches (phat,tM) (branches, theta_eta))
      end

and eval_branch (phat, tM) (BranchBox (cD, (cPsi' , tM', theta'), e)) (theta, eta) = 
  let mt      = mctxToMSub cD in 
  let theta_k = Whnf.mcomp theta' mt in 
    begin try
      (dprint (fun () -> "Unify msub: theta =  " ^ 
		 P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta) ) ; 
       dprint (fun () -> "Unify Refinement  theta_k = " ^ 
                 P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta_k)) ; 
	Unify.unifyMSub theta theta_k ; 
       dprint (fun () -> "After unification: theta =  " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta) ) ; 
       dprint (fun () -> "     theta_k = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta_k)) ; 
       Unify.unify I.LF.Empty cPsi' (tM, LF.id) (C.cnorm (tM', mt), LF.id) ;
       dprint (fun () -> "\n[eval_chk] body with  mt = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub mt)) ; 
      eval_chk e (Whnf.cnormMSub mt, eta))
    with 
	Unify.Unify _ -> raise BranchMismatch
    end



let rec eval i  =  
  let _ = dprint (fun () -> "\n\nSTART EVALUATION\n") in
  begin match eval_chk i (I.LF.MShift 0, Empty) with
    | ConstValue cid -> Syn(None, Const cid)
    | BoxValue (phat, tM) -> Box(None, phat, tM)
    | v -> Value v
  end
