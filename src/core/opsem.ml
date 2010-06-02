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

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [9])

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

  Code below is broken... 

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

(* ********************************************************************* *)
let rec cctxToCSub cO cD cPsi = match cO with
  | Int.LF.Empty -> I.LF.CShift 0
  | Int.LF.Dec (cO, Int.LF.CDecl (_psi, schema)) -> 
      let ctxVar = Int.LF.CtxVar (Int.LF.CInst (ref None, schema, cO, cD)) in
      let cs = cctxToCSub cO cD cPsi in 
        I.LF.CDot (ctxVar, cs)

let mctxToMSub = Ctxsub.mctxToMSub

let rec add_mrecs n_list cs theta eta = begin match n_list with 
  | [] ->  eta
  | n'::n_list' -> 
      let cid' = Comp.index_of_name n' in 
      let e' = (Comp.get cid').Comp.prog in 
      let eta' = add_mrecs n_list' cs theta eta in 
	(dprint (fun () -> "[eval_syn] found -- extend environment with rec. prog."  ^ R.render_cid_prog cid'  ^ "\n");
         dprint (fun () -> "[eval_syn] add to eta with cs = " ^ P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs));
         Cons(RecValue ((cid', e'), cs, theta, eta) ,eta'))
end
 

(* eval e (theta, eta) = v 

where  cD ; cG |- e <= wf_exp
       .       |- theta <= cD
       .  ; .  |- eta   <= [|theta|]cG
*)

let rec eval_syn i theta_eta = 
  let (cs, theta, eta ) = theta_eta in
  let _ = dprint (fun () -> "\n[eval_syn] with  theta = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) in
  let _ = dprint (fun () -> "\n[eval_syn] with  cs = " ^ 
		   P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs)) in
    match i with  
  | Const cid -> 
      let _ = dprint (fun () -> "[eval_syn] Const " ^ R.render_cid_prog cid ) in 
      let n_list = (Comp.get cid).Comp.mut_rec in
      let e = (Comp.get cid).Comp.prog in   
      let rec add_mrecs n_list = match n_list with 
        | [] ->  eta
        | n'::n_list' -> 
            let cid' = Comp.index_of_name n' in 
            let e'   = (Comp.get cid').Comp.prog in 
            let eta' = add_mrecs n_list' in 
	      (dprint (fun () -> "[eval_syn] Const " ^ 
                         R.render_cid_prog cid' ^ 
                         " found – extend environment with rec. prog. \n");
                Cons(RecValue ((cid', e'), cs, theta, eta) ,eta'))
      in 
      let _ = dprint (fun () -> "EVALUATE " ) in
        eval_chk e (cs, theta, (add_mrecs n_list))


  | Var x     -> 
      let _ = dprint (fun () -> "[eval_syn] Looking up " ^ string_of_int x ^ " in environment") in 
	begin match lookupValue x eta with	   
	  | RecValue ((cid,e'), cs', theta', eta') -> 
              let n_list = (Comp.get cid).Comp.mut_rec in
              let eta'' = add_mrecs n_list cs' theta' eta' in  
	        (dprint (fun () -> "[eval_syn] Lookup found RecValue " ^   R.render_cid_prog cid ^ "\n");
	         dprint (fun () -> "\n[eval_syn] with  theta' = " ^ 
		          P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta')); 
                 dprint (fun () -> "\n[eval_syn] with cs' = " ^ P.csubToString I.LF.Empty I.LF.Empty cs' );
                 dprint (fun () -> "\n call eval_chk on the body of " ^ R.render_cid_prog cid ^ "\n");
                 dprint (fun () -> "\n e' = " ^ 
                           P.expChkToString I.LF.Empty I.LF.Empty I.LF.Empty (Whnf.cnormExp (Ctxsub.ctxnorm_exp_chk (e', cs'), theta')));
                 dprint (fun () -> "\n cs (original) = " ^ P.csubToString I.LF.Empty I.LF.Empty cs );
                eval_chk e' (cs', (Whnf.cnormMSub theta'), eta''))
                (* eval_chk e' (theta',Cons(w, eta'))) *)
	  | v -> v
	end 

  | Apply (_ , i', e') -> 
      let w2 = eval_chk e' theta_eta in 
      let _ = dprint (fun () -> "[eval_syn] Apply argument evaluated ") in 
      let _ = dprint (fun () -> "[eval_syn] Extended environment: |env| =  " ^ 
				string_of_int (length_env eta))    in 
      let _ = dprint (fun () -> "\n[eval_syn] with  theta = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) in

      let _ = dprint (fun () -> "\n[eval_syn] with  cs = " ^ 
		   P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs)) in

	begin match eval_syn i' theta_eta with
	  | FunValue ((_loc, _x , e'), cs1, theta1, eta1) -> 
	      let _ = dprint (fun () -> "[eval_syn] Extended environment: |env1| =  " ^ 
				string_of_int (length_env eta1)) in 
	      let _ = dprint (fun () -> "[eval_syn] Extended environment: |env1'| =  " ^ 
				string_of_int (length_env (Cons(w2,eta1)))   ) in 
      let _ = dprint (fun () -> "\n[eval_syn] with  theta1 = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta1)) in
      let _ = dprint (fun () -> "\n[eval_syn] with  cs1 = " ^ 
		   P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs1)) in

	      eval_chk e' (cs1, theta1, Cons(w2,eta1))
	  | _ -> raise (Violation "Expected FunValue")
	end
  | MApp (_, i', (phat, NormObj tM)) -> 
      begin match eval_syn i' theta_eta with
	| MLamValue ((_loc, _u, e'), cs1, theta1, eta1) -> 
            eval_chk e' (cs1, I.LF.MDot(I.LF.MObj(phat, Whnf.cnorm (Ctxsub.ctxnorm (tM,cs), theta)), theta1), eta1)
	| _ -> raise (Violation "Expected MLamValue")
      end


  | MApp (_, i', (phat, NeutObj h)) -> 
      begin match eval_syn i' theta_eta with
	| MLamValue ((_loc, _u, e'), cs1, theta1, eta1) -> 
            eval_chk e' (cs1, I.LF.MDot(I.LF.PObj(phat, Whnf.cnormHead (h, theta)), theta1), eta1)
	| _ -> raise (Violation "Expected MLamValue")
      end

  | CtxApp (_, i', cPsi) -> 
      begin match eval_syn i' theta_eta with
	| CtxValue ((_loc, _psi, e'), cs1, theta1, eta1) -> 
	    let _ = dprint (fun () -> "EVALUATE CtxApp ") in 
	    (* let e1 = Ctxsub.csub_exp_chk (Whnf.cnormDCtx (cPsi,theta)) 1 e' in  *)
	    (* let _ = dprint (fun () -> "CtxApp AFTER substitution cPsi") in  *)
            let cPsi' = Whnf.cnormDCtx (Ctxsub.ctxnorm_dctx (cPsi, cs), theta) in 
            let cs1' = I.LF.CDot(cPsi', cs1) in 
            let _ = dprint (fun () -> "[CtxApp] cPsi = " ^ P.dctxToString I.LF.Empty I.LF.Empty cPsi') in               
            let _ = dprint (fun () -> "[eval_chk] extended cs1 =  " ^ 
	                      P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs1) ) in
            let _ = dprint (fun () -> "[eval_chk] extended cs1' =  " ^ 
	                      P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs1') ) in
	    eval_chk e' (cs1', theta1, eta1)
	| _ -> raise (Violation "Expected CtxValue")
      end 

  | Ann (e, _tau) -> 
      eval_chk e theta_eta


  | Equal(_, i1, i2) -> 
    let v1 = eval_syn i1 theta_eta in 
    let v2 = eval_syn i2 theta_eta in  
    (* begin match (eval_syn i1 theta_eta , eval_syn i2 theta_eta )  with *)
    begin match (v1, v2)  with
          | (BoxValue (psihat, tM), BoxValue ( _ , tN)) ->  
              if Whnf.conv (tM, LF.id) (tN, LF.id) then 
                BoolValue true
              else 
                BoolValue false 

          | ( _ , _ ) -> raise (Violation "Expected atomic object") 
        end 

  | Boolean b -> BoolValue b 


and eval_chk e theta_eta =  
  let (cs, theta,eta) = theta_eta in 
  let _ = dprint (fun () -> "[eval_chk] cs =  " ^ 
		 P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs) ) in
    match e with
      | Syn(_, i) -> eval_syn i theta_eta
(*      | Rec (loc, n, e') -> 
	  let w = RecValue ((loc, n, e'), theta, eta) in  
	  let _ = dprint (fun () -> "[eval_chk] rec-case -1- |env| = " ^ string_of_int (length_env eta) ^ "\n") in 
	  let eta' = Cons(w, eta) in 
	  let _ = dprint (fun () -> "[eval_chk] rec-case -2- |env| = " ^ string_of_int (length_env eta') ^ "\n") in 
	    eval_chk e' (theta, Cons(w, eta))*) 
      | MLam(loc, n, e') -> 
          let _ = dprint (fun () -> "[MLamValue] created : cs = " ^ P.csubToString I.LF.Empty I.LF.Empty cs ) in 
          let _ = dprint (fun () -> "[MLamValue] created : theta = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta )) in 
	  MLamValue ((loc, n ,e'), cs, (Whnf.cnormMSub (Ctxsub.ctxnorm_msub (theta, cs))), eta) 
      | CtxFun (loc, n, e') -> 
          let _ = dprint (fun () -> "[CtxValue] created : cs = " ^ P.csubToString I.LF.Empty I.LF.Empty cs ) in 
	  CtxValue ((loc,n,e'), (Ctxsub.ctxnorm_csub cs), theta, eta)
      | Fun(loc, n, e') -> 
          let _ = dprint (fun () -> "[FunValue] created : cs = " ^ P.csubToString I.LF.Empty I.LF.Empty cs ) in 
          let _ = dprint (fun () -> "[FunValue] created : theta = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub (Ctxsub.ctxnorm_msub (theta,cs)) )) in 
	  FunValue ((loc, n, e'), cs, (Whnf.cnormMSub (Ctxsub.ctxnorm_msub (theta, cs))), eta)
      | Box(loc, phat, tM) -> 
          let phat' = Ctxsub.ctxnorm_psihat (phat,cs) in 
          let tM'   = C.cnorm (Ctxsub.ctxnorm (tM, cs) , theta) in 
          (dprint (fun () -> "[BoxValue] :  " ^ P.expChkToString I.LF.Empty I.LF.Empty I.LF.Empty (Box(loc, phat', tM')) ^ "\n");
	   BoxValue (phat' , tM'))
      | Case(_, _prag, i, branches) ->  
	(match eval_syn i theta_eta with
	  | BoxValue (phat, tM) -> 	  
	      let _ = (dprint (fun () -> "[eval_syn] EVALUATED SCRUTINEE: " ^ 
                                P.expChkToString I.LF.Empty I.LF.Empty I.LF.Empty (Box(None, phat, tM))
                             (*   P.normalToString I.LF.Empty I.LF.Empty (Context.hatToDCtx phat) (tM, LF.id)*)
                             );
                       dprint (fun () -> "[eval_syn] cs = " ^ P.csubToString I.LF.Empty I.LF.Empty cs ))

              in 
	      eval_branches (phat,tM) (branches, theta_eta) 
	  | _ -> raise (Violation "Expected BoxValue for case"))

      | Value v -> v
      | If (_, i, e1, e2) -> 
          begin match eval_syn i theta_eta with 
            | BoolValue true -> eval_chk e1 theta_eta 
            | BoolValue false -> eval_chk e2 theta_eta 
          end
                

and eval_branches (phat,tM) (branches, theta_eta) = match branches with 
  | [] -> raise (Violation "Missing branch - Non-exhaustive pattern match") 
  | b::branches -> 
	let (cs, theta, _ ) = theta_eta in 
      begin try 
	 dprint (fun () -> "\n[eval_branches] try branch with  theta = " ^ 
		   P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) ;  
	eval_branch (phat,tM) b  theta_eta
      with BranchMismatch -> 
	(dprint (fun () -> "[eval_branches] Try next branch...");
	 dprint (fun () -> "\n[eval_branches] with  theta = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta)) ; 
	eval_branches (phat,tM) (branches, theta_eta))
      end

and eval_branch (phat, tM) (BranchBox (cO, cD, (cPsi' , tM', theta', cs'), e)) (cs, theta, eta) = 
  begin try
    let _ = dprint (fun () -> "[eval_branch] cO = " ^ P.octxToString cO ^ "\n cs = " ^ P.csubToString I.LF.Empty I.LF.Empty cs ) in
    let ct      = cctxToCSub cO cD cPsi' in 
    let ct'     = Ctxsub.ccomp cs' ct in 
    let _       = (  dprint (fun () -> "Unify msub: cs =  " ^ 
		               P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub cs) ) ; 
                     dprint (fun () -> "Unify Refinement  ct' = " ^ 
                               P.csubToString I.LF.Empty I.LF.Empty (Ctxsub.ctxnorm_csub ct'))) in 
      
    let _       = Unify.unifyCSub cs ct'  in 
    let ct1'    = Ctxsub.ctxnorm_csub ct' in 
    let ct1     = Ctxsub.ctxnorm_csub ct in 

    let _ = dprint (fun () -> "Unify Refinement  ct1' = " ^ 
                     P.csubToString I.LF.Empty I.LF.Empty  ct1') in 
    let _ = dprint (fun () -> "Unify Refinement  ct1 = " ^ 
                     P.csubToString I.LF.Empty I.LF.Empty ct1) in 
      
    let mt      = mctxToMSub (Ctxsub.ctxnorm_mctx (cD,ct1)) in 
    let theta_k = Whnf.mcomp (Ctxsub.ctxnorm_msub (theta', ct1)) mt in 
      
    let _ = (dprint (fun () -> "Unify msub: theta =  " ^ 
		       P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta) ) ; 
             dprint (fun () -> "Unify Refinement  theta_k = " ^ 
                       P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta_k))) in 

    let _        = Unify.unifyMSub theta theta_k  in 

    let _ =  (dprint (fun () -> "After unification: theta =  " ) ; 
              dprint (fun () ->  P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta) ) ; 
              dprint (fun () -> "     theta_k = " ^ P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub theta_k)) ) in

    let tM1' = C.cnorm (Ctxsub.ctxnorm (tM', ct1), mt) in 
    let mt1'  = Whnf.cnormMSub mt  in 
    let cPsi' = Ctxsub.ctxnorm_dctx (cPsi', ct1) in 
      
    let _     = Unify.unify I.LF.Empty cPsi' (tM, LF.id) (tM1', LF.id)  in 
    let _     = (dprint (fun () -> "\n[eval_chk] body with  mt = " ) ; 
                 dprint (fun () -> P.msubToString I.LF.Empty I.LF.Empty (Whnf.cnormMSub mt1'))) in 
    let _ = dprint (fun () -> "and ct1' = " ^ 
                     P.csubToString I.LF.Empty  I.LF.Empty ct1') in 

    let _ = dprint (fun () -> "PATTERN MATCHn " ^  P.expChkToString I.LF.Empty I.LF.Empty I.LF.Empty (Box(None, phat, tM)) ^ " SUCCESSFUL") in  

         eval_chk e (ct1, mt1', eta) 
 with 
     Unify.Unify _ -> raise BranchMismatch
 end



let rec eval i  =  
  let _ = dprint (fun () -> "\n\nSTART EVALUATION\n") in
  begin match eval_chk i (I.LF.CShift 0, I.LF.MShift 0, Empty) with
    | ConstValue cid -> Syn(None, Const cid)
    | BoxValue (phat, tM) -> Box(None, phat, tM)
    | BoolValue b -> Syn(None, Boolean b)
    | v -> Value v
  end
