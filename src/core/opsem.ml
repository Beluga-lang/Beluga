(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

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

(* ********************************************************************* *)

let rec add_mrecs n_list cs theta eta = match n_list with 
  | [] ->  eta
  | n'::n_list' -> 
      let cid' = Comp.index_of_name n' in
      let e' = (Comp.get cid').Comp.prog in
      let eta' = add_mrecs n_list' cs theta eta in
        (dprint (fun () -> "[eval_syn] found -- extend environment with rec \""  ^ R.render_cid_prog cid' ^ "\"\n"
                );
         Cons (RecValue ((cid', e'), cs, theta, eta),  eta'))

(* eval e (theta, eta) = v 

where  cD ; cG |- e <= wf_exp
       .       |- theta <= cD
       .  ; .  |- eta   <= [|theta|]cG
*)

let rec eval_syn i theta_eta = 
  let (cs, theta, eta ) = theta_eta in
  let _ = dprint (fun () -> "[eval_syn] with  theta = " ^ 
                   P.msubToString I.LF.Empty (Whnf.cnormMSub theta)) in
    match i with  
  | Const cid -> 
      let _ = dprint (fun () -> "[eval_syn] Const " ^ R.render_cid_prog cid) in 
      let n_list = (Comp.get cid).Comp.mut_rec in
      let e = (Comp.get cid).Comp.prog in   
        dprint (fun () -> "EVALUATE");
        eval_chk e (cs, theta, (add_mrecs n_list cs theta eta))


  | Var x     -> 
      let _ = dprint (fun () -> "[eval_syn] Looking up " ^ string_of_int x ^ " in environment") in 
        begin match lookupValue x eta with         
          | RecValue ((cid,e'), cs', theta', eta') -> 
              let n_list = (Comp.get cid).Comp.mut_rec in
              let eta'' = add_mrecs n_list cs' theta' eta' in  
                dprint (fun () -> "[eval_syn] Lookup found RecValue " ^ R.render_cid_prog cid);
                dprint (fun () -> "[eval_syn] with  theta' = " ^ 
                         P.msubToString I.LF.Empty (Whnf.cnormMSub theta')); 
                dprint (fun () -> "  call eval_chk on the body of " ^ R.render_cid_prog cid);
                dprint (fun () -> "  e' = " ^ 
                          P.expChkToString I.LF.Empty I.LF.Empty (Whnf.cnormExp (Ctxsub.ctxnorm_exp_chk (e', cs'), theta')));
                eval_chk e' (cs', (Whnf.cnormMSub theta'), eta'')
                (* eval_chk e' (theta', Cons(w, eta')) *)
          | v -> v
        end 

  | Apply (_ , i', e') -> 
      let w2 = eval_chk e' theta_eta in 
      let _ = dprint (fun () -> "[eval_syn] Apply argument evaluated\n"
                              ^ "[eval_syn] Extended environment: |env| =  "
                              ^ string_of_int (length_env eta) ^ "\n"
                              ^ "[eval_syn] with  theta = "
                              ^ P.msubToString I.LF.Empty (Whnf.cnormMSub theta) ^ "\n"
                     ) in

        begin match eval_syn i' theta_eta with
          | FunValue ((_loc, _x , e'), cs1, theta1, eta1) -> 
              dprint (fun () -> "[eval_syn] Extended environment: |env1| =  "
                              ^ string_of_int (length_env eta1) ^ "\n"
                              ^ "[eval_syn] Extended environment: |env1'| =  "
                              ^ string_of_int (length_env (Cons(w2,eta1))) ^ "\n"
                              ^ "[eval_syn] with  theta1 = "
                              ^ P.msubToString I.LF.Empty (Whnf.cnormMSub theta1) ^ "\n"
                     );

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
            (* let _ = dprint (fun () -> "CtxApp AFTER substitution cPsi") in  *)
            let cPsi' = Whnf.cnormDCtx (Ctxsub.ctxnorm_dctx (cPsi, cs), theta) in 
            let cs1' = I.LF.CDot(cPsi', cs1) in 
              dprint (fun () -> "[CtxApp] cPsi = " ^ P.dctxToString I.LF.Empty cPsi');
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

    match e with
      | Syn(_, i) -> eval_syn i theta_eta
      | MLam(loc, n, e') -> 
          dprint (fun () -> "[MLamValue] created: theta = " ^ P.msubToString I.LF.Empty (Whnf.cnormMSub theta));
          MLamValue ((loc, n ,e'), cs, (Whnf.cnormMSub (Ctxsub.ctxnorm_msub (theta, cs))), eta) 
      | CtxFun (loc, n, e') -> 
          CtxValue ((loc,n,e'), (Ctxsub.ctxnorm_csub cs), theta, eta)
      | Fun(loc, n, e') -> 
          dprint (fun () -> "[FunValue] created: theta = " ^ P.msubToString I.LF.Empty (Whnf.cnormMSub (Ctxsub.ctxnorm_msub (theta,cs))));
          FunValue ((loc, n, e'), cs, (Whnf.cnormMSub (Ctxsub.ctxnorm_msub (theta, cs))), eta)

      | Let (loc, i, (x, e)) -> 
          let w = eval_syn i theta_eta in 
            eval_chk e (cs, theta, Cons (w, eta))

      | Box(loc, phat, tM) -> 
          let phat' = Ctxsub.ctxnorm_psihat (phat,cs) in 
          let tM'   = C.cnorm (Ctxsub.ctxnorm (tM, cs) , theta) in 
            dprint (fun () -> "[BoxValue]:  " ^ P.expChkToString I.LF.Empty I.LF.Empty (Box(loc, phat', tM')));
            BoxValue (phat' , tM')
      | Case(_, _prag, i, branches) ->  
          begin match eval_syn i theta_eta with
          | BoxValue (phat, tM) ->        
              dprint (fun () -> "[eval_syn] EVALUATED SCRUTINEE: " ^ 
                                P.expChkToString I.LF.Empty I.LF.Empty (Box(None, phat, tM))
                             );
              eval_branches (phat,tM) (branches, theta_eta) 
          | _ -> raise (Violation "Expected BoxValue for case")
          end

      | Value v -> v
      | If (_, i, e1, e2) -> 
          begin match eval_syn i theta_eta with 
            | BoolValue true -> eval_chk e1 theta_eta 
            | BoolValue false -> eval_chk e2 theta_eta 
          end
                

and eval_branches (phat,tM) (branches, theta_eta) = match branches with 
  | [] -> raise (Violation "Missing branch -- Non-exhaustive pattern match") 
  | b::branches -> 
      let (cs, theta, _ ) = theta_eta in 
        try 
           dprint (fun () -> "[eval_branches] try branch with  theta = " ^ 
                     P.msubToString I.LF.Empty (Whnf.cnormMSub theta)) ;  
          eval_branch (phat,tM) b  theta_eta
        with BranchMismatch -> 
          (dprint (fun () -> "[eval_branches] Try next branch...");
           dprint (fun () -> "[eval_branches] with  theta = " ^ P.msubToString I.LF.Empty (Whnf.cnormMSub theta)) ; 
          eval_branches (phat,tM) (branches, theta_eta))

and eval_branch (phat, tM) branch (cs, theta, eta) =
  match branch with
    | EmptyBranch (loc, cD, pat, t) ->
      raise (Violation "Case {}-pattern -- coverage checking is off or broken")
    | Branch (loc, cD, cG, PatMetaObj (_, (MetaObj (_, phat, tM))), theta', e) ->
      raise NotImplemented
    | Branch (loc, cD, cG, PatMetaObj (_, (MetaObjAnn (_, cPsi, tM'))), theta', e) ->
      begin
        try
          let mt = Ctxsub.mctxToMSub (Whnf.normMCtx cD) in
          let theta_k = Whnf.mcomp (Whnf.cnormMSub theta') mt in

          let _ = Unify.unifyMSub theta theta_k in

          let tM' = C.cnorm (tM', mt) in
          let mt  = Whnf.cnormMSub mt in

          let _ = Unify.unify I.LF.Empty cPsi (tM, LF.id) (tM', LF.id) in

          eval_chk e (cs, mt, eta)

        with Unify.Unify _ -> raise BranchMismatch
      end
    | _ -> raise NotImplemented

let rec eval e  =  
  dprint (fun () -> "Opsem.eval");
  Debug.indent 2;
  let result = match eval_chk e (I.LF.CShift 0, I.LF.MShift 0, Empty) with
    | ConstValue cid -> Syn(None, Const cid)
    | BoxValue (phat, tM) -> Box(None, phat, tM)
    | BoolValue b -> Syn(None, Boolean b)
    | v -> Value v
  in
    Debug.outdent 2;
    result
