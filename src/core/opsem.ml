(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
*)

open Syntax.Int

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer


let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [9])

type error =
  | MissingBranch

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | MissingBranch ->
          Format.fprintf ppf "Missing branch -- non-exhaustive pattern match."))

exception BranchMismatch

let rec length_env env = begin match env with
  | Comp.Empty -> 0
  | Comp.Cons (_ , env') -> length_env env' + 1
end

let rec lookupValue x env = begin match (x, env) with
  | (1, Comp.Cons (v, env'))  -> v
  | (n, Comp.Cons (_ , env')) -> lookupValue (n-1) env'
  (* otherwise undefined *)
end

(* ********************************************************************* *)

let rec add_mrecs n_list theta eta = match n_list with
  | [] ->  eta
  | n'::n_list' ->
      let cid' = Store.Cid.Comp.index_of_name n' in
      let e' = (Store.Cid.Comp.get cid').Store.Cid.Comp.prog in
      let eta' = add_mrecs n_list' theta eta in
        (dprint (fun () -> "[eval_syn] found -- extend environment with rec \""  ^ R.render_cid_prog cid' ^ "\"\n"
                );
         Comp.Cons (Comp.RecValue ((cid', e'), theta, eta),  eta'))

(* eval e (theta, eta) = v

where  cD ; cG |- e <= wf_exp
       .       |- theta <= cD
       .  ; .  |- eta   <= [|theta|]cG
*)

let rec eval_syn i theta_eta =
  let (theta, eta) = theta_eta in
  let _ = dprint (fun () -> "[eval_syn] with  theta = " ^ P.msubToString LF.Empty (Whnf.cnormMSub theta)) in
  match i with
    | Comp.Const cid ->
      let _ = dprint (fun () -> "[eval_syn] Const " ^ R.render_cid_prog cid) in
      let n_list = (Store.Cid.Comp.get cid).Store.Cid.Comp.mut_rec in
      let e = (Store.Cid.Comp.get cid).Store.Cid.Comp.prog in
      dprint (fun () -> "EVALUATE");
      eval_chk e (theta, (add_mrecs n_list theta eta))

    | Comp.Var x     ->
      let _ = dprint (fun () -> "[eval_syn] Looking up " ^ string_of_int x ^ " in environment") in
      begin match lookupValue x eta with
        | Comp.RecValue ((cid,e'), theta', eta') ->
          let n_list = (Store.Cid.Comp.get cid).Store.Cid.Comp.mut_rec in
          let eta'' = add_mrecs n_list theta' eta' in
          dprint (fun () -> "[eval_syn] Lookup found RecValue " ^ R.render_cid_prog cid);
          dprint (fun () -> "[eval_syn] with  theta' = " ^
            P.msubToString LF.Empty (Whnf.cnormMSub theta'));
          dprint (fun () -> "  call eval_chk on the body of " ^ R.render_cid_prog cid);
          dprint (fun () -> "  e' = " ^
            P.expChkToString LF.Empty LF.Empty (Whnf.cnormExp (e', theta')));
          eval_chk e' ((Whnf.cnormMSub theta'), eta'')
          (* eval_chk e' (theta', Cons (w, eta')) *)
        | v -> v
      end

    | Comp.Apply (_ , i', e') ->
      let w2 = eval_chk e' theta_eta in
      let _ = dprint (fun () -> "[eval_syn] Apply argument evaluated\n"
        ^ "[eval_syn] Extended environment: |env| =  "
        ^ string_of_int (length_env eta) ^ "\n"
        ^ "[eval_syn] with  theta = "
        ^ P.msubToString LF.Empty (Whnf.cnormMSub theta) ^ "\n"
      ) in

      begin match eval_syn i' theta_eta with
        | Comp.FunValue ((_loc, _x , e'), theta1, eta1) ->
          dprint (fun () -> "[eval_syn] Extended environment: |env1| =  "
            ^ string_of_int (length_env eta1) ^ "\n"
            ^ "[eval_syn] Extended environment: |env1'| =  "
            ^ string_of_int (length_env (Comp.Cons (w2,eta1))) ^ "\n"
            ^ "[eval_syn] with  theta1 = "
            ^ P.msubToString LF.Empty (Whnf.cnormMSub theta1) ^ "\n"
          );

          eval_chk e' (theta1, Comp.Cons (w2,eta1))
        | _ -> raise (Error.Violation "Expected FunValue")
      end

    | Comp.MApp (_, i', (phat, Comp.NormObj tM)) ->
      begin match eval_syn i' theta_eta with
        | Comp.MLamValue ((_loc, _u, e'), theta1, eta1) ->
          eval_chk e' (LF.MDot (LF.MObj (phat, Whnf.cnorm (tM, theta)), theta1), eta1)
        | _ -> raise (Error.Violation "Expected MLamValue")
      end


    | Comp.MApp (_, i', (phat, Comp.NeutObj h)) ->
      begin match eval_syn i' theta_eta with
        | Comp.MLamValue ((_loc, _u, e'), theta1, eta1) ->
          eval_chk e' (LF.MDot (LF.PObj (phat, Whnf.cnormHead (h, theta)), theta1), eta1)
        | _ -> raise (Error.Violation "Expected MLamValue")
      end

    | Comp.CtxApp (_, i', cPsi) ->
      begin match eval_syn i' theta_eta with
        | Comp.CtxValue ((_loc, _psi, e'), theta1, eta1) ->
          let _ = dprint (fun () -> "EVALUATE CtxApp ") in
            (* let _ = dprint (fun () -> "CtxApp AFTER substitution cPsi") in  *)
          let cPsi' = Whnf.cnormDCtx (cPsi, theta) in
          let theta1'= LF.MDot(LF.CObj(cPsi'), theta1) in
          dprint (fun () -> "[CtxApp] cPsi = " ^ P.dctxToString LF.Empty cPsi');
          dprint (fun () -> "[CtxApp] theta1' = " ^ P.msubToString LF.Empty  theta1');
          eval_chk e' (theta1', eta1)
        | _ -> raise (Error.Violation "Expected CtxValue")
      end

    | Comp.Ann (e, _tau) ->
      eval_chk e theta_eta


    | Comp.Equal (_, i1, i2) ->
      let v1 = eval_syn i1 theta_eta in
      let v2 = eval_syn i2 theta_eta in
      begin match (v1, v2)  with
        | (Comp.BoxValue (psihat, tM), Comp.BoxValue ( _ , tN)) ->
          if Whnf.conv (tM, Substitution.LF.id) (tN, Substitution.LF.id) then
            Comp.BoolValue true
          else
            Comp.BoolValue false

        | ( _ , _ ) -> raise (Error.Violation "Expected atomic object")
      end

    | Comp.PairVal (_, i1, i2) ->
      let v1 = eval_syn i1 theta_eta in
      let v2 = eval_syn i2 theta_eta in
      Comp.PairValue (v1, v2)

    | Comp.Boolean b -> Comp.BoolValue b

and eval_chk e theta_eta =
  let (theta,eta) = theta_eta in

    match e with
      | Comp.Syn (_, i) -> eval_syn i theta_eta
      | Comp.MLam (loc, n, e') ->
          dprint (fun () -> "[MLamValue] created: theta = " ^ 
                    P.msubToString LF.Empty (Whnf.cnormMSub theta));
          Comp.MLamValue ((loc, n ,e'), Whnf.cnormMSub theta, eta)
      | Comp.CtxFun (loc, n, e') ->
          Comp.CtxValue ((loc,n,e'), Whnf.cnormMSub theta, eta)
      | Comp.Fun (loc, n, e') ->
          dprint (fun () -> "[FunValue] created: theta = " ^ 
                    P.msubToString LF.Empty (Whnf.cnormMSub theta));
          Comp.FunValue ((loc, n, e'), Whnf.cnormMSub theta, eta)

      | Comp.Pair (_, e1, e2) ->
        let v1 = eval_chk e1 theta_eta in
        let v2 = eval_chk e2 theta_eta in
        Comp.PairValue (v1, v2)

      | Comp.Let (loc, i, (x, e)) ->
        let w = eval_syn i theta_eta in
        eval_chk e (theta, Comp.Cons (w, eta))

      | Comp.Box (loc, phat, tM) ->
        let tM'   = Whnf.cnorm (tM, theta) in
        let phat' = Whnf.cnorm_psihat phat theta in
        dprint (fun () -> "[BoxValue]:  " ^ P.expChkToString LF.Empty LF.Empty (Comp.Box (loc, phat, tM')));
        Comp.BoxValue (phat', tM')

      | Comp.Case (loc, _prag, i, branches) ->
        let vscrut = eval_syn i theta_eta in
        eval_branches loc vscrut branches theta_eta

      | Comp.If (_, i, e1, e2) ->
        begin match eval_syn i theta_eta with
          | Comp.BoolValue true -> eval_chk e1 theta_eta
          | Comp.BoolValue false -> eval_chk e2 theta_eta
        end

      | Comp.Value v -> v

and eval_branches loc vscrut branches (theta, eta) = match branches with
  | [] -> raise (Error (loc, MissingBranch))
  | b::branches ->
    try
      dprint (fun () -> "[eval_branches] try branch with theta = " ^ P.msubToString LF.Empty (Whnf.cnormMSub theta));
      eval_branch vscrut b (theta, eta)
    with BranchMismatch ->
      dprint (fun () -> "[eval_branches] Try next branch...");
      dprint (fun () -> "[eval_branches] with  theta = " ^ P.msubToString LF.Empty (Whnf.cnormMSub theta));
      eval_branches loc vscrut branches (theta, eta)

and match_pattern mt vscrut pat =
  match vscrut, pat with
    | _, Comp.PatMetaObj (loc', (Comp.MetaObj (loc'', phat, tM))) ->
      match_pattern mt vscrut
        (Comp.PatMetaObj (loc', Comp.MetaObjAnn (loc'', Context.hatToDCtx phat, tM)))

    | Comp.BoxValue (phat, tM), Comp.PatMetaObj (_, (Comp.MetaObjAnn (_, cPsi, tM'))) ->
      let tM' = Whnf.cnorm (tM', mt) in
      let cPsi = Whnf.cnormDCtx (cPsi, mt) in
      dprint (fun () -> "[evBranch] unify_phat "
        ^ P.dctxToString LF.Empty (Context.hatToDCtx phat)
        ^ " == " ^ P.dctxToString LF.Empty cPsi);
      dprint (fun () -> "[evBranch] unify meta-obj: "
        ^ P.normalToString LF.Empty (Context.hatToDCtx phat) (tM, Substitution.LF.id)
        ^ " == " ^ P.normalToString LF.Empty cPsi (tM', Substitution.LF.id));
      Unify.unify_phat phat (Context.dctxToHat cPsi);
      Unify.unify LF.Empty cPsi (tM, Substitution.LF.id) (tM', Substitution.LF.id)

    | Comp.PairValue (v1, v2), Comp.PatPair (_, pat1, pat2) ->
      dprint (fun () -> "[evBranch] matching a pair.");
      match_pattern mt v1 pat1;
      match_pattern mt v2 pat2

    | _ -> raise Error.NotImplemented

and eval_branch vscrut branch (theta, eta) =
  match branch with
    | Comp.EmptyBranch (loc, cD, pat, t) ->
      raise (Error.Violation "Case {}-pattern -- coverage checking is off or broken")
    | Comp.Branch (loc, cD, cG, pat, theta', e) ->
      begin
        try
          let mt = Ctxsub.mctxToMSub (Whnf.normMCtx cD) in
          let theta_k = Whnf.mcomp (Whnf.cnormMSub theta') mt in
          let _ = Unify.unifyMSub theta theta_k in
          match_pattern mt vscrut pat;
          eval_chk e (Whnf.cnormMSub mt, eta)
        with Unify.Unify msg -> (dprint (fun () -> "Branch failed : " ^ msg) ; raise BranchMismatch)
      end

let rec eval e =
  dprint (fun () -> "Opsem.eval");
  Debug.indent 2;
  let result = match eval_chk e (LF.MShift 0, Comp.Empty) with
    | Comp.ConstValue cid -> Comp.Syn (Syntax.Loc.ghost, Comp.Const cid)
    | Comp.BoxValue (phat, tM) -> Comp.Box (Syntax.Loc.ghost, phat, tM)
    | Comp.BoolValue b -> Comp.Syn (Syntax.Loc.ghost, Comp.Boolean b)
    | v -> Comp.Value v
  in
    Debug.outdent 2;
    result
