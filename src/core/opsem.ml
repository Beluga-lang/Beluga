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

let rec lookupValue x env = match x, env with
  | 1, Comp.Cons (v, env')  -> v
  | n, Comp.Cons (_, env') -> lookupValue (n-1) env'
  | _, _ -> raise (Error.Violation "lookupValue: bad offset.")

(** The Data spine must necessarily be in reverse order, to allow
    constant time applications. The pattern spine, however, is in the
    natural order. This function zips the reverse of the one spine
    with the other spine and discards the result, ie it computes the
    convolution of the two spines and discards the result. *)
let convolve_spines f spine pat_spine =
  (* To avoid doing two traversals of the first spine (once for
     reversing and once for zipping), we use the "There And Back
     Again" trick by Danvy and Goldberg (2202). *)
  let rec loop spine =
    match spine with
      | Comp.DataNil -> pat_spine
      | Comp.DataApp (v, spine') ->
        match loop spine' with
          | Comp.PatApp (_, pat', pat_spine') ->
            f v pat'; pat_spine'
          | _ -> raise (Error.Violation "convolve_spines: spines not the same length.")
  in ignore (loop spine)

(* ********************************************************************* *)

let rec add_mrecs n_list (theta, eta) = match n_list with
  | [] ->  eta
  | n'::n_list' ->
      let cid' = Store.Cid.Comp.index_of_name n' in
      let v = (Store.Cid.Comp.get cid').Store.Cid.Comp.prog in
      let eta' = add_mrecs n_list' (theta, eta) in
      dprint (fun () -> "[eval_syn] found -- extend environment with rec \""  ^ R.render_cid_prog cid' ^ "\"\n");
      Comp.Cons (v,  eta')

(* eval e (theta, eta) = v

where  cD ; cG |- e <= wf_exp
       .       |- theta <= cD
       .  ; .  |- eta   <= [|theta|]cG
*)

let rec eval_syn i (theta, eta) =
  let _ = dprint (fun () -> "[eval_syn] with  theta = " ^ P.msubToString LF.Empty (Whnf.cnormMSub theta)) in
  match i with
    | Comp.Const cid ->
      dprint (fun () -> "[eval_syn] Const " ^ R.render_cid_prog cid);
      begin match (Store.Cid.Comp.get cid).Store.Cid.Comp.prog with
        | Comp.RecValue ((cid,e'), theta', eta') ->
          let n_list = (Store.Cid.Comp.get cid).Store.Cid.Comp.mut_rec in
          let eta'' = add_mrecs n_list (theta', eta') in
          dprint (fun () -> "[eval_syn] Const is RecValue " ^ R.render_cid_prog cid);
          dprint (fun () -> "[eval_syn] with theta' = " ^ P.msubToString LF.Empty (Whnf.cnormMSub theta'));
          dprint (fun () -> "  call eval_chk on the body of " ^ R.render_cid_prog cid);
          dprint (fun () -> "  e' = " ^ P.expChkToString LF.Empty LF.Empty (Whnf.cnormExp (e', theta')));
          eval_chk e' (Whnf.cnormMSub theta', eta'')
        | v -> v
      end

    | Comp.DataConst cid ->
      Comp.DataValue (cid, Comp.DataNil)

    | Comp.Var x ->
      dprint (fun () -> "[eval_syn] Looking up " ^ string_of_int x ^ " in environment");
      begin match lookupValue x eta with
        | Comp.RecValue ((cid,e'), theta', eta') ->
          let n_list = (Store.Cid.Comp.get cid).Store.Cid.Comp.mut_rec in
          let eta'' = add_mrecs n_list (theta', eta') in
          dprint (fun () -> "[eval_syn] Lookup found RecValue " ^ R.render_cid_prog cid);
          dprint (fun () -> "[eval_syn] with theta' = " ^ P.msubToString LF.Empty (Whnf.cnormMSub theta'));
          dprint (fun () -> "  call eval_chk on the body of " ^ R.render_cid_prog cid);
          dprint (fun () -> "  e' = " ^ P.expChkToString LF.Empty LF.Empty (Whnf.cnormExp (e', theta')));
          eval_chk e' (Whnf.cnormMSub theta', eta'')
        | v -> v
      end

    | Comp.Apply (_ , i', e') ->
      let w2 = eval_chk e' (theta, eta) in
      dprint (fun () -> "[eval_syn] Apply argument evaluated\n"
        ^ "[eval_syn] Extended environment: |env| =  "
        ^ string_of_int (length_env eta) ^ "\n"
        ^ "[eval_syn] with  theta = "
        ^ P.msubToString LF.Empty (Whnf.cnormMSub theta) ^ "\n");
      begin match eval_syn i' (theta, eta) with
        | Comp.FunValue ((_loc, _x , e'), theta1, eta1) ->
          dprint (fun () -> "[eval_syn] Extended environment: |env1| =  "
            ^ string_of_int (length_env eta1) ^ "\n"
            ^ "[eval_syn] Extended environment: |env1'| =  "
            ^ string_of_int (length_env (Comp.Cons (w2,eta1))) ^ "\n"
            ^ "[eval_syn] with  theta1 = "
            ^ P.msubToString LF.Empty (Whnf.cnormMSub theta1) ^ "\n");

          eval_chk e' (theta1, Comp.Cons (w2,eta1))

        | Comp.DataValue (cid, spine) ->
          Comp.DataValue (cid, Comp.DataApp (w2, spine))

        | _ -> raise (Error.Violation "Expected FunValue")
      end

    | Comp.MApp (_, i', (phat, Comp.NormObj tM)) ->
      begin match eval_syn i' (theta, eta) with
        | Comp.MLamValue ((_loc, _u, e'), theta1, eta1) ->
          eval_chk e' (LF.MDot (LF.MObj (phat, Whnf.cnorm (tM, theta)), theta1), eta1)
        | Comp.DataValue (cid, spine) ->
          Comp.DataValue (cid, Comp.DataApp (Comp.BoxValue (phat, tM), spine))
        | _ -> raise (Error.Violation "Expected MLamValue")
      end


    | Comp.MApp (_, i', (phat, Comp.NeutObj h)) ->
      begin match eval_syn i' (theta, eta) with
        | Comp.MLamValue ((_loc, _u, e'), theta1, eta1) ->
          eval_chk e' (LF.MDot (LF.PObj (phat, Whnf.cnormHead (h, theta)), theta1), eta1)
        | _ -> raise (Error.Violation "Expected MLamValue")
      end

    | Comp.CtxApp (_, i', cPsi) ->
      begin match eval_syn i' (theta, eta) with
        | Comp.CtxValue ((_loc, _psi, e'), theta1, eta1) ->
          let _ = dprint (fun () -> "EVALUATE CtxApp ") in
          let cPsi' = Whnf.cnormDCtx (cPsi, theta) in
          let theta1'= LF.MDot(LF.CObj(cPsi'), theta1) in
          dprint (fun () -> "[CtxApp] cPsi = " ^ P.dctxToString LF.Empty cPsi');
          dprint (fun () -> "[CtxApp] theta1' = " ^ P.msubToString LF.Empty  theta1');
          eval_chk e' (theta1', eta1)
        | _ -> raise (Error.Violation "Expected CtxValue")
      end

    | Comp.Ann (e, _tau) ->
      eval_chk e (theta, eta)


    | Comp.Equal (_, i1, i2) ->
      let v1 = eval_syn i1 (theta, eta) in
      let v2 = eval_syn i2 (theta, eta) in
      begin match (v1, v2)  with
        | (Comp.BoxValue (psihat, tM), Comp.BoxValue ( _ , tN)) ->
          if Whnf.conv (tM, Substitution.LF.id) (tN, Substitution.LF.id) then
            Comp.BoolValue true
          else
            Comp.BoolValue false

        | ( _ , _ ) -> raise (Error.Violation "Expected atomic object")
      end

    | Comp.PairVal (_, i1, i2) ->
      let v1 = eval_syn i1 (theta, eta) in
      let v2 = eval_syn i2 (theta, eta) in
      Comp.PairValue (v1, v2)

    | Comp.Boolean b -> Comp.BoolValue b

and eval_chk e (theta, eta) =
    match e with
      | Comp.Syn (_, i) -> eval_syn i (theta, eta)
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
        let v1 = eval_chk e1 (theta, eta) in
        let v2 = eval_chk e2 (theta, eta) in
        Comp.PairValue (v1, v2)

      | Comp.Let (loc, i, (x, e)) ->
          let w = eval_syn i (theta, eta) in
            eval_chk e (theta, Comp.Cons (w, eta))

      | Comp.Box (loc, phat, tM) ->
        let tM'   = Whnf.cnorm (tM, theta) in
        let phat' = Whnf.cnorm_psihat phat theta in
        dprint (fun () -> "[BoxValue]:  " ^ P.expChkToString LF.Empty LF.Empty (Comp.Box (loc, phat, tM')));
        Comp.BoxValue (phat', tM')

      | Comp.Case (loc, _prag, i, branches) ->
        let vscrut = eval_syn i (theta, eta) in
        eval_branches loc vscrut branches (theta, eta)

      | Comp.If (_, i, e1, e2) ->
        begin match eval_syn i (theta, eta) with
          | Comp.BoolValue true -> eval_chk e1 (theta, eta)
          | Comp.BoolValue false -> eval_chk e2 (theta, eta)
        end

      | Comp.Hole (_) ->
        raise (Error.Violation "Source contains holes")

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

and match_pattern mt eta v pat =
  let eta = ref eta in
  let rec loop v pat =
    match v, pat with
      | _, Comp.PatMetaObj (loc', (Comp.MetaObj (loc'', phat, tM))) ->
        loop v
          (Comp.PatMetaObj (loc', Comp.MetaObjAnn (loc'', Context.hatToDCtx phat, tM)))

      | _, Comp.PatAnn (_, pat', _) ->
        loop v pat'

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
      | _, Comp.PatMetaObj _ ->
        raise (Error.Violation "Expected box value.")

      | Comp.DataValue (cid, spine), Comp.PatConst (_, pat_cid, pat_spine) ->
        if cid <> pat_cid then
          raise BranchMismatch;
        convolve_spines loop spine pat_spine
      | _, Comp.PatConst _ ->
        raise (Error.Violation "Expected data value.")

      | Comp.PairValue (v1, v2), Comp.PatPair (_, pat1, pat2) ->
        dprint (fun () -> "[evBranch] matching a pair.");
        loop v1 pat1;
        loop v2 pat2
      | _, Comp.PatPair _ ->
        raise (Error.Violation "Expected pair value.")

      | _, Comp.PatFVar (_, _) ->
        raise (Error.Violation "Found PatFVar in opsem.")

      | v, Comp.PatVar (_, _) ->
        eta := Comp.Cons (v, !eta)

      | Comp.BoolValue true, Comp.PatTrue _ -> ()
      | Comp.BoolValue false, Comp.PatFalse _ -> ()
      | Comp.BoolValue _, (Comp.PatTrue _ | Comp.PatFalse _) -> raise BranchMismatch
      | _, (Comp.PatTrue _ | Comp.PatFalse _) -> raise (Error.Violation "Expected Bool value.")

      | _ -> raise Error.NotImplemented
  in loop v pat; !eta

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
          let eta' = match_pattern mt eta vscrut pat in
          eval_chk e (Whnf.cnormMSub mt, eta')
        with Unify.Unify msg -> (dprint (fun () -> "Branch failed : " ^ msg) ; raise BranchMismatch)
      end

let rec eval e =
  dprint (fun () -> "Opsem.eval");
  Debug.indent 2;
  let result = eval_chk e (LF.MShift 0, Comp.Empty) in
  Debug.outdent 2;
  result
