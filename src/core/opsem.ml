(**
   @author Brigitte Pientka
*)

open Support
open Syntax.Int

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprintf, dprint, _) = Debug.makeFunctions' (Debug.toFlags [9])
open Debug.Fmt

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
     Again" trick by Danvy and Goldberg (2002). *)
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

type fun_trim_result =
| FunBranch of Comp.fun_branches_value
| Value of Comp.value

(* eval e (theta, eta) = v

where  cD ; cG |- e <= wf_exp
       .       |- theta <= cD
       .  ; .  |- eta   <= [|theta|]cG
*)

let eval_meta_obj cM theta =
	let loc, cM' = Whnf.cnormMetaObj (cM, theta) in
  (* why on earth do we do this case split? -je *)
  match cM' with
  | LF.ClObj (phat, LF.MObj tM) -> (loc, cM')
  | LF.ClObj (phat, LF.PObj h) -> (loc, cM')
  | LF.CObj cPsi -> (loc, cM')

let rec eval_syn i (theta, eta) =
  dprintf
    begin fun p ->
    p.fmt "[eval_syn] with theta = @[%a@]"
      (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta)
    end;
  match i with
    | Comp.Const (_, cid) ->
      dprint (fun () -> "[eval_syn] Const " ^ R.render_cid_prog cid);
      begin match (Store.Cid.Comp.get cid).Store.Cid.Comp.prog with
        | Some (Comp.ThmValue (cid, Comp.Program e', theta', eta')) ->
          dprintf
            begin fun p ->
            p.fmt "[eval_syn] @[<v>Const is RecValue %s@,\
                   with theta' = %a@,\
                   call eval_chk on the body of %s@,\
                   e' = %a@]"
              (R.render_cid_prog cid)
              (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta')
              (R.render_cid_prog cid)
              (P.fmt_ppr_cmp_exp_chk LF.Empty LF.Empty P.l0) (Whnf.cnormExp (e', theta'))
            end;
          eval_chk e' (Whnf.cnormMSub theta', eta')
        | Some (Comp.ThmValue (_, Comp.Proof _, _, _)) ->
           Misc.not_implemented "eval_syn Const Proof"
        | Some v -> v
        | None ->
           failwith "can't evaluate missing program"
      end

    | Comp.DataConst (_, cid) ->
      Comp.DataValue (cid, Comp.DataNil)

    | Comp.Obs(_, e, _, cid) ->
      let Comp.FunValue fbr = eval_chk e (theta, eta) in
      let rec trim = function
        | Comp.NilValBranch -> FunBranch Comp.NilValBranch
        | Comp.ConsValBranch ((Comp.PatObs(_, cid', _, Comp.PatNil), e, theta, eta), br) when cid = cid' ->
          Value (eval_chk e (theta, eta)) (* should we append theta' and eta'? *)
        | Comp.ConsValBranch ((Comp.PatObs(_, cid', _, ps), e, theta, eta), br) when cid = cid' ->
          begin match trim br with
          | FunBranch br' -> FunBranch (Comp.ConsValBranch ((ps, e, theta, eta), br'))
          (* this is kind of a degenerate case where there's a
             matching branch which is still unresolved but another
             later branch resolved. It indicates overlapping patterns
             that we could want to exclude during coverage *)
          | Value v -> Value v
          end
        | Comp.ConsValBranch ((Comp.PatObs(_, cid', _, ps), e, _, _), br) ->
          trim br
      in
      begin match trim fbr with
      | FunBranch fr -> Comp.FunValue fr
      | Value v -> v
      end

    | Comp.Var (_, x) ->
      dprint (fun () -> "[eval_syn] Looking up " ^ string_of_int x ^ " in environment");
      begin match lookupValue x eta with
        | Comp.ThmValue (cid, Comp.Program e', theta', eta') ->
          dprintf
            begin fun p ->
            p.fmt "[eval_syn] @[<v>Lookup found RecValue %s@,\
                   with theta' = @[%a@]@,\
                   call eval_chk on the body of %s@,\
                   e' = @[%a@]@]"
              (R.render_cid_prog cid)
              (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta')
              (R.render_cid_prog cid)
              (P.fmt_ppr_cmp_exp_chk LF.Empty LF.Empty P.l0) (Whnf.cnormExp (e', theta'))
            end;
          eval_chk e' (Whnf.cnormMSub theta', eta')
        | Comp.ThmValue (_, Comp.Proof _, _, _) ->
           Misc.not_implemented "eval_syn Proof"
        | v -> v
      end

    | Comp.Apply (_ , i', e') ->
      let w2 = eval_chk e' (theta, eta) in
      dprintf
        begin fun p ->
        p.fmt "[eval_syn] @[<v>Apply argument evaluated@,\
               Extended environment: |env| = %d@,\
               With theta = @[%a@]@]"
          (length_env eta)
          (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta)
        end;
      begin match eval_syn i' (theta, eta) with
        | Comp.FnValue (_x , e', theta1, eta1) ->
           dprintf
             begin fun p ->
             p.fmt "[eval_syn] @[<v>Extended environment:@,\
                    |env1| = %d@,\
                    Extended environment: |env1'| = %d@,\
                    with theta1 = @[%a@]@]"
               (length_env eta1)
               (length_env (Comp.Cons (w2,eta1)))
               (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta1)
             end;
          eval_chk e' (theta1, Comp.Cons (w2,eta1))

        | Comp.DataValue (cid, spine) ->
          Comp.DataValue (cid, Comp.DataApp (w2, spine))

        | Comp.FunValue fbr ->
          eval_fun_branches w2 fbr

        | _ -> raise (Error.Violation "Expected FunValue")
      end

    | Comp.MApp (_, i', (l, LF.ClObj(phat, LF.MObj tM)), _, _) ->
      let tM' = Whnf.cnorm (tM, theta) in
        let phat = Whnf.cnorm_psihat phat theta in
      begin match eval_syn i' (theta, eta) with
        | Comp.MLamValue (_u, e', theta1, eta1) ->
          eval_chk e' (LF.MDot (LF.ClObj (phat, LF.MObj tM'), theta1), eta1)
        | Comp.DataValue (cid, spine) ->
          Comp.DataValue (cid, Comp.DataApp (Comp.BoxValue (l, LF.ClObj (phat, LF.MObj tM')), spine))
        | Comp.FunValue fbr ->
          eval_fun_branches (Comp.BoxValue (l, LF.ClObj(phat, LF.MObj tM'))) fbr
        | _ -> raise (Error.Violation "Expected MLamValue ")
      end

    | Comp.MApp (_, i', (l, LF.ClObj (phat, LF.PObj h)), _, _) ->
        let h' = Whnf.cnormHead (h, theta) in
        let phat = Whnf.cnorm_psihat phat theta in
      begin match eval_syn i' (theta, eta) with
        | Comp.MLamValue (_u, e', theta1, eta1) ->
          eval_chk e' (LF.MDot (LF.ClObj (phat, LF.PObj h'), theta1), eta1)
        | Comp.DataValue (cid, spine) ->
          Comp.DataValue (cid, Comp.DataApp (Comp.BoxValue (l, LF.ClObj (phat, LF.PObj h')), spine))
        | Comp.FunValue fbr ->
          eval_fun_branches (Comp.BoxValue (l, LF.ClObj (phat, LF.PObj h'))) fbr
        | _ -> raise (Error.Violation "Expected MLamValue")
      end

    | Comp.MApp (loc, i', (l, LF.CObj cPsi), _, _) ->
      let cPsi' = Whnf.cnormDCtx (cPsi, theta) in
      dprint (fun () -> "EVALUATE CtxApp ");
      dprintf
        begin fun p ->
        p.fmt "[CtxApp] cPsi = @[%a@]"
          (P.fmt_ppr_lf_dctx LF.Empty P.l0) cPsi'
        end;
      begin match eval_syn i' (theta, eta) with
        | Comp.MLamValue (_psi, e', theta1, eta1) ->
          let theta1' =  LF.MDot(LF.CObj(cPsi'), theta1) in
          dprintf
            begin fun p ->
            p.fmt "[CtxApp] theta1' = @[%a@]"
              (P.fmt_ppr_lf_msub LF.Empty P.l0) theta1'
            end;
          eval_chk e' (theta1', eta1)
        | Comp.DataValue (cid, spine) ->
          Comp.DataValue (cid, Comp.DataApp (Comp.BoxValue(l, LF.CObj cPsi'), spine))
        | Comp.FunValue fbr ->
          eval_fun_branches (Comp.BoxValue (l, LF.CObj cPsi')) fbr
        | _ ->
           Format.fprintf Format.std_formatter "@[<v%a@,@]"
             Syntax.Loc.print loc;
           raise (Error.Violation "Expected CtxValue")
      end

    | Comp.AnnBox (cM, _tau) ->
       let loc, cM' = eval_meta_obj cM theta in
       Comp.BoxValue (loc, cM')

    | Comp.PairVal (_, i1, i2) ->
      let v1 = eval_syn i1 (theta, eta) in
      let v2 = eval_syn i2 (theta, eta) in
      Comp.PairValue (v1, v2)

and eval_chk (e : Comp.exp_chk) (theta, eta) =
    match e with
      | Comp.Syn (_, i) -> eval_syn i (theta, eta)
      | Comp.MLam (loc, n, e') ->
         Comp.MLamValue (n, e', Whnf.cnormMSub theta, eta)

      | Comp.Fn (loc, x, e') ->
         Comp.FnValue (x, e', Whnf.cnormMSub theta, eta)

      | Comp.Fun (loc, fbr) ->
         let rec convert_fbranches = function
           | Comp.NilFBranch _ -> Comp.NilValBranch
           | Comp.ConsFBranch (_, (cD, _, ps, e), fb) ->
              let mt = Ctxsub.mctxToMSub (Whnf.normMCtx cD) in
              let _ = Unify.unifyMSub theta mt in
              Comp.ConsValBranch ((ps, e, Whnf.cnormMSub mt, eta), convert_fbranches fb)
         in
         Comp.FunValue (convert_fbranches fbr)


      | Comp.Pair (_, e1, e2) ->
        let v1 = eval_chk e1 (theta, eta) in
        let v2 = eval_chk e2 (theta, eta) in
        Comp.PairValue (v1, v2)

      | Comp.Let (loc, i, (x, e)) ->
          let w = eval_syn i (theta, eta) in
            eval_chk e (theta, Comp.Cons (w, eta))

      | Comp.Box (loc, cM, _) ->
         let loc, cM' = eval_meta_obj cM theta in
         Comp.BoxValue (loc, cM')

      | Comp.Case (loc, _prag, i, branches) ->
        let vscrut = eval_syn i (theta, eta) in
        eval_branches loc vscrut branches (theta, eta)

      | Comp.Hole (_) ->
        raise (Error.Violation "Source contains holes")

and eval_branches loc vscrut branches (theta, eta) = match branches with
  | [] -> raise (Error (loc, MissingBranch))
  | b::branches ->
    try
      dprintf
        begin fun p ->
        p.fmt "[eval_branches] try branch with theta = %a"
          (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta)
        end;
      eval_branch vscrut b (theta, eta)
    with BranchMismatch ->
      dprintf
        begin fun p ->
        p.fmt "[eval_branches] @[<v>Try next branch...@,\
               with theta = @[%a@]@]"
          (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta)
        end;
      eval_branches loc vscrut branches (theta, eta)


and match_cobj (phat, cObj) (cPsi', cObj', mt) =
  let cPsi' = Whnf.cnormDCtx (cPsi', mt) in
  let cObj' = Whnf.cnormClObj cObj' mt in

    Unify.unify_phat phat (Context.dctxToHat cPsi');
    (match cObj, cObj' with
       |  LF.MObj tM , LF.MObj tM' ->
	    Unify.unify LF.Empty cPsi' (tM, Substitution.LF.id) (tM', Substitution.LF.id)
       | LF.PObj h   , LF.PObj h' ->
           Unify.unifyH LF.Empty phat h h')

and match_pattern  (v,eta) (pat, mt) =
  let eta = ref eta in
  let rec loop v pat =
    match v, pat with

      | Comp.BoxValue (_, LF.ClObj (phat, cObj)) ,
	Comp.PatAnn (_, Comp.PatMetaObj (_, (_ , LF.ClObj (_, cObj'))), Comp.TypBox (_, LF.ClTyp (_ , cPsi'))) ->
	  match_cobj (phat, cObj) (cPsi', cObj', mt)

      | Comp.BoxValue (_, LF.ClObj (phat, cObj)) ,
	Comp.PatMetaObj (_, (_ , LF.ClObj (phat', cObj'))) ->
	  match_cobj (phat, cObj) (Context.hatToDCtx phat', cObj', mt)
(*      | Comp.BoxValue (_,LF.ClObj(phat, LF.MObj tM)), Comp.PatMetaObj (_, (_, LF.ClObj (phat', LF.MObj tM'))) ->
	let cPsi = Context.hatToDCtx phat' in
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

      | Comp.BoxValue (_,LF.ClObj(phat, LF.PObj h)), Comp.PatMetaObj (_, (_,LF.ClObj (phat', LF.PObj h'))) ->
          let phat' = Whnf.cnorm_psihat phat' mt in
          let h'    = Whnf.cnormHead (h', mt) in
            Unify.unify_phat phat phat';
            Unify.unifyH LF.Empty phat h h'
      | _, Comp.PatMetaObj (_, (_, LF.ClObj (_, LF.PObj _) )) ->
        raise (Error.Violation "Expected param value.")
*)
      | Comp.BoxValue (_,LF.CObj cPsi), Comp.PatMetaObj (_, (_,LF.CObj cPsi')) ->
        let cPsi' = Whnf.cnormDCtx (cPsi', mt) in
          dprint (fun () -> "[match_pattern] call unifyDCtx ");
          Unify.unifyDCtx LF.Empty cPsi cPsi'
      | _, Comp.PatMetaObj (_, (_,LF.CObj cPsi')) ->
        raise (Error.Violation "Expected context.")


      | _, Comp.PatAnn (_, pat', _) ->
        loop v pat'

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

      | _ ->
         Error.not_implemented' "[opsem] [match_pattern] other cases not implemented"
  in loop v pat; !eta

and eval_branch vscrut branch (theta, eta) =
  match branch with
    | Comp.Branch (loc, cD, cG, pat, theta', e) ->
      begin
        try
          let mt = Ctxsub.mctxToMSub (Whnf.normMCtx cD) in
          let theta_k = Whnf.mcomp (Whnf.cnormMSub theta') mt in
          dprintf
            begin fun p ->
            p.fmt "[eval_branches] try branch with @[<v>theta_k = @[%a@]@,cD = %a@]"
              (P.fmt_ppr_lf_msub LF.Empty P.l0) (Whnf.cnormMSub theta_k)
              (P.fmt_ppr_lf_mctx P.l0) cD
            end;
          Unify.unifyMSub theta theta_k;
          dprintf
            begin fun p ->
            p.fmt "[eval_branches] @[<v>match scrutinee against pattern@,\
                   @[%a@]@,\
                   pattern with mvars:@,\
                   @[%a@]@]"
              (P.fmt_ppr_cmp_pattern cD cG P.l0) pat
              (P.fmt_ppr_cmp_pattern LF.Empty (Whnf.cnormGCtx (cG, mt)) P.l0)
              (Whnf.cnormPattern (pat, mt))
            end;
          let eta' = match_pattern  (vscrut, eta) (pat, mt) in
            eval_chk e (Whnf.cnormMSub mt, eta')
        with Unify.Failure msg -> (dprint (fun () -> "Branch failed : " ^ msg) ; raise BranchMismatch)
	  | e -> (dprint (fun () -> "000 Branch failed\n"); raise e)
      end

and eval_fun_branches v branch =
  let rec eval_branch branch =
      match branch with
      | Comp.NilValBranch -> FunBranch (Comp.NilValBranch)
      | Comp.ConsValBranch ((Comp.PatApp (_, p, Comp.PatNil), e, theta, eta), brs) ->
        begin try
          let eta' = match_pattern (v, eta) (p, theta) in
          Value (eval_chk e (Whnf.cnormMSub theta, eta'))
        with BranchMismatch ->
          eval_branch brs
        | Unify.Failure msg -> (dprint (fun () -> "Branch failed : " ^ msg);
                                eval_branch brs)
        end
      | Comp.ConsValBranch ((Comp.PatApp (_, p, ps), e, theta, eta), brs) ->
        begin try
          let eta' = match_pattern (v, eta) (p, theta) in
          match eval_branch brs with
          | Value v -> Value v              (* This is kind of an odd case that assumes varying length of branches *)
          | FunBranch brs' -> FunBranch (Comp.ConsValBranch ((ps, e, theta, eta'), brs'))
        with BranchMismatch ->
          eval_branch brs
        | Unify.Failure msg -> (dprint (fun () -> "Branch failed : " ^ msg);
                                eval_branch brs)
        end
  in match eval_branch branch with
  | Value v -> v
  | FunBranch f -> Comp.FunValue f


let eval (e : Comp.exp_chk) =
  dprint (fun () -> "Opsem.eval");
  dprintf (fun p -> p.fmt "  @[<v>");
  let result = eval_chk e (LF.MShift 0, Comp.Empty) in
  dprintf (fun p -> p.fmt "@]");
  result
