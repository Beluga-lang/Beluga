(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [5])

module LF = Lfcheck

module Comp = struct

  module Unify = Unify.EmptyTrail
    (* NOTES on handling context variables: -bp
     *
     *  - We should maybe put context variables into a context Omega (not Delta)
     *    It makes it difficult to deal with branches.
     *
     *  Recall: Case(e, branches)  where branch 1 = Pi Delta1. box(psihat. tM1) : A1[Psi1] -> e1
     *
     *  Note that any context variable occurring in Delta, psihat, A and Psi is bound OUTSIDE.
     *  So if
     *
     *  D ; G |- Case (e, branches)  and ctxvar psi in D the branch 1 is actually well formed iff
     *
     *  D, D1 ; Psi1 |- tM1 <= tA1  (where only psi declared in D is relevant to the rest.)
     *
     *  Also, ctx variables are not subject to instantiations during unification / matching
     *  which is used in type checking and type reconstruction.
     *
     *  This has wider implications;
     *
     * - revise indexing structure; the offset of ctxvar is with respect to
     *   a context Omega
     *
     * - Applying substitution for context variables; does it make sense to
     *   deal with it lazily?   It seems complicated to handle lazy context substitutions
     *   AND lazy msubs.
     *
     *  If we keep them in Delta, we need to rewrite mctxToMSub for example;
     *)

  open Context
  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type error =
      IllTyped        of I.mctx * gctx * exp_chk * tclo * tclo
    | PatIllTyped     of I.mctx * gctx * pattern * tclo * tclo
    | Mismatch        of I.mctx * gctx * exp_syn * typeVariant * tclo
    | CtxFunMismatch  of I.mctx * gctx  * tclo 
    | FunMismatch     of I.mctx * gctx  * tclo 
    | MLamMismatch    of I.mctx * gctx  * tclo 
    | PairMismatch    of I.mctx * gctx  * tclo 
    | BoxMismatch     of I.mctx * gctx  * tclo 
    | SBoxMismatch    of I.mctx * gctx  * I.dctx  * I.dctx
    | SynMismatch     of I.mctx * tclo (* expected *) * tclo (* inferred *)
    | SubPattMismatch of (I.mctx * I.dctx * I.sub * I.dctx) * 
                         (I.mctx * I.dctx * I.dctx)  
    | BoxCtxMismatch  of I.mctx * I.dctx * (I.psi_hat * I.normal)
    | PattMismatch    of (I.mctx * I.dctx * I.normal option * I.tclo) * 
                         (I.mctx * I.dctx * I.tclo)  
    | IfMismatch      of I.mctx * gctx  * tclo 
    | EqMismatch      of I.mctx * tclo (* arg1 *) * tclo (* arg2 *)
    | EqTyp           of I.mctx * tclo 
    | MAppMismatch    of I.mctx * (meta_typ * I.msub)
    | AppMismatch     of I.mctx * (meta_typ * I.msub)

  exception Error of Syntax.Loc.t * error

  let string_of_typeVariant = function
    | VariantCross -> "product type"
    | VariantArrow -> "function type"
    | VariantCtxPi -> "context abstraction"
    | VariantPiBox -> "dependent function type"
    | VariantBox   -> "contextual type"

  let _ = Error.register_printer
    (fun (Error (loc, e)) ->
      Error.print_with_location loc (fun ppf ->
        match e with
          | IllTyped (cD, cG, e, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
            Format.fprintf ppf
              "ill-typed expression\n  expected: %a\n  for expression: %a\n  inferred: %a\n\
               Note: Computation-level applications are not automatically left-associative but require parentheses."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              (P.fmt_ppr_cmp_exp_chk cD cG Pretty.std_lvl) e
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau')

          | PatIllTyped (cD, cG, pat, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
            Format.fprintf ppf
              "ill-typed pattern\n  expected: %a\n  for pattern: %a\n  inferred:%a  "
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau) 
              (P.fmt_ppr_pat_obj cD cG Pretty.std_lvl) pat
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau') 

          | Mismatch (cD, cG, i, variant, theta_tau) ->
            Format.fprintf ppf
              "ill-typed expression\n  inferred: %a\n  for expression: %a\n\
               Beluga believes it should be a %s\n\
               Note: Computation-level applications are not automatically left-associative but require parentheses."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i
              (string_of_typeVariant variant)

          | PattMismatch ((cD, cPsi, pattern, sA) , (cD', cPsi', sA')) ->
            Format.fprintf ppf
              "ill-typed pattern\n  expected: %a[%a] \n  inferred: %a[%a]\n  for expression: [%a] %a"
              (P.fmt_ppr_lf_typ cD' cPsi' Pretty.std_lvl) (Whnf.normTyp sA')
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPsi')
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_patternOpt cD' cPsi) pattern

          | SubPattMismatch ((cD, cPsi, sigma, cPhi) , (cD', cPsi', cPhi')) ->
            Format.fprintf ppf
              "ill-typed pattern\n  expected: %a[%a] \n  inferred: %a[%a]\n  for subst-pattern: %a"
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPsi')
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPhi')
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) (Whnf.normDCtx cPhi)
              (P.fmt_ppr_lf_sub cD cPsi Pretty.std_lvl) sigma

          | BoxCtxMismatch (cD, cPsi, (phat, tM)) ->
            Format.fprintf ppf
              "Expected: %a\n  in context %a\n  Used in context %a"
              (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) tM
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl) (Context.hatToDCtx phat)

          | CtxFunMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found Ctx abstraction, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | FunMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found function abstraction, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | MLamMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found MLam abstraction, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | BoxMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found box-expression that does not have type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | SBoxMismatch (cD, _cG, cPsi, cPhi) ->
            Format.fprintf ppf
              "Found substitution that does not have type %a[%a]"
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPhi)

          | IfMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Guard of if-expression does not have type bool; it has type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | PairMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found tuple, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | SynMismatch (cD, theta_tau, theta_tau') ->
            Format.fprintf ppf
              "Expected type  %a\nInferred type  %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau')

          | EqMismatch (cD, ttau1, ttau2) ->
            Format.fprintf ppf
              "Type mismatch on equality:\nComparing objects of type  %a\n with objects of type  %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau1)
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau2)

          | EqTyp (cD, ttau) ->
            Format.fprintf ppf
              "Equality comparison only possible at base types;\nfound objects of type  %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau)

          | AppMismatch (cD, (MetaTyp (tP, cPsi), tau)) ->
            Format.fprintf ppf
              "Expected contextual object ( Psi . M ) of type   %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, tP, cPsi), tau))

          | MAppMismatch (cD, (MetaTyp (tA, cPsi), tau)) ->
            Format.fprintf ppf
              "Expected contextual object ( Psi . M ) of type   %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, tA, cPsi), tau))

          | MAppMismatch (cD, (MetaSchema cid_schema, tau)) ->
            Format.fprintf ppf
              "Expected context of schema  %s"
              (R.render_cid_schema cid_schema)))

  type caseType =
    | IndexObj of I.psi_hat * I.normal
    | DataObj 

  let rec length cD = match cD with
    | I.Empty -> 0
    | I.Dec(cD, _) -> 1 + length cD

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (_,  tau)), 1) -> tau
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let rec split tc d = match (tc, d) with
    | (tc, 0) -> tc
    | (I.MDot (_ft, t), d) -> split t (d - 1)

  (* extend t1 t2 = t
   *
   * Invariant:
   * If    . |- t1 <= cD1
   *   and . |- t2 <= cD2
   *   and FMV(cD1) intersect FMV(cD2) = {}
   *   (i.e. no modal variable occurring in type declarations in cD1
   *    also occurs in a type declaration of cD2)
   * then
   *       . |- t1,t2 <= cD1, cD2   and t = t1,t2
   *)
  let extend t1 t2 = 
    let rec ext t2 = match t2 with
      | I.MShift 0     -> t1
      | I.MDot (ft, t) -> I.MDot (ft, ext t)
      (* other cases should be impossible *)
    in ext t2;;

  let rec checkMetaObj loc cD cM cTt = match  (cM, cTt) with 
  | (MetaCtx (loc, cPsi), (MetaSchema  w, _)) -> 
      LF.checkSchema loc cD cPsi (Schema.get_schema w)

  | (MetaObj (loc, phat, tM), (MetaTyp (tA, cPsi), t)) ->  
      LF.check cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) 
  | (MetaObjAnn (loc, _cPhi, tM), (MetaTyp (tA, cPsi), t)) (* cPhi = cPsi *) ->  
      LF.check cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id)  
;
         
    (* The case for parameter types should be handled separately, for better error messages -bp *)


and checkMetaSpine loc cD mS cKt  = match (mS, cKt) with 
  | (MetaNil , (Ctype _ , _ )) -> ()
  | (MetaApp (mO, mS), (PiKind (_, (cdecl, _ ), cK) , t)) -> 
      begin match cdecl with 
        | I.CDecl (_psi, schema_cid, _ ) -> 
            let MetaCtx (_, cPsi) = mO in 
            let theta' = Ctxsub.csub_msub cPsi 1 t in
            let cK'   = Ctxsub.csub_ckind cD cPsi 1 cK in               
              checkMetaObj loc cD mO (MetaSchema schema_cid , t); 
              checkMetaSpine loc cD mS (cK', theta')

        | I.MDecl (_u, tA, cPsi) -> 
            let MetaObj (loc, psihat, tM) = mO in 
              checkMetaObj loc cD mO (MetaTyp (tA, cPsi), t) ;
              checkMetaSpine loc cD mS (cK, I.MDot (I.MObj(psihat, tM), t)) 
    end


  let rec checkCDecl cD cdecl = match cdecl with 
    | I.CDecl (_, schema_cid, _ ) -> 
        begin try 
          let _ = Schema.get_schema schema_cid in ()
        with _ -> raise (Error.Violation "Schema undefined")
        end
    | I.MDecl (_, tA, cPsi) -> 
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)
    | I.PDecl (_, tA, cPsi) -> 
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)
              

  let rec checkKind cD cK = match cK with
    | Ctype _ -> ()
    | PiKind (_, ((I.CDecl _ ) as cdecl, dep), cK) -> 
        checkCDecl cD cdecl;
        checkKind (I.Dec(cD, cdecl)) cK
    | PiKind (_, (cdecl,dep), cK) -> 
        checkCDecl cD cdecl;
        checkKind (I.Dec(cD, cdecl)) cK
        
  let rec checkTyp cD tau =  match tau with
    | TypBase (loc, c, mS) -> 
        let cK = (CompTyp.get c).CompTyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypBox (_ , tA, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkTyp  cD cPsi (tA, S.LF.id)

    | TypSub (_ , cPhi, cPsi) ->
        LF.checkDCtx cD cPsi;
        LF.checkDCtx cD cPhi
          
    | TypArr (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2
          
    | TypCross (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2
          
    | TypCtxPi ((psi_name, schema_cid, dep ), tau) ->
        let dep' = match dep with Explicit -> I.No | Implicit -> I.Maybe in 
        checkTyp (I.Dec (cD, I.CDecl (psi_name, schema_cid, dep'))) tau
          
    | TypPiBox ((cdecl, _), tau') ->
        dprint (fun () -> "[checkCompTyp] " ^ 
                  P.mctxToString cD ^ " |- " ^ 
                  P.compTypToString cD tau);
        checkCDecl cD cdecl;
        dprint (fun () -> "[checkCompTyp] " ^ 
                  P.mctxToString (I.Dec (cD, cdecl)) ^ " |- " ^ 
                  P.compTypToString (I.Dec (cD, cdecl)) tau');
        checkTyp (I.Dec (cD, cdecl)) tau' 

    | TypBool -> ()

;;


  (* check cD cG e (tau, theta) = ()
   *
   * Invariant:
   *
   * If  ; cD ; cG |- e wf-exp
   * and ; cD |- theta <= cD'
   * and ; cD'|- tau <= c_typ
   * returns ()
   * if  ; cD ; cG |- e <= [|t|]tau
   *
   * otherwise exception Error is raised
   *)
  
  let rec checkW cD (cG : ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (_, f, e), (tau, t)) ->
        check cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t)))) e ttau

    | (Fun (_, x, e), (TypArr (tau1, tau2), t)) ->
        check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t)))) e (tau2, t)

    | (CtxFun (_, psi, e), (TypCtxPi ((_psi, schema, dep ), tau), t)) ->
        let dep' = match dep with Explicit -> I.No | Implicit -> I.Maybe in 
        check (I.Dec(cD, I.CDecl(psi, schema, dep')))  
          (C.cnormCtx (cG, I.MShift 1)) e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.MDecl(_u, tA, cPsi), _), tau), t)) ->
        check (I.Dec(cD, I.MDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.PDecl(_u, tA, cPsi), _), tau), t)) ->
        check (I.Dec(cD, I.PDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.SDecl(_u, cPhi, cPsi), _), tau), t)) ->
        check (I.Dec(cD, I.SDecl(u, C.cnormDCtx (cPhi, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (Pair (_, e1, e2), (TypCross (tau1, tau2), t)) ->
        check cD cG e1 (tau1, t);
        check cD cG e2 (tau2, t)

    | (Let (_, i, (x, e)), (tau, t)) ->          
        let (tau', t') =  C.cwhnfCTyp (syn cD cG i) in
        let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
          check cD cG' e (tau,t)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
        begin match C.cwhnfCTyp (syn cD cG i) with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cD cG' e (tau,t)
          | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
        end

    | (Box (_, _phat, tM), (TypBox (_, tA, cPsi), t)) ->
        begin try
(*        Already done during cwhnfCTyp ... -bp
          let cPsi' = C.cnormDCtx (cPsi, t) in
          let tA'   = C.cnormTyp (tA, t) in
*)
            LF.check cD  cPsi (tM, S.LF.id) (tA, S.LF.id)
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Error.Violation ("Free meta-variable " ^ (R.render_name u)))
        end

    | (SBox (loc , _phat, sigma), (TypSub (_, cPhi, cPsi), t)) ->
        begin try
            LF.checkSub loc cD  cPsi sigma cPhi
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Error.Violation ("Free meta-variable " ^ (R.render_name u)))
        end

    | (Case (loc, prag, Ann (Box (_, phat, tR), TypBox (_, tA', cPsi')),
      branches), (tau, t)) ->
        let tau_s = TypBox (loc, Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi') in
        let _  = LF.check cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in 
        let cA = (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi') in 
        let problem = Coverage.make loc prag Syntax.Int.LF.Empty cD branches cA in
          (* Coverage.stage problem; *)
          checkBranches (IndexObj (phat, tR)) cD cG branches tau_s (tau, t);
          Coverage.process problem

    | (Case (loc, prag, i, branches), (tau, t)) -> 
        begin match C.cwhnfCTyp (syn cD cG i) with
          | (TypBox (loc, tA, cPsi),  t') ->
              let problem = Coverage.make loc prag Syntax.Int.LF.Empty cD branches (tA, cPsi) in
              (* Coverage.stage problem; *)
              let tau_s = TypBox (loc, C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) in 
                checkBranches DataObj cD cG branches tau_s (tau,t);
                Coverage.process problem
          | (tau',t') -> 
              checkBranches DataObj cD cG branches (C.cnormCTyp (tau', t')) (tau,t)
        end

    | (Syn (loc, i), (tau, t)) ->
        let ttau' = (syn cD cG i) in 
        if C.convCTyp (tau,t)  ttau' then 
          ()
        else
          raise (Error (loc, IllTyped (cD, cG, e, (tau,t), ttau')))

    | (If (loc, i, e1, e2), (tau,t)) -> 
        begin match C.cwhnfCTyp (syn cD cG i) with
          | (TypBool , _ ) -> 
              (check cD cG e1 (tau,t) ; 
               check cD cG e1 (tau,t) )
          | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
        end 

  and check cD cG e (tau, t) =
    checkW cD cG e (C.cwhnfCTyp (tau, t));

  and syn cD cG e = match e with
    | Var x   -> (lookup cG x, C.m_id)
    | DataConst c ->
        ((CompConst.get c).CompConst.typ, C.m_id)

    | Const prog ->
        ((Comp.get prog).Comp.typ, C.m_id)

    | Apply (loc , e1, e2) ->
        begin match C.cwhnfCTyp (syn cD cG e1) with
          | (TypArr (tau2, tau), t) ->
              dprint (fun () -> "[SYN: APPLY ] synthesized type  " ^
                          P.compTypToString cD (Whnf.cnormCTyp (TypArr (tau2,
        tau), t) ));
              dprint (fun () -> ("[check: APPLY] argument has appropriate type " ^
                                       P.expChkToString cD cG e2));
              dprint (fun () -> "[check: APPLY] cG " ^ P.gctxToString cD cG );
              check cD cG e2 (tau2, t);
              (tau, t)
          | (tau, t) -> 
              raise (Error (loc, Mismatch (cD, cG, e1, VariantArrow, (tau,t))))
        end

    | CtxApp (loc, e, cPsi) ->
        begin match C.cwhnfCTyp (syn cD cG e) with
          | ((TypCtxPi ((_psi, w, _ ) , tau), t) as tt) ->
              let theta' = I.MDot (I.CObj (cPsi), t) in
              LF.checkSchema loc cD cPsi (Schema.get_schema w);
              (dprint (fun () -> "[check: syn] CtxApp : tau = " ^ 
                         P.compTypToString cD (Whnf.cnormCTyp tt) ); 
               dprint (fun () -> "[check: syn] cPsi = " ^ P.dctxToString cD cPsi );
               dprint (fun () -> "[check: syn] tau1 = " ^
                          P.compTypToString cD (Whnf.cnormCTyp (tau, theta') ))) ; 
                 (tau, theta') 
          | (tau, t) -> 
              raise (Error (loc, Mismatch (cD, cG, e, VariantCtxPi, (tau,t))))
        end
    | MApp (loc, e, (phat, cObj)) ->
        begin match (cObj, C.cwhnfCTyp (syn cD cG e)) with
          | (NormObj tM, (TypPiBox ((I.MDecl(_, tA, cPsi), _ ), tau), t)) ->
              LF.check cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id);
              (tau, I.MDot(I.MObj (phat, tM), t))

          | (NeutObj h, (TypPiBox ((I.PDecl(_, tA, cPsi), _ ), tau), t)) ->
              let _ =  dprint (fun () -> "[check: inferHead] cPsi = " ^
                                 P.dctxToString cD (C.cnormDCtx (cPsi,t) )) in
              let tB = LF.inferHead loc cD (C.cnormDCtx (cPsi,t)) h in 
                if Whnf.convTyp (tB, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) then
                  (tau, I.MDot(I.PObj (phat, h), t))
                else 
                  raise (Error (loc, Mismatch (cD, cG, e, VariantPiBox, (tau,t))))

          | (_ , (tau, t)) -> 
              raise (Error (loc, Mismatch (cD, cG, e, VariantPiBox, (tau,t))))
        end

    | Ann (e, tau) ->
        check cD cG e (tau, C.m_id);
        (tau, C.m_id)

    | Equal(loc, i1, i2) -> 
         let ttau1 = syn cD cG i1 in 
         let ttau2 = syn cD cG i2 in            
           if Whnf.convCTyp ttau1 ttau2 then 
             begin match (Whnf.cwhnfCTyp ttau1) with 
               | (TypBox _ , _ ) ->  (TypBool, C.m_id)
               | (TypBool, _ )   ->  (TypBool, C.m_id)
               | _               ->  raise (Error (loc, EqTyp (cD, ttau1))) 
             end

           else 
             raise (Error(loc, EqMismatch (cD, ttau1, ttau2 )))

    | Boolean _  -> (TypBool, C.m_id)


  and checkPattern cD cG pat ttau = match pat with 
    | PatEmpty (loc, cPsi) -> 
        (match ttau with 
          | (TypBox (_, tA, cPhi) , theta) ->               
              let _ = dprint (fun () -> "[checkPattern] PatEmpty : \n cD = " ^ 
                                P.mctxToString cD ^ 
                                "context of expected  type " ^ 
                                P.dctxToString cD (Whnf.cnormDCtx (cPhi, theta))
                                ^ "\n context given " ^ P.dctxToString cD cPsi) in
              if C.convDCtx (Whnf.cnormDCtx (cPhi, theta)) cPsi then ()
              else 
                raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
          | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
        )

    | PatMetaObj (loc, mO) -> 
        (match ttau with 
          | (TypBox (_, tA, cPsi) , theta) -> 
              checkMetaObj loc cD mO (MetaTyp (tA, cPsi), theta)
          | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
        )
    | pat -> 
        let (loc, ttau') = synPattern cD cG pat in 
          if C.convCTyp ttau ttau' then ()
          else 
            raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat = match pat with 
    | PatConst (loc, c, pat_spine) -> 
        let tau = (CompConst.get c).CompConst.typ in 
          (loc, synPatSpine cD cG pat_spine (tau , C.m_id))
    | PatVar (loc, k) -> (loc, (lookup cG k, C.m_id))
    | PatTrue loc -> (loc, (TypBool, C.m_id))
    | PatFalse loc -> (loc, (TypBool, C.m_id))
    | PatAnn (loc, pat, tau) ->  
        checkPattern cD cG pat (tau, C.m_id);
        (loc, (tau, C.m_id))

  and synPatSpine cD cG pat_spine (tau, theta) = match pat_spine with
    | PatNil  -> (tau, theta)
    | PatApp (_loc, pat, pat_spine)  -> 
        (match (tau, theta) with 
           | (TypArr (tau1, tau2), theta) -> 
               checkPattern cD cG pat (tau1, theta); 
               synPatSpine cD cG pat_spine (tau2, theta)
           | (TypPiBox ((cdecl, _), tau), theta) -> 
               let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in 
                 synPatSpine cD cG pat_spine (tau, theta')
           | (TypCtxPi ((x, w, dep), tau), theta) ->            
             let theta' =  checkPatAgainstCDecl cD pat (I.CDecl(x,w, I.No), theta) in 
               synPatSpine cD cG pat_spine (tau, theta')
        )
          
  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (cdecl, theta) = match cdecl with
    | I.MDecl (_, tA, cPsi) -> 
        let _ = checkMetaObj loc cD mO (MetaTyp (tA, cPsi), theta) in 
          (match mO with
            | MetaObj (_, phat, tM) ->  I.MDot(I.MObj(phat, tM), theta)
            | MetaObjAnn (_, cPsi, tM) -> I.MDot (I.MObj(Context.dctxToHat cPsi, tM), theta)
          )
    | I.CDecl (_, w, _ ) -> 
        let _ = checkMetaObj loc cD mO (MetaSchema w, theta) in 
          (match mO with 
            | MetaCtx (_, cPsi) -> I.MDot (I.CObj (cPsi) , theta)
          )
  and checkBranches caseTyp cD cG branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cD cG branch tAbox ttau) branches

  and checkBranch _caseTyp cD cG branch tau_s (tau, t) =
    match branch with
      | EmptyBranch (loc, cD1', pat, t1) -> 
          let _ = dprint (fun () -> "\nCheckBranch - Empty Pattern\n") in 
          let _ = dprint (fun () -> "cD1 = " ^ P.mctxToString cD1') in 
          let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD) in 
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in 
          let _     = LF.checkMSub  loc cD1' t1 cD in   
            checkPattern cD1' I.Empty pat (tau_p, Whnf.m_id)

      | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) -> 
          let _ = dprint (fun () -> "\nCheckBranch with normal pattern\n") in
          let TypBox (_, (I.Atom(_, a, _) as tP) , cPsi) = tau_s in 
          (* By invariant: cD1' |- t1 <= cD *)
          let tP1   = Whnf.cnormTyp (tP, t1) in 
          let cPsi1 = Whnf.cnormDCtx (cPsi, t1) in 
          let cG'   = Whnf.cnormCtx (cG, t1) in 
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in          
          let _     = LF.checkMSub loc cD1' t1 cD in   
          let _ = dprint (fun () -> "\nChecking refinement substitution : DONE\n") in            
          let _ = checkMetaObj loc cD1' mO  (MetaTyp (tP1, cPsi1), C.m_id) in   
            check cD1' cG' e1 (tau', Whnf.m_id)

      | Branch (loc, cD1', cG1, pat, t1, e1) -> 
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in 
          let cG'   = Whnf.cnormCtx (cG, t1) in 
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n") in
          let _ = dprint (fun () -> "\nChecking refinement substitution\n") in          
          let _     = LF.checkMSub loc  cD1' t1 cD in   
          let _ = dprint (fun () -> "\nChecking refinement substitution : DONE\n") in            
          let _ = checkPattern cD1' cG1 pat (tau_p, Whnf.m_id) in 
            check cD1' (Context.append cG' cG1) e1 (tau', Whnf.m_id)
            

end
  


module Sgn = struct

  type error

  let error_location e = assert false

  let report_error fmt e = assert false

  let rec check_sgn_decls = function
    | [] ->
        ()

    | Syntax.Int.Sgn.Typ (_a, tK) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkKind cD cPsi tK;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Const (_c, tA) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkTyp cD cPsi (tA, Substitution.LF.id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Schema (_w, schema) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkSchema (Syntax.Loc.ghost) cD cPsi schema;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Rec (f, tau, e) :: decls ->
        let cD = Syntax.Int.LF.Empty in
        let cG = Syntax.Int.LF.Empty in
          Comp.checkTyp cD tau;
          Comp.check cD cG e (tau, Whnf.m_id);         
          check_sgn_decls decls 

    | Syntax.Int.Sgn.Pragma (_a) :: decls ->
        check_sgn_decls decls

end
