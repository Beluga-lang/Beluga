(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [5])

module LF = Lfcheck

module Comp = struct

  module E = Error

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

  module P = Pretty.Int.DefaultPrinter

  type caseType =
    | IndexObj of I.psi_hat * I.normal
    | DataObj 

  exception Violation of string
  exception Error of Syntax.Loc.t option * E.error

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

(*** moved to Ctxsub
  let rec mctxToMSub cD = match cD with
    | I.Empty -> 
        C.m_id

    | I.Dec (cD', I.MDecl(_, tA, cPsi)) ->
        let t     = mctxToMSub cD' in
        let cPsi' = Whnf.cnormDCtx (cPsi, t) in
        let tA'   = Whnf.cnormTyp (tA, t) in
        let u     = Whnf.newMVar (cPsi', tA') in
        let phat  = Context.dctxToHat cPsi (*** cPsi' or cPsi? ***) in
          I.MDot (I.MObj (phat, I.Root (None, I.MVar (u, S.LF.id), I.Nil)), t)

    | I.Dec (cD', I.PDecl(_, tA, cPsi)) ->
        let t    = mctxToMSub cD' in
        let p    = Whnf.newPVar (Whnf.cnormDCtx (cPsi, t),  Whnf.cnormTyp (tA, t)) in
        let phat = Context.dctxToHat cPsi in  (*** cPsi' or cPsi? ***)
          I.MDot (I.PObj (phat, I.PVar (p, S.LF.id)), t)
***)
  let mctxToMSub = Ctxsub.mctxToMSub

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


  let rec checkTyp cO cD tau =

    match tau with
        
    | TypBox (_ , tA, cPsi) ->
        LF.checkDCtx cO cD cPsi;
        LF.checkTyp  cO cD cPsi (tA, S.LF.id)

    | TypSub (_ , cPhi, cPsi) ->
        LF.checkDCtx cO cD cPsi;
        LF.checkDCtx cO cD cPhi
          
    | TypArr (tau1, tau2) ->
        checkTyp cO cD tau1;
        checkTyp cO cD tau2
          
    | TypCross (tau1, tau2) ->
        checkTyp cO cD tau1;
        checkTyp cO cD tau2
          
    | TypCtxPi ((psi_name, schema_cid, _ ), tau) ->
        checkTyp (I.Dec (cO, I.CDecl (psi_name, schema_cid))) cD tau
          
    | TypPiBox ((cdecl, _), tau) ->
        checkTyp cO (I.Dec (cD, cdecl)) tau 

    | TypBool -> ()

;;


  (* check cO cD cG e (tau, theta) = ()
   *
   * Invariant:
   *
   * If  cO ; cD ; cG |- e wf-exp
   * and cO ; cD |- theta <= cD'
   * and cO ; cD'|- tau <= c_typ
   * returns ()
   * if  cO ; cD ; cG |- e <= [|t|]tau
   *
   * otherwise exception Error is raised
   *)
  
  let rec checkW cO cD (cG : ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (_, f, e), (tau, t)) ->
        check cO cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t)))) e ttau

    | (Fun (_, x, e), (TypArr (tau1, tau2), t)) ->
        check cO cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t)))) e (tau2, t)

    | (CtxFun (_, psi, e), (TypCtxPi ((_psi, schema, _ ), tau), t)) ->
        check (I.Dec(cO, I.CDecl(psi, schema))) cD cG e (tau, t)

    | (MLam (_, u, e), (TypPiBox ((I.MDecl(_u, tA, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.MDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.PDecl(_u, tA, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.PDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.SDecl(_u, cPhi, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.SDecl(u, C.cnormDCtx (cPhi, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (Pair (_, e1, e2), (TypCross (tau1, tau2), t)) ->
        check cO cD cG e1 (tau1, t);
        check cO cD cG e2 (tau2, t)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cO cD cG' e (tau,t)
          | _ -> raise (Violation "Case scrutinee not of boxed type")
        end

    | (Box (_, _phat, tM), (TypBox (_, tA, cPsi), t)) ->
        begin try
(*        Already done during cwhnfCTyp ... -bp
          let cPsi' = C.cnormDCtx (cPsi, t) in
          let tA'   = C.cnormTyp (tA, t) in
*)
            LF.check cO cD  cPsi (tM, S.LF.id) (tA, S.LF.id)
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Violation ("Free meta-variable " ^ (R.render_name u)))
        end

    | (SBox (loc , _phat, sigma), (TypSub (_, cPhi, cPsi), t)) ->
        begin try
            LF.checkSub loc cO cD  cPsi sigma cPhi
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Violation ("Free meta-variable " ^ (R.render_name u)))
        end

(*    | (SBox (loc , phat, sigma), tau_t) ->
        raise (Violation  ("Found SBox " ^ P.subToString cO cD (Context.hatToDCtx phat) sigma ^ 
                             "\n supposed to have type " ^ P.compTypToString cO cD (Whnf.cnormCTyp tau_t) ^ "\n"))


    | (Box (loc , phat, tM), tau_t) ->
        raise (Violation  ("Found Box " ^ P.normalToString cO cD (Context.hatToDCtx phat) (tM, S.LF.id) ^ 
                             "\n supposed to have type " ^ P.compTypToString cO cD (Whnf.cnormCTyp tau_t) ^ "\n"))

*)
    | (Case (loc, prag, Ann (Box (_, phat, tR), TypBox (_, tA', cPsi')), branches), (tau, t)) ->
        let _  = LF.check cO cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in 
        let cA = (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi') in
        let problem = Coverage.make loc prag cO cD branches cA in
          (* Coverage.stage problem; *)
          checkBranches (IndexObj (phat, tR)) cO cD cG branches cA (tau, t);
          Coverage.process problem

    | (Case (loc, prag, i, branches), (tau, t)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypBox (_, tA, cPsi),  t') ->
              let problem = Coverage.make loc prag cO cD branches (tA, cPsi) in
(*                Coverage.stage problem; *)
                checkBranches DataObj cO cD cG branches (C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) (tau,t);
                Coverage.process problem
          | (tau',t') -> raise (Error (loc, E.CompMismatch(cO, cD, cG, i, E.Box, (tau', t'))))
        end

    | (Syn (loc, i), (tau, t)) ->
        let ttau' = (syn cO cD cG i) in 
        if C.convCTyp (tau,t)  ttau' then 
          ()
        else
          raise (Error (loc, E.CompIllTyped (cO, cD, cG, e, (tau,t), ttau')))

    | (If (loc, i, e1, e2), (tau,t)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypBool , _ ) -> 
              (check cO cD cG e1 (tau,t) ; 
               check cO cD cG e1 (tau,t) )
          | tau_theta' -> raise (Error (loc, E.CompIfMismatch (cO, cD, cG, tau_theta')))
        end 

  and check cO cD cG e (tau, t) =
    dprint (fun () -> "check cO = " ^ P.octxToString cO);
    checkW cO cD cG e (C.cwhnfCTyp (tau, t));

  and syn cO cD cG e = match e with
    | Var x   -> (lookup cG x, C.m_id)
        (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD !!! *)

    | Const prog ->
        ((Comp.get prog).Comp.typ, C.m_id)

    | Apply (loc , e1, e2) ->
        begin match C.cwhnfCTyp (syn cO cD cG e1) with
          | (TypArr (tau2, tau), t) ->
              check cO cD cG e2 (tau2, t);
              (tau, t)
          | (tau, t) -> 
              raise (Error (loc, E.CompMismatch (cO, cD, cG, e1, E.Arrow, (tau,t))))
        end

    | CtxApp (loc, e, cPsi) ->
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypCtxPi ((_psi, w, _ ) , tau), t) ->
              let tau1 = Ctxsub.csub_ctyp cD cPsi 1 (Whnf.cnormCTyp (tau,t)) in
                LF.checkSchema cO cD cPsi (Schema.get_schema w);
                 (* (tau', t') *)
                 (tau1, C.m_id)                
          | (tau, t) -> 
              raise (Error (loc, E.CompMismatch (cO, cD, cG, e, E.CtxPi, (tau,t))))
        end
    | MApp (loc, e, (phat, cObj)) ->
        begin match (cObj, C.cwhnfCTyp (syn cO cD cG e)) with
          | (NormObj tM, (TypPiBox ((I.MDecl(_, tA, cPsi), _ ), tau), t)) ->
              LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id);
              (tau, I.MDot(I.MObj (phat, tM), t))

          | (NeutObj h, (TypPiBox ((I.PDecl(_, tA, cPsi), _ ), tau), t)) ->
              let tB = LF.inferHead loc cO cD cPsi h in 
                if Whnf.convTyp (tB, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) then
                  (tau, I.MDot(I.PObj (phat, h), t))
                else 
                  raise (Error (loc, E.CompMismatch (cO, cD, cG, e, E.PiBox, (tau,t))))

          | (_ , (tau, t)) -> 
              raise (Error (loc, E.CompMismatch (cO, cD, cG, e, E.PiBox, (tau,t))))
        end

    | Ann (e, tau) ->
        check cO cD cG e (tau, C.m_id);
        (tau, C.m_id)

    | Equal(loc, i1, i2) -> 
         let ttau1 = syn cO cD cG i1 in 
         let ttau2 = syn cO cD cG i2 in            
           if Whnf.convCTyp ttau1 ttau2 then 
             begin match (Whnf.cwhnfCTyp ttau1) with 
               | (TypBox _ , _ ) ->  (TypBool, C.m_id)
               | (TypBool, _ )   ->  (TypBool, C.m_id)
               | _               ->  raise (Error (loc, E.CompEqTyp (cO, cD, ttau1))) 
             end

           else 
             raise (Error(loc, E.CompEqMismatch (cO, cD, ttau1, ttau2 )))

    | Boolean _  -> (TypBool, C.m_id)





  and checkBranches caseTyp cO cD cG branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cO cD cG branch tAbox ttau) branches

(*  and checkBranch _caseTyp cO cD cG branch (tP, cPsi) (tau, t) =
    match branch with
      | BranchBox (cD1,  (cPsi1, (I.Root(loc, _, _ ) as tR1), (t1', cD1')),  e1) ->
          (* By invariant: cD1' |- t1' <= cD, cD1 *)
          let _         = LF.checkMSub cO cD1' t1' (Context.append cD cD1) in  
          let (tP1,s1)  = LF.syn cO cD1 cPsi1 (tR1, S.LF.id)  in 

          (* Apply to the type tP1[Psi1] the refinement substitution t1' *)
          (* cD1 ; cPsi1 |- tM1 <= tA1 
           * cD1'  |- t1' <= cD, cD1  and 
           * cD, cD1 |- MShift (n+n1) . u_n . ... . u_1  <= cD1
           *       t1 = MShift (n+n1) . u_n . ... . u_1  
           *)
          let n1  = length cD1 in 
          let n   = length cD  in 
          let t1  =  Whnf.mvar_dot (I.MShift n) cD1 in   
          (* cD1' |- t1_b <= cD1  where t1_b is the refinement substitution we apply to the pattern 
                                  and its context and type
           *)
          let t1_b      = Whnf.mcomp t1 t1' in 
          (* cD1'          |- cPsi1' ctx   where cPsi1' is the context of the pattern *)
          (* cD1' ; cPsi1' |- sP1' <- type  where sP1'  is the type of the pattern    *)
          let sP1'      = (Whnf.cnormTyp (tP1, t1_b), Whnf.cnormSub (s1, t1_b)) in 
          let cPsi1'    = Whnf.cnormDCtx (cPsi1, t1_b) in  

          (* Apply to the type of the scrutinee tP[Psi] the refinement substitution t1' *)
          (* cD |- cPsi ctx  and cD, cD1 |- MShift n1 <= cD
           *                 and cD1'    |- t1'       <= cD, CD1
           *               then  cD1' |- t1'' <= cD
           *)
          let t1''  = Whnf.mcomp (I.MShift n1) t1' in 
          let cPsi' = Whnf.cnormDCtx (cPsi, t1'') in  
          let tP'   = Whnf.cnormTyp (tP, t1'') in 

          (* Verify that the refinement substitution t1' 
           * makes the type of the pattern equal to the type of the scrutinee 
           * 
           * and cD1' |- |[t1'']|cPsi = |[t1]|cPs1
           * and cD1' ; |[t1]|cPsi1 |-  |[t1]|tP1 <= type
           * and cD1' ; |[t1]|cPsi1 |- |[t1]|tP1 = |[t1'']|tP
           *)

          let  _    = (if Whnf.convDCtx cPsi1' cPsi'
                         && Whnf.convTyp sP1' (tP', S.LF.id)
                       then  ()
                       else raise (Error (loc, E.CompPattMismatch ((cO, cD1, cPsi1, tR1, (tP1,s1)), 
                                                                   (cO, cD, cPsi, (tP, S.LF.id)))))) in 

          (* let t' = Whnf.mvar_dot t cD1 in  
             let t''  = Whnf.mcomp t' t1'' in *)
          (* if cD |- t <= cD0 then
             cD, cD1 |- t' <= cD0, cD1  *)


          let cG' = Whnf.cnormCtx (cG, t1'') in 
          let t'' = Whnf.mcomp t t1'' in

          let _ = dprint (fun () -> "\nCheckBranch with pattern\n Pi " ^
                        P.mctxToString cO cD1 ^ " . " ^ 
                        P.normalToString cO cD1 cPsi1 (tR1, S.LF.id) ^ "\n   =>  " ^ 
                            P.expChkToString cO cD1' cG' e1 ^ 
                            "\n has type "  ^ P.compTypToString cO cD1' (Whnf.cnormCTyp (tau, t'')) ^ "\n" 
                       ) in
                 
          in
            check cO cD1' cG' e1 (tau, t'');
*)
  and checkBranch _caseTyp cO cD cG branch (tP, cPsi) (tau, t) =
    match branch with
      | BranchBox  (cO1',  cD1',  (_cPsi1, NormalPattern(I.Root(loc, _, _ ) as tR1, e1),  t1,  cs)) ->
          (* By invariant: cD1' |- t1 <= cD *)
          let _     = LF.checkMSub cO1' cD1' t1 (Ctxsub.ctxnorm_mctx (cD,cs)) in  
          let tP1   = Ctxsub.ctxnorm_typ (Whnf.cnormTyp (tP, t1), cs) in 
          let cPsi1 = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx (cPsi, t1), cs) in

          let _  = LF.check cO1' cD1' cPsi1 (tR1, S.LF.id)  (tP1, S.LF.id) in 


          let cG' = Whnf.cnormCtx (Ctxsub.ctxnorm_gctx (cG, cs), t1) in 
          let t'' = Whnf.mcomp t t1 in

          let tau  = Whnf.cnormCTyp (tau, t'') in
          let tau' = Ctxsub.ctxnorm_ctyp (tau, cs) in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n Pi " ^
                        P.octxToString cO1' ^ " ; \n" ^ 
                        P.mctxToString cO1' cD1' ^ " ;\n " ^ 
                        P.normalToString cO1' cD1' cPsi1 (tR1, S.LF.id) ^ "\n   =>  " ^ 
                            P.expChkToString cO1' cD1' cG' e1 ^ 
                            "\n has type "  ^ P.compTypToString cO1' cD1' tau' ^ "\n" 
                       )
          in
            check cO1' cD1' cG' e1 (tau', Whnf.m_id)

      | BranchBox (cO1', cD1',  (_cPsi1, EmptyPattern, t1, cs)) ->
          (* By invariant: cD1' |- t1 <= cD *)
          let _     = LF.checkMSub cO1' cD1' t1 (Ctxsub.ctxnorm_mctx (cD,cs)) in  

          let t'' = Whnf.mcomp t t1 in

          let tau  = Whnf.cnormCTyp (tau, t'') in
          let tau' = Ctxsub.ctxnorm_ctyp (tau, cs) in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n Pi " ^
                        P.octxToString cO1' ^ " ; \n" ^ 
                        P.mctxToString cO1' cD1' ^ " ;\n " ^ 
                        "{} (EmptyPattern)" ^
                            "\n has type "  ^ P.compTypToString cO1' cD1' tau')
          in
            ()

end
  


module Sgn = struct

  let rec check_sgn_decls = function
    | [] ->
        ()

    | Syntax.Int.Sgn.Typ (_a, tK) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cO   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkKind cO cD cPsi tK;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Const (_c, tA) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cO   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkTyp cO cD cPsi (tA, Substitution.LF.id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Schema (_w, schema) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cO   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkSchema cO cD cPsi schema;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Rec (_f, tau, e) :: decls ->
        let cD = Syntax.Int.LF.Empty in
        let cO = Syntax.Int.LF.Empty in
        let cG = Syntax.Int.LF.Empty in
          Comp.checkTyp cO cD tau;
          Comp.check cO cD cG e (tau, Whnf.m_id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Pragma (_a) :: decls ->
        check_sgn_decls decls

end
