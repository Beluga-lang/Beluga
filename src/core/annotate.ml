(* Like check.ml, but produces annotated syntax nodes rather than returning unit *)

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [5])

module LF = struct
open Context
open Store.Cid
open Syntax.Int.LF

module Print = Pretty.Int.DefaultPrinter

module Unify = Unify.EmptyTrail

type error =
  | CtxVarMisCheck   of mctx * dctx * tclo * schema
  | CtxVarMismatch   of mctx * ctx_var * schema
  | CtxVarDiffer     of mctx * ctx_var * ctx_var
  | CheckError       of mctx * dctx * nclo * tclo
  | TupleArity       of mctx * dctx * nclo * trec_clo
  | SigmaMismatch    of mctx * dctx * trec_clo * trec_clo
  | KindMismatch     of mctx * dctx * sclo * (kind * sub)
  | TypMismatch      of mctx * dctx * nclo * tclo * tclo
  | IllTypedSub      of mctx * dctx * sub * dctx
  | SpineIllTyped    of int * int
  | LeftoverFV
  | ParamVarInst     of mctx * dctx * tclo
  | CtxHatMismatch   of mctx * dctx (* expected *) * psi_hat (* found *) * (Syntax.Loc.t * mfront)
  | IllTypedMetaObj  of mctx * clobj * dctx * cltyp 
  | TermWhenVar      of mctx * dctx * normal
  | SubWhenRen       of mctx * dctx * sub

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | ParamVarInst (cD, cPsi, sA) ->
            Format.fprintf ppf "Parameter variable of type %a does not appear as a declaration in context %a. @ @ It may be that no parameter variable of this type exists in the context or the type of the parameter variable is a projection of a declaration in the context."
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi

      | CtxVarMisCheck (c0, cPsi, sA, sEl ) ->
            Format.fprintf ppf "Type %a doesn't check against schema %a."
               (P.fmt_ppr_lf_typ c0 cPsi Pretty.std_lvl) (Whnf.normTyp sA)
               (P.fmt_ppr_lf_schema Pretty.std_lvl) sEl

      | CtxVarMismatch (cO, var, expected) ->
          Format.fprintf ppf "Context variable %a doesn't check against schema %a."
            (P.fmt_ppr_lf_ctx_var cO) var
            (P.fmt_ppr_lf_schema Pretty.std_lvl) expected

      | CtxVarDiffer (cO, var, var1) ->
          Format.fprintf ppf "Context variable %a not equal to %a."
            (P.fmt_ppr_lf_ctx_var cO) var
            (P.fmt_ppr_lf_ctx_var cO) var1

      | CheckError (cD, cPsi, sM, sA) ->
          Format.fprintf ppf
      "Expression %a does not check against %a."
      (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) (Whnf.norm sM)
      (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)

      | SigmaMismatch (cD, cPsi, sArec, sBrec) ->
        Error.report_mismatch ppf
    "Sigma type mismatch."
    "Expected type" (P.fmt_ppr_lf_typ_rec cD cPsi Pretty.std_lvl) (Whnf.normTypRec sArec)
    "Actual type"   (P.fmt_ppr_lf_typ_rec cD cPsi Pretty.std_lvl) (Whnf.normTypRec sBrec)

      | TupleArity (cD, cPsi, sM, sA) ->
  Error.report_mismatch ppf
    "Arity of tuple doesn't match type."
    "Tuple" (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl)  (Whnf.norm sM)
    "Type"  (P.fmt_ppr_lf_typ_rec cD cPsi Pretty.std_lvl) (Whnf.normTypRec sA)

      | KindMismatch (cD, cPsi, sS, sK) ->
  Error.report_mismatch ppf
          "Ill-kinded type."
    "Expected kind:" Format.pp_print_string                      (P.kindToString cPsi sK)
    "for spine:"     (P.fmt_ppr_lf_spine cD cPsi Pretty.std_lvl) (Whnf.normSpine sS)

      | TypMismatch (cD, cPsi, sM, sA1, sA2) ->
        Error.report_mismatch ppf
          "Ill-typed term."
    "Expected type" (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA1)
    "Inferred type" (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA2);
        Format.fprintf ppf
          "In expression: %a@."
          (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) (Whnf.norm sM)

      | IllTypedSub (cD, cPsi, s, cPsi') ->
        Format.fprintf ppf "Ill-typed substitution.@.";
        Format.fprintf ppf "    Substitution: %a@."
          (P.fmt_ppr_lf_sub cD cPsi Pretty.std_lvl) s;
        Format.fprintf ppf "    does not take context: %a@."
          (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi';
        Format.fprintf ppf "    to context: %a@."
          (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi;

      | SpineIllTyped (n_expected, n_actual) ->
  Error.report_mismatch ppf
    "Ill-typed spine."
    "Expected number of arguments" Format.pp_print_int n_expected
    "Actual number of arguments"   Format.pp_print_int n_actual

      | LeftoverFV ->
    Format.fprintf ppf "Leftover free variable."
      | IllTypedMetaObj (cD, cM, cPsi, mT) -> 
            Format.fprintf ppf
              "Meta object %a does not have type %a."
              (P.fmt_ppr_lf_mfront cD Pretty.std_lvl) (ClObj (Context.dctxToHat cPsi, cM))
              (P.fmt_ppr_lf_mtyp cD) (ClTyp (mT, cPsi))
      | CtxHatMismatch (cD, cPsi, phat, cM) ->
          let cPhi = Context.hatToDCtx (Whnf.cnorm_psihat phat Whnf.m_id) in
            Error.report_mismatch ppf
              "Type checking encountered ill-typed meta-object. This is a bug in type reconstruction."
              "Expected context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx  cPsi)
              "Given context" (P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl) cPhi;
              Format.fprintf ppf
                "In expression: %a@."
                (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM
      | TermWhenVar (cD, cPsi, tM) ->
  Format.fprintf ppf "A term was found when expecting a variable.@." ;
  Format.fprintf ppf "Offending term: %a @." 
    (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) tM
      | SubWhenRen (cD, cPsi, sub) -> 
  Format.fprintf ppf "A substitution was found when expecting a renaming.@." ;
  Format.fprintf ppf "Offending substitution: %a @." 
    (P.fmt_ppr_lf_sub cD cPsi Pretty.std_lvl) sub
  ))

exception SpineMismatch

let rec convPrefixCtx cPsi cPsi' = match (cPsi, cPsi') with
  | (_ , Empty) ->
      true

  | (Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB))) ->
      Whnf.convTyp (tA, Substitution.LF.id) (tB, Substitution.LF.id) && convPrefixCtx cPsi1 cPsi2

  | _ -> false

(* let rec convSubsetCtx cPsi cPsi' = match cPsi, cPsi' with
  | (_ , Empty) -> true
  | Dec (cPsi1, TypDecl (_, tA)), Dec (cPsi2, TypDecl (_, tB)) -> 
      if Whnf.convTyp (tA, Substitution.LF.id) (tB, Substitution.LF.id) then 
  convSubsetCtx cPsi1 cPsi2 
      else 
  convSubsetCtx cPsi1 cPsi'
*)

(* let rec dot_k s k = if k = 0 then s
else dot_k (Substitution.LF.dot1 s) (k-1) *)

let rec convPrefixTypRec sArec sBrec  = match (sArec, sBrec) with
  | ((SigmaLast (_, lastA), s), (SigmaLast (_, lastB), s')) ->
      Whnf.convTyp (lastA, s) (lastB, s')

  | ((SigmaElem (_xA, tA, recA), s), (SigmaLast (x,tB), s')) ->
      Whnf.convTyp (tA, s) (tB, s') ||
  convPrefixTypRec (recA, Substitution.LF.dot1 s) 
                   (SigmaLast (x,tB), Substitution.LF.comp s' Substitution.LF.shift)

  | ((SigmaElem (_xA, tA, recA), s), ((SigmaElem(xB, tB, recB) as rB), s')) ->
      if Whnf.convTyp (tA, s) (tB, s') 
      then convPrefixTypRec (recA, Substitution.LF.dot1 s) (recB, Substitution.LF.dot1 s') 
      else convPrefixTypRec (recA, Substitution.LF.dot1 s) (rB, Substitution.LF.comp s' Substitution.LF.shift)  

  | ((SigmaLast _ , _ ), _ ) -> false

let prefixSchElem (SchElem(cSome1, typRec1)) (SchElem(cSome2, typRec2)) =
  convPrefixCtx cSome1 cSome2 && 
    convPrefixTypRec (typRec1, Substitution.LF.id) (typRec2, Substitution.LF.id) 


(* ctxToSub' cPhi cPsi = s

   if x1:A1, ... xn:An = cPsi
   then D = u1:A1[cPhi], ... un:An[cPhi]

   s.t. D; cPhi |- u1[id]/x1 ... un[id]/xn : cPsi
*)
let rec ctxToSub' cPhi cPsi = match cPsi with
  | Null -> Ctxsub.ctxShift cPhi (* Substitution.LF.id *)
  | DDec (cPsi', TypDecl (n, tA)) ->
    let s = ((ctxToSub' cPhi cPsi') : sub) in
    let u     = Whnf.etaExpandMV cPhi (tA, s) n Substitution.LF.id Maybe in
    Dot (Obj u, s)

(* check cD cPsi (tM, s1) (tA, s2) = ()
 *
 * Invariant:
 *
 * If   ; cD ; cPsi |- s1 <= cPsi1
 * and  ; cD ; cPsi |- s2 <= cPsi2    cPsi2 |- tA <= type
 * returns ()
 * if there exists an tA' s.t.
 * ; cD ; cPsi1 |- tM      <= tA'
 * and  ; cD ; cPsi  |- tA'[s1]  = tA [s2] : type
 * and  ; cD ; cPsi  |- tM [s1] <= tA'[s1]
 * otherwise exception Error is raised
 *)
(* let rec checkW cD cPsi sM sA = match sM, sA with
  | (Lam (loc, name, tM), s1), (PiTyp ((TypDecl (x, tA), t), tB), s2) -> (* Offset by 1 *)    
    (Synann.LF.Lam (
      loc, 
      name, 
      (check cD
        (DDec (cPsi, Substitution.LF.decSub tX s2))
        (tM, Substitution.LF.dot1 s1)
        (tB, Substitution.LF.dot1 s2)),
        (PiTyp ((TypDecl (x, tA), t), tB), s2)
    ), s1)      

  | (Lam (loc, _, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

  | (LFHole loc, s1), s -> (Synann.LF.LFHole (loc, s), s1)

  | (Tuple (loc, tuple), s1), (Sigma typRec, s2) ->    
    (Synann.LF.Tuple (loc, (checkTuple loc cD cPsi (tuple, s1) (typRec, s2)), (Sigma typRec, s2)), s1)    

  | (Tuple (loc, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

  | (Root (loc, _h, _tS), _s (* id *)), (Atom _, _s') ->    
    (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
    begin
      try
        let _ = dprint (fun () -> "[ROOT check] " ^
          P.mctxToString cD ^ " ; " ^
          P.dctxToString cD cPsi ^ " |- " ^
          P.normalToString cD cPsi sM ^
          " <= " ^ P.typToString cD cPsi sA ) 
        in
        let sP = syn cD cPsi sM 
        in
        let _ = dprint (fun () -> "[ROOT check] synthesized " ^
          P.mctxToString cD ^ " ; " ^
          P.dctxToString cD cPsi ^ " |- " ^
          P.normalToString cD cPsi sM ^
          " => " ^ P.typToString cD cPsi sP ) 
        in  
        let _ = dprint (fun () -> "       against " ^ P.typToString cD cPsi sA) 
        in
        let (tP', tQ') = (Whnf.normTyp sP , Whnf.normTyp sA) in
        (if not (Whnf.convTyp  (tP', Substitution.LF.id) (tQ', Substitution.LF.id)) 
        then raise (Error (loc, TypMismatch (cD, cPsi, sM, sA, sP)));
        Synann.LF.Root (loc, ))
      with SpineMismatch ->
        raise (Error (loc, (CheckError (cD, cPsi, sM, sA))))
    end

  | (Root (loc, _, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA))) *)

let rec checkW cD cPsi sM sA = match sM, sA with
  | (Lam (loc, name, tM), s1), (PiTyp ((TypDecl (_x, _tA) as tX, _), tB), s2) -> (* Offset by 1 *)    
    check cD
      (DDec (cPsi, Substitution.LF.decSub tX s2))
      (tM, Substitution.LF.dot1 s1)
      (tB, Substitution.LF.dot1 s2);
      Typeinfo.LF.add loc (Typeinfo.LF.mk_entry cD cPsi sA) ("Lam" ^ " " ^ Pretty.Int.DefaultPrinter.normalToString cD cPsi sM)

  | (LFHole _, _), _ -> ()
  | (Lam (loc, _, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

  | (Tuple (loc, tuple), s1), (Sigma typRec, s2) ->    
    checkTuple loc cD cPsi (tuple, s1) (typRec, s2);
    Typeinfo.LF.add loc (Typeinfo.LF.mk_entry cD cPsi sA) ("Tuple" ^ " " ^ Pretty.Int.DefaultPrinter.normalToString cD cPsi sM)

  | (Tuple (loc, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

  | (Root (loc, _h, _tS), _s (* id *)), (Atom _, _s') ->    
    (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
    begin
      try
        let _ = dprint (fun () -> "[ROOT check] " ^
    P.mctxToString cD ^ " ; " ^
    P.dctxToString cD cPsi ^ " |- " ^
    P.normalToString cD cPsi sM ^
          " <= " ^ P.typToString cD cPsi sA ) in
        let sP = syn cD cPsi sM in
        let _ = dprint (fun () -> "[ROOT check] synthesized " ^
    P.mctxToString cD ^ " ; " ^
    P.dctxToString cD cPsi ^ " |- " ^
    P.normalToString cD cPsi sM ^
          " => " ^ P.typToString cD cPsi sP ) in
  Typeinfo.LF.add loc (Typeinfo.LF.mk_entry cD cPsi sA) ("Root" ^ " " ^ Pretty.Int.DefaultPrinter.normalToString cD cPsi sM);
  let _ = dprint (fun () -> "       against " ^
    P.typToString cD cPsi sA) in
        let (tP', tQ') = (Whnf.normTyp sP , Whnf.normTyp sA) in
        if not (Whnf.convTyp  (tP', Substitution.LF.id) (tQ', Substitution.LF.id)) then
          raise (Error (loc, TypMismatch (cD, cPsi, sM, sA, sP)))
      with SpineMismatch ->
        raise (Error (loc, (CheckError (cD, cPsi, sM, sA))))
    end

  | (Root (loc, _, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

and check cD cPsi sM sA = checkW cD cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and checkTuple loc cD cPsi (tuple, s1) (trec, s2) =
  let loop (tuple, s1) (typRec, s2) = match tuple, typRec with
    | Last tM,   SigmaLast (n, tA) -> checkW cD cPsi (tM, s1) (tA, s2)
    | Cons (tM, tuple),   SigmaElem (_x, tA, typRec) ->
      checkW cD cPsi (tM, s1) (tA, s2);
      checkTuple loc cD cPsi (tuple, s1) (typRec, Dot (Obj tM, s2))
    | _, _ -> raise (Error (loc, TupleArity (cD, cPsi, (Tuple (loc, tuple), s1), (trec, s2)))) in
  loop (tuple, s1) (trec, s2)


and syn cD cPsi (Root (loc, h, tS), s (* id *)) =
  let rec spineLength = function
    | Nil -> 0
    | SClo (tS, _) -> spineLength tS
    | App (_, tS) -> 1 + spineLength tS in

  let rec typLength = function
    | Atom _ -> 0
    | PiTyp (_, tB2) -> 1 + typLength tB2 in

  let rec syn tS sA = match tS, sA with
    | (Nil, _), sP -> sP

    | (SClo (tS, s'), s), sA ->    
      syn (tS, Substitution.LF.comp s' s) sA

    | (App (tM, tS), s1), (PiTyp ((TypDecl (_, tA1), _), tB2), s2) ->
      check cD cPsi (tM, s1) (tA1, s2);
      let tB2 = Whnf.whnfTyp (tB2, Dot (Obj (Clo (tM, s1)), s2)) in
      syn (tS, s1) tB2 in

  let (sA', s') = Whnf.whnfTyp (inferHead loc cD cPsi h Subst, Substitution.LF.id) in
  (* Check first that we didn't supply too many arguments. *)
  if typLength sA' < spineLength tS 
  then raise (Error (loc, SpineIllTyped (typLength sA', spineLength tS)));  
  syn (tS, s) (sA', s')

(* TODO: move this function somewhere else, and get rid of duplicate in reconstruct.ml  -jd 2009-03-14 *)

(* inferHead loc cD cPsi h = tA
 *
 * Invariant:
 *
 * returns tA if
 * cD ; cPsi |- h => tA
 * where cD ; cPsi |- tA <= type
 * else exception Error is raised.
 *)
and inferHead loc cD cPsi head cl = match head, cl with
  | BVar k', _ ->
    let (_, _l) = dctxToHat cPsi in
    let TypDecl (_, tA) = ctxDec cPsi k' in
    tA

  | Proj (tuple_head, target), _ ->
    let srecA = match tuple_head with
      | BVar k' ->
        let TypDecl (_, Sigma recA) = ctxSigmaDec cPsi k' in
        let _ = dprint (fun () -> "[InferHead] " ^ P.dctxToString cD cPsi) in
        let _ = dprint (fun () -> "|-  " ^  P.headToString cD cPsi head ^ "\n" ^
          " where " ^ P.headToString cD cPsi tuple_head ^
    " has type " ^ P.typRecToString cD cPsi (recA, Substitution.LF.id)) in
        (recA, Substitution.LF.id)
      | PVar (p, s) ->
        let (_, Sigma recA, cPsi') = Whnf.mctxPDec cD p in
        checkSub loc cD cPsi s Subst cPsi';
        (recA, s)
    in
    let (_tA, s) as sA = getType tuple_head srecA target 1 in
    dprint (fun () -> "getType (" ^ P.headToString cD cPsi head ^ ") = " ^ P.typToString cD cPsi sA);
    dprint (fun () -> "s = " ^ P.subToString cD cPsi s);
    TClo sA

  | Const c, Subst ->
    (Term.get c).Term.typ

  | MVar (Offset u, s), Subst ->
    (* cD ; cPsi' |- tA <= type *)
    let (_, tA, cPsi') = Whnf.mctxMDec cD u in
    let _ = dprint (fun () -> "[inferHead] " ^ P.headToString cD cPsi head ) in
    let _ = dprint (fun () -> "[inferHead] " ^ P.dctxToString cD cPsi ^ "   |-   " ^
      P.subToString cD cPsi s ^ " <= " ^ P.dctxToString cD cPsi') in
    checkSub loc cD cPsi s Subst cPsi' ;
    TClo (tA, s)

  | MVar (Inst (_n, {contents = None}, _cD, ClTyp (MTyp tA,cPsi'), _cnstr, _), s), Subst ->
    let _ = dprint (fun () -> "[inferHead] " ^ P.headToString cD cPsi head ) in
    let _ = dprint (fun () -> "[inferHead] " ^ P.dctxToString cD cPsi ^ "   |-   " ^
      P.subToString cD cPsi s ^ " <= " ^ P.dctxToString cD cPsi') in
    checkSub loc cD cPsi s Subst cPsi' ;
    TClo (tA, s)

  | MMVar (((_n, {contents = None}, cD' , ClTyp (MTyp tA,cPsi'), _cnstr, _) , t'), r), Subst ->
    let _ = dprint (fun () -> "[inferHead] MMVar " ^ P.headToString cD cPsi head ) in
    let _ = dprint (fun () -> " cD = " ^ P.mctxToString cD) in
    let _ = dprint (fun () -> " t' = " ^ P.msubToString cD t' ) in
    let _ = dprint (fun () -> " cD' = " ^ P.mctxToString cD') in
    let _ = checkMSub loc cD t' cD' in
    let _ = dprint (fun () -> "[inferHead] MMVar - msub done \n") in
    checkSub loc cD cPsi r Subst (Whnf.cnormDCtx (cPsi', t')) ;
    TClo(Whnf.cnormTyp (tA, t'), r)

  | Const _, Ren
  | MVar _, Ren
  | MMVar _, Ren -> raise (Error (loc, TermWhenVar (cD, cPsi, (Root (loc, head, Nil)))))

  | PVar (p, s), _ ->
    (* cD ; cPsi' |- tA <= type *)
    let (_, tA, cPsi') = Whnf.mctxPDec cD p in
    dprnt "[inferHead] PVar case";
    dprint (fun () -> "[inferHead] PVar case:    s = " ^ P.subToString cD cPsi s);
    dprint (fun () -> "check: cPsi' (context of pvar)    = " ^ P.dctxToString cD cPsi' ^ "\n"
      ^ "check:  cPsi (context in pattern) = " ^ P.dctxToString cD cPsi ^ "\n"
      ^ "check: synthesizing " ^ P.typToString cD cPsi (tA, s) ^ " for PVar" ^ "\n"
      ^ "check: cD = " ^ P.mctxToString cD);
    checkSub loc cD cPsi s cl cPsi';
    (* Check that something of type tA could possibly appear in cPsi *)
(*    if not (canAppear cD cPsi head (tA, s) loc) then
      raise (Error (loc, ParamVarInst (cD, cPsi, (tA, s)))); *)
    (* Return p's type from cD *)
    TClo (tA, s)

  | FVar _, _ ->
    raise (Error (loc, LeftoverFV))


(* and canAppear cD cPsi head sA loc=
  match cPsi with
    | Null -> true (* we need to succeed because coverage should detect that
                      it is not inhabited *)

    | CtxVar ctx_var ->
      begin let (Schema elems) = Schema.get_schema (lookupCtxVarSchema cD ctx_var) in
            try let _ = checkTypeAgainstSchemaProj loc cD (* Null *) cPsi head (TClo sA) (* schema *) elems  in
                true
            with
              | (Match_failure _) as exn -> raise exn
              | _ -> false
      end

    | DDec (rest, TypDecl(_x, _tB)) ->
      canAppear cD rest head sA loc
      ||
        false (* should check if sA = tB; unimplemented.
                 This should only matter when using a parameter variable
                 somewhat gratuitously, as p .. x y when the context variable schema
                 doesn't include elements of type sA, but x or y do have type sA *)
 *)
(* checkSub loc cD cPsi s cPsi' = ()
 *
 * Invariant:
 *
 * succeeds iff cD ; cPsi |- s : cPsi'
 *)
and checkSub loc cD cPsi1 s1 cl cPsi1' =
  let svar_le = function 
    | Ren, Ren 
    | Subst, Subst
    | Ren, Subst -> ()
    | Subst, Ren ->
      raise (Error (loc, SubWhenRen(cD, cPsi1, s1)))
  in
  let rec checkSub loc cD cPsi s cPsi' = match cPsi, s, cPsi' with
    | cPsi, EmptySub, Null -> ()
    | cPsi, Undefs, Null -> ()
    | Null, Shift 0, Null -> ()

    | cPhi, SVar (offset, k, s'), cPsi ->
      (*  cD ; cPhi |- SVar (offset, shift, s') : cPsi
          cD(offset) =  Psi'[Phi'] (i.e. Phi'  |- offset  : Psi')
                          Psi'  |- shift (cs , k) : Psi
                          Phi   |- s'             : Phi'
      *)
      let (_, cPsi', cl', cPhi') = Whnf.mctxSDec cD offset in
      svar_le (cl', cl) ;
      checkSub loc cD cPsi' (Shift k) cPsi;
      checkSub loc cD cPhi  s'            cPhi'

    | CtxVar psi, Shift 0, CtxVar psi' ->
      (* if psi = psi' then *)
      if not (psi = psi') then
(*      if not (subsumes cD psi' psi) then *)
  raise (Error (loc, IllTypedSub (cD, cPsi1, s1, cPsi1')))

    (* SVar case to be added - bp *)

    | DDec (cPsi, _tX),  Shift k,  Null ->
      if k > 0 then
  checkSub loc cD cPsi (Shift (k - 1)) Null
      else
  raise (Error (loc, IllTypedSub (cD, cPsi1, s1, cPsi1')))

    | DDec (cPsi, _tX),  Shift k,  CtxVar psi ->
      if k > 0 then
  checkSub loc cD cPsi (Shift (k - 1)) (CtxVar psi)
      else
  raise (Error (loc, IllTypedSub (cD, cPsi1, s1, cPsi1')))

    | cPsi',  Shift k,  cPsi ->
      if k >= 0 then
  checkSub loc cD cPsi' (Dot (Head (BVar (k + 1)), Shift (k + 1))) cPsi
      else
  raise (Error (loc, IllTypedSub (cD, cPsi1, s1, cPsi1')))

    | cPsi', Dot (Head h, s'), DDec (cPsi, TypDecl (_, tA2))
    (* | cPsi', Dot (Obj (Root(_,h,Nil)), s'), DDec (cPsi, TypDecl (_, tA2)) *) ->
      let _ = checkSub loc cD cPsi' s' cPsi
      (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
      and tA1 = inferHead loc cD cPsi' h cl in
      if not (Whnf.convTyp (tA1, Substitution.LF.id) (tA2, s')) then
  raise (Error (loc, IllTypedSub (cD, cPsi1, s1, cPsi1')))

    | cPsi', Dot (Obj tM, s'), DDec (cPsi, TypDecl (_, tA2)) when cl = Subst ->
      (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
      let _ = checkSub loc cD cPsi' s' cPsi in
      (* ensures that s' is well-typed and [s']tA2 is well-defined *)
      check cD cPsi' (tM, Substitution.LF.id) (tA2, s')

    | _, Dot (Obj tM, _), DDec (_,_) when cl = Ren ->
      raise (Error (loc, TermWhenVar (cD, cPsi, tM)))

    | cPsi1, s, cPsi2 ->
      raise (Error (loc, IllTypedSub (cD, cPsi1, s1, cPsi1')))
  in checkSub loc cD cPsi1 s1 cPsi1'

(*****************)
(* Kind Checking *)
(*****************)

(* kind checking is only applied to type constants declared in
 * the signature;
 *
 * All constants declared in the signature do not contain any
 * contextual variables, hence Delta = .
 *)

(* synKSpine cD cPsi (tS, s1) (K, s2)
 *
 * Invariant:
 *
 * succeeds iff cD ; cPsi |- [s1]tS <= [s2]K
 *)
and synKSpine cD cPsi sS1 sK = match sS1, sK with
  | (Nil, _), sK ->
    sK

  | (SClo (tS, s'), s), sK ->
    synKSpine cD cPsi (tS, Substitution.LF.comp s' s) sK

  | (App (tM, tS), s1), (PiKind ((TypDecl (_, tA1), _), kK), s2) ->
    check cD cPsi (tM, s1) (tA1, s2);
    synKSpine cD cPsi (tS, s1) (kK, Dot (Obj (Clo (tM, s1)), s2))

  | (App _, _), (Typ, _) ->
    raise SpineMismatch

(* checkTyp (cD, cPsi, (tA,s))
 *
 * Invariant:
 *
 * succeeds iff cD ; cPsi |- [s]tA <= type
 *)
and checkTyp' cD cPsi (tA, s) =

  match tA with
    | Atom (loc, a, tS) ->
      let tK = (Typ.get a).Typ.kind in
      begin try
        let (tK', _s) = synKSpine cD cPsi (tS, s) (tK, Substitution.LF.id) in
        if tK' = Typ then
    ()
        else
    raise (Error (loc, (KindMismatch (cD, cPsi, (tS, s), (tK, Substitution.LF.id)))))
        with SpineMismatch ->
          raise (Error (loc, (KindMismatch (cD, cPsi, (tS, s), (tK, Substitution.LF.id)))))
      end

    | PiTyp ((TypDecl (x, tA), _), tB) ->
      checkTyp cD cPsi (tA, s);
      checkTyp cD (DDec (cPsi, TypDecl (x, TClo (tA, s)))) (tB, Substitution.LF.dot1 s)

    | Sigma arec -> checkTypRec cD cPsi (arec, s)

and checkTyp cD cPsi sA = checkTyp' cD cPsi (Whnf.whnfTyp sA)


(* checkTypRec cD cPsi (recA, s)
 *
 * Invariant:
 *
 * succeeds iff cD ; cPsi |- [s]recA <= type
 *)
and checkTypRec cD cPsi (typRec, s) = match typRec with
  | SigmaLast(n, lastA) ->
    checkTyp cD cPsi (lastA, s)

  | SigmaElem(_x, tA, recA) ->
    checkTyp   cD cPsi (tA, s);
    checkTypRec cD
      (DDec (cPsi, Substitution.LF.decSub (TypDecl (Id.mk_name Id.NoName, tA)) s))
      (recA, Substitution.LF.dot1 s)

(* checkKind cD cPsi K
 *
 * Invariant:
 *
 * succeeds iff cD ; cPsi |- K kind
 *)
and checkKind cD cPsi kind = match kind with
  | Typ ->
    ()

  | PiKind ((TypDecl (x, tA), _), kind) ->
    checkTyp cD cPsi (tA, Substitution.LF.id);
    checkKind cD (DDec (cPsi, TypDecl (x, tA))) kind


(* checkDec cD cPsi (x:tA, s)
 *
 * Invariant:
 *
 * succeeds iff ; cD ; cPsi |- [s]tA <= type
 *)
and checkDec cD cPsi (decl, s) = match decl with
  | TypDecl (_, tA) -> checkTyp cD cPsi (tA, s)

(* checkDCtx cD cPsi
 *
 * Invariant:
 *
 * succeeds iff ; cD |- cPsi ctx
 * f   *)
and checkDCtx cD cPsi = match cPsi with
  | Null ->  ()
  | DDec (cPsi, tX)     ->
    checkDCtx cD cPsi;
    checkDec cD cPsi (tX, Substitution.LF.id)

  (*    | CtxVar (CtxOffset psi_offset)  ->
        if psi_offset <= (Context.length cO) then
        ()
        else
        raise (Violation "Context variable out of scope")
  *)
  | CtxVar (CtxOffset k) ->
    (dprint (fun () -> "[chkDCtx] lookup CtxVar where k = " ^ R.render_offset k
      ^ " in \n cD = " ^ P.mctxToString cD ^ "\n");
     let (_,CTyp _)  = Whnf.mctxLookup cD k in ())

(* other cases should be impossible -bp *)


and projectCtxIntoDctx = function
  | Empty -> Null
  | Dec (rest, last) -> DDec (projectCtxIntoDctx rest, last)

(* checkTypeAgainstSchema loc cD cPsi tA sch (elements : sch_elem list)
 *   sch = full schema, for error messages
 *   elements = elements to be tried
 *)
and checkTypeAgainstSchema loc cD cPsi tA elements =
  (* if tA is not a Sigma, "promote" it to a one-element typRec *)
  let _ = dprint (fun () ->
    "checkTypeAgainstSchema "
    ^ P.typToString cD cPsi (tA, Substitution.LF.id)
    ^ "  against  "
    ^ P.schemaToString (Schema elements))
  in
  match elements with
    | [] ->
      raise (Error (loc, CtxVarMisCheck (cD, cPsi, (tA, Substitution.LF.id), Schema elements)))

    | element :: elements ->
      try
        instanceOfSchElem cD cPsi (tA, Substitution.LF.id) element
      with
        | (Match_failure _) as exn -> raise exn
        | _ -> checkTypeAgainstSchema loc cD cPsi tA elements

and instanceOfSchElem cD cPsi (tA, s) (SchElem (some_part, block_part)) =
  let _ = dprint (fun () -> "instanceOfSchElem...") in
  let sArec = match Whnf.whnfTyp (tA, s) with
    | (Sigma tArec,s') -> (tArec, s')
    | (nonsigma, s') -> (SigmaLast (None, nonsigma), s') in
  let _ = dprint (fun () -> "tA =" ^ P.typToString cD cPsi (tA, s)) in
  let dctx        = projectCtxIntoDctx some_part in
  let _ =  dprint (fun () -> "***Check if it is an instance of a schema element ...") in
  let _ =  dprint (fun () -> "*** "
    ^ "\n   cPsi = " ^ P.dctxToString cD cPsi
    ^ "\n   dctx = " ^ P.dctxToString cD dctx ) in

  let _ =  dprint (fun () -> "***Check if it is an instance of a schema element ...") in
  let dctxSub     = ctxToSub' cPsi dctx in
  let _ = dprint (fun () -> "dctxSub = " ) in
  let _ = dprint (fun () ->  P.subToString cD cPsi dctxSub) in
  (* let phat        = dctxToHat cPsi in *)
  let _ =  dprint (fun () -> "***Unify.unifyTypRec ("
    ^ "\n   cPsi = " ^ P.dctxToString cD cPsi
    ^ "\n   dctx = " ^ P.dctxToString cD dctx
    ^ "\n   " ^  P.typToString cD cPsi (tA, s) ) in

  (* P.typRecToString cD cPsi sArec  *)
  (*    let _ = dprint (fun () ->
        "\n== " ^ P.typRecToString cD cPsi (block_part, dctxSub) ) in  *)
  let _ = dprint (fun () ->  "== " ) in
  let _ = dprint (fun () -> P.typRecToString cD cPsi (block_part, dctxSub) ) in
  begin
    try
      Unify.unifyTypRec cD cPsi sArec (block_part, dctxSub);
      dprint (fun () -> "instanceOfSchElem\n"
        ^ "  block_part = " ^ P.typRecToString cD cPsi (block_part, dctxSub) ^ "\n"
        ^ "  succeeded.");
      (block_part, dctxSub)
    with (Unify.Failure _) as exn ->
      dprint (fun () -> "Type  "
        ^ P.typRecToString cD cPsi sArec ^ "  doesn't unify with  "
        ^ P.typRecToString cD cPsi (block_part, dctxSub));
      raise exn
  end


(* checkTypeAgainstSchemaProj loc cD cPsi head tA sch (elements : sch_elem list)
 *   sch = full schema, for error messages
 *   elements = elements to be tried
 *)
(* and checkTypeAgainstSchemaProj loc cD cPsi head tA elements =
  (* if tA is not a Sigma, "promote" it to a one-element typRec *)
  let _ = dprint (fun () ->
    "checkTypeAgainstSchema "
    ^ P.typToString cD cPsi (tA, Substitution.LF.id)
    ^ "  against  "
    ^ P.schemaToString (Schema elements))
  in
  match elements with
    | [] ->
      raise (Error (loc, CtxVarMisCheck (cD, cPsi, (tA, Substitution.LF.id), Schema elements)))

    | element :: elements ->
      try
        let (SchElem (_cPhi, trec)) = element in
        existsInstOfSchElemProj loc cD cPsi (tA, Substitution.LF.id) (head, 1, blockLength trec) element
      with
        | (Match_failure _) as exn -> raise exn
        | _ -> checkTypeAgainstSchema loc cD cPsi tA elements
 *)
(* and existsInstOfSchElemProj loc cD cPsi sA (h,i, n) elem = if i > n then
  raise (Error (loc, ParamVarInst (cD, cPsi, sA)))
else
  begin try
    instanceOfSchElemProj cD cPsi sA (h, i) elem
  with _ ->
    existsInstOfSchElemProj loc cD cPsi sA (h, i+1, n) elem
  end
 *)

and instanceOfSchElemProj cD cPsi (tA, s) (var, k) (SchElem (cPhi, trec)) =
  let tA_k (* : tclo *) = getType var (trec, Substitution.LF.id) k 1 in
  let _ = dprint (fun () -> "instanceOfSchElemProj...") in
  let (_tA'_k, subst) =
  instanceOfSchElem cD cPsi (tA, s) (SchElem (cPhi, SigmaLast (None, TClo tA_k)))
  (* tA'_k = [subst] (tA_k) = [s]tA *)
  in
  (trec, subst)


(* The rule for checking a context against a schema is
 *
 *  psi::W \in \Omega
 *  -----------------
 *   ... |- psi <= W
 *
 * so checking a context element against a context element is just equality.
 *)

and checkElementAgainstElement _cD elem1 elem2 =
  let result =
    (*         Whnf.convSchElem elem1 elem2 (* (cSome1 = cSome2) && (block1 = block2)  *) in *)
    prefixSchElem elem2 elem1 (* (cSome1 = cSome2) && (block1 = block2)  *) in
    dprint (fun () -> "checkElementAgainstElement "
    ^ P.schemaToString (Schema[elem1])
    ^ " <== "
    ^ P.schemaToString (Schema[elem2])
    ^ ":  "
    ^ string_of_bool result);
  result

(* checkElementAgainstSchema cD sch_elem (elements : sch_elem list) *)
and checkElementAgainstSchema cD sch_elem elements =
  List.exists (checkElementAgainstElement cD sch_elem) elements

(*  and subset f list =
    begin match list with [] -> true
    | elem::elems -> f elem
*)

and checkSchema loc cD cPsi (Schema elements as schema) =
  dprint (fun () -> "checkSchema "
    ^ P.dctxToString cD cPsi ^ " against " ^ P.schemaToString schema);
  match cPsi with
    | Null -> ()
    | CtxVar (CInst ((_, {contents = Some (ICtx cPhi)}, _, _, _, _), _ )) ->
      checkSchema loc cD cPhi schema
    | CtxVar ((CtxOffset _ ) as phi) ->
      let Schema phiSchemaElements =
  Schema.get_schema (lookupCtxVarSchema cD phi) in
      (*            if not (List.forall (fun phiElem -> checkElementAgainstSchema cD phiElem elements) phiSchemaElements) then *)
      (*            if not (List.for_all (fun elem -> checkElementAgainstSchema cD elem phiSchemaElements) elements ) then *)
      if List.exists (fun elem -> checkElementAgainstSchema cD elem phiSchemaElements) elements then ()
      else
        raise (Error (loc, CtxVarMismatch (cD, phi, schema)))

    | DDec (cPsi', decl) ->
      begin
        checkSchema loc cD cPsi' schema
        ; match decl with
          | TypDecl (_x, tA) ->
            let _ = checkTypeAgainstSchema loc cD cPsi' tA elements in ()
      end

 (* If subsumes psi phi succeeds then there exists  wk_sub
    such that  psi |-  wk_sub : phi
    and in addition (more importantly), there exists a str_sub
    phi |- str_sub : psi
    *)
 and subsumes cD psi phi = match psi, phi with
  | CtxOffset psi_var , CtxOffset phi_var ->
      let Schema psi_selem = Schema.get_schema (lookupCtxVarSchema cD psi) in
      let Schema phi_selem = Schema.get_schema (lookupCtxVarSchema cD phi) in
        List.for_all (fun elem -> checkElementAgainstSchema Empty elem  phi_selem) psi_selem
  | _, _ -> false

(*
 and checkElemIrrelevant (SchElem (cPsi1, tArec1)) (SchElem (cPsi2, tArec2)) =
  begin match elemPostfix (tArec1, id) (tArec2, id) with
    | None -> true
    | Some (tArec, s) -> (* tArec1, tArec = tArec2 *)
        checkTypRecIrr (tArec, s) (tArec1, id)
  end
*)
(* tArec~> cPsi then for all tP in tArec1,   thin (tP, cPsi)

tArec1 ~> list of type families forms "basis"
for each tA in tArec, check that  Subord.relevant  tA basis = []


 and checkTypRecIrr (SigmaLast tA, s)

*)

(*  and elemPostfix sArec sBrec = match (sArec, sBrec) with
   | ((SigmaLast(_, lastA), s), (SigmaLast(_, lastB), s')) ->
       None

   | ((SigmaElem (_xA, tA, recA), s), (SigmaLast(_, tB), s')) ->
       Some (recA,s)

   | ((SigmaElem (_xA, _tA, recA), s), (SigmaElem(_xB, _tB, recB), s')) ->
       elemPostfix (recA, Substitution.LF.dot1 s) (recB, Substitution.LF.dot1 s')
 *)


and checkSchemaWf (Schema elements ) =
    let rec checkElems elements = match elements with
      | [] -> ()
      | SchElem (cPsi, trec) :: els ->
          checkTypRec Empty (projectCtxIntoDctx cPsi) (trec, Substitution.LF.id)
          ; checkElems els
    in
      checkElems elements

and checkClObj cD loc cPsi' cM cTt = match (cM, cTt) with
  | MObj tM, (MTyp tA, t) ->
     check cD cPsi' (tM, Substitution.LF.id) (Whnf.cnormTyp (tA, t), Substitution.LF.id)

  | SObj tM, (STyp (cl, tA), t) ->
     checkSub loc cD cPsi' tM cl (Whnf.cnormDCtx (tA, t))
  | PObj h, (PTyp tA, t)
  | MObj (Root(_,h,Nil)), (PTyp tA, t) (* This is ugly *) -> 
      let tA' = inferHead loc cD cPsi' h Ren in
      let tA  = Whnf.cnormTyp (tA, t) in
      dprint (fun () -> "Checking parameter object against: " ^ (P.typToString cD cPsi' (tA,Substitution.LF.id)));
        if Whnf.convTyp (tA, Substitution.LF.id) (tA', Substitution.LF.id) then ()
  else failwith "Parameter object fails to check" (* TODO: Better error message *)

  | _ , _ -> raise (Error (loc, (IllTypedMetaObj (cD, cM, cPsi', Whnf.cnormClTyp cTt))))

and checkMetaObj cD (loc,cM) cTt = match  (cM, cTt) with
  | (CObj cPsi, (CTyp (Some w), _)) ->
      checkSchema loc cD cPsi (Schema.get_schema w)      

  | (ClObj(phat, tM), (ClTyp (tp, cPsi), t)) ->
      let cPsi' = Whnf.cnormDCtx (cPsi, t) in
      if phat = Context.dctxToHat cPsi' then
        checkClObj cD loc cPsi' tM (tp, t)
      else
        raise (Error (loc, CtxHatMismatch (cD, cPsi', phat, (loc,cM))))
  | MV u , (mtyp1 , t) -> 
      let mtyp1 = Whnf.cnormMTyp (mtyp1, t) in
    let (_, mtyp2) = Whnf.mctxLookup cD u in
    if Whnf.convMTyp mtyp1 mtyp2 
    then ()
    else raise (Error.Violation ("Contextual substitution ill-typed"))
;


  (* checkMSub loc cD ms cD'  = ()

     if cD |- ms <= cD' then checkMSub succeeds.

  *)
and checkMSub loc cD  ms cD'  = match ms, cD' with
    | MShift k, Empty ->
        if (Context.length cD) = k then ()
        else
          raise (Error.Violation ("Contextual substitution ill-typed - 1"))

    | MShift k, cD' ->
  if k >= 0 then
    checkMSub loc cD (MDot (MV (k+1), MShift (k+1))) cD'
  else raise (Error.Violation ("Contextual substitution ill-formed"))
    | MDot (mft, ms) , Dec (cD1, Decl(_, mtyp, _)) ->
      checkMetaObj cD (loc, mft) (mtyp, ms);
      checkMSub loc cD ms cD1

    | _ , _ ->
        raise (Error.Violation ("Contextual substitution ill-typed\n " ^
                            P.mctxToString cD ^ " |- " ^
                            P.msubToString cD ms ^ " <= "
                         ^ " = " ^ P.mctxToString cD'))

end

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

  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type error =
    | IllegalParamTyp of I.mctx * I.dctx * I.typ
    | MismatchChk     of I.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of I.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of I.mctx * gctx * pattern * tclo * tclo
    | CtxFunMismatch  of I.mctx * gctx  * tclo
    | FunMismatch     of I.mctx * gctx  * tclo
    | MLamMismatch    of I.mctx * gctx  * tclo
    | PairMismatch    of I.mctx * gctx  * tclo
    | BoxMismatch     of I.mctx * gctx  * tclo
    | SBoxMismatch    of I.mctx * gctx  * I.dctx  * I.dctx
    | SynMismatch     of I.mctx * tclo (* expected *) * tclo (* inferred *)
    | BoxCtxMismatch  of I.mctx * I.dctx * (I.psi_hat * I.normal)
    | PattMismatch    of (I.mctx * meta_obj * meta_typ) * 
                   (I.mctx * meta_typ)
(*    | PattMismatch    of (I.mctx * I.dctx * I.normal option * I.tclo) *
                         (I.mctx * I.dctx * I.tclo) *)
    | IfMismatch      of I.mctx * gctx  * tclo
    | EqMismatch      of I.mctx * tclo (* arg1 *) * tclo (* arg2 *)
    | EqTyp           of I.mctx * tclo
    | MAppMismatch    of I.mctx * (meta_typ * I.msub)
    | AppMismatch     of I.mctx * (meta_typ * I.msub)
    | CtxMismatch     of I.mctx * I.dctx (* expected *) * I.dctx (* found *) * meta_obj
    | TypMismatch     of I.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name * string
    | InvalidRecCall
    | MissingTotal of Id.cid_prog
    (* | IllTypedMetaObj of I.mctx * meta_obj * meta_typ  *)

(*  type rec_call = bool *)

  exception Error of Syntax.Loc.t * error

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT
(*  let matchMetaV mC = match mC with 
    | MetaCtx (_, I.CtxVar _ ) -> true
    | MetaObj (_, phat, I.Root (_ , I.MVar (_ , s), _ )) -> 
  s = S.Shift 0 || (s = S.EmptySub && phat = (None, 0))
    | MetaObjAnn (_, cPsi, I.Root (_ , I.MVar (_ , s), _ )) -> 
  s = S.Shift 0 || (s = S.EmptySub && cPsi = I.Null)
    | MetaParam (_, phat, I.Root (_ , I.PVar (_ , s ), _ )) -> 
  s = S.Shift 0 || (s = S.EmptySub && phat = (None, 0))
    | MetaSubObj (_, phat, I.SVar (_, 0, s)) -> 
  s = S.Shift 0 || (s = S.EmptySub && phat = (None, 0))
    | MetaSubObjAnn (_, cPsi, I.SVar (_, 0, s)) -> 
  s = S.Shift 0 || (s = S.EmptySub && cPsi = I.Null)
    | _ -> false
*)
  let string_of_typeVariant = function
    | VariantCross -> "product type"
    | VariantArrow -> "function type"
    | VariantCtxPi -> "context abstraction"
    | VariantPiBox -> "dependent function type"
    | VariantBox   -> "contextual type"

  let _ = Error.register_printer
    (fun (Error (loc, err)) ->
      Error.print_with_location loc (fun ppf ->
        match err with
          | MissingTotal prog ->
            Format.fprintf ppf "Function %s not known to be total."
              (R.render_cid_prog prog)
          | InvalidRecCall ->
            Format.fprintf ppf "Recursive call not structurally smaller."
          | IllegalParamTyp (cD, cPsi, tA) ->
            Format.fprintf ppf
              "Parameter type %a is illegal."
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp (tA, Substitution.LF.id))
          | UnsolvableConstraints (f,cnstrs) ->
            Format.fprintf ppf
            "Unification in type reconstruction encountered constraints because the given signature contains unification problems which fall outside the decideable pattern fragment.\n\nCommon causes are:\n\n- there are meta-variables which are not only applied to a distinct set of bound variables \n- a meta-variable in the program depends on a context, but it must be in fact closed \n\nThe constraint \n \n %s \n\n was not solvable. \n \n The program  %s is considered ill-typed. "
              cnstrs (R.render_name f)

          | CtxMismatch (cD, cPsi, cPhi, cM) ->
            Error.report_mismatch ppf
              "Type checking Ill-typed meta-object. This is a bug in type reconstruction."
              "Expected context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx  cPsi)
              "Given context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPhi);
              Format.fprintf ppf
                "In expression: %a@."
                (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM

          | MismatchChk (cD, cG, e, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
            Error.report_mismatch ppf
              "Ill-typed expression."
              "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau');
            Format.fprintf ppf
              "In expression: %a@."
              (P.fmt_ppr_cmp_exp_chk cD cG Pretty.std_lvl) e

          | MismatchSyn (cD, cG, i, variant, theta_tau) ->
            Error.report_mismatch ppf
              "Ill-typed expression."
              "Expected" Format.pp_print_string (string_of_typeVariant variant)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau);
            Format.fprintf ppf
              "In expression: %a@."
              (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i

          | PatIllTyped (cD, cG, pat, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau');
            Format.fprintf ppf
              "In pattern: %a@."
              (P.fmt_ppr_pat_obj cD cG Pretty.std_lvl) pat

          | PattMismatch ((cD, _cM, mT) , (cD', mT')) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type"
              (P.fmt_ppr_cmp_typ cD' Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, mT'))
              "Inferred type"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, mT))

(*          | PattMismatch ((cD, cPsi, pattern, sA) , (cD', cPsi', sA')) ->
            Error.report_mismatch ppf
              "Ill-typed pattern."
              "Expected type"
              (P.fmt_ppr_cmp_typ cD' Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, MetaTyp (Whnf.normTyp sA', Whnf.normDCtx cPsi')))
              "Inferred type"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
              (TypBox (Syntax.Loc.ghost, MetaTyp (Whnf.normTyp sA, Whnf.normDCtx cPsi)))
*)
          | BoxCtxMismatch (cD, cPsi, (phat, tM)) ->
            Format.fprintf ppf
              "Expected: %a\n  in context %a\n  Used in context %a"
              (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) tM
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl) (Context.hatToDCtx phat)

          | CtxFunMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found context abstraction, but expected type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | FunMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found function abstraction, but expected type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | MLamMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found MLam abstraction, but expected type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | BoxMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found box-expression that does not have type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | SBoxMismatch (cD, _cG, cPsi, cPhi) ->
            Format.fprintf ppf
              "Found substitution that does not have type %a[%a]."
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPhi)

          | IfMismatch (cD, _cG, theta_tau) ->
            Error.report_mismatch ppf
              "Type error in guard of if expression."
        "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) TypBool
        "Actual type"   (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | PairMismatch (cD, _cG, theta_tau) ->
            Format.fprintf ppf "Found tuple, but expected type %a"
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

          | SynMismatch (cD, theta_tau, theta_tau') ->
            Error.report_mismatch ppf
              "Ill-typed expression."
              "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
              "Inferred type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau')

          | EqMismatch (cD, ttau1, ttau2) ->
            Error.report_mismatch ppf
              "Type mismatch on equality."
              "Type of LHS" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau1)
              "Type of RHS" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau2)

          | EqTyp (cD, ttau) ->
            Error.report_mismatch ppf
              "Equality comparison only possible at base types."
              "Expected type" Format.pp_print_string                "base type"
              "Actual type"   (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp ttau)

          | AppMismatch (cD, (ctyp, theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, ctyp), theta))

          | MAppMismatch (cD, (ctyp, theta)) ->
            Format.fprintf ppf
              "Expected contextual object of type %a."
              (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, ctyp), theta))
          (* | Typmismatch (cD, (tau1, theta1), (tau2, theta2)) -> *)
          (*     Error.report_mismatch ppf *)
          (*       "Type of destructor did not match the type it was expected to have." *)
          (*       "Type of destructor" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) *)
          (*       (Whnf.cnormCTyp (tau1, theta1)) *)
          (*       "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) *)
          (*       (Whnf.cnormCTyp (tau2, theta2))) *)
      ))

  type caseType =
    | IndexObj of meta_obj
    | DataObj
    | IndDataObj
    | IndIndexObj of meta_obj

  let is_inductive case_typ = match case_typ with
    | IndDataObj -> true 
    | IndIndexObj mC -> true
    | _ -> false

  let is_indMObj cD x = match Whnf.mctxLookupDep cD x with
    | (_, _ , I.Inductive) -> true
    | (_, _ , _) -> false



let mark_ind cD k = 
  let rec lookup cD k' =  match cD, k' with
    | I.Dec (cD, I.Decl (u, cdec,dep)), 1 -> 
   I.Dec (cD, I.Decl (u, cdec, I.Inductive))
     | I.Dec (_cD, I.DeclOpt u), 1 -> 
   raise (Error.Violation "Expected declaration to have type")
    | I.Dec (cD, dec), k' -> I.Dec (lookup cD (k' - 1), dec)
    | I.Empty , _  -> raise (Error.Violation ("Meta-variable out of bounds -- looking for " ^ string_of_int k ^ "in context"))
 in
    lookup cD k


  let rec fmv_normal (cD:I.mctx) tM = match tM with 
    | I.Root (_, h, tS) -> fmv_spine (fmv_head cD h) tS
    | I.Lam (_, _ , tM) -> fmv_normal cD tM
    | I.LFHole _ -> cD
    | I.Tuple (_, tuple) -> fmv_tuple cD tuple 

  and fmv_head (cD:I.mctx) h = match h with
    | I.MVar (I.Offset k, s) | I.PVar (k, s) -> 
  fmv_subst  (mark_ind cD k) s
    | I.Proj (h, _ ) -> fmv_head cD h
    | _ -> cD

  and fmv_tuple (cD:I.mctx) tuple = match tuple with
    | I.Last tM -> fmv_normal cD tM
    | I.Cons (tM, tuple) -> fmv_tuple (fmv_normal cD tM) tuple

  and fmv_spine (cD:I.mctx) tS = match tS with 
    | I.Nil -> cD
    | I.App (tM, tS) -> fmv_spine (fmv_normal cD tM) tS

  and fmv_hat (cD:I.mctx) phat = match phat with 
    | (Some (I.CtxOffset k), _ ) -> mark_ind cD k
    | _ -> I.Empty

  and fmv_dctx (cD:I.mctx) cPsi = match cPsi with 
    | I.Null -> cD
    | I.CtxVar (I.CtxOffset k) -> mark_ind cD k 
    | I.DDec (cPsi, decl) -> fmv_decl (fmv_dctx cD cPsi) decl

  and fmv_decl (cD:I.mctx) decl = match decl with 
    | I.TypDecl (_, tA) -> fmv_typ cD tA
    | _ -> cD

  and fmv_typ (cD:I.mctx) tA = match tA with 
    | I.Atom (_, _, tS) -> fmv_spine cD tS
    | I.PiTyp ((decl, _ ) , tA) -> fmv_typ (fmv_decl cD decl) tA
    | I.Sigma trec -> fmv_trec cD trec

  and fmv_trec (cD:I.mctx) trec = match trec with 
    | I.SigmaLast (_, tA) -> fmv_typ cD tA
    | I.SigmaElem (_, tA, trec) -> fmv_trec (fmv_typ cD tA) trec

  and fmv_subst (cD:I.mctx) s = match s with 
    | I.Dot (f, s) -> fmv_subst (fmv_front cD f) s
    | I.SVar (k, _, s) -> fmv_subst (mark_ind cD k) s
    | _ -> cD
  
  and fmv_front (cD:I.mctx) f = match f with 
    | I.Head h -> fmv_head cD h
    | I.Obj tM -> fmv_normal cD tM
    | I.Undef -> cD

  let fmv_mobj cD cM = match cM with 
    | _ , I.CObj (cPsi) -> fmv_dctx cD cPsi
    | _, I.ClObj (phat, I.MObj tM) -> fmv_normal cD tM
    | _, I.ClObj (phat, I.PObj h) -> fmv_head (fmv_hat cD phat) h
    | _, I.ClObj (phat, I.SObj s) ->  fmv_subst (fmv_hat cD phat) s

  let rec fmv cD pat = match pat with
    | PatConst (_ , _ , pat_spine) -> fmv_pat_spine cD pat_spine 
    | PatVar (_ , _ ) | PatTrue _ | PatFalse _ -> cD
    | PatPair (_, pat1, pat2) ->  fmv (fmv cD pat1) pat2
    | PatMetaObj (_, cM) -> fmv_mobj cD cM
    | PatAnn (_, pat, _) -> fmv cD pat

  and fmv_pat_spine cD pat_spine = match pat_spine with 
    | PatNil -> cD
    | PatApp (_, pat, pat_spine) -> 
  fmv_pat_spine  (fmv cD pat) pat_spine
        
  let mvarsInPatt cD pat = 
    fmv cD pat 

  let rec id_map_ind cD1' t cD = match t, cD with
    | I.MShift k, I.Empty -> cD1'
    | I.MShift k, cD ->
  if k >= 0 then
    id_map_ind cD1' (I.MDot (I.MV (k+1), I.MShift (k+1))) cD
  else raise (Error.Violation ("Contextual substitution ill-formed"))

    | I.MDot (I.MV u, ms), I.Dec(cD, I.Decl (_u, mtyp1, dep)) ->
  if Total.is_inductive dep then 
    let cD1' = mark_ind cD1' u in 
      id_map_ind cD1' ms cD
  else 
    id_map_ind cD1' ms cD

    | I.MDot (mf, ms), I.Dec(cD, I.Decl (_u, mtyp1, dep)) ->
  (match mf with 
     | I.ClObj (_, I.MObj(I.Root (_, I.MVar (I.Offset u, I.Shift 0), I.Nil)))
     | I.ClObj (_, I.MObj(I.Root (_, I.PVar (u, I.Shift 0), I.Nil)))
     | I.ClObj (_, I.PObj(I.PVar (u, I.Shift 0)))
     | I.CObj(I.CtxVar (I.CtxOffset u))
     | I.ClObj (_ , I.SObj (I.SVar (u, 0, I.Shift 0))) ->
         if Total.is_inductive dep then 
     let cD1' = mark_ind cD1' u in 
       id_map_ind cD1' ms cD
         else 
     id_map_ind cD1' ms cD
     | _ -> id_map_ind cD1' ms cD)




(*  let ind_to_string case_typ = match case_typ with
    | IndDataObj -> "IndDataObj"
    | IndIndexObj (_ , _ ) -> "IndIndexObj"
    | _ -> "NON-INDUCTIVE"
*)

(*  let is_ind _cD _x  = true 
 match x with
    | I.Offset x, sigma -> 
  let (_, tA, cPsi', dp) = Whnf.mctxMDec cD u in
        let d = match dep with
         | I.Inductive -> true
         | _ -> false in 
         is_id sigma && dep 




*)

  let getLoc (loc,cM) = loc


  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

let rec checkParamTypeValid cD cPsi tA =
  let rec checkParamTypeValid' (cPsi0,n) = match cPsi0 with
  | Syntax.Int.LF.Null -> () (* raise (Error (Syntax.Loc.ghost, IllegalParamTyp  (cD, cPsi, tA))) *)
  | Syntax.Int.LF.CtxVar psi ->
     (* tA is an instance of a schema block *)
      let Syntax.Int.LF.Schema s_elems =
  Schema.get_schema (Context.lookupCtxVarSchema cD psi) in
      begin try
        let _ = LF.checkTypeAgainstSchema (Syntax.Loc.ghost) cD cPsi tA s_elems in ()
        with _ -> raise (Error (Syntax.Loc.ghost, IllegalParamTyp  (cD, cPsi, tA)))
      end

  | Syntax.Int.LF.DDec (cPsi0', Syntax.Int.LF.TypDecl (x, tB)) ->
     (* tA is instance of tB *)
    let tB' = Syntax.Int.LF.TClo(tB, Syntax.Int.LF.Shift n) in
    let ms  = Ctxsub.mctxToMSub cD in
    let tB0 = Whnf.cnormTyp (tB', ms) in
    begin try Unify.unifyTyp cD cPsi (tA, Substitution.LF.id) (tB0, Substitution.LF.id) with
      | _ ->  checkParamTypeValid' (cPsi0', n+1)
    end
  in
  checkParamTypeValid' (cPsi , 1)

and checkMetaSpine loc cD mS cKt  = match (mS, cKt) with
  | (MetaNil , (Ctype _ , _ )) -> ()
  | (MetaApp (mO, mS), (PiKind (_, I.Decl (_u, ctyp,_), cK) , t)) ->
    let loc = getLoc mO in
    LF.checkMetaObj cD mO (ctyp, t);
    checkMetaSpine loc cD mS (cK, I.MDot (metaObjToMFront mO, t))
  
  let checkClTyp cD cPsi = function
    | I.MTyp tA ->
        LF.checkTyp  cD cPsi (tA, S.LF.id)
    | I.PTyp tA ->
        LF.checkTyp  cD cPsi (tA, S.LF.id);
        checkParamTypeValid cD cPsi tA
    | I.STyp (_, cPhi) ->
      LF.checkDCtx cD cPhi
  let checkCLFTyp cD ctyp = match ctyp with
    | I.CTyp (Some schema_cid) ->
        begin try
          let _ = Schema.get_schema schema_cid in ()
        with _ -> raise (Error.Violation "Schema undefined")
        end
    | I.CTyp None -> ()
    | I.ClTyp (tp, cPsi) ->
        LF.checkDCtx cD cPsi;
        checkClTyp cD cPsi tp

  let checkCDecl cD cdecl = match cdecl with
    | I.Decl (_, ctyp, _) -> checkCLFTyp cD ctyp

  let rec checkKind cD cK = match cK with
    | Ctype _ -> ()
    | PiKind (_, cdecl, cK) ->
        checkCDecl cD cdecl;
        checkKind (I.Dec(cD, cdecl)) cK

  let rec checkTyp cD tau =  match tau with
    | TypBase (loc, c, mS) ->
        let cK = (CompTyp.get c).CompTyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypCobase (loc, c, mS) ->
        let cK = (CompCotyp.get c).CompCotyp.kind in
          checkMetaSpine loc cD mS (cK , C.m_id)

    | TypBox (_ , ctyp) -> checkCLFTyp cD ctyp

    | TypArr (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2

    | TypCross (tau1, tau2) ->
        checkTyp cD tau1;
        checkTyp cD tau2

    | TypPiBox (cdecl, tau') ->
        dprint (fun () -> "[checkCompTyp] " ^
                  P.mctxToString cD ^ " |- " ^
                  P.compTypToString cD tau);
        checkCDecl cD cdecl;
        dprint (fun () -> "[checkCompTyp] " ^
                  P.mctxToString (I.Dec (cD, cdecl)) ^ " |- " ^
                  P.compTypToString (I.Dec (cD, cdecl)) tau');
        checkTyp (I.Dec (cD, cdecl)) tau'

    | TypBool -> ()
    | TypInd tau -> checkTyp cD tau
;;


(* extend_mctx cD (x, cdecl, t) = cD' 

   if cD mctx 
      cD' |- cU   where cdecl = _ : cU
      cD  |- t : cD
   the 
      cD, x:[t]U  mctx

 *)
let extend_mctx cD (x, cdecl, t) = match cdecl with
  | I.Decl (_u, cU, dep) ->
      I.Dec (cD, I.Decl (x, C.cnormMTyp (cU, t), dep))

let rec extract_var i = match i with 
  | Var (_, x) -> Some x
  | Apply (_, i, _ ) -> extract_var i
  | MApp (_, i, _ ) -> extract_var i
  | _ -> None

let useIH loc cD cG cIH_opt e2 = match cIH_opt with
  | None -> None
  | Some cIH ->
  (* We are making a recursive call *)
    let cIH = match cIH with
      | I.Empty -> raise (Error (loc, InvalidRecCall))
      | cIH  -> match e2 with
          | Box (_,cM) -> 
        ( dprint (fun () -> "\nCheck whether compatible IH exists\n");
    dprint (fun () -> "cIH " ^ Total.ih_to_string cD cG cIH ^ "\n");
    dprint (fun () -> "Recursive call on " ^ P.metaObjToString cD cM ^ "\n");
        Total.filter cD cG cIH (loc, M cM))
    | Syn(_, i) -> (match extract_var i with 
          | Some x -> Total.filter cD cG cIH (loc, V x)
          | None ->  Total.filter cD cG cIH (loc, E))
          (* | _      -> raise (Error (loc, InvalidRecCall)) *)
    in
    let _ = dprint (fun () -> "[useIH] Partially used IH: " ^ Total.ih_to_string cD cG cIH) in
  (* We have now partially checked for the recursive call *)
    match cIH with
      | I.Dec(_ , WfRec (_, [], _ )) ->
      (* We have fully used a recursive call and we now are finished checking for well-formedness
         of rec. call. *)
        None
      | I.Empty -> raise (Error (loc, InvalidRecCall))
      | _ -> Some cIH

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

  let rec checkW cD ((cG , cIH) : ctyp_decl I.ctx * ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (loc, f, e), (tau, t)) ->        
        Synann.Comp.Rec(
          loc,
          f,
          (check cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t))), (Total.shift cIH)) e ttau),
          (tau, t)
        )        

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->        
        Synann.Comp.Fun(
          loc,
          x,
          (check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t))), (Total.shift cIH)) e (tau2, t)),
          (TypArr (tau1, tau2), t)
        )        

    | (Cofun (loc, bs), (TypCobase (l, cid, sp), t)) ->       
         let f = fun (CopatApp (loc, dest, csp), e') ->
           let (ttau', csp') = synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau
           in
           (Synann.Comp.CopatApp (loc, dest, csp'), (check cD (cG,cIH) e' ttau'))
         in 
         Synann.Comp.Cofun(loc, List.map f bs, (TypCobase (l, cid, sp), t))

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->
        Synann.Comp.MLam(
          loc,
          u,
          (check (extend_mctx cD (u, cdec, t)) (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))   e (tau, C.mvar_dot1 t)),
          (TypPiBox (cdec, tau), t)
        )
  
    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->
        Synann.Comp.Pair(
          loc,
          (check cD (cG,cIH) e1 (tau1, t)),          
          (check cD (cG,cIH) e2 (tau2, t)),
          (TypCross (tau1, tau2), t)
        )

    | (Let (loc, i, (x, e)), (tau, t)) ->
        let (_ , tau', t', i_ann) = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
          Synann.Comp.Let(
            loc,
            i_ann,
            (x, (check cD (cG', Total.shift cIH) e (tau,t))),
            (tau, t)
          )

    | (LetPair (loc, i, (x, y, e)), (tau, t)) ->
        let (_ , tau', t', i_ann) = syn cD (cG,cIH) i in
        let (tau', t') =  C.cwhnfCTyp (tau',t') in
        begin match (tau',t') with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                Synann.Comp.LetPair(
                  loc,
                  i_ann,
                  (x, y, (check cD (cG', (Total.shift (Total.shift cIH))) e (tau,t))),
                  (tau, t)
                )                
          | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
        end

    | (Box (loc, cM), (TypBox (l, mT), t)) -> (* Offset by 1 *)       
        begin try
           Synann.Comp.Box(
              loc,
              (* (LF.checkMetaObj cD cM (mT, t)), *) cM,
              (TypBox (l, mT), t)
           )                      
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Error.Violation ("Free meta-variable " ^ (R.render_name u)))
        end

    | (Case (loc, prag, Ann (Box (loc2, (l,cM)), (TypBox (loc3, mT) as tau0_sc)), branches), (tau, t)) ->
        let (total_pragma, tau_sc, projOpt) =  (match  cM with
          | I.ClObj (_ , I.MObj (I.Root (_, I.PVar (x,s) , _ )))
          | I.ClObj (_ , I.PObj (I.PVar (x,s)))  ->
            let order = 
              if !Total.enabled && is_indMObj cD x 
              then IndIndexObj (l,cM)  
              else IndexObj (l,cM) 
            in
              (order, TypBox(loc, convToParamTyp (Whnf.cnormMetaTyp (mT, C.m_id))), None)
          | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k ), _ )))
          | I.ClObj (_, I.PObj (I.Proj (I.PVar (x,s), k))) ->
            let order = 
              if  !Total.enabled && is_indMObj cD x 
              then IndIndexObj (l,cM) 
              else IndexObj (l,cM) 
            in
              (order, TypBox (loc, convToParamTyp(Whnf.cnormMetaTyp (mT, C.m_id))), Some k)
          | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x,s), _ ))) -> 
            let order = 
              if  !Total.enabled && is_indMObj cD x 
              then ((* print_string ("\n inductive in " ^ P.metaObjToString cD cM ^ "\n");*) IndIndexObj (l,cM)) 
              else ((* print_string ("\n NOT inductive " ^ P.metaObjToString cD cM ^ "\n in cD = " ^ P.mctxToString cD ^  "\n");*) IndexObj (l,cM)) 
            in
              (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
          | I.CObj (I.CtxVar (I.CtxOffset k)) -> 
            let order = 
              if  !Total.enabled && is_indMObj cD k 
              then IndIndexObj (l,cM) else IndexObj (l,cM) 
            in
              (order, TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
          | _ -> 
            (IndexObj (l,cM), TypBox (loc, Whnf.cnormMetaTyp (mT, C.m_id)), None)
        ) 
        in
        (* let cM_ann  = LF.checkMetaObj cD (loc,cM) (mT, C.m_id)  in    *)     
        let problem = Coverage.make loc prag cD branches tau_sc in
          (* Coverage.stage problem; *)
          let branches_ann = checkBranches total_pragma cD (cG,cIH) branches tau0_sc (tau, t) in          
          let _ = Coverage.process problem projOpt in
        Synann.Comp.Case
        (
          loc,
          prag,
          (* Ann (Box (loc2, (l, cM_ann)), (TypBox (loc3, mT))), *)          
          Synann.Comp.Ann (Synann.Comp.Box (loc2, (l, cM), ((TypBox (loc3, mT)), C.m_id)), (TypBox (loc3, mT)), ((TypBox (loc3, mT)), C.m_id)),
          branches_ann,
          (tau, t)
        )

    | (Case (loc, prag, i, branches), (tau, t)) ->
      let chkBranch total_pragma cD (cG, cIH) i branches (tau,t) = 
        let (_ , tau', t', i_ann) = syn cD (cG,cIH) i in
          begin match C.cwhnfCTyp (tau',t') with
            | (TypBox (loc', mT),  t') ->
              let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
              let problem = Coverage.make loc prag cD branches tau_s in
                let branches_ann = checkBranches total_pragma cD (cG,cIH) branches tau_s (tau,t) in
                let _ = Coverage.process problem None in 
                Synann.Comp.Case (loc, prag, i_ann, branches_ann, (tau, t))
            | (tau',t') ->
              let tau_s = C.cnormCTyp (tau', t') in
              let problem = Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) in
                let branches_ann = checkBranches total_pragma cD (cG,cIH) branches tau_s (tau,t) in
                let _ = Coverage.process problem None in
                Synann.Comp.Case (loc, prag, i_ann, branches_ann, (tau, t))

          end
      in 
      if !Total.enabled 
      then
      (match i with 
      | Var (_, x)  ->  
        let (f,tau') = lookup cG x in
         (* let _ = print_string 
          ("\nTotality checking enabled - encountered " 
          ^ P.expSynToString cD cG i ^ " with type " 
          ^ P.compTypToString cD tau' ^ "\n") 
         in*)
          let ind = match Whnf.cnormCTyp (tau', Whnf.m_id) with 
          | TypInd _tau -> 
            (
              (* print_string 
                ("Encountered Var " ^ P.expSynToString cD cG i 
                ^ " - INDUCTIVE\n"); *)
            true)
          | _ -> 
            ( 
              (* print_string 
                ("Encountered Var " ^ P.expSynToString cD cG i 
                ^ " - NON-INDUCTIVE\n");*) 
            false) 
          in 
          if ind then
            chkBranch IndDataObj cD (cG,cIH) i branches (tau,t)
          else 
            chkBranch DataObj cD (cG,cIH) i branches (tau,t)
      | _ -> chkBranch DataObj cD (cG,cIH) i branches (tau,t)
      )
     else chkBranch DataObj cD (cG,cIH) i branches (tau,t)

    | (Syn (loc, i), (tau, t)) -> 
      let (_, tau',t', i_ann) = syn cD (cG,cIH) i in
      let (tau',t') = Whnf.cwhnfCTyp (tau',t') in
      if C.convCTyp (tau,t)  (tau',t') then
        Synann.Comp.Syn (
          loc,
          i_ann,
          (tau, t)
        )
      else
        raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), (tau',t'))))

    | (If (loc, i, e1, e2), (tau,t)) ->
        let (_flag, tau', t', i_ann) = syn cD (cG,cIH) i in
        let (tau',t') = C.cwhnfCTyp (tau',t') in
          begin match  (tau',t') with
          | (TypBool , _ ) ->
              Synann.Comp.If (
                loc,
                i_ann, 
                (check cD (cG,cIH) e1 (tau,t)),
                (check cD (cG,cIH) e2 (tau,t)), (* Both branches check e1 in check, error? *)
                (tau, t)
              )                             
          | tau_theta' -> raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
        end

    | (Hole (loc, f), (tau, t)) -> Synann.Comp.Hole (loc, f, (tau, t))

  and check cD (cG, cIH) e (tau, t) =
    let _ =  
      dprint (fun () -> "[check]  " ^ P.expChkToString cD cG e 
        ^ " against \n" ^ P.mctxToString cD ^ " |- " 
        ^ P.compTypToString cD (Whnf.cnormCTyp (tau, t))
      ) in
    checkW cD (cG, cIH) e (C.cwhnfCTyp (tau, t))

  and syn cD (cG,cIH) e : (gctx option * typ * I.msub * Synann.Comp.exp_syn) = match e with
    | Var (loc, x)   ->
      let (f,tau') = lookup cG x in      
      let tau = 
      match Whnf.cnormCTyp (tau', Whnf.m_id) with 
       | TypInd tau -> tau 
       | _ -> tau'
      in 
      if Total.exists_total_decl f 
      then
        (Some cIH, tau, C.m_id, Synann.Comp.Var (loc, x, (tau, C.m_id)))
      else
        (None, tau, C.m_id, Synann.Comp.Var (loc, x, (tau, C.m_id)))

    | DataConst (loc, c) ->
        (None,(CompConst.get c).CompConst.typ, C.m_id, Synann.Comp.DataConst (loc, c, ((CompConst.get c).CompConst.typ, C.m_id)))

    | DataDest (loc, c) ->  
        (None,(CompDest.get c).CompDest.typ, C.m_id, Synann.Comp.DataDest (loc, c, ((CompDest.get c).CompDest.typ, C.m_id)))

    | Const (loc,prog) -> 
        if !Total.enabled then
          if (Comp.get prog).Comp.total then
            (None,(Comp.get prog).Comp.typ, C.m_id, Synann.Comp.Const (loc, prog, ((Comp.get prog).Comp.typ, C.m_id)))
          else
            raise (Error (loc, MissingTotal prog))
        else
          (None,(Comp.get prog).Comp.typ, C.m_id, Synann.Comp.Const (loc, prog, ((Comp.get prog).Comp.typ, C.m_id)))

    | Apply (loc , e1, e2) ->
        let (cIH_opt , tau1, t1, e1_ann) = syn cD (cG,cIH) e1 in
        let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
        begin match (tau1, t1) with
          | (TypArr (tau2, tau), t) ->
              let e2_ann = check cD (cG,cIH) e2 (tau2, t) in              
              (useIH loc cD cG cIH_opt e2, tau, t, Synann.Comp.Apply (loc, e1_ann, e2_ann, (tau, t)))
          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
        end

    | MApp (loc, e, mC) ->
      let (cIH_opt, tau1, t1, e_ann) = syn cD (cG, cIH) e in
        begin match (C.cwhnfCTyp (tau1,t1)) with
          | (TypPiBox ((I.Decl (_ , ctyp, _)), tau), t) ->
             (* let mC_ann = LF.checkMetaObj cD mC (ctyp, t) in *)
             LF.checkMetaObj cD mC (ctyp, t);
             (useIH loc cD cG cIH_opt (Box (loc, mC)), 
              tau, I.MDot(metaObjToMFront mC, t), 
              (* Synann.Comp.MApp (loc, e_ann, mC_ann, (tau, I.MDot(metaObjToMFront mC, t)))) *)
              Synann.Comp.MApp (loc, e_ann, mC, (tau, I.MDot(metaObjToMFront mC, t))))
          | (tau, t) ->
              raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
        end

    | PairVal (loc, i1, i2) ->
        let (_, tau1,t1, i1_ann) =  syn cD (cG,cIH) i1 in
        let (_, tau2,t2, i2_ann) =  syn cD (cG,cIH) i2 in
        let (tau1,t1)    = C.cwhnfCTyp (tau1, t1) in
        let (tau2,t2)    = C.cwhnfCTyp (tau2, t2) in
          (None, 
          TypCross (TypClo (tau1,t1), TypClo (tau2,t2)), 
          C.m_id,
            Synann.Comp.PairVal (
              loc, 
              i1_ann, 
              i2_ann, 
              (TypCross (TypClo (tau1,t1), TypClo (tau2,t2)), C.m_id)
            )
          )

    | Ann (e, tau) ->
        (None, tau, C.m_id, Synann.Comp.Ann ((check cD (cG, cIH) e (tau, C.m_id)), tau, (tau, C.m_id)))

    | Equal(loc, i1, i2) ->
         let (_, tau1, t1, i1_ann) = syn cD (cG,cIH) i1 in
         let (_, tau2, t2, i2_ann) = syn cD (cG,cIH) i2 in
           if Whnf.convCTyp (tau1,t1) (tau2,t2) then
             begin match Whnf.cwhnfCTyp (tau1,t1) with
               | (TypBox _ , _ ) ->  (None, TypBool, C.m_id, Synann.Comp.Equal(loc, i1_ann, i2_ann, (TypBool, C.m_id)))
               | (TypBool, _ )   ->  (None, TypBool, C.m_id, Synann.Comp.Equal(loc, i1_ann, i2_ann, (TypBool, C.m_id)))
               | (tau1,t1)       ->  raise (Error (loc, EqTyp (cD, (tau1,t1))))
             end

           else
             raise (Error(loc, EqMismatch (cD, (tau1,t1), (tau2,t2))))

    | Boolean b  -> (None, TypBool, C.m_id, Synann.Comp.Boolean (b, (TypBool, C.m_id)))

  and synObs cD csp ttau1 ttau2 = match (csp, ttau1, ttau2) with
    | (CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) ->
        if Whnf.convCTyp (tau1, theta) (tau', theta') then
          ((tau2, theta), Synann.Comp.CopatNil loc)
        else
          raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))
    | (CopatApp (loc, dest, csp'), (TypArr (tau1, tau2), theta), (tau', theta')) ->
        if Whnf.convCTyp (tau1, theta) (tau', theta') then
          let (ttau', csp'') = synObs cD csp' ((CompDest.get dest).CompDest.typ, Whnf.m_id) (tau2, theta) in
          (ttau', Synann.Comp.CopatApp (loc, dest, csp''))
        else
          raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))

  and checkPattern cD cG pat ttau = match pat with
    | PatEmpty (loc, cPsi) ->
        (match ttau with
          | (TypBox (_, I.ClTyp (I.MTyp tA, cPhi)) , theta) | (TypBox (_, I.ClTyp (I.PTyp tA, cPhi)), theta) ->
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
          | (TypBox (_, ctyp) , theta) ->
              LF.checkMetaObj cD mO (ctyp, theta)
          | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
        )
    | PatPair (loc, pat1, pat2) ->
        (match ttau with
           | (TypCross (tau1, tau2), theta) ->
               checkPattern cD cG pat1 (tau1, theta);
               checkPattern cD cG pat2 (tau2, theta)
           | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau))))

    | pat ->
        let (loc, ttau') = synPattern cD cG pat in
        let tau' = Whnf.cnormCTyp ttau' in
        let tau = Whnf.cnormCTyp ttau in
        let ttau' = (tau', Whnf.m_id) in
        let ttau = (tau, Whnf.m_id) in
        let _ = dprint (fun () -> "\n Checking conv: " ^ P.compTypToString cD tau
        ^ "\n == " ^ P.compTypToString cD tau' ^ "\n") in
          if C.convCTyp ttau  ttau' then ()
          else
            raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat = match pat with
    | PatConst (loc, c, pat_spine) ->
        let tau = (CompConst.get c).CompConst.typ in
          (loc, synPatSpine cD cG pat_spine (tau , C.m_id))
    | PatVar (loc, k) -> (loc, (lookup' cG k, C.m_id))
    | PatTrue loc -> (loc, (TypBool, C.m_id))
    | PatFalse loc -> (loc, (TypBool, C.m_id))
    | PatAnn (loc, pat, tau) ->
        checkPattern cD cG pat (tau, C.m_id);
        (loc, (tau, C.m_id))

  and synPatSpine cD cG pat_spine (tau, theta) = match pat_spine with
    | PatNil  -> (tau, theta)
    | PatApp (_loc, pat, pat_spine)  ->
      begin match (tau, theta) with
        | (TypArr (tau1, tau2), theta) ->
          checkPattern cD cG pat (tau1, theta);
          synPatSpine cD cG pat_spine (tau2, theta)
        | (TypPiBox (cdecl, tau), theta) ->
          let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
          synPatSpine cD cG pat_spine (tau, theta')
      end

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    LF.checkMetaObj cD mO (ctyp, theta);
    I.MDot(metaObjToMFront mO, theta)

  and checkBranches caseTyp cD cG branches tau_s ttau =
    List.map (fun branch -> checkBranch caseTyp cD cG branch tau_s ttau) branches

  and checkBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
      | EmptyBranch (loc, cD1', pat, t1) ->
          let _ = dprint (fun () -> "\nCheckBranch - Empty Pattern\n") in
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
            (LF.checkMSub  loc cD1' t1 cD;
            checkPattern cD1' I.Empty pat (tau_p, Whnf.m_id));
          Synann.Comp.EmptyBranch (loc, cD1', pat, t1)

      | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) ->
(*         let _ = print_string ("\nCheckBranch with meta-obj pattern : " ^  P.metaObjToString cD1'  mO 
        ^ "\nwhere scrutinee has type " ^
        P.compTypToString cD tau_s ^ "\n") in *)
          let TypBox (_, mT) = tau_s in
          (* By invariant: cD1' |- t1 <= cD *)
    let mT1   = Whnf.cnormMetaTyp (mT, t1) in
          let cG'   = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
          let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in          
          let (cD1',cIH')  = if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (loc', mO)) then
                         let cD1' = mvarsInPatt cD1' (PatMetaObj(loc', mO)) in 
         (* print_string "Inductive and Structurally smaller\n"; *)
         (cD1', Total.wf_rec_calls cD1' (I.Empty))
           else (cD1', I.Empty) in 
    let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD
                   else cD1' in  
    (* let _ = print_string ("Outer cD = " ^ P.mctxToString cD ^ "\nInner cD' = " ^ P.mctxToString cD1' ^ "\n\n") in *)
            (LF.checkMSub loc cD1' t1 cD;
       LF.checkMetaObj cD1' mO (mT1, C.m_id);
            Synann.Comp.Branch (loc, cD1', cG, PatMetaObj (loc', mO), t1, (check cD1' (cG', Context.append cIH cIH') e1 (tau', Whnf.m_id))))

      | Branch (loc, cD1', cG1, pat, t1, e1) ->
          let tau_p = Whnf.cnormCTyp (tau_s, t1) in
          let cG'   = Whnf.cnormCtx (cG, t1) in
          let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
          let t''   = Whnf.mcomp t t1 in
          let tau'  = Whnf.cnormCTyp (tau, t'') in
(*          let _     = print_string ("\nCheckBranch with general pattern:" ^ P.patternToString  cD1' cG1 pat ^ "\n") in 
         let _ = print_string ("\nwhere scrutinee has type" ^
        P.compTypToString cD tau_s ^ "\n") in *)
    let k     = Context.length cG1 in 
    let cIH0  = Total.shiftIH cIH k in 
          let (cD1', cIH')  = if is_inductive caseTyp && Total.struct_smaller pat then
                       let cD1' = mvarsInPatt cD1' pat in (cD1', Total.wf_rec_calls cD1' cG1)
                     else (cD1', I.Empty) in
    let cD1' = if !Total.enabled then id_map_ind cD1' t1 cD
                   else cD1' in  
    (* let _ = print_string ("\nOuter cD = " ^ P.mctxToString cD ^ "\nInner cD' = " ^ P.mctxToString cD1' ^ "\nGiven ref. subst. = " ^ P.msubToString cD1' t1 ^ "\n") in *)
          (LF.checkMSub loc  cD1' t1 cD;
           checkPattern cD1' cG1 pat (tau_p, Whnf.m_id);
           Synann.Comp.Branch (loc, cD1', cG1, pat, t1, (check cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') e1 (tau', Whnf.m_id))))

  let rec wf_mctx cD = match cD with
    | I.Empty -> ()
    | I.Dec (cD, cdecl) ->
        (wf_mctx cD ; checkCDecl cD cdecl)


  let syn cD cG e =
    let cIH = Syntax.Int.LF.Empty in
    let (_ , tau, t, e_ann) = syn cD (cG,cIH) e in
      ((tau, t), e_ann)

  let check cD cG e ttau =
    let cIH = Syntax.Int.LF.Empty in      
      check cD (cG,cIH) e ttau

end