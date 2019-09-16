module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [5])
open Debug.Fmt

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
  | MissingType of string

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | ParamVarInst (cD, cPsi, sA) ->
            Format.fprintf ppf "Parameter variable of type %a does not appear as a declaration in context %a. @ @ It may be that no parameter variable of this type exists in the context or the type of the parameter variable is a projection of a declaration in the context."
              (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)
              (P.fmt_ppr_lf_dctx cD P.l0) cPsi

      | CtxVarMisCheck (c0, cPsi, sA, sEl ) ->
            Format.fprintf ppf "Type %a doesn't check against schema %a."
               (P.fmt_ppr_lf_typ c0 cPsi P.l0) (Whnf.normTyp sA)
               (P.fmt_ppr_lf_schema P.l0) sEl

      | CtxVarMismatch (cO, var, expected) ->
          Format.fprintf ppf "Context variable %a doesn't check against schema %a."
            (P.fmt_ppr_lf_ctx_var cO) var
            (P.fmt_ppr_lf_schema P.l0) expected

      | CtxVarDiffer (cO, var, var1) ->
          Format.fprintf ppf "Context variable %a not equal to %a."
            (P.fmt_ppr_lf_ctx_var cO) var
            (P.fmt_ppr_lf_ctx_var cO) var1

            | MissingType name ->
               Format.fprintf ppf "Need to know type of %s" name

      | CheckError (cD, cPsi, sM, sA) ->
          Format.fprintf ppf
	    "Expression %a does not check against %a."
	    (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM)
	    (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)

      | SigmaMismatch (cD, cPsi, sArec, sBrec) ->
        Error.report_mismatch ppf
	  "Sigma type mismatch."
	  "Expected type" (P.fmt_ppr_lf_typ_rec cD cPsi P.l0) (Whnf.normTypRec sArec)
	  "Actual type"   (P.fmt_ppr_lf_typ_rec cD cPsi P.l0) (Whnf.normTypRec sBrec)

      | TupleArity (cD, cPsi, sM, sA) ->
	Error.report_mismatch ppf
	  "Arity of tuple doesn't match type."
	  "Tuple" (P.fmt_ppr_lf_normal cD cPsi P.l0)  (Whnf.norm sM)
	  "Type"  (P.fmt_ppr_lf_typ_rec cD cPsi P.l0) (Whnf.normTypRec sA)

      | KindMismatch (cD, cPsi, sS, sK) ->
	Error.report_mismatch ppf
          "Ill-kinded type."
	  "Expected kind:" (P.fmt_ppr_lf_kind cPsi P.l0) (Whnf.normKind sK)
	  "for spine:"     (P.fmt_ppr_lf_spine cD cPsi P.l0) (Whnf.normSpine sS)

      | TypMismatch (cD, cPsi, sM, sA1, sA2) ->
        Error.report_mismatch ppf
          "Ill-typed term."
	  "Expected type" (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA1)
	  "Inferred type" (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA2);
        Format.fprintf ppf
          "In expression: %a@."
          (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM)

      | IllTypedSub (cD, cPsi, s, cPsi') ->
        Format.fprintf ppf "Ill-typed substitution.@.";
        Format.fprintf ppf "    Substitution: %a@."
          (P.fmt_ppr_lf_sub cD cPsi P.l0) s;
        Format.fprintf ppf "    does not take context: %a@."
          (P.fmt_ppr_lf_dctx cD P.l0) cPsi';
        Format.fprintf ppf "    to context: %a@."
          (P.fmt_ppr_lf_dctx cD P.l0) cPsi;

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
              (P.fmt_ppr_lf_mfront cD P.l0) (ClObj (Context.dctxToHat cPsi, cM))
              (P.fmt_ppr_lf_mtyp cD) (ClTyp (mT, cPsi))
      | CtxHatMismatch (cD, cPsi, phat, cM) ->
          let cPhi = Context.hatToDCtx (Whnf.cnorm_psihat phat Whnf.m_id) in
            Error.report_mismatch ppf
              "Type checking encountered ill-typed meta-object. This is a bug in type reconstruction."
              "Expected context" (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx  cPsi)
              "Given context" (P.fmt_ppr_lf_psi_hat cD P.l0) cPhi;
              Format.fprintf ppf
                "In expression: %a@."
                (P.fmt_ppr_cmp_meta_obj cD P.l0) cM
      | TermWhenVar (cD, cPsi, tM) ->
	Format.fprintf ppf "A term was found when expecting a variable.@." ;
	Format.fprintf ppf "Offending term: %a @."
	  (P.fmt_ppr_lf_normal cD cPsi P.l0) tM
      | SubWhenRen (cD, cPsi, sub) ->
	Format.fprintf ppf "A substitution was found when expecting a renaming.@." ;
	Format.fprintf ppf "Offending substitution: %a @."
	  (P.fmt_ppr_lf_sub cD cPsi P.l0) sub
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

let rec dot_k s k = if k = 0 then s
else dot_k (Substitution.LF.dot1 s) (k-1)

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
let rec checkW cD cPsi sM sA = match sM, sA with
  | (Lam (loc, name, tM), s1), (PiTyp ((TypDecl (_x, _tA) as tX, _), tB), s2) -> (* Offset by 1 *)
    check cD
      (DDec (cPsi, Substitution.LF.decSub tX s2))
      (tM, Substitution.LF.dot1 s1)
      (tB, Substitution.LF.dot1 s2);
    Typeinfo.LF.add loc (Typeinfo.LF.mk_entry cD cPsi sA)
      (let open Format in
       fprintf str_formatter "Lam %a"
         (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM);
       flush_str_formatter ())

  | (LFHole (loc, m_name), _), _ ->
     begin
       let info = Holes.LfHoleInfo { cPsi; Holes.lfGoal = sA } in
       let name = Holes.name_of_option m_name in
       let _ = Holes.add { Holes.loc = loc; Holes.name = name; Holes.cD = cD; Holes.info = info } in
       ()
     end
  | (Lam (loc, _, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

  | (Tuple (loc, tuple), s1), (Sigma typRec, s2) ->
    checkTuple loc cD cPsi (tuple, s1) (typRec, s2);
    Typeinfo.LF.add loc (Typeinfo.LF.mk_entry cD cPsi sA)
      (let open Format in
       fprintf str_formatter "Tuple %a"
         (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM);
       flush_str_formatter ())

  | (Tuple (loc, _), _), _ ->
    raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

  | (Root (loc, _h, _tS), _s (* id *)), (Atom _, _s') ->
    (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
    begin
      try
        dprintf
          (fun p ->
            p.fmt "[ROOT check] %a ; %a |- %a <= %a"
              (P.fmt_ppr_lf_mctx P.l0) cD
              (P.fmt_ppr_lf_dctx cD P.l0) cPsi
              (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM)
              (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA));
        let sP = syn cD cPsi sM in
        dprintf
          (fun p ->
            p.fmt "[ROOT check] @[<v>synthesized:@,%a ; %a |- %a <= %a@,against %a@]"
              (P.fmt_ppr_lf_mctx P.l0) cD
              (P.fmt_ppr_lf_dctx cD P.l0) cPsi
              (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM)
              (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sP)
              (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)
          );
	  Typeinfo.LF.add loc (Typeinfo.LF.mk_entry cD cPsi sA)
	    (let open Format in
       fprintf str_formatter "Root %a"
         (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM);
       flush_str_formatter ());
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
  if typLength sA' < spineLength tS then
    raise (Error (loc, SpineIllTyped (typLength sA', spineLength tS)));
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
        dprintf
          (fun p ->
            p.fmt "[InferHead] @[<v>%a |- %a@,where %a has type %a@]"
              (P.fmt_ppr_lf_dctx cD P.l0) cPsi
              (P.fmt_ppr_lf_head cD cPsi P.l0) head
              (P.fmt_ppr_lf_head cD cPsi P.l0) tuple_head
              (P.fmt_ppr_lf_typ_rec cD cPsi P.l0) recA
          );
        (recA, Substitution.LF.id)
      | PVar (p, s) ->
        let (_, Sigma recA, cPsi') = Whnf.mctxPDec cD p in
        checkSub loc cD cPsi s Subst cPsi';
        (recA, s)
    in
    let (_tA, s) as sA = getType tuple_head srecA target 1 in
    dprintf
      (fun p ->
        p.fmt "[inferHead-Proj] @[<v>getType (%a) = %a@,s = %a@]"
          (P.fmt_ppr_lf_head cD cPsi P.l0) head
          (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)
          (P.fmt_ppr_lf_sub cD cPsi P.l0) s
      );
    TClo sA


  | Const c, Subst ->
    (Term.get c).Term.typ

  | MVar (Offset u, s), Subst ->
    (* cD ; cPsi' |- tA <= type *)
    let (_, tA, cPsi') = Whnf.mctxMDec cD u in
    dprintf
      (fun p ->
        let f = P.fmt_ppr_lf_dctx cD P.l0 in
        p.fmt "[inferHead] @[<v>%a@,%a |- %a <= %a@]"
          (P.fmt_ppr_lf_head cD cPsi P.l0) head
          f cPsi
          (P.fmt_ppr_lf_sub cD cPsi P.l0) s
          f cPsi');
    checkSub loc cD cPsi s Subst cPsi' ;
    TClo (tA, s)

  | MVar (Inst (_n, {contents = None}, _cD, ClTyp (MTyp tA,cPsi'), _cnstr, _), s), Subst ->
     dprintf
       (fun p ->
         let f = P.fmt_ppr_lf_dctx cD P.l0 in
         p.fmt "[inferHead] @[<v>%a@,%a |- %a <= %a@]"
           (P.fmt_ppr_lf_head cD cPsi P.l0) head
           f cPsi
           (P.fmt_ppr_lf_sub cD cPsi P.l0) s
           f cPsi');
    checkSub loc cD cPsi s Subst cPsi' ;
    TClo (tA, s)

  | MMVar (((_n, {contents = None}, cD' , ClTyp (MTyp tA,cPsi'), _cnstr, _) , t'), r), Subst ->
     dprintf
       (fun p ->
         let f = P.fmt_ppr_lf_mctx P.l0 in
         p.fmt "[inferHead] @[<v>MMVar %a@,cD = %a@,t' = %a@,cD' = %a@]"
           (P.fmt_ppr_lf_head cD cPsi P.l0) head
           f cD
           (P.fmt_ppr_lf_msub cD P.l0) t'
           f cD');
    checkMSub loc cD t' cD';
    dprint (fun () -> "[inferHead] MMVar - msub done \n");
    checkSub loc cD cPsi r Subst (Whnf.cnormDCtx (cPsi', t')) ;
    TClo(Whnf.cnormTyp (tA, t'), r)

  | Const _, Ren
  | MVar _, Ren
  | MMVar _, Ren -> raise (Error (loc, TermWhenVar (cD, cPsi, (Root (loc, head, Nil)))))

  | PVar (p, s), _ ->
    (* cD ; cPsi' |- tA <= type *)
    let (_, tA, cPsi') = Whnf.mctxPDec cD p in
    dprnt "[inferHead] PVar case";
    dprintf
      (fun p ->
        p.fmt "[inferHead] @[<v>PVar case: s = %a@,check: @[<v>cPsi' (context of pvar) = %a@,cPsi (pattern context) = %a@,synthesizing %a for PVar@,cD = %a@]@]"
          (P.fmt_ppr_lf_sub cD cPsi P.l0) s
          (P.fmt_ppr_lf_dctx cD P.l0) cPsi'
          (P.fmt_ppr_lf_dctx cD P.l0) cPsi
          (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tA, s))
          (P.fmt_ppr_lf_mctx P.l0) cD);
    checkSub loc cD cPsi s cl cPsi';
    (* Check that something of type tA could possibly appear in cPsi *)
(*    if not (canAppear cD cPsi head (tA, s) loc) then
      raise (Error (loc, ParamVarInst (cD, cPsi, (tA, s)))); *)
    (* Return p's type from cD *)
    TClo (tA, s)

  | FVar _, _ ->
    raise (Error (loc, LeftoverFV))


and canAppear cD cPsi head sA loc=
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
     dprintf
       (fun p ->
         p.fmt "[chkDCtx] lookup CtxVar @[<v>where k = %s@,in cD = %a@]"
           (R.render_offset k)
           (P.fmt_ppr_lf_mctx P.l0) cD);
     let (_,CTyp _)  = Whnf.mctxLookup cD k in ()

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
  dprintf
    (fun p ->
      p.fmt "[checkTypeAgainstSchema] @[%a@ against %a@]"
        (P.fmt_ppr_lf_typ cD cPsi P.l0) tA
        (P.fmt_ppr_lf_schema P.l0) (Schema elements));
  match elements with
    | [] ->
      raise (Error (loc, CtxVarMisCheck (cD, cPsi, (tA, Substitution.LF.id), Schema elements)))

    | element :: elements ->
      try
        instanceOfSchElem cD cPsi (tA, Substitution.LF.id) element
      with
      | (Match_failure _) as exn -> raise exn (* XXX why? -je *)
      | _ -> checkTypeAgainstSchema loc cD cPsi tA elements

and instanceOfSchElem cD cPsi (tA, s) (SchElem (some_part, block_part)) =
  let _ = dprint (fun () -> "instanceOfSchElem...") in
  let sArec = match Whnf.whnfTyp (tA, s) with
    | (Sigma tArec,s') -> (tArec, s')
    | (nonsigma, s') -> (SigmaLast (None, nonsigma), s') in
  dprintf
    (fun p ->
      p.fmt "[instanceOfSchElem] tA = %a"
        (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tA, s)));
  let dctx        = projectCtxIntoDctx some_part in
  let dctxSub     = ctxToSub' cPsi dctx in
  dprintf
    (fun p ->
      let f = P.fmt_ppr_lf_dctx cD P.l0 in
      p.fmt "[instanceOfSchElem] @[<v>Check if it is an instance of a schema element ...@,\
             cPsi = %a@,\
             dctx = %a@,\
             dctxSub = %a@]"
        f cPsi f dctx
        (P.fmt_ppr_lf_sub cD cPsi P.l0) dctxSub);

  (* let phat        = dctxToHat cPsi in *)
  dprintf
    begin fun p ->
    let f = P.fmt_ppr_lf_dctx cD P.l0 in
    p.fmt "[instanceOfSchElem] @[<v>Unify.unifyTypRec@,\
           cPsi = %a@,\
           dctx = %a@,\
           @[%a == %a@]@]"
      f cPsi
      f dctx
      (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tA, s))
      (P.fmt_ppr_lf_typ_rec cD cPsi P.l0) (Whnf.normTypRec (block_part, dctxSub))
    end;

  begin
    try
      Unify.unifyTypRec cD cPsi sArec (block_part, dctxSub);
      dprintf
        begin fun p ->
        p.fmt "[instanceOfSchElem] @[<v>block_part = %a@,succeeded@]"
          (P.fmt_ppr_lf_typ_rec cD cPsi P.l0) (Whnf.normTypRec (block_part, dctxSub))
        end;
      (block_part, dctxSub)
    with (Unify.Failure _) as exn ->
      dprintf
        begin fun p ->
        let f = P.fmt_ppr_lf_typ_rec cD cPsi P.l0 in
        p.fmt "[instanceOfSchElem] @[<v>type unification failed@,@[%a@ =/= %a@]@]"
          f (Whnf.normTypRec sArec) f (Whnf.normTypRec (block_part, dctxSub))
        end;
      raise exn
  end


(* checkTypeAgainstSchemaProj loc cD cPsi head tA sch (elements : sch_elem list)
 *   sch = full schema, for error messages
 *   elements = elements to be tried
 *)
and checkTypeAgainstSchemaProj loc cD cPsi head tA elements =
  (* if tA is not a Sigma, "promote" it to a one-element typRec *)
  dprintf
    begin fun p ->
    p.fmt "[checkTypeAgainstSchemaProj] @[<v>%a@,against@,%a@]"
      (P.fmt_ppr_lf_typ cD cPsi P.l0) tA
      (P.fmt_ppr_lf_schema P.l0) (Schema elements)
    end;
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

and existsInstOfSchElemProj loc cD cPsi sA (h,i, n) elem = if i > n then
  raise (Error (loc, ParamVarInst (cD, cPsi, sA)))
else
  begin try
    instanceOfSchElemProj cD cPsi sA (h, i) elem
  with _ ->
    existsInstOfSchElemProj loc cD cPsi sA (h, i+1, n) elem
  end


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
    prefixSchElem elem2 elem1 (* (cSome1 = cSome2) && (block1 = block2)  *)
  in
  dprintf
    begin fun p ->
    p.fmt "[checkElementAgainstElement] @[<2>%a <== %a@ : %b@] "
      (P.fmt_ppr_lf_schema P.l0) (Schema [elem1])
      (P.fmt_ppr_lf_schema P.l0) (Schema [elem2])
      result
    end;
  result

(* checkElementAgainstSchema cD sch_elem (elements : sch_elem list) *)
and checkElementAgainstSchema cD sch_elem elements =
  List.exists (checkElementAgainstElement cD sch_elem) elements

(*  and subset f list =
    begin match list with [] -> true
    | elem::elems -> f elem
*)

and checkSchema loc cD cPsi (Schema elements as schema) =
  dprintf
    begin fun p ->
    p.fmt "[checkSchema] @[<v>%a@,against@,%a@]"
      (P.fmt_ppr_lf_dctx cD P.l0) cPsi
      (P.fmt_ppr_lf_schema P.l0) schema
    end;
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

 and elemPostfix sArec sBrec = match (sArec, sBrec) with
   | ((SigmaLast(_, lastA), s), (SigmaLast(_, lastB), s')) ->
       None

   | ((SigmaElem (_xA, tA, recA), s), (SigmaLast(_, tB), s')) ->
       Some (recA,s)

   | ((SigmaElem (_xA, _tA, recA), s), (SigmaElem(_xB, _tB, recB), s')) ->
       elemPostfix (recA, Substitution.LF.dot1 s) (recB, Substitution.LF.dot1 s')



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
      dprintf
        begin fun p ->
        let f = P.fmt_ppr_lf_typ cD cPsi' P.l0 in
        p.fmt "[checkClObj] @[<v>check parameter object against:@,\
               %a@,\
               inferred type of parameter object:@,\
               %a@]"
          f tA f tA'
        end;
        if Whnf.convTyp (tA, Substitution.LF.id) (tA', Substitution.LF.id) then ()
	else raise (Error (loc, (IllTypedMetaObj (cD, cM, cPsi', Whnf.cnormClTyp cTt))))

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
    if Whnf.convMTyp mtyp1 mtyp2 then ()
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
       let s =
         let open Format in
         fprintf str_formatter "@[<v 2>Contextual substitution ill-typed@,\
                                %a |- %a <= %a"
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_lf_msub cD P.l0) ms
           (P.fmt_ppr_lf_mctx P.l0) cD';
         flush_str_formatter ()
       in
       raise (Error.Violation s)
