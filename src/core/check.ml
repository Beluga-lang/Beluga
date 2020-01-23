(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
open Support

let (dprintf, dprint, dprnt) =
  Debug.makeFunctions' (Debug.toFlags [5])
open Debug.Fmt

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

  open Store.Cid
  module Loc = Syntax.Loc
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type mismatch_kind =
    [ `fn
    | `mlam
    | `box
    | `ctxfun
    | `pair
    ]

  type error =
    | IllegalParamTyp of I.mctx * I.dctx * I.typ
    | MismatchChk     of I.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of I.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of I.mctx * gctx * pattern * tclo * tclo
    | BasicMismatch   of mismatch_kind * I.mctx * gctx * tclo
    | SBoxMismatch    of I.mctx * gctx  * I.dctx  * I.dctx
    | SynMismatch     of I.mctx * tclo (* expected *) * tclo (* inferred *)
    | BoxCtxMismatch  of I.mctx * I.dctx * (I.dctx_hat * I.normal)
    | PattMismatch    of (I.mctx * meta_obj * meta_typ) *
                           (I.mctx * meta_typ)
    (*    | PattMismatch    of (I.mctx * I.dctx * I.normal option * I.tclo) *
          (I.mctx * I.dctx * I.tclo) *)
    | MAppMismatch    of I.mctx * (meta_typ * I.msub)
    | AppMismatch     of I.mctx * (meta_typ * I.msub)
    | CtxMismatch     of I.mctx * I.dctx (* expected *) * I.dctx (* found *) * meta_obj
    | TypMismatch     of I.mctx * tclo * tclo
    | UnsolvableConstraints of Id.name option * string
    | InvalidRecCall
    | MissingTotal    of Id.cid_prog
    | NotImpossible   of I.mctx * gctx * typ * exp_syn
  (* | IllTypedMetaObj of I.mctx * meta_obj * meta_typ  *)

  (*  type rec_call = bool *)

  exception Error of Syntax.Loc.t * error

  let throw loc e = raise (Error (loc, e))

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT

  (** Analyzes a contextual object to decide whether it's a
      (contextual) variable and rewrites its type from MTyp to PTyp if
      necessary. This is crucial for coverage checking of a case analysis
      on a parameter variable.
      Also returns the index of the variable (so we can later decide
      if it's a variable we're doing induction on) as well what
      projection, if any, is applied to the parameter variable.
   *)
  let fixParamTyp mC mT = match mC with
    (* cases for a parameter variable without a projection *)
    | I.(ClObj (_, (PObj (PVar (x, _)) | MObj (Root (_, I.PVar (x, _), _))))) ->
       Some x, convToParamTyp mT, None
    (* cases for a parameter variable with a projection *)
    | I.(ClObj (_, (PObj (I.Proj (I.PVar (x, _), k)) | MObj (Root (_, Proj (PVar (x, _), k), _))))) ->
       Some x, convToParamTyp mT, Some k
    (* cases for a context variable or a metavariable *)
    | I.(CObj (CtxVar (CtxOffset x)) | ClObj(_, MObj (Root (_, MVar (Offset x, _), _)))) ->
       Some x, mT, None
    | _ -> None, mT, None

  let string_of_typeVariant = function
    | VariantCross -> "product type"
    | VariantArrow -> "function type"
    | VariantCtxPi -> "context abstraction"
    | VariantPiBox -> "dependent function type"
    | VariantBox   -> "contextual type"

  let format_error ppf = function
    | MissingTotal prog ->
       Format.fprintf ppf "Function %s not known to be total."
         (R.render_cid_prog prog)
    | InvalidRecCall ->
       Format.fprintf ppf "Recursive call not structurally smaller."
    | IllegalParamTyp (cD, cPsi, tA) ->
       Format.fprintf ppf
         "Parameter type %a is illegal."
         (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tA, Substitution.LF.id))
    | UnsolvableConstraints (f, cnstrs) ->
       let fname = match f with None -> "" | Some g -> " " ^ (Id.render_name g) in
       let msg1 =
         "Unification in type reconstruction encountered constraints \
          because the given signature contains unification problems \
          which fall outside the (decidable) pattern fragment;"
       in
       let msg2 =
         "there are meta-variables which are not only applied \
          to a distinct set of bound variables;"
       in
       let msg3 =
         "a meta-variable in the program depends on a context, but \
          that meta-varaible must be in fact closed."
       in
       let open Format in
       fprintf ppf
         "@[<v>%a@,@,\
          Common causes are:@,
          @[<v>\
          - @[%a@]@,\
          - @[%a@]@,@]@,@,\
          The constraint@,  @[%a@]@,\
          could not be solved.@,
          The program @[%a@] is considered ill-typed.@]"
         pp_print_string msg1
         pp_print_string msg2
         pp_print_string msg3
         pp_print_string cnstrs
         pp_print_string fname

    | CtxMismatch (cD, cPsi, cPhi, cM) ->
       Error.report_mismatch ppf
         "Type checking Ill-typed meta-object. This is a bug in type reconstruction."
         "Expected context" (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx  cPsi)
         "Given context" (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx cPhi);
       Format.fprintf ppf
         "In expression: %a@."
         (P.fmt_ppr_cmp_meta_obj cD P.l0) cM

    | MismatchChk (cD, cG, e, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
       Error.report_mismatch ppf
         "Ill-typed expression."
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau');
       Format.fprintf ppf
         "In expression: %a@."
         (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e

    | MismatchSyn (cD, cG, i, variant, theta_tau) ->
       Error.report_mismatch ppf
         "Ill-typed expression."
         "Expected" Format.pp_print_string (string_of_typeVariant variant)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau);
       Format.fprintf ppf
         "In expression: %a@."
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i

    | PatIllTyped (cD, cG, pat, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
       Error.report_mismatch ppf
         "Ill-typed pattern."
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau');
       Format.fprintf ppf
         "In pattern: %a@."
         (P.fmt_ppr_cmp_pattern cD cG P.l0) pat

    | PattMismatch ((cD, _cM, mT) , (cD', mT')) ->
       Error.report_mismatch ppf
         "Ill-typed pattern."
         "Expected type"
         (P.fmt_ppr_cmp_typ cD' P.l0)
         (TypBox (Syntax.Loc.ghost, mT'))
         "Inferred type"
         (P.fmt_ppr_cmp_typ cD P.l0)
         (TypBox (Syntax.Loc.ghost, mT))

    (*          | PattMismatch ((cD, cPsi, pattern, sA) , (cD', cPsi', sA')) ->
                Error.report_mismatch ppf
                "Ill-typed pattern."
                "Expected type"
                (P.fmt_ppr_cmp_typ cD' P.l0)
                (TypBox (Syntax.Loc.ghost, MetaTyp (Whnf.normTyp sA', Whnf.normDCtx cPsi')))
                "Inferred type"
                (P.fmt_ppr_cmp_typ cD P.l0)
                (TypBox (Syntax.Loc.ghost, MetaTyp (Whnf.normTyp sA, Whnf.normDCtx cPsi)))
     *)
    | BoxCtxMismatch (cD, cPsi, (phat, tM)) ->
       Format.fprintf ppf
         "@[<v>Found expression@,  @[%a@,in context %a@]@,but it was expected in context@,  %a@]"
         (P.fmt_ppr_lf_normal cD cPsi P.l0) tM
         (P.fmt_ppr_lf_dctx_hat cD P.l0) (Context.hatToDCtx phat)
         (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx cPsi)

    | BasicMismatch (k, cD, _cG, ttau) ->
       let tau = Whnf.cnormCTyp ttau in
       let print_mismatch_kind ppf : mismatch_kind -> unit =
         let p s = Format.fprintf ppf "%s" s in
         function
         | `fn -> p "function abstraction"
         | `mlam -> p "meta abstraction (mlam)"
         | `ctxfun -> p "context abstraction"
         | `box -> p "box-expression"
         | `pair -> p "tuple"
       in
       Format.fprintf ppf "@[<v>Found@,  %a@,but expected expression of type@,  %a@]"
         print_mismatch_kind k
         (P.fmt_ppr_cmp_typ cD P.l0) tau

    | SBoxMismatch (cD, _cG, cPsi, cPhi) ->
       Format.fprintf ppf
         "Found substitution that does not have type %a[%a]."
         (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx cPsi)
         (P.fmt_ppr_lf_dctx cD P.l0) (Whnf.normDCtx cPhi)

    | SynMismatch (cD, theta_tau, theta_tau') ->
       Error.report_mismatch ppf
         "Ill-typed expression."
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
         "Inferred type" (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau')

    | AppMismatch (cD, (ctyp, theta)) ->
       Format.fprintf ppf
         "Expected contextual object of type %a."
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, ctyp), theta))

    | MAppMismatch (cD, (ctyp, theta)) ->
       Format.fprintf ppf
         "Expected contextual object of type %a."
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (TypBox(Syntax.Loc.ghost, ctyp), theta))
    | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
       Error.report_mismatch ppf
         "Type of destructor did not match the type it was expected to have."
         "Type of destructor" (P.fmt_ppr_cmp_typ cD P.l0)
         (Whnf.cnormCTyp (tau1, theta1))
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0)
         (Whnf.cnormCTyp (tau2, theta2))

    | NotImpossible (cD, cG, tau, i) ->
       Format.fprintf ppf
         "@[<v>The expression@,  @[%a@]@,is not impossible.@,Its type@,  @[%a@]@,is (possibly) inhabited.@]"
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
         (P.fmt_ppr_cmp_typ cD P.l0) tau
  let _ =
    Error.register_printer
      (fun (Error (loc, err)) -> Error.print_with_location loc (fun ppf -> format_error ppf err))

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



  (** Marks the variable at index k in cD as Inductive. *)
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
    | _ -> cD

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
    | PatVar (_ , _ ) | PatFVar (_, _) -> cD
    | PatPair (_, pat1, pat2) ->  fmv (fmv cD pat1) pat2
    | PatMetaObj (_, cM) -> fmv_mobj cD cM
    | PatAnn (_, pat, _) -> fmv cD pat

  and fmv_pat_spine cD pat_spine = match pat_spine with
    | PatNil -> cD
    | PatApp (_, pat, pat_spine) ->
       fmv_pat_spine  (fmv cD pat) pat_spine

  let mvars_in_patt cD pat =
    fmv cD pat

  let rec id_map_ind (cD1' : I.mctx) t (cD : I.mctx) : I.mctx = match t, cD with
    | I.MShift k, I.Empty -> cD1'
    | I.MShift k, cD when k < 0 ->
       raise (Error.Violation "Contextual substitution ill-formed")
    | I.MDot (_, _), I.Empty ->
       Error.violation "Contextual substitution ill-formed"
    | I.MShift k, cD -> (* k >= 0 *)
       id_map_ind cD1' (I.MDot (I.MV (k+1), I.MShift (k+1))) cD

    | I.MDot (I.MV u, ms), I.Dec(cD, I.Decl (_u, mtyp1, dep)) ->
       if Total.is_inductive dep then
         let cD1' = mark_ind cD1' u in
         id_map_ind cD1' ms cD
       else
         id_map_ind cD1' ms cD

    | I.MDot (mf, ms), I.Dec(cD, I.Decl (_u, mtyp1, dep)) ->
       begin
         match mf with
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
         | _ -> id_map_ind cD1' ms cD
       end

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

  let lookup cG k =
    Context.lookup' cG k
    |> Maybe.get
    |> function
      | CTypDecl (u, tau, wf_tag) -> (u, tau, wf_tag)

  let lookup' cG k =
    let (_, tau, _) = lookup cG k in
    tau

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

    | TypArr (_, tau1, tau2) ->
       checkTyp cD tau1;
       checkTyp cD tau2

    | TypCross (_, tau1, tau2) ->
       checkTyp cD tau1;
       checkTyp cD tau2

    | TypPiBox (_, cdecl, tau') ->
       dprintf
         begin fun p ->
         p.fmt "[checkCompTyp] @[%a@ |- %a@]"
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       checkCDecl cD cdecl;
       dprintf
         begin fun p ->
         p.fmt "[checkCompTyp] @[%a@ |- %a@]"
           (P.fmt_ppr_lf_mctx P.l0) (I.Dec (cD, cdecl))
           (P.fmt_ppr_cmp_typ (I.Dec (cD, cdecl)) P.l0) tau'
         end;
       checkTyp (I.Dec (cD, cdecl)) tau'

    | TypInd tau -> checkTyp cD tau


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
    | None ->
       dprnt "[useIH] we are not making a recursive call";
       None
    | Some cIH ->
       (* We are making a recursive call *)
       dprint
         (fun _ -> "[useIH] here we are doing induction today");
       let cIH = match cIH with
         | I.Empty -> raise (Error (loc, InvalidRecCall))
         | cIH  ->
            match e2 with
            | Box (_,cM) ->
               dprintf
                 begin fun p ->
                 p.fmt "[useIH] @[<v>check whether compatible IH exists@,\
                        cIH = @[%a@]@,\
                        recursive call on: @[%a@]@]"
                   (Total.fmt_ppr_ihctx cD cG) cIH
                   (P.fmt_ppr_cmp_meta_obj cD P.l0) cM
                 end;
               Total.filter cD cG cIH (loc, M cM)
            | Syn(_, i) ->
               match extract_var i with
               | Some x -> Total.filter cD cG cIH (loc, V x)
               | None ->  Total.filter cD cG cIH (loc, E)
       in
       dprintf
         begin fun p ->
         p.fmt "[useIH] Partially used IH: %a"
           (Total.fmt_ppr_ihctx cD cG) cIH
         end;
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

  let checkMetaObj cD cM cT t =
    try
      LF.checkMetaObj cD cM (cT, t);
      Typeinfo.Comp.add (getLoc cM)
        (Typeinfo.Comp.mk_entry cD (TypBox (getLoc cM, cT), t))
        ("Box " ^ Fmt.stringify (P.fmt_ppr_cmp_meta_obj cD P.l0) cM)
    with Whnf.FreeMVar (I.FMVar (u, _ )) ->
      Error.violation ("Free meta-variable " ^ Id.render_name u)

  let rec checkW cD (cG , cIH) total_decs e ttau =
    let decide_ind cM x =
      if Misc.List.nonempty total_decs && is_indMObj cD x
      then
        let _ =
          dprintf
            (fun p ->
              p.fmt "[checkBranch] doing induction on a box-type");
        in
        IndIndexObj cM
      else IndexObj cM
    in
    let decide_ind_maybe cM k =
      Maybe.(get_default (IndexObj cM) (k $> decide_ind cM))
    in
    match (e, ttau) with
    | (Fn (loc, x, e), (TypArr (_, tau1, tau2), t)) ->
       check cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t), false)), (Total.shift cIH)) total_decs e (tau2, t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Fn " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (Fun (loc, fbr), _) ->
       checkFBranches cD (cG, cIH) total_decs fbr ttau

    | (MLam (loc, u, e), (TypPiBox (_, cdec, tau), t)) ->
       (check (extend_mctx cD (u, cdec, t))
          (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1)) total_decs e (tau, C.mvar_dot1 t);
        Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
          ("MLam " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e))

    | (Pair (loc, e1, e2), (TypCross (_, tau1, tau2), t)) ->
       check cD (cG,cIH) total_decs e1 (tau1, t);
       check cD (cG,cIH) total_decs e2 (tau2, t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Pair " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (Let (loc, i, (x, e)), (tau, t)) ->
       let (_ , tau', t') = syn cD (cG,cIH) total_decs i in
       let (tau', t') =  C.cwhnfCTyp (tau',t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'), false)) in
       check cD (cG', Total.shift cIH) total_decs e (tau,t);
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Let " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
       let (_ , tau', t') = syn cD (cG,cIH) total_decs i in
       let (tau', t') =  C.cwhnfCTyp (tau',t') in
       begin match (tau',t') with
       | (TypCross (_, tau1, tau2), t') ->
          let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'), false)), CTypDecl (y, TypClo(tau2, t'), false)) in
          check cD (cG', (Total.shift (Total.shift cIH))) total_decs e (tau,t)
       | _ -> raise (Error.Violation "Case scrutinee not of product type")
       end

    | (Box (loc, cM), (TypBox (l, mT), t)) ->
       checkMetaObj cD cM mT t

    | Impossible (loc, i), (tau, t) ->
       dprintf
         begin fun p ->
         p.fmt "[syn] [impossible] @[<v>checking (supposedly) impossible expression@,\
                i = @[%a@]@,\
                at @[%a@]@]"
           P.(fmt_ppr_cmp_exp_syn cD cG l0) i
           Loc.print loc
         end;
       let _, tau_sc, t' = syn cD (cG, cIH) total_decs i in
       let tau_sc = Whnf.cnormCTyp (tau_sc, t') in
       dprintf
         begin fun p ->
         p.fmt "[syn] [impossible] @[<v>synthesized type for scrutinee@,\
                i = @[%a@]@,\
                tau_sc[t'] = @[%a@]@]"
           P.(fmt_ppr_cmp_exp_syn cD cG l0) i
           P.(fmt_ppr_cmp_typ cD l0) tau_sc
         end;
       let total_pragma, tau_sc, projOpt =
         match i, tau_sc with
         | AnnBox ((l, mC), _), TypBox (loc, mT) ->
            dprint (fun _ -> "[syn] [impossible] we are splitting on a meta-object");
            let k, mT, projOpt = fixParamTyp mC (Whnf.cnormMTyp (mT, C.m_id)) in
            ( decide_ind_maybe (l, mC) k
            , TypBox (loc, mT)
            , projOpt
            )
         | _, _ ->
            dprint (fun _ -> "[syn] [impossible] we are splitting on a comp object");
            DataObj, tau_sc, None
       in
       if not (Coverage.is_impossible cD tau_sc) then
         throw loc (NotImpossible (cD, cG, tau_sc, i));

       dprintf
         begin fun p ->
         p.fmt "[syn] [impossible] passed at %a"
           Loc.print loc
         end

    | (Case (loc, prag, (AnnBox ((l, cM), mT) as i), branches), (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
         let (k, mT, projOpt) = fixParamTyp cM (Whnf.cnormMTyp (mT, C.m_id)) in
         ( Maybe.(get_default (IndexObj (l, cM)) (k $> decide_ind (l, cM)))
         , TypBox (loc, mT)
         , projOpt
         )
       in
       let _  = LF.checkMetaObj cD (loc,cM) (mT, C.m_id)  in

       (* Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau) ("Case 1" ^ " " ^ Pretty.Int.DefaultPrinter.expChkToString cD cG e); *)

       (* Instead of None, we can give (l, mT) in order to start the
          coverage checker out with the current LF normal term.
          However, this causes some tests to fail, so we leave it out.
          Theoretically, this improves the coverage checker by
          allowing to consider more cases as covering, especially in
          situations with nested cases.
        *)
       let problem = Coverage.make loc prag cD branches tau_sc None in
       (* Coverage.stage problem; *)
       checkBranches total_pragma cD (cG,cIH) total_decs
         (i, branches)
         (TypBox (Syntax.Loc.ghost, mT))
         (tau, t);
       Coverage.process problem projOpt

    | (Case (loc, prag, i, branches), (tau, t)) ->
       let chkBranch total_pragma cD (cG, cIH) i branches (tau,t) =
         let (_ , tau', t') = syn cD (cG,cIH) total_decs i in
         let tau_s = C.cnormCTyp (tau', t') in
         let problem =
           Coverage.make loc prag cD branches (Whnf.cnormCTyp (tau',t')) None
         in
         checkBranches total_pragma cD (cG,cIH) total_decs (i, branches) tau_s (tau,t);
         Coverage.process problem None
       in
       if Misc.List.nonempty total_decs then
         (match i with
          | Var (_, x)  ->
             let (f,tau', wf_tag) = lookup cG x in
             (* let _ = print_string ("\nTotality checking enabled - encountered " ^ P.expSynToString cD cG i ^
                " with type " ^ P.compTypToString cD tau' ^ "\n") in*)
             let ind = match Whnf.cnormCTyp (tau', Whnf.m_id) with
               | TypInd _tau -> ( (*print_string ("Encountered Var " ^
                                    P.expSynToString cD cG i ^ " -        INDUCTIVE\n");*)  true)
               | _ -> ((* print_string ("Encountered Var " ^
                          P.expSynToString cD cG i ^ " -        NON-INDUCTIVE\n");*) false) in
             if ind || wf_tag then
               chkBranch IndDataObj cD (cG,cIH) i branches (tau,t)
             else
               chkBranch DataObj cD (cG,cIH) i branches (tau,t)
          | _ -> chkBranch DataObj cD (cG,cIH) i branches (tau,t)
         )
       else
         chkBranch DataObj cD (cG,cIH) i branches (tau,t)

    | (Syn (loc, i), (tau, t)) ->
       let _ = dprint (fun () -> "check --> syn") in
       let (_, tau',t') = syn cD (cG,cIH) total_decs i in
       let (tau',t') = Whnf.cwhnfCTyp (tau',t') in
       let tau' = Whnf.cnormCTyp (tau', t') in
       let tau = Whnf.cnormCTyp (tau, t) in
       if C.convCTyp (tau, Whnf.m_id)  (tau', Whnf.m_id) then
         Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
           ("Syn " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e)
       else
         raise (Error (loc, MismatchChk (cD, cG, e, (tau,t), (tau',t'))))

    | (Hole (loc, id, name), (tau, t)) ->
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ttau)
         ("Hole " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e);
       let open Holes in
       match get (by_id id) with
       | None ->
          let info = { Holes.cG; compGoal = (tau, t); compSolution = None } in
          let h = { Holes.loc ; name ; cD ; info } in
          let h = Holes.Exists (Holes.CompInfo, h) in
          Holes.assign id h
       | Some (_, (Exists (w, h))) ->
          match w with
          | LFInfo ->
             Error.violation "wrong hole kind"
          | CompInfo ->
             let { compSolution; compGoal; _ } = h.info in
             if not (Whnf.convCTyp compGoal (tau, t)) then
               Error.violation "mismatched hole type";
             match compSolution with
             | None -> ()
             | Some e -> checkW cD (cG, cIH) total_decs e (tau, t)

  and check cD (cG, cIH) total_decs e (tau, t) =
    dprintf
      begin fun p ->
      p.fmt "[check] %a against %a |- %a"
        (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e
        (P.fmt_ppr_lf_mctx P.l0) cD
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau, t))
      end;
    checkW cD (cG, cIH) total_decs e (C.cwhnfCTyp (tau, t));

  and syn cD (cG,cIH) total_decs e : (gctx option * typ * I.msub) = match e with
    | Var (loc, x)   ->
       let (f,tau', _) = lookup cG x in
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD (tau', C.m_id))
         ("Var " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);

       (* We need to strip the type of any variable here because check
          works with annotated types in general. So variables would
          get introduced with a star-type, but just one level deep. *)
       let tau =
         match Whnf.cnormCTyp (tau', Whnf.m_id) with
         | TypInd tau -> tau
         | _ -> tau'
       in
       (None, tau, C.m_id)

    | DataConst (loc, c) ->
       (Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((CompConst.get c).CompConst.typ, C.m_id))
          ("DataConst " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);
        (None,(CompConst.get c).CompConst.typ, C.m_id))

    | Obs (loc, e, t, obs) ->
       let tau0 = (CompDest.get obs).CompDest.obs_type in
       let tau1 = (CompDest.get obs).CompDest.return_type in
       check cD (cG, cIH) total_decs e (tau0, t);
       (None, tau1, t)

    (* | DataDest (loc, c) -> *)
    (*     (dprint (fun () -> "DataDest ... "); *)
    (*     (None,(CompDest.get c).CompDest.typ, C.m_id)) *)

    | Const (loc,prog) ->
       Typeinfo.Comp.add loc (Typeinfo.Comp.mk_entry cD ((Comp.get prog).Comp.typ, C.m_id))
         ("Const " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);
       let e = Comp.get prog in
       let tau = Comp.(e.typ) in
       (* First we need to decide whether we are calling a function in
          the current mutual block. *)
       begin match Total.lookup_dec e.Comp.name total_decs with
       | None -> (* No, we aren't. *)
          (None, tau, C.m_id)
       | Some d -> (* Yes we are, and d is its total dec *)
          (* Second, need to check whether the function we're calling
             actually requires totality checking. *)
          match option_of_total_dec_kind d.order with
          | None -> (* No, it doesn't. *)
             (None, tau, C.m_id)
          | Some _ -> (* yes, it actually requires totality checking *)
             Some cIH, tau, C.m_id
       end

    | Apply (loc , e1, e2) ->
       let (cIH_opt , tau1, t1) = syn cD (cG,cIH) total_decs e1 in
       let (tau1,t1) = C.cwhnfCTyp (tau1,t1) in
       begin match (tau1, t1) with
       | (TypArr (_, tau2, tau), t) ->
          check cD (cG,cIH) total_decs e2 (tau2, t);
          Typeinfo.Comp.add
            loc
            (Typeinfo.Comp.mk_entry cD (tau, t))
            ("Apply " ^ Fmt.stringify (P.fmt_ppr_cmp_exp_syn cD cG P.l0) e);
          (useIH loc cD cG cIH_opt e2, tau, t)

       | (tau, t) ->
          raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau,t))))
       end

    | MApp (loc, e, mC) ->
       let (cIH_opt, tau1, t1) = syn cD (cG, cIH) total_decs e in
       begin match (C.cwhnfCTyp (tau1,t1)) with
       | (TypPiBox (_, (I.Decl (_ , ctyp, _)), tau), t) ->
          LF.checkMetaObj cD mC (ctyp, t);
          dprintf
            (fun p ->
              let open Maybe in
              let _ =
                cIH_opt
                $> fun cIH ->
                   p.fmt "[syn] [MApp] @[<v>cIH = @[%a@]@]"
                     (Total.fmt_ppr_ihctx cD cG) cIH
              in
              ()
            );
          (useIH loc cD cG cIH_opt (Box (loc, mC)), tau, I.MDot(metaObjToMFront mC, t))
       | (tau, t) ->
          raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau,t))))
       end

    | PairVal (loc, i1, i2) ->
       let (_, tau1,t1) =  syn cD (cG,cIH) total_decs i1 in
       let (_, tau2,t2) =  syn cD (cG,cIH) total_decs i2 in
       let (tau1,t1)    = C.cwhnfCTyp (tau1, t1) in
       let (tau2,t2)    = C.cwhnfCTyp (tau2, t2) in
       ( None
       , TypCross
           ( loc
           , TypClo (tau1,t1)
           , TypClo (tau2,t2))
       , C.m_id
       )

    | AnnBox (cM, cT) ->
       checkMetaObj cD cM cT C.m_id;
       (None, TypBox (getLoc cM, cT), C.m_id)

  (* and synObs cD csp ttau1 ttau2 = match (csp, ttau1, ttau2) with *)
  (*   | (CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) -> *)
  (*       if Whnf.convCTyp (tau1, theta) (tau', theta') then *)
  (*         (tau2, theta) *)
  (*       else *)
  (*         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta')))) *)
  (*   | (CopatApp (loc, dest, csp'), (TypArr (tau1, tau2), theta), (tau', theta')) -> *)
  (*       if Whnf.convCTyp (tau1, theta) (tau', theta') then *)
  (*         synObs cD csp' ((CompDest.get dest).CompDest.typ, Whnf.m_id) (tau2, theta) *)
  (*       else *)
  (*         raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta')))) *)

  and checkPattern cD cG pat ttau = match pat with
    | PatMetaObj (loc, mO) ->
       (match ttau with
        | (TypBox (_, ctyp) , theta) ->
           LF.checkMetaObj cD mO (ctyp, theta)
        | _ -> raise (Error (loc, BasicMismatch (`box, cD, I.Empty, ttau)))
       )
    | PatPair (loc, pat1, pat2) ->
       begin match ttau with
        | (TypCross (_, tau1, tau2), theta) ->
           checkPattern cD cG pat1 (tau1, theta);
           checkPattern cD cG pat2 (tau2, theta)
        | _ -> raise (Error (loc, BasicMismatch (`pair, cD, cG, ttau)))
       end

    | pat ->
       let (loc, ttau') = synPattern cD cG pat in
       let tau' = Whnf.cnormCTyp ttau' in
       let tau = Whnf.cnormCTyp ttau in
       let ttau' = (tau', Whnf.m_id) in
       let ttau = (tau, Whnf.m_id) in
       dprintf
         begin fun p ->
         p.fmt "[checkPattern] @[<v>Checking conv: @[%a@ ==@ %a@]@]"
           (P.fmt_ppr_cmp_typ cD P.l0) tau
           (P.fmt_ppr_cmp_typ cD P.l0) tau'
         end;
       if C.convCTyp ttau  ttau' then ()
       else
         raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat = match pat with
    | PatConst (loc, c, pat_spine) ->
       let tau = (CompConst.get c).CompConst.typ in
       (loc, synPatSpine cD cG pat_spine (tau , C.m_id))
    | PatVar (loc, k) -> (loc, (lookup' cG k, C.m_id))
    | PatAnn (loc, pat, tau) ->
       checkPattern cD cG pat (tau, C.m_id);
       (loc, (tau, C.m_id))

  and synPatSpine cD cG pat_spine (tau, theta) = match pat_spine with
    | PatNil  -> (tau, theta)
    | PatApp (_loc, pat, pat_spine)  ->
       begin match (tau, theta) with
       | (TypArr (_, tau1, tau2), theta) ->
          checkPattern cD cG pat (tau1, theta);
          synPatSpine cD cG pat_spine (tau2, theta)
       | (TypPiBox (_, cdecl, tau), theta) ->
          let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
          synPatSpine cD cG pat_spine (tau, theta')
       end
    | PatObs (loc, obs, t, pat_spine) ->
       dprintf
         begin fun p ->
         p.fmt "[synPatSpine] t = %a"
           (P.fmt_ppr_lf_msub cD P.l0) t
         end;
       let tau0 = (CompDest.get obs).CompDest.obs_type in
       let tau1 = (CompDest.get obs).CompDest.return_type in
       if Whnf.convCTyp (tau,theta) (tau0,t) then
         synPatSpine cD cG pat_spine (tau1, t)
       else
         raise (Error (loc, TypMismatch (cD, (tau,theta), (tau0,t))))

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    LF.checkMetaObj cD mO (ctyp, theta);
    I.MDot(metaObjToMFront mO, theta)

  and checkBranches caseTyp cD cG total_decs (i, branches) tau_s ttau =
    List.iter (fun branch -> checkBranch caseTyp cD cG total_decs (i, branch) tau_s ttau) branches

  and checkBranch caseTyp cD (cG, cIH) total_decs (i, branch) tau_s (tau, t) =
    match branch with
    | Branch (loc, cD1', _cG, PatMetaObj (loc', mO), t1, e1) ->
       dprintf
         begin fun p ->
           p.fmt "[checkBranch] @[<v>with meta-obj pattern: @[%a@]@,\
                  where scrutinee has type @[%a@]@]"
             (P.fmt_ppr_cmp_meta_obj cD1' P.l0) mO
             (P.fmt_ppr_cmp_typ cD P.l0) tau_s
         end;
       let TypBox (_, mT) = tau_s in
       (* By invariant: cD1' |- t1 <= cD *)
       let mT1   = Whnf.cnormMTyp (mT, t1) in
       let cG'   = Whnf.cnormCtx (Whnf.normCtx cG, t1) in
       let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
       let t''   = Whnf.mcomp t t1 in
       let tau'  = Whnf.cnormCTyp (tau, t'') in
       let (cD1',cIH')  =
         if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (loc', mO))
         then
           (* marks in the context as inductive all mvars appearing in
              the pattern *)
           let cD1' = mvars_in_patt cD1' (PatMetaObj (loc', mO)) in
           ( cD1'
           (* ^ cD is the outer meta-context; cD1' is the refined
              meta-context + induction marks;
              t1 is the refinement substitution that relates cD to cD1'.
            *)
           , Total.wf_rec_calls cD1' I.Empty total_decs
           )
         else (cD1', I.Empty)
       in
       let cD1' = id_map_ind cD1' t1 cD in
       let cIH0' = Total.wf_rec_calls cD1' cG' total_decs in
       LF.checkMSub loc cD1' t1 cD;
       LF.checkMetaObj cD1' mO (mT1, C.m_id);
       check cD1' (cG', Context.append cIH (Context.append cIH0' cIH')) total_decs e1 (tau', Whnf.m_id)

    | Branch (loc, cD1', cG1, pat, t1, e1) ->
       let tau_p = Whnf.cnormCTyp (tau_s, t1) in
       let cG'   = Whnf.cnormCtx (cG, t1) in
       let cIH   = Whnf.cnormCtx (Whnf.normCtx cIH, t1) in
       let t''   = Whnf.mcomp t t1 in
       let tau'  = Whnf.cnormCTyp (tau, t'') in
       dprintf
         begin fun p ->
         p.fmt "[checkBranch] @[<v>at %a with general pattern@,\
                @[%a@]@,\
                where scrutinee has type @[%a@]@]"
           Syntax.Loc.print_short loc
           (P.fmt_ppr_cmp_pattern cD1' cG P.l0) pat
           (P.fmt_ppr_cmp_typ cD P.l0) tau_s
         end;
       let k     = Context.length cG1 in
       let cIH0  = Total.shiftIH cIH k in
       let (cD1', cG1', cIH') =
         if is_inductive caseTyp && Total.struct_smaller pat
         then
           let cG1' = Total.mark_gctx cG1 in
           let cD1' = mvars_in_patt cD1' pat in
           ( cD1'
           , cG1'
           , Total.wf_rec_calls cD1' cG1' total_decs
           )
         else (cD1', cG1, I.Empty)
       in
       let cIH0' = Total.shiftIH (Total.wf_rec_calls cD1' cG' total_decs) k in
       dprintf
         begin fun p ->
         match cIH0' with
         | I.Empty -> ()
         | _ ->
            p.fmt "[checkBranch] @[<v>generated IH from previous cG = @[%a@]@,\
                   cIH0' = @[%a@]@]"
              (P.fmt_ppr_cmp_gctx cD1' P.l0) cG'
              (Total.fmt_ppr_ihctx cD1' (Context.append cG' cG1')) cIH0'
         end;

       let cD1' =
         if Misc.List.null total_decs
         then cD1'
         else id_map_ind cD1' t1 cD
       in

       LF.checkMSub loc  cD1' t1 cD;
       checkPattern cD1' cG1' pat (tau_p, Whnf.m_id);
       check
         cD1'
         ( Context.append cG' cG1'
         , Context.append cIH0 (Context.append cIH0' cIH')
         )
         total_decs
         e1
         (tau', Whnf.m_id)

  and checkFBranches cD ((cG , cIH) : ctyp_decl I.ctx * ctyp_decl I.ctx) total_decs fbr ttau = match fbr with
    | NilFBranch _ -> ()
    | ConsFBranch (_, (cD', cG', patS, e), fbr') ->
       let (tau2', t') = synPatSpine cD' cG' patS ttau in
       dprintf
         begin fun p ->
         p.fmt "[checkFBranches] tau2' = @[%a@]"
           (P.fmt_ppr_cmp_typ cD' P.l0) (Whnf.cnormCTyp (tau2', t'))
         end;
       check cD' (cG', (Total.shift cIH)) total_decs e (tau2', t');
       checkFBranches cD (cG, cIH) total_decs fbr' ttau
  let rec wf_mctx cD = match cD with
    | I.Empty -> ()
    | I.Dec (cD, cdecl) ->
       (wf_mctx cD ; checkCDecl cD cdecl)

  (* takes a normalised tau, peels off assumptions, and returns a triple (cD', cG', tau') *)
  let rec unroll cD cG tau =
    match tau with
    | TypPiBox (_, c_decl, tau') ->
       (* TODO ensure c_decl name is unique in context *)
       let cD' = Syntax.Int.LF.Dec (cD, c_decl) in
       unroll cD' cG tau'
    | TypArr (_, t1, t2) ->
       (* TODO use contextual name generation *)
       let name = Id.mk_name Id.NoName in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDecl (name, t1, false)) in
       unroll cD cG' t2
    | _ -> (cD, cG, tau)

  let rec proof cD cG cIH total_decs p ttau =
    match p with
    | Incomplete g ->
       (* TODO check that g matches the current proof state *)
       (* TODO add g to a store of proof holes *)
       ()
    | Command (cmd, p') ->
        begin match cmd with
        | By (i_kind, e_syn, name, tau, bty) ->
           let (_, tau, m_sub) = syn cD (cG, cIH) total_decs e_syn in
           let tau' = Whnf.cnormCTyp (tau, m_sub) in
           let cG' = I.(Dec (cG, CTypDecl (name, tau', false))) in
           proof cD cG' cIH total_decs p' ttau
        | Unbox (_, name, mT) ->
           let cD' = I.(Dec (cD, Decl (name, mT, No))) in
           proof cD' cG cIH total_decs p' ttau
        end
    | Directive d ->
       directive cD cG cIH total_decs d ttau

  and directive cD cG cIH total_decs (d : directive) ttau =
    match d with
    | Intros (Hypothetical (h, p)) ->
       let tau = Whnf.cnormCTyp ttau in
       let (cD', cG', tau') = unroll cD cG tau in
       (* TODO check that cD and cG are convertible with cD' and cG' *)
       proof cD' cG' cIH total_decs p (tau', Whnf.m_id)

    | Solve e_chk ->
       check cD (cG, cIH) total_decs e_chk ttau

    | ContextSplit (i, tau, bs) ->
       assert false

    | MetaSplit (i, tau, bs) ->
        let handle_branch (SplitBranch ((cD, head), (Hypothetical (h, p_i)))) =
          ()
        in
        List.iter handle_branch bs;
        assert false

    | CompSplit (i, tau, bs) ->
        let handle_branch (SplitBranch (cid, (Hypothetical (h, p_i)))) =
          ()
        in
        List.iter handle_branch bs;
        assert false

  let syn cD cG (total_decs : total_dec list) ?cIH:(cIH = Syntax.Int.LF.Empty) e =
    let cIH, tau, ms = syn cD (cG,cIH) total_decs e in
    cIH, (tau, ms)

  let check cD cG (total_decs : total_dec list) ?cIH:(cIH = Syntax.Int.LF.Empty) e ttau =
    check cD (cG,cIH) total_decs e ttau

  let thm cD cG total_decs ?cIH:(cIH = Syntax.Int.LF.Empty) t ttau =
    match t with
    | Syntax.Int.Comp.Program e -> check cD cG total_decs ~cIH: cIH e ttau
    | Syntax.Int.Comp.Proof p -> proof cD cG cIH total_decs p ttau

end
