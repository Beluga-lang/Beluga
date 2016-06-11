module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
(* open Printf *)

(* exception AnnotError of string *)

(* let (dprint, _) = Debug.makeFunctions (Debug.toFlags [5]) *)

module PrettyAnn = struct

  open Annotated
  open Format

  module R = Store.Cid.DefaultRenderer
  module R' = Store.Cid.NamedRenderer

  let print_tstr tstr =
    match tstr with
    | None -> ""
    | Some str -> str

  let rec phatToDCtx phat = match phat with
    | (None,      0) -> Syntax.Int.LF.Null
    | (Some psi , 0) -> Syntax.Int.LF.CtxVar psi
    | (ctx_v    , k) ->
       Syntax.Int.LF.DDec (phatToDCtx (ctx_v, k-1), Syntax.Int.LF.TypDeclOpt (Id.mk_name Id.NoName))

  let rec _get_names_dctx : Syntax.Int.LF.dctx -> Id.name list = function
    | Syntax.Int.LF.Null -> []
    | Syntax.Int.LF.CtxVar psi -> []
    | Syntax.Int.LF.DDec (cPsi', Syntax.Int.LF.TypDecl (n, _))
    | Syntax.Int.LF.DDec (cPsi', Syntax.Int.LF.TypDeclOpt n) -> n :: _get_names_dctx cPsi'

  let rec get_names_mctx : Syntax.Int.LF.mctx -> Id.name list = function
    | Syntax.Int.LF.Empty -> []
    | Syntax.Int.LF.Dec (cD', Syntax.Int.LF.Decl (n, _, _))
    | Syntax.Int.LF.Dec (cD', Syntax.Int.LF.DeclOpt n) -> n :: get_names_mctx cD'

  let rec get_names_gctx : Syntax.Int.Comp.gctx -> Id.name list = function
    | Syntax.Int.LF.Empty -> []
    | Syntax.Int.LF.Dec (cG', Syntax.Int.Comp.WfRec (n, _, _))
    | Syntax.Int.LF.Dec (cG', Syntax.Int.Comp.CTypDecl (n, _))
    | Syntax.Int.LF.Dec (cG', Syntax.Int.Comp.CTypDeclOpt n) -> n :: get_names_gctx cG'

  let fresh_name_dctx (cPsi : Syntax.Int.LF.dctx) : Id.name -> Id.name =
    Id.gen_fresh_name (_get_names_dctx cPsi)
  let fresh_name_mctx (cD : Syntax.Int.LF.mctx) : Id.name -> Id.name =
    Id.gen_fresh_name (get_names_mctx cD)
  let fresh_name_gctx (cG : Syntax.Int.Comp.gctx) : Id.name -> Id.name  =
    Id.gen_fresh_name (get_names_gctx cG)

  let rec expChkToString cD cG e =
    match e with
    | Comp.Rec (_, x, e, _, tstr) ->
       let x = fresh_name_gctx cG x in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x) in
       sprintf "{Rec|rec %s =>@ %s%s}"
	       (Id.render_name x)
	       (expChkToString cD cG' e)
	       (print_tstr tstr)
    | Comp.Fun (_, x, e, _, tstr) ->
       let x = fresh_name_gctx cG x in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x) in
       sprintf "{Fun|fn %s =>@ %s%s}"
	       (Id.render_name x)
	       (expChkToString cD cG' e)
	       (print_tstr tstr)
    | Comp.MLam (_, u, e, _, tstr) ->
       let u = fresh_name_mctx cD u in
       let cD' = Syntax.Int.LF.Dec (cD, Syntax.Int.LF.DeclOpt u) in
       let cG' = Whnf.cnormCtx (cG, Syntax.Int.LF.MShift 1) in
       sprintf "{MLam|mlam %s =>@ %s%s}"
	       (Id.render_name u)
	       (expChkToString cD' cG' e)
	       (print_tstr tstr)
    | Comp.Pair (_, e1, e2, _, tstr) ->
       sprintf "{Pair|(%s, %s)%s}"
	       (expChkToString cD cG e1)
	       (expChkToString cD cG e2)
	       (print_tstr tstr)
    | Comp.LetPair (_, i, (x, y, e), _, tstr) ->
       let x = fresh_name_gctx cG x in
       let y = fresh_name_gctx cG y in
       let cG' = Syntax.Int.LF.Dec (Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x),
				    Syntax.Int.Comp.CTypDeclOpt y) in
       sprintf "{LetPair|@[<2>let <%s, %s> = %s@ in %s@]%s}"
	       (Id.render_name x)
	       (Id.render_name y)
	       (expSynToString cD cG i)
	       (expChkToString cD cG' e)
	       (print_tstr tstr)
    | Comp.Let (_, i, (x, e), _, tstr) ->
       let x = fresh_name_gctx cG x in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x) in
       sprintf "{Let|@[<2>let %s = %s@ in %s@]%s}"
	       (Id.render_name x)
	       (expSynToString cD cG i)
	       (expChkToString cD cG' e)
	       (print_tstr tstr)
    (*| Comp.Box (_, cM, _, tstr) ->
       sprintf "{Box| %s%s}"
	       (metaObjToString cD cM)
	       (print_tstr tstr)*)
    | Comp.Box (_, cM, _, tstr) ->
       sprintf "$%s$"
         (metaObjToString cD cM)
    | Comp.Case (_, prag, i, bs, _, tstr) ->
       sprintf "{Case|@[<v> case @[%s@] of %s %s @]@,%s}"
	       (expSynToString cD cG i)
	       (match prag with Pragma.RegularCase -> " " | Pragma.PragmaNotCase -> " %not ")
	       (branchesToString cD cG bs)
	       (print_tstr tstr)
    | Comp.Syn (_, i, _, tstr) ->
       sprintf "{Syn|%s%s}"
	       (expSynToString cD cG i)
	       (print_tstr tstr)
    | Comp.If (_, i, e1, e2, _, tstr) ->
       sprintf "{If|@[<2>if %s@[<-1>then %s @]else %s@]%s}"
	       (expSynToString cD cG i)
	       (expChkToString cD cG e1)
	       (expChkToString cD cG e2)
	       (print_tstr tstr)
    | Comp.Hole (_, f, _, tstr) ->
       let x = f () in
       sprintf "{Hole| ? { %d }%s}"
	       x
	       (print_tstr tstr)

  and expSynToString cD cG i =
    match i with

    (* Comp.Var (_, x, _, tstr) ->
       sprintf "{Var|%s%s}"
	       (R.render_var cG x)
	       (print_tstr tstr)*)
    | Comp.Var (_, x, _, tstr) ->
       sprintf "%s"
         (R'.render_var_latex cG x)
    | Comp.Const (_, prog, _, tstr) ->
       sprintf "{Const|%s%s}"
	       (R.render_cid_prog prog)
	       (print_tstr tstr)
    | Comp.DataConst (_, c, _, tstr) ->
       sprintf "{DataConst|%s%s}"
	       (R.render_cid_comp_const c)
	       (print_tstr tstr)
    | Comp.DataDest (_, c, _, tstr) ->
       sprintf "{DataDest|%s%s}"
	       (R.render_cid_comp_dest c)
	       (print_tstr tstr)
    (*| Comp.Apply (_, i, e, _, tstr) ->
       sprintf "{Apply|%s %s%s}"
	       (expSynToString cD cG i)
	       (expChkToString cD cG e)
	       (print_tstr tstr)*)
    | Comp.Apply (_, i, e, _, tstr) ->
       sprintf "%s %s"
         (expSynToString cD cG i)
         (expChkToString cD cG e)
    | Comp.MApp (_, i, mC, _, tstr) ->
       sprintf "{MApp|%s $%s$%s}"
	       (expSynToString cD cG i)
	       (metaObjToString cD mC)
	       (print_tstr tstr)
    | Comp.PairVal (_, i1, i2, _, tstr) ->
       sprintf "{PairVal|(%s, %s)%s}"
	       (expSynToString cD cG i1)
	       (expSynToString cD cG i2)
	       (print_tstr tstr)
    | Comp.Ann (e, _, _, tstr) ->
       sprintf "{Ann|%s%s}"
	       (expChkToString cD cG e)
	       (print_tstr tstr)
    | Comp.Equal (_, i1, i2, _, tstr) ->
       sprintf "{Equal|%s == %s%s}"
	       (expSynToString cD cG i1)
	       (expSynToString cD cG i2)
	       (print_tstr tstr)
    | Comp.Boolean (b, _, tstr) ->
       sprintf "{Boolean|%s%s}"
	       (if b then "ttrue" else "ffalse")
	       (print_tstr tstr)

  and metaObjToString cD (loc, mO) = match mO with
    | LF.CObj cPsi ->
       sprintf "[%s]" (dctxToString cD cPsi)
    | LF.ClObj (phat, tM) ->
       let cPsi = phatToDCtx phat in
         sprintf "[%s \\entails %s]"
          (psiHatToString cD cPsi)
          (clobjToString cD cPsi tM)
    | LF.MV k ->
       sprintf "%s" (R'.render_cvar cD k)

  (* we work with Syntax.Int.LF.dctx *)
  and dctxToString cD cPsi =
    P.fmt_ppr_lf_dctx cD Pretty.std_lvl str_formatter cPsi
    ; flush_str_formatter ()

  (* we work with Syntax.Int.LF.psi_hat *)
  and psiHatToString cD cPsi =
    P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl str_formatter cPsi
    ; flush_str_formatter ()


  and clobjToString cD cPsi tM = match tM with
    | LF.MObj m -> normalToString cD cPsi m
    | LF.SObj s -> subToString cD cPsi s
    | LF.PObj h -> headToString cD cPsi "" h

  and normalToString cD cPsi m =
    (*let rec dropSpineLeft ms n = match (ms, n) with
      | (_, 0) -> ms
      | (LF.Nil, _) -> ms
      | (LF.App (m, rest, str), n) -> dropSpineLeft rest (n - 1)
    in 
    let deimplicitize_spine h ms = match h with
      | Syntax.Int.LF.Const c ->
        let implicit_arguments = Store.Cid.Term.get_implicit_arguments c in
         dropSpineLeft ms implicit_arguments
      | Syntax.Int.LF.MVar _
      | Syntax.Int.LF.BVar _
      | Syntax.Int.LF.PVar _
      | Syntax.Int.LF.FMVar _
      | Syntax.Int.LF.FPVar _
      | Syntax.Int.LF.Proj _
      | Syntax.Int.LF.FVar _
      | Syntax.Int.LF.AnnH _ ->
         ms
     in*) 
     match m with
       | LF.Lam (_, x, m, str1, tclo, str2) ->
          let x = fresh_name_dctx cPsi x in
            sprintf "{\\lambda %s. %s}" 
             (Id.render_name_latex x) 
             (normalToString cD (Syntax.Int.LF.DDec(cPsi, Syntax.Int.LF.TypDeclOpt x)) m)
       | LF.LFHole _ -> "?"
       | LF.Tuple (_, tuple, _, _, _) ->
          sprintf "{<%s>}"
           (tupleToString cD cPsi tuple)
       | LF.Root (_, h, LF.Nil, str1, tclo, str2) ->
          sprintf "{%s}"
           (* call head with "": no space in LaTex *)
           (headToString cD cPsi "" h)
       | LF.Root (_, h, ms, str1, tclo, str2) ->
          (*let ms = deimplicitize_spine h ms in*)
           sprintf "{%s %s}"
            (* call head with "~": space in LaTex *)
            (headToString cD cPsi "~" h)
            (spineToString cD cPsi ms)
       | LF.Clo(tM, s) -> 
          (* don't want to implement Whnf.norm for Annotated.normal *)
          (*normalToString cD cPsi (Whnf.norm (tM, s))*)
          "Clo"


  and tupleToString cD cPsi tuple =
    "tuple"

  and subToString cD cPSi s =
    "sub"

  (* we work with Syntax.Int.LF.head *)
  and headToString cD cPsi tilde h = 
    P.fmt_ppr_lf_head_latex cD cPsi Pretty.std_lvl tilde str_formatter h
    ; flush_str_formatter ()
    
  and spineToString cD cPsi ms = match ms with
    | LF.Nil -> ""
    | LF.App (m, LF.Nil, str) ->
       sprintf "%s"
        (normalToString cD cPsi m)
    | LF.App (m, ms, str) ->
       sprintf "%s %s"
        (normalToString cD cPsi m)
        (spineToString cD cPsi ms)
    
  and branchesToString cD cG bs =
    match bs with
    | [] -> ""
    | b :: [] -> sprintf "%s" (branchToString cD cG b)
    | b :: bs -> sprintf "%s%s" (branchToString cD cG b) (branchesToString cD cG bs)

  and branchToString cD cG b =
    match b with
    | Comp.EmptyBranch (_, cD1, pat, _) ->
       sprintf "@ {EmptyBranch|@ @[<v2>| @[<v0> @[%s@] @] @]}"
	       (patternToString cD1 Syntax.Int.LF.Empty pat)
    | Comp.Branch (_, cD1', _cG, Comp.PatMetaObj (_, mO, _, _), _, e) ->
       sprintf "@ {Branch|@[<v2>| @[<v0>@[%s@] => @]@ @[<2> %s@]@]}@ "
	       (metaObjToString cD1' mO)
	       (expChkToString cD1' cG e)
    | Comp.Branch (_, cD1', cG', pat, _, e) ->
       let cG_t = cG in
       let cG_ext = Context.append cG_t cG' in
       sprintf "@ {Branch|@[<v2>| @[<v0> @[ |- %s  @]  => @]@ @[<2>@ %s@]@]}@ "
	       (patternToString cD1' cG' pat)
	       (expChkToString cD1' cG_ext e)

  and patternToString cD cG pat = "{pattern|Unsupported}"
end

module LF = struct
  open Context
  open Store.Cid
  open Syntax.Int.LF

  module Unify = Unify.EmptyTrail

  module C = Whnf
  module Ann = Annotated

  type error =
    (* | CtxVarMisCheck   of mctx * dctx * tclo * schema *)
    (* | CtxVarMismatch   of mctx * ctx_var * schema *)
    (* | CtxVarDiffer     of mctx * ctx_var * ctx_var *)
    | CheckError       of mctx * dctx * nclo * tclo
    | TupleArity       of mctx * dctx * nclo * trec_clo
    (* | SigmaMismatch    of mctx * dctx * trec_clo * trec_clo *)
    (* | KindMismatch     of mctx * dctx * sclo * (kind * sub) *)
    | TypMismatch      of mctx * dctx * nclo * tclo * tclo
    | IllTypedSub      of mctx * dctx * sub * dctx
    | SpineIllTyped    of int * int
    | LeftoverFV
    (* | ParamVarInst     of mctx * dctx * tclo *)
    | CtxHatMismatch   of mctx * dctx (* expected *) * psi_hat (* found *) * (Syntax.Loc.t * mfront)
    | IllTypedMetaObj  of mctx * clobj * dctx * cltyp
    | TermWhenVar      of mctx * dctx * normal
    | SubWhenRen       of mctx * dctx * sub

  exception Error of Syntax.Loc.t * error
  let _ = Error.register_printer
	    (fun (Error (loc, err)) ->
	     Error.print_with_location
	       loc (fun ppf ->
		    match err with
		    (* | ParamVarInst (cD, cPsi, sA) -> *)
		    (*       Format.fprintf ppf "Parameter variable of type %a does not appear as a declaration in context %a. @ @ It may be that no parameter variable of this type exists in the context or the type of the parameter variable is a projection of a declaration in the context." *)
		    (*         (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA) *)
		    (*         (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi *)

		    (* | CtxVarMisCheck (c0, cPsi, sA, sEl ) -> *)
		    (*       Format.fprintf ppf "Type %a doesn't check against schema %a." *)
		    (*          (P.fmt_ppr_lf_typ c0 cPsi Pretty.std_lvl) (Whnf.normTyp sA) *)
		    (*          (P.fmt_ppr_lf_schema Pretty.std_lvl) sEl *)

		    (* | CtxVarMismatch (cO, var, expected) -> *)
		    (*     Format.fprintf ppf "Context variable %a doesn't check against schema %a." *)
		    (*       (P.fmt_ppr_lf_ctx_var cO) var *)
		    (*       (P.fmt_ppr_lf_schema Pretty.std_lvl) expected *)

		    (* | CtxVarDiffer (cO, var, var1) -> *)
		    (*     Format.fprintf ppf "Context variable %a not equal to %a." *)
		    (*       (P.fmt_ppr_lf_ctx_var cO) var *)
		    (*       (P.fmt_ppr_lf_ctx_var cO) var1 *)

		    | CheckError (cD, cPsi, sM, sA) ->
			Format.fprintf ppf
			    "Expression %a does not check against %a."
	    (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) (Whnf.norm sM)
			    (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)

		    (* | SigmaMismatch (cD, cPsi, sArec, sBrec) -> *)
		    (*   Error.report_mismatch ppf *)
		    (*	  "Sigma type mismatch." *)
		    (*	  "Expected type" (P.fmt_ppr_lf_typ_rec cD cPsi Pretty.std_lvl) (Whnf.normTypRec sArec) *)
		    (*	  "Actual type"   (P.fmt_ppr_lf_typ_rec cD cPsi Pretty.std_lvl) (Whnf.normTypRec sBrec) *)

		    | TupleArity (cD, cPsi, sM, sA) ->
			Error.report_mismatch ppf
			  "Arity of tuple doesn't match type."
			  "Tuple" (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl)  (Whnf.norm sM)
			  "Type"  (P.fmt_ppr_lf_typ_rec cD cPsi Pretty.std_lvl) (Whnf.normTypRec sA)

		    (* | KindMismatch (cD, cPsi, sS, sK) -> *)
		    (*	Error.report_mismatch ppf *)
		    (*     "Ill-kinded type." *)
		    (*	  "Expected kind:" Format.pp_print_string                      (P.kindToString cPsi sK) *)
		    (*	  "for spine:"     (P.fmt_ppr_lf_spine cD cPsi Pretty.std_lvl) (Whnf.normSpine sS) *)

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

  let mk_tstr cD cPsi sA =
    if !Typeinfo.generate_annotations then
      Some (P.typToString cD cPsi sA)
    else
      None

  let mk_nstr cD cPsi sM =
    Some (P.normalToString cD cPsi sM)

  let rec annotateMetaObj cD (loc, cM) cTt =
    match (cM, cTt) with
    | (CObj cPsi, (CTyp (Some w), _)) ->
       (loc, Ann.LF.CObj cPsi)
    | (ClObj (phat, tM), (ClTyp (tp, cPsi), t)) ->
       let cPsi' = C.cnormDCtx (cPsi, t) in
       if phat = Context.dctxToHat cPsi' then
	 let tM' = annotateClObj cD loc cPsi' tM (tp, t) in
	 (loc, Ann.LF.ClObj (phat, tM'))
       else
	 raise (Error (loc, CtxHatMismatch (cD, cPsi, phat, (loc, cM))))
    | (MV u, (mtyp1, t)) ->
       let mtyp1 = C.cnormMTyp (mtyp1, t) in
       let (_, mtyp2) = C.mctxLookup cD u in
       if C.convMTyp mtyp1 mtyp2 then
	 (loc, Ann.LF.MV u)
       else
	 raise (Error.Violation ("Contextual substitution ill-typed"))

  and annotateClObj cD loc cPsi' cM cTt =
    match (cM, cTt) with
    | (MObj tM, (MTyp tA, t)) ->
       let tM' =
	 ann cD cPsi' (tM, Substitution.LF.id) (C.cnormTyp (tA, t), Substitution.LF.id)
       in
       Ann.LF.MObj tM'
    | (SObj tM, (STyp (cl, tA), t)) ->
       let tM' = tM in
       Ann.LF.SObj tM'
    | (PObj h, (PTyp tA, t)) ->
       let (tA', h') = inferHead loc cD cPsi' h Ren in
       let tA = C.cnormTyp (tA, t) in
       if C.convTyp (tA, Substitution.LF.id) (tA', Substitution.LF.id) then
	 Ann.LF.PObj h'
       else
	 raise (Error (loc, (IllTypedMetaObj (cD, cM, cPsi', C.cnormClTyp cTt))))
    | (MObj (Root(l, h, Nil) as sM), (PTyp tA, t)) ->
       let (tA', h') = inferHead loc cD cPsi' h Ren in
       let tA = C.cnormTyp (tA, t) in
       if C.convTyp (tA, Substitution.LF.id) (tA', Substitution.LF.id) then
	 let sA = (tA, Substitution.LF.id) in
	 Ann.LF.MObj (Ann.LF.Root (l, h', Ann.LF.Nil, mk_nstr cD cPsi' (sM, Substitution.LF.id),
				   sA, mk_tstr cD cPsi' sA))
       else
	 raise (Error (loc, (IllTypedMetaObj (cD, cM, cPsi', C.cnormClTyp cTt))))
    | _, _ -> raise (Error (loc, (IllTypedMetaObj (cD, cM, cPsi', C.cnormClTyp cTt))))

  (* TODO Not actually necessary to return the head, fix this later *)
  and inferHead loc cD cPsi head cl =
    match head, cl with
    | BVar k', _ ->
       let (_, _l) = dctxToHat cPsi in
       let TypDecl (_, tA) = ctxDec cPsi k' in
       (tA, head)

    | Proj (tuple_head, target), _ ->
       let srecA =
	 match tuple_head with
	 | BVar k' ->
	    let TypDecl (_, Sigma recA) = ctxSigmaDec cPsi k' in
	    (recA, Substitution.LF.id)
	 | PVar (p, s) ->
	    let (_, Sigma recA, cPsi') = C.mctxPDec cD p in
	    (recA, s)
       in
       let (_tA, s) as sA = getType tuple_head srecA target 1 in
       (TClo sA, head)

    | Const c, Subst ->
       ((Term.get c).Term.typ, head)

    | MVar (Offset u, s), Subst ->
       (* cD ; cPsi' |- tA <= type *)
       let (_, tA, cPsi') = Whnf.mctxMDec cD u in
       (TClo (tA, s), head)

    | MVar (Inst (_n, {contents = None}, _cD, ClTyp (MTyp tA,cPsi'), _cnstr, _), s), Subst ->
       (TClo (tA, s), head)

    | MMVar (((_n, {contents = None}, cD' , ClTyp (MTyp tA,cPsi'), _cnstr, _) , t'), r), Subst ->
       (TClo(Whnf.cnormTyp (tA, t'), r), head)

    | Const _, Ren
    | MVar _, Ren
    | MMVar _, Ren -> raise (Error (loc, TermWhenVar (cD, cPsi, (Root (loc, head, Nil)))))

    | PVar (p, s), _ ->
       (* cD ; cPsi' |- tA <= type *)
       let (_, tA, cPsi') = Whnf.mctxPDec cD p in
       (TClo (tA, s), head)

    | FVar _, _ ->
       raise (Error (loc, LeftoverFV))

  and ann cD cPsi sM sA =
    (* print_string (sprintf "Assigned %s with type %s\n" *)
    (* 		 (P.normalToString cD cPsi sM) *)
    (* 		 (P.typToString cD cPsi sA)); *)
    ann' cD cPsi sM sA

  and ann' cD cPsi sM sA = match sM, sA with
    | (Lam (loc, name, tM), s1), (PiTyp ((TypDecl (_x, _tA) as tX, _), tB), s2) ->
       let tM' =
	 ann cD (DDec (cPsi, Substitution.LF.decSub tX s2))
	     (tM, Substitution.LF.dot1 s1) (tB, Substitution.LF.dot1 s2)
       in
       Ann.LF.Lam (loc, name, tM', mk_nstr cD cPsi sM, sA, mk_tstr cD cPsi sA)

    | ((Lam (loc, _, _), _), _) ->
       raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

    | ((Tuple (loc, tuple), s1), (Sigma typRec, s2)) ->
       let tuple' =
	 annTuple loc cD cPsi (tuple, s1) (typRec, s2)
       in
       Ann.LF.Tuple (loc, tuple', mk_nstr cD cPsi sM, sA, mk_tstr cD cPsi sA)

    | (Tuple (loc, _), _), _ ->
       raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

    | ((Root (loc, _h, _tS), _s), (Atom _, _s')) ->
       begin
	 let (sP, h', tS') = syn cD cPsi sM in
	 let (tP', tQ') = (C.normTyp sP, C.normTyp sA) in
	 if (C.convTyp (tP', Substitution.LF.id) (tQ', Substitution.LF.id)) then
	   Ann.LF.Root (loc, h', tS', mk_nstr cD cPsi sM, sA, mk_tstr cD cPsi sA)
	 else
	   raise (Error (loc, TypMismatch (cD, cPsi, sM, sA, sP)))
       end

    | (Root (loc, _, _), _), _ ->
       raise (Error (loc, CheckError (cD, cPsi, sM, sA)))

    | (LFHole loc, _), _ ->
       Ann.LF.LFHole (loc, mk_nstr cD cPsi sM, sA, mk_tstr cD cPsi sA)

  and annTuple loc cD cPsi (tuple, s1) (trec, s2) =
    let loop (tuple, s1) (typRec, s2) =
      match tuple, typRec with
      | Last tM, SigmaLast (n, tA) ->
	 let tM' = ann cD cPsi (tM, s1) (tA, s2) in
	 Ann.LF.Last tM'
      | Cons (tM, tuple), SigmaElem (_x, tA, typRec) ->
	 let tM' = ann cD cPsi (tM, s1) (tA, s2) in
	 let tuple' = annTuple loc cD cPsi (tuple, s1) (typRec, Dot (Obj tM, s2)) in
	 Ann.LF.Cons (tM', tuple')
      | _, _ -> raise (Error (loc, TupleArity (cD, cPsi, (Tuple (loc, tuple), s1), (trec, s2))))
    in
    loop (tuple, s1) (trec, s2)

  and syn cD cPsi (Root (loc, h, tS), s) =
    (* print_string (sprintf "[syn] tM: %s\n" (P.normalToString cD cPsi (Root (loc, h, tS), s))); *)
    let rec spineLength = function
      | Nil -> 0
      | SClo (tS, _) -> spineLength tS
      | App (_, tS) -> 1 + spineLength tS
    in

    let rec typLength = function
      | Atom _ -> 0
      | PiTyp (_, tB2) -> 1 + typLength tB2
    in

    let rec syn tS sA =
      match tS, sA with
      | (Nil, _), sP -> (sP, Ann.LF.Nil)
      | (SClo (tS, s'), s), sA ->
	 let (sA', tS') = syn (tS, Substitution.LF.comp s' s) sA in
	 (sA', Ann.LF.SClo (tS', s'))
      | (App (tM, tS), s1), (PiTyp ((TypDecl (_, tA1), _), tB2), s2) ->
	 (* print_string (sprintf "[syn] tM: %s\n" (P.normalToString cD cPsi (tM, s1))); *)
	 let tM' = ann cD cPsi (tM, s1) (tA1, s2) in
	 let tB2 = C.whnfTyp (tB2, Dot (Obj (Clo (tM, s1)), s2)) in
	 let (sA', tS') = syn (tS, s1) tB2 in
	 (sA', Ann.LF.App (tM', tS', P.spineToString cD cPsi (App (tM, tS), s1)))
    in

    let (tA', h') = inferHead loc cD cPsi h Subst in
    (* print_string ("[inferHead] h: " ^ P.headToString cD cPsi h *)
    (* 		  ^ "\ntA' :" ^ P.typToString cD cPsi (tA', Substitution.LF.id) ^ "\n"); *)
    let (sA', s') =
      C.whnfTyp (tA', Substitution.LF.id)
    in
    if typLength sA' < spineLength tS then
      raise (Error (loc, SpineIllTyped (typLength sA', spineLength tS)));
    let (sA', tS') = syn (tS, s) (sA', s') in

    (* We're done with the spine, so we can safely deal with implicit args. *)
    (* Done in the same manner as in pretty printing. *)
    let rec dropSpineLeft tS n = match (tS, n) with
      | (_, 0) -> tS
      | (Ann.LF.Nil, _) -> tS
      | (Ann.LF.App (_, rest, _), n) -> dropSpineLeft rest (n-1)
    in
    let deimplicitize_spine h tS = match h with
      | Const c ->
	 let imp_args = Term.get_implicit_arguments c in
	 dropSpineLeft tS imp_args
      | _ -> tS
    in

    (sA', h', deimplicitize_spine h' tS')
end

module Comp = struct

  module Unify = Unify.EmptyTrail

  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf
  module Ann = Annotated

  type typeVariant = (* VariantCross | *) VariantArrow | (* VariantCtxPi | *) VariantPiBox (* | VariantBox *)

  type error =
    | MismatchChk     of I.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of I.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of I.mctx * gctx * pattern * tclo * tclo
    | PairMismatch    of I.mctx * gctx  * tclo
    | BoxMismatch     of I.mctx * gctx  * tclo
    | IfMismatch      of I.mctx * gctx  * tclo
    | EqMismatch      of I.mctx * tclo (* arg1 *) * tclo (* arg2 *)
    | EqTyp           of I.mctx * tclo
    | TypMismatch     of I.mctx * tclo * tclo
    | InvalidRecCall
    | MissingTotal of Id.cid_prog

  exception Error of Syntax.Loc.t * error

  let convToParamTyp mT = match mT with
    | I.ClTyp (I.MTyp tA, cPsi) -> I.ClTyp (I.PTyp tA, cPsi)
    | mT -> mT

  let string_of_typeVariant = function
    (* | VariantCross -> "product type" *)
    | VariantArrow -> "function type"
    (* | VariantCtxPi -> "context abstraction" *)
    | VariantPiBox -> "dependent function type"
    (* | VariantBox   -> "contextual type" *)

  let _ = Error.register_printer
    (fun (Error (loc, err)) ->
      Error.print_with_location loc (fun ppf ->
	match err with
	  | MissingTotal prog ->
	    Format.fprintf ppf "Function %s not known to be total."
	      (R.render_cid_prog prog)
	  | InvalidRecCall ->
	    Format.fprintf ppf "Recursive call not structurally smaller."

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
	  | BoxMismatch (cD, _cG, theta_tau) ->
	    Format.fprintf ppf "Found box-expression that does not have type %a."
	      (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

	  | IfMismatch (cD, _cG, theta_tau) ->
	    Error.report_mismatch ppf
	      "Type error in guard of if expression."
	      "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) TypBool
	      "Actual type"   (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

	  | PairMismatch (cD, _cG, theta_tau) ->
	    Format.fprintf ppf "Found tuple, but expected type %a"
	      (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

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

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (f,  tau)), 1) -> (f,tau)
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
	lookup cG' (k - 1)

  let lookup' cG k =
    let (f,tau) = lookup cG k in tau

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
			Total.filter cD cG cIH (loc, M cM)
		   | Syn(_, i) -> (match extract_var i with
				   | Some x -> Total.filter cD cG cIH (loc, V x)
				   | None ->  Total.filter cD cG cIH (loc, E))
       (* | _      -> raise (Error (loc, InvalidRecCall)) *)
       in
       (* We have now partially checked for the recursive call *)
       match cIH with
       | I.Dec(_ , WfRec (_, [], _ )) ->
	  (* We have fully used a recursive call and we now are finished checking for
	   well-formedness of rec. call. *)
	  None
       | I.Empty -> raise (Error (loc, InvalidRecCall))
       | _ -> Some cIH


  let mk_tstr cD ttau =
    if !Typeinfo.generate_annotations then
      Some (P.subCompTypToString cD ttau)
    else
      None

  let rec ann cD cG e ttau =
    let cIH = I.Empty in
    annotate cD (cG, cIH) e ttau

  and annotate cD (cG, cIH) e ttau =
    let e' = annotate' cD (cG, cIH) e ttau in
    print_string (Printf.sprintf "[annotate - chk]\n\t[int] %s\n\t========>\n\t[ann] %s\n"
			  (P.expChkToString cD cG e)
			  (PrettyAnn.expChkToString cD cG e')
		 );
    e'

  and annotate' cD (cG, cIH) e ttau =
    match (e, ttau) with
    | (Rec (loc, f, e), (tau, t)) ->
       annotate cD (I.Dec (cG, CTypDecl (f, TypClo (tau, t))), (Total.shift cIH)) e ttau;

    | (Fun (loc, x, e), (TypArr (tau1, tau2), t)) ->
       let e' = annotate cD (I.Dec (cG, CTypDecl (x, TypClo (tau1, t))), (Total.shift cIH))
			 e (tau2, t)
       in
       Ann.Comp.Fun (loc, x, e', ttau, mk_tstr cD ttau)

    | (Cofun (loc, bs), (TypCobase (l, cid, sp), t)) ->
       let f = fun (CopatApp (loc, dest, csp), e) ->
	 let (ttau', csp') = synObs cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) ttau in
	 let e' = annotate cD (cG, cIH) e ttau' in
	 (csp', e')
       in
       let bs' = List.map f bs in
       Ann.Comp.Cofun (loc, bs', ttau, mk_tstr cD ttau)

    (* Toss explicit MLams *)
    | (MLam (loc, u, e), (TypPiBox (I.Decl (_, cU, I.Maybe) as cdec, tau), t)) ->
       annotate (extend_mctx cD (u, cdec, t))
		(C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
		e (tau, C.mvar_dot1 t)

    | (MLam (loc, u, e), (TypPiBox (cdec, tau), t)) ->
       let e' = annotate (extend_mctx cD (u, cdec, t))
			 (C.cnormCtx (cG, I.MShift 1), C.cnormCtx (cIH, I.MShift 1))
			 e (tau, C.mvar_dot1 t)
       in
       Ann.Comp.MLam (loc, u, e', ttau, mk_tstr cD ttau)

    | (Pair (loc, e1, e2), (TypCross (tau1, tau2), t)) ->
       let e1' = annotate cD (cG, cIH) e1 (tau1, t) in
       let e2' = annotate cD (cG, cIH) e2 (tau2, t) in
       Ann.Comp.Pair (loc, e1', e2', ttau, mk_tstr cD ttau)

    | (Let (loc, i, (x, e)), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       let cG' = I.Dec (cG, CTypDecl (x, TypClo (tau', t'))) in
       let e' = annotate cD (cG', Total.shift cIH) e (tau, t) in
       Ann.Comp.Let (loc, i', (x, e'), ttau, mk_tstr cD ttau)

    | (LetPair (loc, i, (x, y, e)), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypCross (tau1, tau2), t') ->
	    let cG = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))),
			    CTypDecl (y, TypClo (tau2, t')))
	    in
	    let e' = annotate cD (cG, (Total.shift (Total.shift cIH))) e (tau, t) in
	    Ann.Comp.LetPair (loc, i', (x, y, e'), ttau, mk_tstr cD ttau)
	 | _ -> raise (Error.Violation "Case scrutinee not of boxed type")
       end

    | (Box (loc, cM), (TypBox (l, mT), t)) ->
       begin
	 try
	   let cM' = LF.annotateMetaObj cD cM (mT, t) in
	   Ann.Comp.Box (loc, cM', ttau, mk_tstr cD ttau)
	 with C.FreeMVar (I.FMVar (u, _)) ->
	   raise (Error.Violation ("Free meta-variable " ^ (Id.render_name u)))
       end

    | (Case (loc, prag, Ann (Box (loc', (l, cM)), (TypBox (_, mT) as tau0_sc)), branches)
      , (tau, t)) ->
       let (total_pragma, tau_sc, projOpt) =
	 begin
	   match cM with
	   | I.ClObj (_ , I.MObj (I.Root (_, I.PVar (x,s) , _ )))
	   | I.ClObj (_ , I.PObj (I.PVar (x,s)))  ->
	      let order = if !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l, cM)
			  else
			    IndexObj (l, cM)
	      in
	      (order, TypBox(loc, convToParamTyp (C.cnormMetaTyp (mT, C.m_id))), None)
	   | I.ClObj (_, I.MObj (I.Root (_, I.Proj (I.PVar (x,s), k ), _ )))
	   | I.ClObj (_, I.PObj (I.Proj (I.PVar (x,s), k))) ->
	      let order = if  !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l,cM)
			  else
			    IndexObj (l,cM)
	      in
	      (order, TypBox (loc, convToParamTyp(C.cnormMetaTyp (mT, C.m_id))), Some k)
	   | I.ClObj (_, I.MObj (I.Root (_, I.MVar (I.Offset x,s), _ ))) ->
	      let order = if  !Total.enabled && is_indMObj cD x then
			    IndIndexObj (l,cM)
			  else
			    IndexObj (l,cM)
	      in
	      (order, TypBox (loc, C.cnormMetaTyp (mT, C.m_id)), None)
	   | I.CObj (I.CtxVar (I.CtxOffset k)) ->
	      let order = if  !Total.enabled && is_indMObj cD k then
			    IndIndexObj (l,cM)
			  else
			    IndexObj (l,cM)
	      in
	      (order, TypBox (loc, C.cnormMetaTyp (mT, C.m_id)), None)
	   | _ ->
	      (IndexObj (l,cM), TypBox (loc, C.cnormMetaTyp (mT, C.m_id)), None)
	 end
       in
       let (l, cM)  = LF.annotateMetaObj cD (loc,cM) (mT, C.m_id)  in

       let problem = Coverage.make loc prag cD branches tau_sc in
       let branches' = annBranches total_pragma cD (cG,cIH) branches tau0_sc (tau, t) in
       Coverage.process problem projOpt;
       let ttau' = (tau0_sc, C.m_id) in
       let ttau'' = (tau_sc, C.m_id) in
       Ann.Comp.Case (loc, prag,
		      Ann.Comp.Ann (
			  Ann.Comp.Box (loc', (l, cM),
					ttau'', mk_tstr cD ttau''
			), tau0_sc, ttau', mk_tstr cD ttau'),
		      branches', ttau, mk_tstr cD ttau
		     )

    | (Case (loc, prag, i, branches), (tau, t)) ->
       let annoBranch total_pragma cD (cG, cIH) i branches (tau, t) =
	 let ((_, tau', t'), i') = syn cD (cG, cIH) i in
	 begin
	   match C.cwhnfCTyp (tau', t') with
	   | (TypBox (loc', mT), t') ->
	      let tau_s = TypBox (loc', C.cnormMetaTyp (mT, t')) in
	      let problem = Coverage.make loc prag cD branches tau_s in
	      let branches' = annBranches total_pragma cD (cG, cIH) branches tau_s (tau, t) in
	      Coverage.process problem None;
	      (i', branches')
	   | (tau', t') ->
	      let tau_s = C.cnormCTyp (tau', t') in
	      let problem = Coverage.make loc prag cD branches (C.cnormCTyp (tau', t')) in
	      let branches' = annBranches total_pragma cD (cG, cIH) branches tau_s (tau, t) in
	      Coverage.process problem None;
	      (i', branches')
	 end
       in
       let (i', branches') =
	 if !Total.enabled then
	   begin
	     match i with
	     | Var (_, x) ->
		let (f, tau') = lookup cG x in
		let ind =
		  match Whnf.cnormCTyp (tau', Whnf.m_id) with
		  | TypInd _tau -> true
		  | _ -> false
		in
		if ind then
		  annoBranch IndDataObj cD (cG, cIH) i branches (tau, t)
		else
		  annoBranch DataObj cD (cG, cIH) i branches (tau, t)
	     | _ ->
		annoBranch DataObj cD (cG, cIH) i branches (tau, t)
	   end
	 else
	   annoBranch DataObj cD (cG, cIH) i branches (tau, t)
       in
       Ann.Comp.Case (loc, prag, i', branches', ttau, mk_tstr cD ttau)

    | (Syn (loc, i), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       if C.convCTyp (tau, t) (tau', t') then
	 Ann.Comp.Syn (loc, i', ttau, mk_tstr cD ttau)
       else
	 raise (Error (loc, MismatchChk (cD, cG, e, (tau, t), (tau', t'))))

    | (If (loc, i, e1, e2), (tau, t)) ->
       let ((_, tau', t'), i') = syn cD (cG, cIH) i in
       let (tau', t') = C.cwhnfCTyp (tau', t') in
       begin
	 match (tau', t') with
	 | (TypBool, _) ->
	    let e1' = annotate cD (cG, cIH) e1 (tau, t) in
	    let e2' = annotate cD (cG, cIH) e2 (tau, t) in
	    Ann.Comp.If (loc, i', e1', e2', ttau, mk_tstr cD ttau)
	 | tau_theta' ->
	    raise (Error (loc, IfMismatch (cD, cG, tau_theta')))
       end

    | (Hole (loc, f), (tau, t)) ->
       Ann.Comp.Hole (loc, f, ttau, mk_tstr cD ttau)

  and synObs cD csp ttau1 ttau2 =
    match (csp, ttau1, ttau2) with
    | (CopatNil loc, (TypArr (tau1, tau2), theta), (tau', theta')) ->
       if C.convCTyp (tau1, theta) (tau', theta') then
	 ((tau2, theta), Ann.Comp.CopatNil loc)
       else
	 raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau', theta'))))
    | (CopatApp (loc, dest, csp'), (TypArr (tau1, tau2), theta), (tau', theta')) ->
       if C.convCTyp (tau1, theta) (tau', theta') then
	 let (ttau, csp'') =
	   synObs cD csp' ((CompDest.get dest).CompDest.typ, C.m_id) (tau2, theta)
	 in
	 (ttau, Ann.Comp.CopatApp (loc, dest, csp''))
       else
	 raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau', theta'))))

  and strip_mapp_args cD cG i =
    let (i', _) = strip_mapp_args' cD cG i in i'

  and strip_mapp_args' cD cG i =
    match i with
    | Ann.Comp.Const (_, prog, _, _) ->
       (i, implicitCompArg (Comp.get prog).Comp.typ)
    | Ann.Comp.DataConst (_, c, _, _) ->
       (i, implicitCompArg (CompConst.get c).CompConst.typ)
    | Ann.Comp.Var (_, x, _, _) ->
       begin
	 match Context.lookup cG x with
	 | None -> (i, [])
	 | Some tau -> (i, implicitCompArg tau)
       end
    | Ann.Comp.Apply (loc, i, e, ttau, tstr) ->
       let (i', _) = strip_mapp_args' cD cG i in
       (Ann.Comp.Apply (loc, i', e, ttau, tstr), [])
    | Ann.Comp.MApp (loc, i1, mC, ttau, tstr) ->
       let (i', stripArg) = strip_mapp_args' cD cG i1 in
       begin
	 match stripArg with
	 | false :: sA -> (i', sA)
	 | true :: sA -> (Ann.Comp.MApp (loc, i', mC, ttau, tstr), sA)
	 | [] -> (i', [])
       end
    | Ann.Comp.PairVal (loc, i1, i2, ttau, tstr) ->
       let (i1', _) = strip_mapp_args' cD cG i1 in
       let (i2', _) = strip_mapp_args' cD cG i2 in
       (Ann.Comp.PairVal (loc, i1', i2', ttau, tstr), [])
    | Ann.Comp.Equal (loc, i1, i2, ttau, tstr) ->
       let (i1', _) = strip_mapp_args' cD cG i1 in
       let (i2', _) = strip_mapp_args' cD cG i2 in
       (Ann.Comp.Equal (loc, i1', i2', ttau, tstr), [])
    | _ -> (i, [])
  and implicitCompArg tau =
    match tau with
    | TypPiBox ((I.Decl (_, I.ClTyp (I.MTyp _, _), I.Maybe)), tau) ->
       false :: implicitCompArg tau
    | TypPiBox (_, tau) ->
       true :: implicitCompArg tau
    | _ -> []

  and syn cD (cG, cIH) e =
    let ((cIH_opt, tau, t), e') = syn' cD (cG, cIH) e in
    print_string (Printf.sprintf "[annotate - syn]\n\t[int] %s\n\t========>\n\t[ann] %s\n"
			  (P.expSynToString cD cG e)
			  (PrettyAnn.expSynToString cD cG e')
		 );
    ((cIH_opt, tau, t), strip_mapp_args cD cG e')

  and syn' cD (cG, cIH) e =
    match e with
    | Var (loc, x) ->
       let (f, tau') = lookup cG x in
       let tau =
	 match C.cnormCTyp (tau', Whnf.m_id) with
	 | TypInd tau -> tau
	 | _ -> tau'
       in
       let ttau = (tau, C.m_id) in
       if Total.exists_total_decl f then
	 ((Some cIH, tau, C.m_id), Ann.Comp.Var (loc, x, ttau, mk_tstr cD ttau))
       else
	 ((None, tau, C.m_id), Ann.Comp.Var (loc, x, ttau, mk_tstr cD ttau))

    | DataConst (loc, c) ->
       let ttau = ((CompConst.get c).CompConst.typ, C.m_id) in
       ((None, (CompConst.get c).CompConst.typ, C.m_id),
	 Ann.Comp.DataConst (loc, c, ttau, mk_tstr cD ttau))

    | DataDest (loc, c) ->
       let ttau = ((CompDest.get c).CompDest.typ, C.m_id) in
       ((None, (CompDest.get c).CompDest.typ, C.m_id),
	 Ann.Comp.DataDest (loc, c, ttau, mk_tstr cD ttau))

    | Const (loc, prog) ->
       if !Total.enabled then
	 if (Comp.get prog).Comp.total then
	   let ttau = ((Comp.get prog).Comp.typ, C.m_id) in
	   ((None, (Comp.get prog).Comp.typ, C.m_id),
	    Ann.Comp.Const (loc, prog, ttau, mk_tstr cD ttau))
	 else
	   raise (Error (loc, MissingTotal prog))
       else
	 let ttau = ((Comp.get prog).Comp.typ, C.m_id) in
	 ((None, (Comp.get prog).Comp.typ, C.m_id),
	  Ann.Comp.Const (loc, prog, ttau, mk_tstr cD ttau))

    | Apply (loc, e1, e2) ->
       let ((cIH_opt, tau1, t1), e1') = syn cD (cG, cIH) e1 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       begin
	 match (tau1, t1) with
	 | (TypArr (tau2, tau), t) ->
	    let e2' = annotate cD (cG, cIH) e2 (tau2, t) in
	    ((useIH loc cD cG cIH_opt e2, tau, t),
	    Ann.Comp.Apply (loc, e1', e2', (tau, t), mk_tstr cD (tau, t)))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, e1, VariantArrow, (tau, t))))
       end

    | MApp (loc, e, mC) ->
       let ((cIH_opt, tau1, t1), e') = syn cD (cG, cIH) e in
       begin
	 match (C.cwhnfCTyp (tau1, t1)) with
	 | (TypPiBox ((I.Decl (_, ctyp, _)), tau), t) ->
	    let mC' = LF.annotateMetaObj cD mC (ctyp, t) in
	    let t' = I.MDot (metaObjToMFront mC, t) in
	    ((useIH loc cD cG cIH_opt (Box (loc, mC)), tau, t'),
	    Ann.Comp.MApp (loc, e', mC', (tau, t'), mk_tstr cD (tau, t')))
	 | (tau, t) ->
	    raise (Error (loc, MismatchSyn (cD, cG, e, VariantPiBox, (tau, t))))
       end

    | PairVal (loc, i1, i2) ->
       let ((_, tau1, t1), i1') = syn cD (cG, cIH) i1 in
       let ((_, tau2, t2), i2') = syn cD (cG, cIH) i2 in
       let (tau1, t1) = C.cwhnfCTyp (tau1, t1) in
       let (tau2, t2) = C.cwhnfCTyp (tau2, t2) in
       let tau = TypCross (TypClo (tau1, t1), TypClo (tau2, t2)) in
       ((None, tau, C.m_id),
       Ann.Comp.PairVal (loc, i1', i2', (tau, C.m_id), mk_tstr cD (tau, C.m_id)))

    | Ann (e, tau) ->
       let e' = annotate cD (cG, cIH) e (tau, C.m_id) in
       ((None, tau, C.m_id),
	Ann.Comp.Ann (e', tau, (tau, C.m_id), mk_tstr cD (tau, C.m_id)))

    | Equal (loc, i1, i2) ->
       let ((_, tau1, t1), i1') = syn cD (cG, cIH) i1 in
       let ((_, tau2, t2), i2') = syn cD (cG, cIH) i2 in
       if C.convCTyp (tau1, t1) (tau2, t2) then
	 begin
	   match C.cwhnfCTyp (tau1, t1) with
	   | (TypBox _, _) ->
	      ((None, TypBool, C.m_id),
	      Ann.Comp.Equal (loc, i1', i2', (TypBool, C.m_id), mk_tstr cD (TypBool, C.m_id)))
	   | (TypBool, _) ->
	      ((None, TypBool, C.m_id),
	      Ann.Comp.Equal (loc, i1', i2', (TypBool, C.m_id), mk_tstr cD (TypBool, C.m_id)))
	   | (tau1, t1) -> raise (Error (loc, EqTyp (cD, (tau1, t1))))
	 end
       else
	 raise (Error (loc, EqMismatch (cD, (tau1, t1), (tau2, t2))))

    | Boolean b ->
       ((None, TypBool, C.m_id),
       Ann.Comp.Boolean (b, (TypBool, C.m_id), mk_tstr cD (TypBool, C.m_id)))

  and annBranches caseTyp cD (cG, cIH) branches tau_s ttau =
    List.map (fun branch -> annBranch caseTyp cD (cG, cIH) branch tau_s ttau) branches

  and annBranch caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    (* print_string ("[annBranch] branch = " ^ P.branchToString cD cG branch); *)
    annBranch' caseTyp cD (cG, cIH) branch tau_s (tau, t)

  and annBranch' caseTyp cD (cG, cIH) branch tau_s (tau, t) =
    match branch with
    | EmptyBranch (loc, cD1', pat, t1) ->
       let tau_p = C.cnormCTyp (tau_s, t1) in
       (* LF.checkMSub loc cD1' t1 cD *)
       let pat' = annPattern cD1' I.Empty pat (tau_p, C.m_id) in
       Ann.Comp.EmptyBranch (loc, cD1', pat', t1)

    | Branch (loc, cD1', cG', PatMetaObj (loc',mO), t1, e1) ->
       let TypBox (_, mT) = tau_s in
       let mT1 = C.cnormMetaTyp (mT, t1) in
       let cG' = C.cnormCtx (C.normCtx cG, t1) in
       let cIH = C.cnormCtx (C.normCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let (cD1', cIH') =
	 if is_inductive caseTyp && Total.struct_smaller (PatMetaObj (loc', mO)) then
	   let cD1' = mvarsInPatt cD1' (PatMetaObj (loc', mO)) in
	   (cD1', Total.wf_rec_calls cD1' (I.Empty))
	 else
	   (cD1', I.Empty)
       in
       let cD1' = if !Total.enabled then
		    id_map_ind cD1' t1 cD
		  else
		    cD1'
       in
       (* LF.checkMSub loc cD1' t1 cD *)
       let mO' = LF.annotateMetaObj cD1' mO (mT1, C.m_id) in
       let e1' = annotate cD1' (cG', Context.append cIH cIH') e1 (tau', C.m_id) in
       let ttau = (tau_s, C.m_id) in
       Ann.Comp.Branch (loc, cD1', cG',
			Ann.Comp.PatMetaObj (loc', mO', ttau, mk_tstr cD ttau), t1, e1')

    | Branch (loc, cD1', cG1, pat, t1, e1) ->
       let tau_p = C.cnormCTyp (tau_s, t1) in
       let cG' = C.cnormCtx (cG, t1) in
       let cIH = C.cnormCtx (C.normCtx cIH, t1) in
       let t'' = C.mcomp t t1 in
       let tau' = C.cnormCTyp (tau, t'') in
       let k = Context.length cG1 in
       let cIH0 = Total.shiftIH cIH k in
       let (cD1', cIH') = if is_inductive caseTyp && Total.struct_smaller pat then
			    let cD1' = mvarsInPatt cD1' pat in (cD1', Total.wf_rec_calls cD1' cG1)
			  else
			    (cD1', I.Empty)
       in
       let cD1' = if !Total.enabled then
		    id_map_ind cD1' t1 cD
		  else
		    cD1'
       in
       (* LF.checkMSub loc cD1' t1 cD *)
       let pat' = annPattern cD1' cG1 pat (tau_p, C.m_id) in
       let e1' =
	 annotate cD1' ((Context.append cG' cG1), Context.append cIH0 cIH') e1 (tau', C.m_id)
       in
       Ann.Comp.Branch (loc, cD1', cG1, pat', t1, e1')

  and annPattern cD cG pat ttau =
    match pat with
    | PatEmpty (loc, cPsi) ->
       begin
	 match ttau with
	 | (TypBox (_, I.ClTyp (I.MTyp tA, cPhi)), theta)
	 | (TypBox (_, I.ClTyp (I.PTyp tA, cPhi)), theta) ->
	    if C.convDCtx (C.cnormDCtx (cPhi, theta)) cPsi then
	      Ann.Comp.PatEmpty (loc, cPsi, ttau, mk_tstr cD ttau)
	    else
	      raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
	 | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatMetaObj (loc, mO) ->
       begin
	 match ttau with
	 | (TypBox (_, ctyp), theta) ->
	    let mO' = LF.annotateMetaObj cD mO (ctyp, theta) in
	    Ann.Comp.PatMetaObj (loc, mO', ttau, mk_tstr cD ttau)
	 | _ -> raise (Error (loc, BoxMismatch (cD, I.Empty, ttau)))
       end

    | PatPair (loc, pat1, pat2) ->
       begin
	 match ttau with
	 | (TypCross (tau1, tau2), theta) ->
	    let pat1' = annPattern cD cG pat1 (tau1, theta) in
	    let pat2' = annPattern cD cG pat2 (tau2, theta) in
	    Ann.Comp.PatPair (loc, pat1', pat2', ttau, mk_tstr cD ttau)
	 | _ -> raise (Error (loc, PairMismatch (cD, cG, ttau)))
       end

    | pat ->
       let ((loc, ttau'), pat') = synPattern cD cG pat in
       let tau' = C.cnormCTyp ttau' in
       let tau = C.cnormCTyp ttau in
       let ttau' = (tau', C.m_id) in
       let ttau = (tau, C.m_id) in
       if C.convCTyp ttau ttau' then
	 pat'
       else
	 raise (Error (loc, PatIllTyped (cD, cG, pat, ttau, ttau')))

  and synPattern cD cG pat =
    match pat with
    | PatConst (loc, c, pat_spine) ->
       let tau = (CompConst.get c).CompConst.typ in
       let ttau = (tau, C.m_id) in
       let (ttau', pat_spine') = synPatSpine cD cG pat_spine ttau in
       ((loc, ttau'), Ann.Comp.PatConst (loc, c, pat_spine', ttau', mk_tstr cD ttau'))

    | PatVar (loc, k) ->
       let tau = lookup' cG k in
       let ttau = (tau, C.m_id) in
       ((loc, ttau), Ann.Comp.PatVar (loc, k, ttau, mk_tstr cD ttau))

    | PatTrue loc ->
       ((loc, (TypBool, C.m_id)),
	Ann.Comp.PatTrue (loc, (TypBool, C.m_id), mk_tstr cD (TypBool, C.m_id)))

    | PatFalse loc ->
       ((loc, (TypBool, C.m_id)),
	Ann.Comp.PatFalse (loc, (TypBool, C.m_id), mk_tstr cD (TypBool, C.m_id)))

    | PatAnn (loc, pat, tau) ->
       let pat' = annPattern cD cG pat (tau, C.m_id) in
       ((loc, (tau, C.m_id)),
       Ann.Comp.PatAnn (loc, pat', tau, (tau, C.m_id), mk_tstr cD (tau, C.m_id)))

  and synPatSpine cD cG pat_spine (tau, theta) =
    match pat_spine with
    | PatNil -> ((tau, theta), Ann.Comp.PatNil ((tau, theta), mk_tstr cD (tau, theta)))
    | PatApp (loc, pat, pat_spine) ->
       begin
	 match (tau, theta) with
	 | (TypArr (tau1, tau2), theta) ->
	    let pat' = annPattern cD cG pat (tau1, theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau2, theta) in
	    (ttau, Ann.Comp.PatApp (loc, pat', pat_spine', ttau, mk_tstr cD ttau))
	 (* Implicit magic here? *)
	 | (TypPiBox ((I.Decl (_, ctyp, I.Maybe)) as cdecl, tau), theta) ->
	    let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau, theta') in
	    (ttau, pat_spine')
	 | (TypPiBox ((I.Decl (_, ctyp, _)) as cdecl, tau), theta) ->
	    let theta' = checkPatAgainstCDecl cD pat (cdecl, theta) in
	    let tau' = TypBox (loc, ctyp) in
	    let pat' = annPattern cD cG pat (tau', theta) in
	    let (ttau, pat_spine') = synPatSpine cD cG pat_spine (tau, theta') in
	    (ttau, Ann.Comp.PatApp (loc, pat', pat_spine', ttau, mk_tstr cD ttau))
       end

  and checkPatAgainstCDecl cD (PatMetaObj (loc, mO)) (I.Decl(_,ctyp,_), theta) =
    let _ = () (* LF.checkMetaObj cD mO (ctyp, theta) *) in
    I.MDot(metaObjToMFront mO, theta)

end
