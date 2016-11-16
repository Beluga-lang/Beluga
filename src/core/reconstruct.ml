(**

   @author Brigitte Pientka
*)

open Store
open Store.Cid
open Syntax
open Substitution
open Id
open ConvSigma

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail
module C     = Whnf

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer
module T = Store.Cid.Typ

let strengthen : bool ref =  Lfrecon.strengthen

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

type error =
  | ValueRestriction    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | IllegalCase         of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | CompScrutineeTyp    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.LF.tclo * Int.LF.dctx
  | MetaObjContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.dctx
  | PatternContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | ContextSchemaClash  of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | MetaObjectClash     of Int.LF.mctx * (Int.Comp.meta_typ)
  | MissingMetaObj
  | TooManyMetaObj
  | CompTypEmpty       of Int.LF.mctx * Int.Comp.tclo
  | TypeAbbrev         of Id.name
  | CtxHatMismatch        of Int.LF.mctx * Int.LF.ctyp * Int.LF.psi_hat
  | PatternMobj
  | PatAnn
  | PatIndexMatch  of Int.LF.mctx * Int.Comp.meta_obj
  | MCtxIllformed of Int.LF.mctx
  | ScrutineeBlock
  | TypMismatch        of Int.LF.mctx * Int.Comp.tclo * Int.Comp.tclo
  | ErrorMsg of string

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | ErrorMsg str -> Format.fprintf ppf "NOT IMPLEMENTED: %s" str

        | MCtxIllformed cD ->
            Format.fprintf ppf "Unable to abstract over the free meta-variables due to dependency on the specified meta-variables. The following meta-context was reconstructed, but is ill-formed: %a"
              (P.fmt_ppr_lf_mctx Pretty.std_lvl) cD
        | PatIndexMatch (cD, cM) ->
            Format.fprintf ppf "Pattern matching on index argument %a fails. @@\
  Note that unification is conservative and will fail if it cannot handle a case."
              (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM
        | PatAnn     ->
            Format.fprintf ppf
              "Type annotations on context variables and parameter variables not supported at this point."
        | PatternMobj ->
            Format.fprintf ppf
              "Expected a meta-object; Found a computation-level pattern"
        | ScrutineeBlock ->
            Format.fprintf ppf
              "Pattern Matching on an object of Sigma-type (block) is not allowed."
        | CtxHatMismatch (cD, tau, phat) ->
            Format.fprintf ppf
              "Context mismatch@.\
               @ @ expected: %a@."
            (P.fmt_ppr_lf_mtyp cD) tau
            (* (P.fmt_ppr_lf_psi_hat cD Pretty.std_lvl) (Context.hatToDCtx phat) *)
        | TypeAbbrev a ->
          Format.fprintf ppf
            "Type definition %s cannot contain any free meta-variables in its type."
            (Id.render_name a)
        | CompTypEmpty (cD, (tau, theta)) ->
          Format.fprintf ppf
           "Coverage cannot determine whether a computation-level type %a is empty;@.\
            currently, we only attempt to show LF-level types to be empty, if this can be done trivially.@\
            Try splitting further.\n"
            (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp (tau,theta))

        | ValueRestriction (cD, cG, i, theta_tau) ->
          Format.fprintf ppf
            "value restriction [pattern matching]@.\
             @ @ expected: boxed type@.\
             @ @ inferred: %a@.\
             @ @ for expression: %a@.\
             @ @ in context:@.    %s"
            (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)
            (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i
            "[no comp-level context printing yet]" (* TODO print context? *)

        | IllegalCase (cD, cG, i, theta_tau) ->
          Format.fprintf ppf
            "Cannot pattern-match on values of this type.@.";
          Format.fprintf ppf
            "  @[<v>Scrutinee: %a@;\
                    Type: %a@]"
            (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i
            (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.cnormCTyp theta_tau)

        | CompScrutineeTyp (cD, cG, i, sP, cPsi) ->
          Format.fprintf ppf
            "Type [%a . %a]@.\
             of scrutinee %a@.\
             in meta-context %a@. \
             and comp. context %a@. \
             is not closed@ or requires that some meta-variables@ introduced in the pattern@ \
             are further restricted,@ i.e. some variable dependencies cannot happen.@ \
             This error may indicate@ that some implicit arguments that are reconstructed@ \
             should be restricted.@."
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi
            (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sP)
            (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i
            (P.fmt_ppr_lf_mctx Pretty.std_lvl) (Whnf.normMCtx cD)
            (P.fmt_ppr_cmp_gctx cD Pretty.std_lvl) (Whnf.cnormCtx (cG, Whnf.m_id))


        | MetaObjContextClash (cD, cPsi, cPhi) ->
          Error.report_mismatch ppf
            "Context of meta-object does not match expected context."
            "Expected context"    (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi
            "Encountered context" (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPhi;

        | PatternContextClash (cD, cPsi, cD', cPsi') ->
          Error.report_mismatch ppf
            "Context clash in pattern."
            "Pattern's context"   (P.fmt_ppr_lf_dctx cD Pretty.std_lvl)  cPsi
            "Scrutinee's context" (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) cPsi';
          Format.fprintf ppf
            "Note that we do not allow the context in the pattern@ \
             to be more general than the context in the scrutinee."

        | ContextSchemaClash (cD, cPsi, cD', cPsi') ->
          Error.report_mismatch ppf
            "Context schema clash."
            "Expected context"    (P.fmt_ppr_lf_dctx cD Pretty.std_lvl)  cPsi
            "Encountered context" (P.fmt_ppr_lf_dctx cD' Pretty.std_lvl) cPsi';

       | MetaObjectClash (cD, mC) ->
           Format.fprintf ppf
             "Meta-object type clash.@ \
              Expected meta-object of type: %a"
             (P.fmt_ppr_meta_typ cD Pretty.std_lvl) mC;

       | MissingMetaObj      ->
           Format.fprintf ppf
             "Too few meta-objects supplied to data-constructor"

       | TooManyMetaObj      ->
           Format.fprintf ppf
             "Too many meta-objects supplied to data-constructor"

       | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
           Error.report_mismatch ppf
             "Type of destructor did not match the type it was expected to have."
             "Type of destructor" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
             (Whnf.cnormCTyp (tau1, theta1))
             "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
             (Whnf.cnormCTyp (tau2, theta2))
))


(* extend_mctx cD (x, cdecl, t) = cD'

   if cD mctx
      cD' |- cU   where cdecl = _ : cU
      cD  |- t : cD
   the
      cD, x:[t]U  mctx

 *)
let extend_mctx cD (x, cdecl, t) =
 Int.LF.Dec(cD, Whnf.cnormCDecl (cdecl, t))


let mk_name_cdec cdec = match cdec with
  | Int.LF.Decl (u, _, _) -> mk_name (SomeName u)

(* etaExpandMMV loc cD cPsi sA  = tN
 *
 *  cD ; cPsi   |- [s]A <= typ
 *
 *  cD ; cPsi   |- tN   <= [s]A
 *)


type caseType  = (* IndexObj of Int.LF.psi_hat * Int.LF.normal *)
  | IndexObj of Int.Comp.meta_obj
  | DataObj

let normCaseType (cT, t) = match cT with
  | DataObj -> DataObj
  | IndexObj mO -> IndexObj (Whnf.cnormMetaObj (mO, t))

(* type typAnn  = FullTyp of Apx.LF.typ | PartialTyp of cid_typ *)

type mTypSkelet = MT of cid_typ * Int.LF.dctx | CT of Id.cid_schema

let mtypeSkelet loc mT = match mT with
  | Int.LF.ClTyp (Int.LF.MTyp Int.LF.Atom(_, a, _), cPsi) -> MT (a, cPsi)
  | Int.LF.CTyp (Some w) -> CT w
  | _ -> raise (Error (loc, ScrutineeBlock))

let rec elDCtxAgainstSchema loc recT cD psi s_cid = match psi with
  | Apx.LF.Null -> Int.LF.Null
  | Apx.LF.CtxHole ->
    Int.LF.CtxVar (Whnf.newCVar None cD (Some s_cid) Int.LF.Maybe)

  | Apx.LF.CtxVar ((Apx.LF.CtxOffset _ ) as c_var) ->
      let schema = Schema.get_schema s_cid in
      let c_var = Lfrecon.elCtxVar c_var in
      let cPsi' = Int.LF.CtxVar (c_var) in
        begin try
          Check.LF.checkSchema loc cD cPsi' schema ;
          cPsi'
        with _ -> raise (Check.LF.Error (loc, Check.LF.CtxVarMismatch (cD, c_var, schema)))
        end
  | Apx.LF.CtxVar (Apx.LF.CtxName psi ) ->
      (* This case should only be executed when c_var occurs in a pattern *)
      begin try
        let (_ , Int.LF.Decl (_, Int.LF.CTyp (Some s_cid'), _)) = FCVar.get psi in
          if s_cid = s_cid' then Int.LF.CtxVar (Int.LF.CtxName psi)
          else
            (let schema = Schema.get_schema s_cid in
             let c_var' = Int.LF.CtxName psi in
               raise (Check.LF.Error (Syntax.Loc.ghost, Check.LF.CtxVarMismatch (cD, c_var', schema))))
      with Not_found ->
        (FCVar.add psi (cD, Int.LF.Decl (psi, Int.LF.CTyp (Some s_cid), Int.LF.Maybe));
         Int.LF.CtxVar (Int.LF.CtxName psi))
      end
  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtxAgainstSchema loc recT cD psi' s_cid in
      let tA   = Lfrecon.elTyp recT cD cPsi a in
      (* let _ = Check.LF.checkTypeAgainstSchema cO cD cPsi' tA elements in          *)
      let _ = dprint (fun () -> "[elDCtxAgainstSchema] " ^ Id.render_name x ^ ":" ^
                        P.typToString cD cPsi (tA, LF.id)) in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))

(* performs reconstruction of cPsi2 while comparing it with cPsi1
   this is (apparently) necessary to get the right schema for context holes? *)
let unifyDCtxWithFCVar loc cD cPsi1 cPsi2 =
  let rec loop cD cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
    | (Int.LF.Null , Apx.LF.Null) -> ()

    | (Int.LF.CtxVar (Int.LF.CInst ((_n, ({contents = None} as cvar_ref), _cO, Int.LF.CTyp (Some s_cid), _, _), _cD)) , cPsi) ->
      begin
	let cPsi = elDCtxAgainstSchema loc Lfrecon.Pibox cD cPsi s_cid in
        Unify.instantiateCtxVar (cvar_ref, cPsi);
        match Context.ctxVar cPsi with
          | None -> ()
          | Some (Int.LF.CtxName psi) ->
            FCVar.add psi (cD, Int.LF.Decl (psi, Int.LF.CTyp (Some s_cid), Int.LF.Maybe))
          | _ -> ()
      end

    | (cPsi, Apx.LF.CtxHole) -> ()
    | (Int.LF.CtxVar (Int.LF.CtxOffset psi1_var) , Apx.LF.CtxVar (Apx.LF.CtxOffset psi2_var)) when psi1_var = psi2_var -> ()
    | (Int.LF.CtxVar (Int.LF.CtxName g) , Apx.LF.CtxVar (Apx.LF.CtxName h)) when g = h -> ()

    | (Int.LF.DDec (cPsi1, Int.LF.TypDecl(_ , tA1)) ,
       Apx.LF.DDec (cPsi2, Apx.LF.TypDecl(_ , tA2))) ->
      loop cD cPsi1 cPsi2;
      let tA2 = Lfrecon.elTyp Lfrecon.Pibox cD cPsi1 tA2 in
      Unify.unifyTyp cD cPsi1 (tA1, LF.id) (tA2, LF.id)

    | (Int.LF.DDec (cPsi1, Int.LF.TypDecl(_ , tA1)) ,
       Apx.LF.DDec (cPsi2, Apx.LF.TypDeclOpt _)) ->
      loop cD cPsi1 cPsi2

    | (Int.LF.DDec (cPsi1, Int.LF.TypDeclOpt _), _) -> failwith "Unexpected case"

    | _ -> raise (Unify.Failure "context clash")

  in loop cD (Whnf.normDCtx cPsi1)  cPsi2

(* -------------------------------------------------------------*)

let rec apx_length_typ_rec t_rec = match t_rec with
  | Apx.LF.SigmaLast _ -> 1
  | Apx.LF.SigmaElem (x, _ , rest ) ->
      (print_string (Id.render_name x ^ "  ");
      1 + apx_length_typ_rec rest )

let rec lookup cG k = match cG, k with
  | Int.LF.Dec (_cG', Int.Comp.CTypDecl (_, tau)), 1 -> Whnf.cnormCTyp (tau, Whnf.m_id)
  | Int.LF.Dec ( cG', Int.Comp.CTypDecl (_, _tau)), k -> lookup cG' (k-1)

(* -------------------------------------------------------------*)

(* Solve free variable constraints *)


(* ******************************************************************* *)

let rec elTypDeclCtx cD  = function
  | Apx.LF.Empty ->
      Int.LF.Empty

  | Apx.LF.Dec (ctx, Apx.LF.TypDecl (name, typ)) ->
      let ctx'     = elTypDeclCtx cD ctx in
      let tA       = Lfrecon.elTyp Lfrecon.Pi cD (Context.projectCtxIntoDctx ctx') typ in
      let typDecl' = Int.LF.TypDecl (name, tA) in
        Int.LF.Dec (ctx', typDecl')

let elSchElem (Apx.LF.SchElem (ctx, typRec)) =
   let cD = Int.LF.Empty in
   let _ = dprint (fun () -> "elTypDeclCtx \n") in
   let el_ctx = elTypDeclCtx cD ctx in
   let dctx = Context.projectCtxIntoDctx el_ctx in
   let _ = dprint (fun () -> "[elSchElem] some context = "
                     ^ P.dctxToString Int.LF.Empty dctx ^ "\n") in
   let _ = dprint (fun () ->  ("\n[elSchElem] apx nblock has length "
                               ^ string_of_int (apx_length_typ_rec typRec)
                               ^ "\n")) in
   let typRec' = Lfrecon.elTypRec Lfrecon.Pi cD dctx typRec in
   let s_elem   = Int.LF.SchElem(el_ctx, typRec') in
      (dprint (fun () -> "[elSchElem] " ^ P.schElemToString s_elem);
       s_elem)

let elSchema (Apx.LF.Schema el_list) =
   Int.LF.Schema (List.map elSchElem el_list)

let elSvar_class = function
  | Apx.LF.Ren -> Int.LF.Ren
  | Apx.LF.Subst -> Int.LF. Subst

let elClTyp recT cD cPsi = function
  | Apx.LF.MTyp a -> Int.LF.MTyp (Lfrecon.elTyp recT cD cPsi a)
  | Apx.LF.STyp (cl, phi) -> Int.LF.STyp (elSvar_class cl, Lfrecon.elDCtx recT cD phi)
  | Apx.LF.PTyp a -> Int.LF.PTyp (Lfrecon.elTyp recT cD cPsi a)

let elCTyp recT cD = function
  | Apx.LF.ClTyp (cl, psi) ->
    let cPsi = Lfrecon.elDCtx recT cD psi in
    Int.LF.ClTyp (elClTyp recT cD cPsi cl, cPsi)
  | Apx.LF.CTyp schema_cid -> Int.LF.CTyp (Some schema_cid)

let elCDecl recT cD (Apx.LF.Decl(u, ctyp,dep)) =
    let dep = match dep with | Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
    Int.LF.Decl (u, elCTyp recT cD ctyp, dep)


let rec elMCtx recT delta = match delta with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (delta, cdec) ->
      let cD    = elMCtx recT delta in
      let cdec' = elCDecl recT cD cdec in
        Int.LF.Dec (cD, cdec')


(* ******************************************************************* *)
(* Elaboration of computations                                         *)
(* Given a type-level constant a of type K , it will generate the most general
 * type a U1 ... Un
 *)

let mgAtomicTyp cD cPsi a kK =
  let (flat_cPsi, conv_list) = flattenDCtx cD cPsi in
  let s_proj   = gen_conv_sub conv_list in
  let rec genSpine sK = match sK with
    | (Int.LF.Typ, _s) ->
        Int.LF.Nil

    | (Int.LF.PiKind ((Int.LF.TypDecl (_n, tA1), _ ), kK), s) ->
        let tA1' = strans_typ cD cPsi (tA1, s) conv_list in
        let h    = if !strengthen then
              	   (let (ss', cPhi') = Subord.thin' cD a flat_cPsi in
                       (* cPhi |- ss' : cPhi' *)
                     let ssi' = LF.invert ss' in
                       (* cPhi' |- ssi : cPhi *)
                       (* cPhi' |- [ssi]tQ    *)
                     let u  = Whnf.newMMVar None (cD, cPhi' , Int.LF.TClo (tA1', ssi')) Int.LF.Maybe in
                     let ss_proj = LF.comp ss' s_proj in
                       Int.LF.MMVar ((u, Whnf.m_id), ss_proj))
                   else
                     let u  = Whnf.newMMVar None (cD, flat_cPsi , tA1')  Int.LF.Maybe in
                     Int.LF.MMVar ((u, Whnf.m_id), s_proj)
        in
        let tR = Int.LF.Root (Syntax.Loc.ghost, h, Int.LF.Nil) in  (* -bp needs to be eta-expanded *)

        let _ = dprint (fun () -> "Generated meta^2-variable " ^
                          P.normalToString cD cPsi (tR, LF.id)) in
        let _ = dprint (fun () -> "of type : " ^ P.dctxToString cD flat_cPsi ^
                          " |- " ^ P.typToString cD flat_cPsi (tA1',LF.id)) in
        let _ = dprint (fun () -> "orig type : " ^ P.dctxToString cD cPsi ^
                          " |- " ^ P.typToString cD cPsi (tA1,s)) in
        let tS = genSpine (kK, Int.LF.Dot (Int.LF.Head h, s)) in
        (* let tS = genSpine (kK, Int.LF.Dot (Int.LF.Obj tR , s)) in  *)
          Int.LF.App (tR, tS)

  in
    Int.LF.Atom (Syntax.Loc.ghost, a, genSpine (kK, LF.id))


let rec mgTyp cD cPsi tA = begin match tA with
  | Int.LF.Atom (_, a, _) ->
      mgAtomicTyp cD cPsi a (Typ.get a).Typ.kind

  | Int.LF.Sigma trec ->
      Int.LF.Sigma (mgTypRec cD cPsi trec )

  | Int.LF.PiTyp ((tdecl, dep), tA) ->
   let tdecl' = mgTypDecl cD cPsi tdecl in
     Int.LF.PiTyp ((tdecl', dep),
		   mgTyp cD (Int.LF.DDec (cPsi, tdecl')) tA)
 end

 and mgTypDecl cD cPsi tdecl = begin match tdecl with
   | Int.LF.TypDecl (x, tA) ->
       Int.LF.TypDecl (x, mgTyp cD cPsi tA)
 end

 and mgTypRec cD cPsi trec = begin match trec with
   | Int.LF.SigmaLast(n, tA) -> Int.LF.SigmaLast (n, mgTyp cD cPsi tA)
   | Int.LF.SigmaElem (x, tA, trec) ->
       let tA' = mgTyp cD cPsi tA in
       let trec' = mgTypRec cD (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA'))) trec in
	 Int.LF.SigmaElem (x, tA', trec')
 end

let metaObjToFt (loc, m) = m


let mmVarToCMetaObj loc' mV = function
  | Int.LF.MTyp tA   -> Int.LF.MObj (Int.LF.Root(loc', Int.LF.MMVar ((mV, Whnf.m_id), LF.id), Int.LF.Nil))
  | Int.LF.PTyp tA   -> Int.LF.PObj (Int.LF.MPVar ((mV, Whnf.m_id), LF.id))
  | Int.LF.STyp (_, cPhi) -> Int.LF.SObj (Int.LF.MSVar (0, ((mV, Whnf.m_id), LF.id)))

let mmVarToMetaObj loc' mV = function
  | Int.LF.ClTyp (mt, cPsi) ->
    Int.LF.ClObj (Context.dctxToHat cPsi, mmVarToCMetaObj loc' mV mt)
  | Int.LF.CTyp schema_cid ->
    Int.LF.CObj(Int.LF.CtxVar (Int.LF.CInst (mV, Whnf.m_id)))

let genMetaVar' loc' cD (loc, n , ctyp, t) =
  let ctyp' = C.cnormMTyp (ctyp, t) in
  let mO = mmVarToMetaObj loc' (Whnf.newMMVar' (Some n) (cD, ctyp') Int.LF.Maybe) ctyp' in
  ((loc',mO), Int.LF.MDot(mO,t))

let rec genMApp loc cD (i, tau_t) = genMAppW loc cD (i, Whnf.cwhnfCTyp tau_t)

and genMAppW loc cD (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox (Int.LF.Decl(n, ctyp, Int.LF.Maybe), tau), theta) ->
    let (cM,t') = genMetaVar' loc cD (loc, n, ctyp, theta) in
    genMApp loc cD (Int.Comp.MApp (loc, i, cM), (tau, t'))
  | _ ->
      let _ = dprint (fun () -> "[genMApp]  done " ^
                                P.mctxToString cD ^ " \n   |- " ^
                                P.compTypToString cD (Whnf.cnormCTyp tau_t)) in
        (i, tau_t)


(* elCompKind  cPsi k = K *)
let rec elCompKind cD k = match k with
  | Apx.Comp.Ctype loc ->
      Int.Comp.Ctype loc

  | Apx.Comp.PiKind (loc, cdecl, k') ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl   in
      let tK     = elCompKind  (Int.LF.Dec (cD, cdecl')) k' in
        Int.Comp.PiKind (loc, cdecl', tK)

let elClObj cD loc cPsi' clobj mtyp = match clobj, mtyp with
  | Apx.Comp.MObj tM, Int.LF.MTyp tA ->
    Int.LF.MObj (Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA, LF.id))
  | Apx.Comp.SObj s, Int.LF.STyp (cl, cPhi') ->
    Int.LF.SObj (Lfrecon.elSub loc Lfrecon.Pibox cD cPsi' s cl cPhi')
  | Apx.Comp.MObj m, Int.LF.STyp (cl, cPhi') -> (* This fixes up an ambiguity *)
    Int.LF.SObj (Lfrecon.elSub loc Lfrecon.Pibox cD cPsi' (Apx.LF.Dot(Apx.LF.Obj m, Apx.LF.EmptySub)) cl cPhi')
  | Apx.Comp.MObj (Apx.LF.Root (_,h,Apx.LF.Nil) as tM), Int.LF.PTyp tA' ->
    (* TODO: Something a little more gentle.. *)
    let Int.LF.Root (_, h, Int.LF.Nil) = Lfrecon.elTerm  Lfrecon.Pibox cD cPsi' tM (tA', LF.id) in
    Int.LF.PObj h
  | _ , _ -> raise (Error (loc,  MetaObjectClash (cD, Int.LF.ClTyp (mtyp, cPsi'))))

let rec elMetaObj' cD loc cM cTt = match cM , cTt with
  | (Apx.Comp.CObj psi, (Int.LF.CTyp (Some w))) ->
      let cPsi' = elDCtxAgainstSchema loc Lfrecon.Pibox cD psi w in
        Int.LF.CObj cPsi'

  | (Apx.Comp.ClObj (cPhi, clobj), (Int.LF.ClTyp (mtyp, cPsi'))) ->
      let _ =
        try unifyDCtxWithFCVar loc cD cPsi' cPhi
        with Unify.Failure _ ->
	  let cPhi = Lfrecon.elDCtx Lfrecon.Pibox cD cPhi in
	  raise (Error (loc, MetaObjContextClash (cD, cPsi', cPhi))) in
      Int.LF.ClObj (Context.dctxToHat cPsi', elClObj cD loc cPsi' clobj mtyp)

  | (_ , _) -> raise (Error (loc,  MetaObjectClash (cD, cTt)))

and elMetaObj cD (loc,cM) cTt =
  let ctyp = C.cnormMTyp cTt in
  let r = elMetaObj' cD loc cM ctyp in
  let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
  let _   = dprint (fun () -> "[elMetaObj] type = " ^ P.mtypToString cD ctyp ) in
  let _   = dprint (fun () -> "[elMetaObj] term = " ^ P.metaObjToString cD (loc,r) ) in
  loc, r

and elMetaObjCTyp loc cD m theta ctyp =
  let cM = elMetaObj cD m (ctyp, theta) in
  (cM, Int.LF.MDot (metaObjToFt cM, theta))

and elMetaSpine loc cD s cKt  = match (s, cKt) with
  | (Apx.Comp.MetaNil , (Int.Comp.Ctype _ , _ )) -> Int.Comp.MetaNil

  | (Apx.Comp.MetaNil , (Int.Comp.PiKind (_, cdecl , _cK), theta )) ->
       raise (Error (loc, MissingMetaObj))

  | (Apx.Comp.MetaApp (m, s), (Int.Comp.Ctype _ , _ )) ->
       raise (Error (loc, TooManyMetaObj))

  | (s, (Int.Comp.PiKind (loc', Int.LF.Decl (n, ctyp, Int.LF.Maybe), cK), theta)) ->
    let (mO,t') = genMetaVar' loc cD (loc', n, ctyp, theta) in
    Int.Comp.MetaApp(mO, elMetaSpine loc cD s (cK, t'))

  | (Apx.Comp.MetaApp (m, s), (Int.Comp.PiKind (_, Int.LF.Decl(_,ctyp,_), cK) , theta)) ->
    let (mO,t') = elMetaObjCTyp loc cD m theta ctyp in
    Int.Comp.MetaApp(mO, elMetaSpine loc cD s (cK, t'))

let rec spineToMSub cS' ms = match cS' with
  | Int.Comp.MetaNil -> ms
  | Int.Comp.MetaApp (mO, mS) ->
    spineToMSub mS (Int.LF.MDot(metaObjToFt mO, ms))

let rec elCompTyp cD tau = match tau with
  | Apx.Comp.TypBase (loc, a, cS) ->
      let _ = dprint (fun () -> "[elCompTyp] Base : " ^ R.render_cid_comp_typ a) in
      let tK = (CompTyp.get a).CompTyp.kind in
      let _ = dprint (fun () -> "[elCompTyp] of kind : " ^ P.compKindToString cD tK) in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypBase (loc, a ,cS')

| Apx.Comp.TypCobase (loc, a, cS) ->
      let _ = dprint (fun () -> "[elCompCotyp] Cobase : " ^ R.render_cid_comp_cotyp a) in
      let tK = (CompCotyp.get a).CompCotyp.kind in
      let _ = dprint (fun () -> "[elCompCotyp] of kind : " ^ P.compKindToString cD tK) in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypCobase (loc, a ,cS')

  | Apx.Comp.TypDef (loc, a, cS) ->
      let tK = (CompTypDef.get a).CompTypDef.kind in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
      let tau = (CompTypDef.get a).CompTypDef.typ in
        (* eager expansion of type definitions - to make things simple for now
           -bp *)
      let ms = spineToMSub cS' (Int.LF.MShift 0) in
        Whnf.cnormCTyp (tau, ms)
        (* Int.Comp.TypDef (loc, a, cS') *)

  | Apx.Comp.TypBox (loc, (_,Apx.LF.ClTyp (Apx.LF.MTyp a, psi))) ->
      let _ = dprint (fun () -> "[elCompTyp] TypBox" ) in
      let cPsi = Lfrecon.elDCtx (Lfrecon.Pibox) cD psi in
      let _ = dprint (fun () -> "[elCompTyp] TypBox - cPsi = " ^ P.dctxToString cD cPsi) in
      let tA   = Lfrecon.elTyp (Lfrecon.Pibox) cD cPsi a in
      let tT = Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp tA, cPsi)) in
        (dprint (fun () -> "[elCompTyp] " ^ P.compTypToString cD tT);
         tT)

  | Apx.Comp.TypBox (loc, (_,Apx.LF.ClTyp (Apx.LF.STyp (c,psi), phi))) ->
      let cPsi = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
      let cPhi = Lfrecon.elDCtx Lfrecon.Pibox cD phi in
        Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.STyp (elSvar_class c,cPsi), cPhi))

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cD tau1 in
      let tau2' = elCompTyp cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCross (tau1, tau2) ->
      let tau1' = elCompTyp cD tau1 in
      let tau2' = elCompTyp cD tau2 in
        Int.Comp.TypCross (tau1', tau2')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl  in
      let tau'   = elCompTyp (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox (cdecl', tau')

  | Apx.Comp.TypBool -> Int.Comp.TypBool
  | Apx.Comp.TypInd tau -> Int.Comp.TypInd (elCompTyp cD tau)

(* *******************************************************************************)



let mgCompTyp cD (loc, c) =
  let cK = (CompTyp.get c).CompTyp.kind in
  let _ = dprint (fun () -> "[mgCompTyp] kind of constant " ^
              (R.render_cid_comp_typ c)) in
  let _ = dprint (fun () -> "               " ^
                    P.compKindToString Int.LF.Empty cK) in
  let rec genMetaSpine (cK, t) = match (cK, t) with
    | (Int.Comp.Ctype _, _t) -> Int.Comp.MetaNil
    | (Int.Comp.PiKind (loc', Int.LF.Decl(n,ctyp,_), cK), t) ->
        let (mO, t') = genMetaVar' loc cD (loc', n , ctyp, t) in
        let mS = genMetaSpine (cK, t') in
          Int.Comp.MetaApp (mO, mS) in
  let mS = genMetaSpine (cK, Whnf.m_id) in
    Int.Comp.TypBase (loc, c, mS)

let rec mgCtx cD' (cD, cPsi) = begin match cPsi with
  | Int.LF.CtxVar (Int.LF.CtxOffset psi_var) ->
      let (n , sW) = Whnf.mctxCDec cD psi_var in
	Int.LF.CtxVar (Int.LF.CInst ((n, ref None, cD', Int.LF.CTyp (Some sW),
                                      ref [], Int.LF.Maybe), Whnf.m_id))
  | Int.LF.Null -> Int.LF.Null
  | Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA)) ->
      let cPsi' = mgCtx cD' (cD, cPsi) in
      let tA'   = mgTyp cD' cPsi' tA in
	Int.LF.DDec (cPsi', Int.LF.TypDecl (x, tA'))
   end

let rec inferPatTyp' cD' (cD_s, tau_s) = match tau_s with
  | Int.Comp.TypBool -> Int.Comp.TypBool
  | Int.Comp.TypCross (tau1, tau2) ->
      let tau1' = inferPatTyp' cD' (cD_s, tau1) in
      let tau2' = inferPatTyp' cD' (cD_s, tau2) in
        Int.Comp.TypCross (tau1', tau2')

  | Int.Comp.TypBase (loc, c, _ )  -> mgCompTyp cD' (loc, c)

 | Int.Comp.TypCobase (loc, c, _ )  -> mgCompTyp cD' (loc, c)

  | Int.Comp.TypArr (tau1, tau2)  ->
      let tau1' = inferPatTyp' cD' (cD_s, tau1) in
      let tau2' = inferPatTyp' cD' (cD_s, tau2) in
        Int.Comp.TypArr (tau1', tau2')

  | Int.Comp.TypPiBox ((Int.LF.Decl (x, mtyp,dep)), tau) ->
    let mtyp' = mgCTyp cD' cD_s mtyp in
    let tau'  = inferPatTyp' (Int.LF.Dec (cD', Int.LF.Decl(x, mtyp',dep)))
                             (Int.LF.Dec (cD_s, Int.LF.Decl(x, mtyp,dep)), tau) in
    Int.Comp.TypPiBox (Int.LF.Decl (x, mtyp',dep), tau')

  | Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp (Int.LF.Atom(_, a, _) as _tP) , cPsi))  ->
      let cPsi' = mgCtx cD' (cD_s, cPsi) in
      let tP' = mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind  in
        Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp tP', cPsi'))

and mgClTyp cD' cD_s cPsi' = function
  | Int.LF.MTyp tA -> Int.LF.MTyp (mgTyp cD' cPsi' tA)
  | Int.LF.PTyp tA -> Int.LF.PTyp (mgTyp cD' cPsi' tA)
  | Int.LF.STyp (cl, cPhi) -> Int.LF.STyp (cl, mgCtx cD' (cD_s, cPhi))
and mgCTyp cD' cD_s = function
  | Int.LF.ClTyp (t, cPsi) ->
    let cPsi' = mgCtx cD' (cD_s, cPsi) in
    Int.LF.ClTyp (mgClTyp cD' cD_s cPsi' t, cPsi')
  | Int.LF.CTyp sW -> Int.LF.CTyp sW


let inferPatTyp cD' (cD_s, tau_s) = inferPatTyp' cD' (cD_s, Whnf.cnormCTyp (tau_s, Whnf.m_id))

(* *******************************************************************************)

(* cD |- csp : theta_tau1 => theta_tau2 *)
let rec elCofunExp cD csp theta_tau1 theta_tau2 =
  match (csp, theta_tau1, theta_tau2) with
    | (Apx.Comp.CopatNil loc, (Int.Comp.TypArr (tau1, tau2), theta), (tau', theta')) ->
        if Whnf.convCTyp (tau1, theta) (tau', theta') then
          (Int.Comp.CopatNil loc, (tau2, theta))
        else raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))
    | (Apx.Comp.CopatApp (loc, dest, csp'),
       (Int.Comp.TypArr (tau1, tau2), theta), (tau', theta')) ->
        if Whnf.convCTyp (tau1, theta) (tau', theta') then
          let (csp'', theta_tau') = elCofunExp cD csp'
            ((CompDest.get dest).CompDest.typ,Whnf.m_id) (tau2, theta) in
            (Int.Comp.CopatApp (loc, dest, csp''), theta_tau')
        else raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta'))))
          (*  | (Apx.Comp.CopatMeta (loc, mo, csp'), (Int.Comp.*)

let rec elExp cD cG e theta_tau = elExpW cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Fun (loc, ps, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
    let (cG', ps', ttau2) = elPatSpine cD cG ps theta_tau in
    let x = match ps with
      | Apx.Comp.PatApp (_, Apx.Comp.PatVar (_, x,_), Apx.Comp.PatNil _) -> x
      | _ -> raise (Error (loc, ErrorMsg "fn definition does not support patterns yet. Please provide a single variable instead."))
    in (* We lose name information of PatVar during reconstruction. Need to match on Apx instead... *)
      (* let cG' = Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo (tau1, theta))) in *)
      (* let cG' = Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Whnf.cnormCTyp (tau1, theta))) in *)
      let e' = elExp cD cG' e ttau2 in
      let e'' =  Whnf.cnormExp (Int.Comp.Fun (loc, x, e'), Whnf.m_id) in
      let _ = dprint (fun () -> "[elExp] Fun " ^ Id.render_name x ^ " done ") in
      let _ = dprint (fun () -> "         cD = " ^ P.mctxToString cD ^
                              "\n         cG = " ^ P.gctxToString cD cG') in
      let _ = dprint (fun () -> "[elExp] " ^ P.expChkToString cD cG' e'' ) in
      let _ = dprint (fun () -> "[elExp] has type " ^
                        P.compTypToString cD (Whnf.cnormCTyp theta_tau)) in
        e''

  | (Apx.Comp.Cofun (loc, bs), (Int.Comp.TypCobase (_, a, sp), theta)) ->
      let copatMap = function (Apx.Comp.CopatApp (loc, dest, csp), e')  ->
          let (csp', theta_tau') =
            elCofunExp cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) theta_tau
          in (Int.Comp.CopatApp (loc, dest, csp'), elExpW cD cG e' theta_tau')
      in let bs' = List.map copatMap bs
      in Int.Comp.Cofun (loc, bs')

  (* Allow uniform abstractions for all meta-objects *)
  | (Apx.Comp.MLam (loc, u, e) , (Int.Comp.TypPiBox((Int.LF.Decl(_,_,Int.LF.No)) as cdec, tau), theta)) ->
      let cD' = extend_mctx cD (u, cdec, theta) in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (loc, u, e')

  | (e, (Int.Comp.TypPiBox((Int.LF.Decl(_,_,Int.LF.Maybe)) as cdec, tau), theta))  ->
      let u = mk_name_cdec cdec in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = extend_mctx cD (u, cdec, theta) in
      let e' = Apxnorm.cnormApxExp cD (Apx.LF.Empty) e (cD', Int.LF.MShift 1) in
      let e' = elExp cD' cG' e' (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (Syntax.Loc.ghost, u , e')

  | (Apx.Comp.Syn (loc, i), (tau,t)) ->
      let _ = dprint (fun () -> "[elExp] Syn") in
      let _ = dprint (fun () -> "[elExp] cG = " ^
                        P.mctxToString cD ^ " |- " ^ P.gctxToString cD cG) in
      let (i1,tau1) = elExp' cD cG i in
      let _ = dprint (fun () -> "\n[elExp] Syn i = " ^
                        P.expSynToString cD cG (Whnf.cnormExp' (i1, Whnf.m_id))) in
      let _ = dprint (fun () -> "[elExp] Syn done: \n" ^
                        P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau1))  in
      let (i', tau_t') = genMApp loc cD (i1, tau1) in
      let _ = dprint (fun () -> "[elExp] Unify computation-level types: \n" ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t') ^ " \n      ==        \n"
                        ^
                        P.compTypToString cD (Whnf.cnormCTyp (tau,t) )) in
      let tau0 = Whnf.cnormCTyp (tau,t) in
      let tau1 = Whnf.cnormCTyp tau_t' in
        begin try
          Unify.unifyCompTyp cD (tau0, Whnf.m_id) (tau1, Whnf.m_id);
          dprint (fun () -> "Unified computation-level types\n") ;
          dprint (fun () -> "     " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t') ^ "\n         == \n"
                        ^
                        P.compTypToString cD (Whnf.cnormCTyp (tau,t)) ^ "\n") ;
          Int.Comp.Syn (loc, i')
        with
          | ConvSigma.Error (_loc, msg) ->
              raise (ConvSigma.Error (loc, msg))
          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, (tau,t), tau_t')))
        end


  | (Apx.Comp.Pair(loc, e1, e2), (Int.Comp.TypCross (tau1, tau2), theta)) ->
      let e1' = elExp cD cG e1 (tau1, theta) in
      let e2' = elExp cD cG e2 (tau2, theta) in
        Int.Comp.Pair (loc, e1', e2')

  | (Apx.Comp.LetPair (loc, i, (x, y, e)), (tau, theta)) ->
      let (i', tau_theta') = elExp' cD cG i in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypCross (tau1, tau2), t) ->
              let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Whnf.cnormCTyp (tau1, t))) in
              let cG2 = Int.LF.Dec (cG1, Int.Comp.CTypDecl (y, Whnf.cnormCTyp (tau2, t))) in
              let e'  =  elExp cD cG2 e (tau, theta) in
                Int.Comp.LetPair (loc, i', (x, y, e'))

          | _ -> raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantCross, tau_theta')))
              (* TODO postpone to reconstruction *)
        end

  | (Apx.Comp.Let (loc, i, (x, e)), (tau, theta)) ->
      let (i', (tau',theta')) = elExp' cD cG i in
      let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Whnf.cnormCTyp (tau',theta'))) in
      let e'  =  elExp cD cG1 e (tau, theta) in
        Int.Comp.Let (loc, i', (x,  e'))


  | (Apx.Comp.Box (loc, cM), (Int.Comp.TypBox (_loc, cT), theta)) ->
     Int.Comp.Box (loc, elMetaObj cD cM (cT, theta))

  | (Apx.Comp.Case (loc, prag, i, branches), ((tau, theta) as tau_theta)) ->
      let _ = dprint (fun () -> "[elExp] case ") in
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp] case on " ^ P.expSynToString cD cG (Whnf.cnormExp' (i', Whnf.m_id))) in
      begin match (i', C.cwhnfCTyp tau_theta') with
        | (Int.Comp.Ann (Int.Comp.Box (_ , mC), _ ) as i,
           (Int.Comp.TypBox (_, mT) as tau_s, t (* m_id *))) ->
          let _ = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          if Whnf.closedMetaObj mC then
            let recBranch b =
              let b = elBranch (IndexObj mC) cD cG b (i, tau_s) tau_theta in
              let _ = Gensym.MVarData.reset () in
              b in
            let branches' = List.map recBranch branches in
            Int.Comp.Case (loc, prag, i, branches')
          else
            raise (Error (loc, ValueRestriction (cD, cG, i, (tau_s,t))))

        | (Int.Comp.Ann (Int.Comp.Box (_ , _), _ ) as i, (tau_s, t)) ->
          raise (Error (loc, (IllegalCase (cD, cG, i, (tau_s, t)))))

        | (i, (Int.Comp.TypBox (_, Int.LF.ClTyp (Int.LF.MTyp tP, cPsi)) as tau_s, _mid)) ->
          let _      = dprint (fun () -> "[elExp]"
            ^ "Contexts cD  = " ^ P.mctxToString cD ^ "\n"
            ^ "cG = " ^ P.gctxToString cD cG ^ "\n"
            ^ "Expected Pattern has type :" ^
            P.typToString cD cPsi (tP, LF.id)
            ^  "\n Context of expected pattern type : "
            ^  P.dctxToString cD cPsi
            ^ "\n Checking closedness ... ") in
          if Whnf.closedTyp (Whnf.cnormTyp (tP, Whnf.m_id), LF.id) &&
            Whnf.closedDCtx (Whnf.cnormDCtx (cPsi, Whnf.m_id))
             && Whnf.closedGCtx (Whnf.cnormCtx (cG, Whnf.m_id))
          then
            let recBranch b =
              let _ = dprint (fun () -> "[elBranch - DataObj] " ^
                P.expSynToString cD cG (Whnf.cnormExp' (i, Whnf.m_id)) ^
                " of type "
                ^ P.compTypToString cD tau_s
                ^ "\n") in
              let b = elBranch DataObj cD cG b (i, tau_s) tau_theta in
              let _ = Gensym.MVarData.reset () in
              b in
            let branches' = List.map recBranch branches in
            let b = Int.Comp.Case (loc, prag, i, branches') in
            let _ = (dprint (fun () -> "[elBranch - DataObj] ");
                     dprint (fun () -> "             of type "
                       ^ P.compTypToString cD tau_s
                       ^ " done");
                     dprint (fun () -> "cG = " ^ P.gctxToString cD cG);
                     dprint(fun () ->  "    Reconstructed branch: " ^
                       P.expChkToString cD cG b)) in
            b
          else raise (Error (loc, CompScrutineeTyp (cD, cG, i', (tP, LF.id), cPsi)))

        | (i, (tau_s, t)) ->
          let recBranch b =
            let _ = dprint (fun () -> "[elBranch - PatObj] has type " ) in
            let tau_s = Whnf.cnormCTyp (tau_s, t) in
            let _ = dprint (fun () -> "         " ^ P.compTypToString cD tau_s ^ "\n") in

            let b = elBranch DataObj cD cG b (i, tau_s) tau_theta in
            Gensym.MVarData.reset () ; b in

          let branches' = List.map recBranch branches in
          let _ = dprint (fun () -> "[elBranch - PatObj] of type " ) in
          let _ = dprint (fun () ->  P.compTypToString cD tau_s
            ^ " done \n") in
          Int.Comp.Case (loc, prag, i, branches')

      end

  | (Apx.Comp.If (loc, i, e1, e2), ((tau, theta) as tau_theta)) ->
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypBool , _ ) ->
              let e1' = elExp cD cG e1 tau_theta in
              let e2' = elExp cD cG e2 tau_theta in
                Int.Comp.If (loc, i', e1', e2')
          | _  -> raise (Check.Comp.Error (loc, Check.Comp.IfMismatch (cD, cG, tau_theta')))
        end

  | (Apx.Comp.Hole (loc), (tau, theta)) ->
    let () = Holes.collect (loc, cD, cG, (tau, theta)) in
    Int.Comp.Hole (loc, (fun () -> Holes.getHoleNum loc))

  (* TODO postpone to reconstruction *)
  (* Error handling cases *)
  | (Apx.Comp.Fun (loc, _x, _e),  tau_theta ) ->
      raise (Check.Comp.Error (loc, Check.Comp.FunMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.MLam (loc, _u, _e), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.MLamMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.Pair(loc, _ , _ ), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.PairMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.Box (loc, _ ) , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BoxMismatch (cD, cG, tau_theta)))

and elExp' cD cG i = match i with
  | Apx.Comp.Var (loc, offset) ->
      let tau = lookup cG offset in
      let _ = dprint (fun () -> "[elExp'] Variable " ^ R.render_var cG offset
                        ^ " has type " ^
                        P.compTypToString cD tau) in
      (Int.Comp.Var (loc, offset), (tau, C.m_id))

  | Apx.Comp.DataConst (loc, c) ->
      let _ = dprint (fun () -> "[elExp'] DataConst " ^ R.render_cid_comp_const  c ^
                        "\n has type " ^ P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD ((CompConst.get c).CompConst.typ)) in
     (Int.Comp.DataConst (loc, c), ((CompConst.get c).CompConst.typ, C.m_id))

  | Apx.Comp.DataDest (loc, c) ->
      let _ = dprint (fun () -> "[elExp'] DataDest " ^ R.render_cid_comp_dest  c ^
                        "\n has type " ^ P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD ((CompDest.get c).CompDest.typ)) in
     (Int.Comp.DataDest (loc, c), ((CompDest.get c).CompDest.typ, C.m_id))

  | Apx.Comp.Const (loc,prog) ->
     (Int.Comp.Const (loc,prog), ((Comp.get prog).Comp.typ, C.m_id))

  | Apx.Comp.Apply (loc, i, e) ->
      let _ = dprint (fun () -> "[elExp'] Apply") in
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] Apply - generated implicit arguments") in
        begin match e , tau_theta' with
          | e , (Int.Comp.TypArr (tau2, tau), theta) ->
              let _ = dprint (fun () -> "[elExp'] Inferred type for i' = " ^
                                P.expSynToString cD cG (Whnf.cnormExp' (i', Whnf.m_id)) ^ "\n      " ^
                                P.compTypToString cD (Whnf.cnormCTyp (Int.Comp.TypArr (tau2,tau), theta))
                                ^ "\n") in
              let _ = dprint (fun () -> "[elExp'] Check argument has type " ^
                                P.compTypToString cD (Whnf.cnormCTyp (tau2,theta))) in
              let _ = dprint (fun () -> "\n[elExp'] Result has type " ^
                                P.compTypToString cD (Whnf.cnormCTyp (tau,theta))
                             ^ "\n") in
              let tau' = Whnf.cnormCTyp (tau, theta) in

              let e' = elExp cD cG e (tau2, theta) in

              let i'' = Int.Comp.Apply (loc, i', e') in

              (* let tau'' = Whnf.cnormCTyp (tau', Whnf.m_id) in *)
              let _ = dprint (fun () -> "[elExp'] Apply done : " ) in
              let _ = dprint (fun () -> " cD = " ^ P.mctxToString cD) in
              let _ = dprint (fun () -> "         " ^
                                P.expSynToString cD cG (Whnf.cnormExp' (i'', Whnf.m_id))) in
              let _ = dprint (fun () -> "         has type " ^
                                P.compTypToString cD tau' ^ "\n") in
               (*  (i'', (tau, theta))  - not returnig the type in normal form
      leads to subsequent whnf failure and the fact that indices for context in
      MetaObj are off *)
                (i'', (tau', Whnf.m_id))
          | Apx.Comp.Box (_,mC) , (Int.Comp.TypPiBox (Int.LF.Decl(_,ctyp,_), tau), theta) ->
	        let cM = elMetaObj cD mC (ctyp, theta) in
	        (Int.Comp.MApp (loc, i', cM), (tau, Int.LF.MDot (metaObjToFt cM, theta)))
          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantArrow, tau_theta')))
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.BoxVal (loc, (loc',Apx.Comp.ClObj (psi, Apx.Comp.MObj r))) ->
      let _ = dprint (fun () -> "[elExp'] BoxVal dctx ") in
      let cPsi     = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
      let _ = dprint (fun () -> "[elExp'] BoxVal dctx done: " ^ P.dctxToString cD cPsi ) in
      let (tR, sP) = Lfrecon.elClosedTerm' Lfrecon.Pibox cD cPsi r  in
      let _ = dprint (fun () -> "[elExp'] BoxVal tR done ") in
      (* let sP    = synTerm Lfrecon.Pibox cD cPsi (tR, LF.id) in *)
      let phat     = Context.dctxToHat cPsi in
      let tau      = Int.Comp.TypBox (Syntax.Loc.ghost, Int.LF.ClTyp (Int.LF.MTyp (Int.LF.TClo sP), cPsi)) in
      let cM       = (loc, Int.LF.ClObj(phat, Int.LF.MObj tR)) in
        (Int.Comp.Ann (Int.Comp.Box (loc, cM), tau), (tau, C.m_id))

  | Apx.Comp.BoxVal (loc, (_loc',Apx.Comp.ClObj (phat, _r))) ->
     raise (Error (loc, ErrorMsg "Found MetaObj"))
  | Apx.Comp.BoxVal (loc, (loc', Apx.Comp.CObj (cpsi))) ->
(*     raise (Error (loc, ErrorMsg "Found CtxObj")) *)
     begin
       match cpsi with
       | Apx.LF.CtxVar (ctxvar) ->
	  let c_var = Lfrecon.elCtxVar ctxvar in
	  let cM = (loc', Int.LF.CObj (Int.LF.CtxVar c_var)) in
	  begin
	    match c_var with
	    | (Int.LF.CtxOffset offset) as phi ->
	       let sW = Context.lookupCtxVarSchema cD  phi in
	       let tau = Int.Comp.TypBox (Syntax.Loc.ghost, Int.LF.CTyp (Some sW)) in
	       (Int.Comp.Ann (Int.Comp.Box (loc, cM), tau), (tau, C.m_id))
	    | _ ->
	       raise (Error (loc, ErrorMsg
				    "In general the schema of the given context  cannot be uniquely inferred"))
	  end
     end

  | Apx.Comp.PairVal (loc, i1, i2) ->
      let (i1', (tau1,t1)) = genMApp loc cD (elExp' cD cG i1) in
      let (i2', (tau2,t2)) = genMApp loc cD (elExp' cD cG i2) in
        (Int.Comp.PairVal (loc, i1', i2'),
         (Int.Comp.TypCross (Whnf.cnormCTyp (tau1,t1), Whnf.cnormCTyp (tau2,t2)), C.m_id))


  | Apx.Comp.Ann (e, tau) ->
      let tau' = elCompTyp cD tau in
      let e'   = elExp cD cG e (tau', C.m_id) in
        (Int.Comp.Ann (e', tau'), (tau', C.m_id))


  | Apx.Comp.Equal (loc, i1, i2) ->
      let _ = dprint (fun () -> "[elExp'] Equal ... ") in
      let (i1', ttau1) = genMApp loc cD (elExp' cD cG i1) in
      let (i2', ttau2) = genMApp loc cD (elExp' cD cG i2) in
       if Whnf.convCTyp ttau1 ttau2 then
         (Int.Comp.Equal (loc, i1', i2'), (Int.Comp.TypBool , C.m_id))
       else
         raise (Check.Comp.Error (loc, Check.Comp.EqMismatch (cD, ttau1, ttau2 )))


  | Apx.Comp.Boolean (_ , b)  -> (Int.Comp.Boolean b, (Int.Comp.TypBool, C.m_id))



(* We don't check that each box-expression has approximately
 * the same type as the expression we analyze.
 *
 *)
(*

  recPattern cD delta psi m tPopt =

  Assumptions:
      cO ; cD ; cPsi |- tPopt
      omega ; delta ; psi |- m


* recPattern becomes redundant when we adopt the new parser as default.

*)

and recMObj loc cD' cM (cD, mTskel) = match cM, mTskel with
  | (loc, Apx.Comp.CObj (psi)), CT w ->
      let cPsi' = Lfrecon.checkDCtx loc Lfrecon.Pibox cD' psi w in
      let _    = Lfrecon.solve_constraints  cD' in
      let (cD1', cM', mT') =
	Abstract.mobj cD' (loc, Int.LF.CObj cPsi') (Int.LF.CTyp (Some w)) in
	begin try
	  let l_cd1'    = Context.length cD1'  in
	  let l_delta   = Context.length cD'  in
	    Check.Comp.wf_mctx cD1' ;
            ((l_cd1', l_delta), cD1', cM', mT')
	with
          | Check.Comp.Error (_ , msg) -> raise (Check.Comp.Error (loc, msg))
          |  _ -> raise (Error (loc,MCtxIllformed cD1'))
	end

  | (loc,Apx.Comp.ClObj (psi, Apx.Comp.MObj m)), MT (a, cPsi) ->
      let cPsi' = inferCtxSchema loc (cD, cPsi) (cD', psi) in
      let _     = dprint (fun () -> "[recMObj] inferCtxSchema ... ") in
      let _     = dprint (fun () ->  "Scrutinee's context " ^ P.mctxToString cD ^ " |- " ^ P.dctxToString cD cPsi) in
      let _     = dprint (fun () ->  "Pattern's context  " ^ P.mctxToString cD' ^ " |- " ^ P.dctxToString cD' cPsi') in
      let _     = dprint (fun () -> "[recMObj] inferCtxSchema done") in
      let _     = dprint (fun () -> "[mgAtomicTyp] Generate mg type in context " ^
			    P.dctxToString cD' cPsi' ) in
      let tP'  = mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind in
      let _    = dprint (fun () -> "[recMObj] Reconstruction of pattern of type  " ^
			   P.typToString cD' cPsi' (tP', LF.id)) in
      let tR   = Lfrecon.elTerm' Lfrecon.Pibox cD' cPsi' m (tP', LF.id) in
      let _    = Lfrecon.solve_constraints  cD' in
      let _    = dprint (fun () -> "recMObj: Elaborated pattern...\n" ^ P.mctxToString cD' ^ "  ;   " ^
			   P.dctxToString cD' cPsi' ^ "\n   |-\n    "  ^ P.normalToString cD' cPsi' (tR, LF.id) ^
			   "\n has type " ^ P.typToString cD' cPsi' (tP', LF.id) ^ "\n") in
      let phat = Context.dctxToHat cPsi' in
      let (cD1', cM', mT') =
	Abstract.mobj cD' (loc, Int.LF.ClObj (phat, Int.LF.MObj tR)) (Int.LF.ClTyp (Int.LF.MTyp tP', cPsi')) in
	begin try
	  let _   = dprint (fun () -> "recMObj: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                              P.mctxToString cD1' ^ "  |-    " ^ P.metaObjToString cD1' cM' ^ " :  "  ^
                              P.metaTypToString cD1' mT' ^ "\n  ") in
	  let l_cd1'    = Context.length cD1'  in
	  let l_delta   = Context.length cD'  in
	    Check.Comp.wf_mctx cD1' ;
            ((l_cd1', l_delta), cD1', cM', mT')
	with
          | Check.Comp.Error (_ , msg) -> raise (Check.Comp.Error (loc, msg))
          (* |  _ -> raise (Error (loc,MCtxIllformed cD1')) *)
	end

(* inferCtxSchema loc (cD, cPsi) (cD', cPsi') = ()
    cPsi is the context of the scrutinee
    cPsi' is the context of the pattern
    return elaborated cPsi'
    or raise exception
   TODO: This is very similar to unifyDCtxWithFCVar
*)
and inferCtxSchema loc (cD,cPsi) (cD', cPsi') = match (cPsi , cPsi') with
      | (Int.LF.Null , Apx.LF.Null) -> Int.LF.Null
      | (Int.LF.CtxVar (Int.LF.CtxOffset psi1_var), cPsi') ->
          let _ = dprint (fun () -> "[inferSchema] outside context cD = " ^ P.mctxToString cD )
          in
          let _ = dprint (fun () -> "[inferSchema] local context in branch : cD' " ^ P.mctxToString cD' ) in
          let _ = dprint (fun () -> "[inferSchema] looking up psi = " ^
                            P.dctxToString cD cPsi) in
          let (_ , s_cid) = Whnf.mctxCDec cD psi1_var in
	  elDCtxAgainstSchema loc Lfrecon.Pibox cD' cPsi' s_cid

      | (Int.LF.DDec (cPsi1, Int.LF.TypDecl(_ , _tA1)) , Apx.LF.DDec (cPsi2, Apx.LF.TypDecl(x , tA2))) ->
        let cPsi'' = inferCtxSchema loc (cD, cPsi1) (cD',cPsi2) in
	let tA = Lfrecon.elTyp Lfrecon.Pibox cD' cPsi'' tA2 in
	Int.LF.DDec (cPsi'', Int.LF.TypDecl (x, tA))
      | _ ->
	let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD' cPsi' in
	raise (Error (loc, PatternContextClash (cD, cPsi, cD', cPsi')))

(* ********************************************************************************)
(* Elaborate computation-level patterns *)

and elPatMetaObj cD pat (cdecl, theta) = begin match pat with
  | Apx.Comp.PatMetaObj (loc, cM) ->
    let (mO,t') = elMetaObjCTyp loc cD cM theta cdecl in
    (Int.Comp.PatMetaObj (loc, mO), t')
  | Apx.Comp.PatEmpty (loc, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatConst (loc, _, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatFVar (loc, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatVar (loc, _ , _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatPair (loc, _ , _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatTrue loc -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatFalse loc -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatAnn (loc, _, _) -> raise (Error (loc, PatAnn))

end

and elPatChk (cD:Int.LF.mctx) (cG:Int.Comp.gctx) pat ttau = match (pat, ttau) with
  | (Apx.Comp.PatEmpty (loc, cpsi), (tau, theta)) ->
      let cPsi' = Lfrecon.elDCtx (Lfrecon.Pibox) cD cpsi in
      let Int.Comp.TypBox (_ , Int.LF.ClTyp (Int.LF.MTyp _tQ, cPsi_s)) = Whnf.cnormCTyp ttau  in
        begin try
          Unify.unifyDCtx (Int.LF.Empty) cPsi' cPsi_s;
          (Int.LF.Empty, Int.Comp.PatEmpty (loc, cPsi'))
        with Unify.Failure _msg ->
          raise (Error.Violation "Context mismatch in pattern")
        end
  | (Apx.Comp.PatVar (loc, name, x) , (tau, theta)) ->
      let tau' = Whnf.cnormCTyp (tau, theta) in
      let _  = dprint (fun () -> "Inferred type of pat var " ^ Id.render_name name )  in
      let _ = dprint (fun () -> " ..... as   " ^ P.compTypToString cD  tau')
      in
      (Int.LF.Dec(cG, Int.Comp.CTypDecl (name, tau')),
       Int.Comp.PatVar (loc, x))
(*  | (Apx.Comp.PatFVar (loc, x) , ttau) ->
       (FPatVar.add x (Whnf.cnormCTyp ttau);
        (* indexing guarantees that all pattern variables occur uniquely *)
       Int.Comp.PatFVar (loc, x))
*)
  | (Apx.Comp.PatTrue  loc, (Int.Comp.TypBool, _)) ->
      (cG, Int.Comp.PatTrue loc)
  | (Apx.Comp.PatFalse loc, (Int.Comp.TypBool, _)) ->
      (cG, Int.Comp.PatFalse loc)
  | (Apx.Comp.PatConst (loc, _c, _), ttau) ->
      let (cG', pat', ttau') = elPatSyn cD cG pat in
      let _ = dprint (fun () -> "[elPatChk] expected tau : = " ^
                        P.compTypToString cD (Whnf.cnormCTyp ttau)) in
      let _ = dprint (fun () -> "[elPatChk] inferred tau' : = " ^
                        P.compTypToString cD (Whnf.cnormCTyp ttau')) in
        begin try
          Unify.unifyCompTyp cD ttau ttau' ;
          (cG', pat')
        with Unify.Failure msg ->
          dprint (fun () -> "Unify Error: " ^ msg) ;
           raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, ttau, ttau')))
        end

  | (Apx.Comp.PatPair (loc, pat1, pat2) , (Int.Comp.TypCross (tau1, tau2), theta)) ->
      let (cG1, pat1') = elPatChk cD cG pat1 (tau1, theta) in
      let (cG2, pat2') = elPatChk cD cG1 pat2 (tau2, theta) in
        (cG2, Int.Comp.PatPair (loc, pat1', pat2'))

  | (Apx.Comp.PatMetaObj (loc, cM) , (Int.Comp.TypBox (_loc, ctyp), theta)) ->
     (cG, Int.Comp.PatMetaObj (loc, elMetaObj cD cM (ctyp, theta)))
  (* Error handling cases *)
  | (Apx.Comp.PatTrue loc , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.PatIllTyped (cD, Int.LF.Empty,
                                                            Int.Comp.PatTrue loc, tau_theta, (Int.Comp.TypBool, Whnf.m_id))))
  | (Apx.Comp.PatFalse loc , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.PatIllTyped (cD, Int.LF.Empty,
                                                            Int.Comp.PatFalse loc, tau_theta, (Int.Comp.TypBool, Whnf.m_id))))
  | (Apx.Comp.PatPair(loc, _ , _ ), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.PairMismatch (cD, Int.LF.Empty, tau_theta)))
  | (Apx.Comp.PatMetaObj (loc, _) , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BoxMismatch (cD, Int.LF.Empty, tau_theta)))
  | (Apx.Comp.PatAnn (loc, _, _ ) , ttau) ->
      let (cG', pat', ttau') = elPatSyn cD cG pat in
      let _ = dprint (fun () -> "[elPatChk] expected tau : = " ^
                        P.compTypToString cD (Whnf.cnormCTyp ttau)) in
      let _ = dprint (fun () -> "[elPatChk] inferred tau' : = " ^
                        P.compTypToString cD (Whnf.cnormCTyp ttau')) in
        begin try
          Unify.unifyCompTyp cD ttau ttau' ;
          (cG', pat')
        with Unify.Failure msg ->
          dprint (fun () -> "Unify Error: " ^ msg) ;
          raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, ttau, ttau')))
        end


 and elPatSyn (cD:Int.LF.mctx) (cG:Int.Comp.gctx) pat = match pat with
  | Apx.Comp.PatAnn (loc, pat, tau) ->
      let tau' = elCompTyp cD tau in
      let (cG', pat') = elPatChk cD cG pat (tau', Whnf.m_id) in
        (cG', Int.Comp.PatAnn (loc, pat', tau'), (tau', Whnf.m_id))

  | Apx.Comp.PatConst (loc, c, pat_spine) ->
      let tau = (CompConst.get c).CompConst.typ in
      let _   = dprint (fun () -> "[elPat] PatConst = " ^ R.render_cid_comp_const c)
      in
      let (cG1, pat_spine', ttau') = elPatSpine cD cG pat_spine (tau, Whnf.m_id) in
        (cG1, Int.Comp.PatConst (loc, c, pat_spine'), ttau')
(*
  | Apx.Comp.PatTrue  loc ->  (Int.Comp.PatTrue loc ,
                               (Int.Comp.TypBool, Whnf.m_id))
  | Apx.Comp.PatFalse loc -> (Int.Comp.PatFalse loc,
                              (Int.Comp.TypBool, Whnf.m_id))
*)

and elPatSpine (cD:Int.LF.mctx) (cG:Int.Comp.gctx) pat_spine ttau =
  elPatSpineW cD cG pat_spine (Whnf.cwhnfCTyp ttau)

and elPatSpineW cD cG pat_spine ttau = match pat_spine with
  | Apx.Comp.PatNil loc ->
      (match ttau with
	| (Int.Comp.TypPiBox (Int.LF.Decl (n, ctyp, Int.LF.Maybe), tau), theta) ->
	  let (mO,t') = genMetaVar' loc cD (loc, n, ctyp, theta) in
          let pat'  = Int.Comp.PatMetaObj (loc, mO) in
          let ttau' = (tau, t') in
          let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
              (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)
          | _ ->   (cG, Int.Comp.PatNil, ttau))

  | Apx.Comp.PatApp (loc, pat', pat_spine')  ->
      (match ttau with
         | (Int.Comp.TypArr (tau1, tau2), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let _ = dprint (fun () -> "[elPatChk] ttau1 = " ^
                               P.compTypToString cD (Whnf.cnormCTyp (tau1, theta))) in
             let (cG', pat) = elPatChk cD cG pat' (tau1, theta) in
             let (cG'', pat_spine, ttau2) = elPatSpine cD cG' pat_spine' (tau2, theta) in
               (cG'', Int.Comp.PatApp (loc, pat, pat_spine), ttau2)
	 | (Int.Comp.TypPiBox ((Int.LF.Decl (n, ctyp, Int.LF.Maybe)), tau), theta) ->
	     let _ = (dprint (fun () -> "[elPatSpine] TypPiBox implicit ttau = ");
                      dprint (fun () -> "       " ^ P.compTypToString cD (Whnf.cnormCTyp ttau))) in
	     let (mO,t') = genMetaVar' loc cD (loc, n, ctyp, theta) in
             let pat'  = Int.Comp.PatMetaObj (loc, mO) in
             let ttau' = (tau, t')
             in
             let _ = (dprint (fun() -> "[elPatSpine] elaborate spine against " );
                      dprint (fun () -> "theta = " ^ P.msubToString cD t');
                      dprint (fun () -> "ttau'   " ^ P.compTypToString cD (Whnf.cnormCTyp ttau'))) in
             let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
               (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

          | (Int.Comp.TypPiBox (Int.LF.Decl (_,ctyp,dep), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypPiBox explicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let (pat, theta') = elPatMetaObj cD pat' (ctyp, theta) in
             let _ = dprint (fun () -> "[elPatSpine] pat = " ^ P.patternToString cD cG pat ) in
             let _ = dprint (fun () -> "[elPatSpine] remaining pattern spine must have type : " ) in
             let _ = dprint (fun () -> "              " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta'))) in
             let (cG1, pat_spine, ttau2) = elPatSpine cD cG pat_spine' (tau, theta') in
               (cG1, Int.Comp.PatApp (loc, pat, pat_spine), ttau2)

          | _ ->  raise (Error (loc, TooManyMetaObj))
      )

and recPatObj' cD pat (cD_s, tau_s) = match pat with
  | Apx.Comp.PatAnn (_ , (Apx.Comp.PatMetaObj (loc, _) as pat') , Apx.Comp.TypBox (loc', (_,Apx.LF.ClTyp(Apx.LF.MTyp a, psi)))) ->
      let _ = dprint (fun () -> "[recPatObj' - PatMetaObj] scrutinee has type tau = " ^ P.compTypToString cD_s  tau_s) in
          let Int.Comp.TypBox (_ , Int.LF.ClTyp (Int.LF.MTyp _tQ, cPsi_s)) = tau_s  in
	  let cPsi = inferCtxSchema loc (cD_s, cPsi_s) (cD, psi) in
	  let tP   = Lfrecon.elTyp (Lfrecon.Pibox) cD cPsi a in
          let ttau' = (Int.Comp.TypBox(loc', Int.LF.ClTyp (Int.LF.MTyp tP, cPsi)), Whnf.m_id) in
          let (cG', pat') = elPatChk cD Int.LF.Empty pat'  ttau' in
            (cG', pat', ttau')

  | Apx.Comp.PatEmpty (loc, cpsi) ->
      begin match tau_s with
       | Int.Comp.TypBox (_ , Int.LF.ClTyp (Int.LF.MTyp (Int.LF.Atom(_, a, _) as _tQ), cPsi_s)) ->
         let cPsi       = inferCtxSchema loc (cD_s, cPsi_s) (cD, cpsi) in
         let tP     =  mgAtomicTyp cD cPsi a (Typ.get a).Typ.kind in
         let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of empty type  " ^
                        P.typToString cD cPsi (tP, LF.id)) in
         let ttau' = (Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp tP, cPsi)), Whnf.m_id) in
           (Int.LF.Empty, Int.Comp.PatEmpty (loc, cPsi), ttau')
      | _ -> raise (Error (loc, CompTypEmpty (cD_s, (tau_s, Whnf.m_id))))
    end
  | Apx.Comp.PatAnn (_ , pat, tau) ->
      let _ = dprint (fun () -> "[recPatObj' PatAnn] scrutinee has type tau = " ^ P.compTypToString cD_s  tau_s) in
      let tau' = elCompTyp cD tau in
      let ttau' = (tau', Whnf.m_id) in
      let (cG', pat') = elPatChk cD Int.LF.Empty pat ttau' in
        (cG', pat', ttau')

  | _ ->
      let _ = dprint (fun () -> "[recPatObj'] -~~> inferPatTyp ") in
      let _ = dprint (fun () -> "[inferPatTyp] : tau_s = " ^ P.compTypToString cD_s  tau_s) in
      let tau_p = inferPatTyp cD (cD_s, tau_s) in
      let _ = dprint (fun () -> "[inferPatTyp] : tau_p = " ^ P.compTypToString cD  tau_p) in
      let ttau' = (tau_p, Whnf.m_id) in
      let (cG', pat')  = elPatChk cD Int.LF.Empty pat ttau' in
        (cG', pat', ttau')


and recPatObj loc cD pat (cD_s, tau_s) =
  let _ = dprint (fun () -> "[recPatObj] scrutinee has type tau = " ) in
  let _ = dprint (fun () -> "       " ^  P.compTypToString cD_s  tau_s) in
  let (cG', pat', ttau') = recPatObj' cD pat (cD_s, tau_s) in
    (* cD' ; cG' |- pat' => tau' (may contain free contextual variables) *)
    (* where cD' = cD1, cD and cD1 are the free contextual variables in pat'
       cG' contains the free computation-level variables in pat'
       cG' and cD' are handled destructively via FVar and FCVar store
      *)
    let _                      = Lfrecon.solve_constraints cD in
    let _ = dprint (fun () -> "[recPatObj] pat (before abstraction) = " ) in
    let _ = dprint (fun () -> "               " ^
                      P.gctxToString cD cG' ) in
    let _ = dprint (fun () -> " \n  |-  " ^
                      P.patternToString cD cG' pat' ) in
    let _ = dprint (fun () -> "[recPatObj] Abstract over pattern and its type") in
    let (cD1, cG1, pat1, tau1) = Abstract.patobj loc cD (Whnf.cnormCtx (cG', Whnf.m_id)) pat' (Whnf.cnormCTyp ttau') in
      begin try
        Check.Comp.wf_mctx cD1 ;
        (* cD1 ; cG1 |- pat1 => tau1 (contains no free contextual variables) *)
        let l_cd1                  = Context.length cD1 in
        let l_delta                = Context.length cD  in
          ((l_cd1, l_delta), cD1, cG1,  pat1, tau1)
      with
          _ -> raise (Error (loc,MCtxIllformed cD1))
      end

(* synRefine caseT (cD, cD1) (Some tR1) (cPsi, tP) (cPsi1, tP1) = (t, cD1')

   if  cD, cD1 ; cPsi  |- tP  <= type
       cD1; cPsi1 |- tP1 <= type
       cD, cD1 ; cPsi  |- tR1 <= tP

   then
       cD1' |- t <= cD, cD1    and

       cD1' |- |[t]|(|[r]|cPsi)  =   |[t]|(|[r1]|cPsi1)
       cD1' ; |[t]|(|[r]|cPsi) |- |[t]|(|[r]|cP)  =   |[t]|(|[r1]|tP1)
*)
and synRefine loc caseT (cD, cD1) pattern1 mT mT1 =
  let cD'    = Context.append cD cD1 in  (*         cD'  = cD, cD1     *)
  let _ = dprint (fun () -> "\n cD' = " ^ P.mctxToString cD' ) in
  let _ = dprint (fun () -> "\n Expected Pattern type : " ^ P.metaTypToString cD' mT ^ "\n") in
  let _ = dprint (fun () -> "\n Inferred Pattern type : " ^ P.metaTypToString cD1 mT1 ) in
  let t      = Ctxsub.mctxToMSub cD'  in                   (*         .  |- t   <= cD'   *)
  let n      = Context.length cD1 in
  let m      = Context.length cD in
  let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
    (* cD, cD1 |- t1 <= cD1 *)
  let mt1    = Whnf.mcomp t1 t in        (*         .  |- mt1 <= cD1   *)
  let mT'    = Whnf.cnormMetaTyp (mT, t) in
  let mT1'   = Whnf.cnormMetaTyp (mT1, mt1) in
  let _ = dprint (fun () -> "BEFORE Unify: \n" ^  "  Inferred pattern type: " ^  P.metaTypToString Int.LF.Empty mT1'
              ^ "\n  Expected pattern type: " ^ P.metaTypToString Int.LF.Empty  mT') in
  let _ = begin try
    Unify.unifyMetaTyp Int.LF.Empty (mT',C.m_id) (mT1', C.m_id) ;
    dprint (fun () -> "Unify successful: \n" ^  "  Inferred pattern type: " ^  P.metaTypToString Int.LF.Empty mT1'
              ^ "\n  Expected pattern type: " ^ P.metaTypToString Int.LF.Empty  mT')
  with Unify.Failure msg ->
    dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n"
	      ^  "  Inferred pattern type: " ^  P.metaTypToString Int.LF.Empty mT1'
              ^ "\n  Expected pattern type: " ^ P.metaTypToString Int.LF.Empty mT');
    raise (Check.Comp.Error (loc, Check.Comp.PattMismatch ((cD1, pattern1, mT1),
                                                           (cD, mT))))
  end
  in
  let _ = begin match caseT with
    | IndexObj cM ->
        begin try
          (dprint (fun () -> "Pattern matching on index object...unify scrutinee with pattern");
           Unify.unifyMetaObj Int.LF.Empty (cM,  t)  (pattern1, mt1)	 (mT', C.m_id);
	   dprint (fun () -> "Unification successful: \n" ^  "  Scrutinee: " ^
		     P.metaObjToString Int.LF.Empty ( Whnf.cnormMetaObj(cM,t) )
              ^ "\n  Pattern: " ^ P.metaObjToString Int.LF.Empty  (Whnf.cnormMetaObj (pattern1, mt1)))
)
        with Unify.Failure msg ->
          (dprint (fun () -> "Unify ERROR: " ^ msg);
           raise (Error (loc, PatIndexMatch (cD, cM))))
	    (*                      raise (Error.Violation "Pattern matching on index
				    argument failed")*)
	end

    | DataObj -> ()
  end
  in
  let _ = dprint (fun () -> "t = " ^ P.msubToString Int.LF.Empty t) in
  let _ = dprnt "AbstractMSub..." in
    (* cD1' |- t' <= cD' *)
  let (t', cD1') = Abstract.msub (Whnf.cnormMSub t) in
  let rec drop t l_delta1 = match (l_delta1, t) with
        | (0, t) -> t
        | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

  let t0   = drop t' n in  (* cD1' |- t0 <= cD *)
  let cM = Whnf.cnormMetaObj (pattern1, Whnf.mcomp t1 t') in
    (* cD1' ; cPsi1_new |- tR1 <= tP1' *)
  let _ = dprint (fun () -> "synRefine [Substitution] t': " ^ P.mctxToString cD1' ^
                    "\n|-\n" ^ P.msubToString cD1' t' ^ "\n <= " ^ P.mctxToString cD' ^ "\n") in
    (t0, t', cD1', cM)

and synPatRefine loc caseT (cD, cD_p) pat (tau_s, tau_p) =
 begin try
   let cD'  = Context.append cD cD_p in   (* cD'  = cD, cD_p   *)
    let _   = dprint (fun () -> "[synPatRefine] cD' = "
                           ^ P.mctxToString cD') in
   let _   = dprint (fun () -> "[synPatRefine] cD' |- tau_s = " ^ P.compTypToString cD' tau_s) in
    let t   = Ctxsub.mctxToMSub cD'  in  (* .  |- t   <= cD'  *)
    let _   = dprint (fun () -> "[synPatRefine] mctxToMSub .  |- t <= cD' ") in
    let _ = dprint (fun () -> "                        " ^
                      P.msubToString  Int.LF.Empty (Whnf.cnormMSub t)) in
    let n   = Context.length cD_p in
    let m   = Context.length cD in
    let t1  = Whnf.mvar_dot (Int.LF.MShift m) cD_p in
      (* cD, cD_p |- t1 <= cD_p *)
    let mt1 = Whnf.mcomp t1 t in         (* .  |- mt1 <= cD1   *)
   let _   = dprint (fun () -> "[synPatRefine] . |- [t]tau_s = " ^
                       P.compTypToString cD' (Whnf.cnormCTyp (tau_s,t))) in
    let tau_s' = Whnf.cnormCTyp (Whnf.cnormCTyp (tau_s, Whnf.m_id), t) in
    let _ = dprint (fun () -> ".... [t]tau_s done ") in
    let tau_p' = Whnf.cnormCTyp (tau_p, mt1) in
    let _  = begin match (caseT, pat) with
               | (DataObj, _) -> ()
               | (IndexObj (_, Int.LF.ClObj (phat, Int.LF.MObj tR')), Int.Comp.PatMetaObj (_, (_,Int.LF.ClObj (__, Int.LF.MObj tR1)))) ->
                   begin try
                     (dprint (fun () -> "Pattern matching on index object...");
                      Unify.unify Int.LF.Empty (Context.hatToDCtx phat) (C.cnorm (tR',  t),  LF.id)
                                                     (C.cnorm (tR1, mt1), LF.id))
                   with Unify.Failure msg ->
                     (dprint (fun () -> "Unify ERROR: " ^ msg);
                      raise (Error.Violation "Pattern matching on index argument failed"))
                   end
               | _ -> raise (Error.Violation "Pattern matching on index objects which are not meta-terms not allowed")
             end
    in

    let _ = dprint (fun () -> "Unify : Inferred pattern type "
                          ^  "  tau_p' =  "
                          ^ P.compTypToString Int.LF.Empty tau_p'
                          ^ "\n   Expected pattern type tau_s' = "
                          ^ P.compTypToString Int.LF.Empty tau_s') in
    let _  = begin try
              Unify.unifyCompTyp (Int.LF.Empty) (tau_s', Whnf.m_id) (tau_p', Whnf.m_id)
             with Unify.Failure msg ->
               (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n"
                          ^  "  Inferred pattern type: "
                          ^ P.compTypToString Int.LF.Empty tau_p'
                          ^ "\n   Expected pattern type: "
                          ^ P.compTypToString Int.LF.Empty tau_s');
                raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, (tau_s', Whnf.m_id), (tau_p', Whnf.m_id)))))
             end in

    let _ = dprnt "AbstractMSub..." in
      (* cD1' |- t' <= cD' where cD' = cD, cD_p *)
    let (t', cD1') = Abstract.msub (Whnf.cnormMSub t) in
    let _ = dprnt "AbstractMSub... done " in
    let rec drop t l_delta1 = match (l_delta1, t) with
        | (0, t) -> t
        | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

    let t0   = drop t' n in  (* cD1' |- t0 <= cD *)

    let pat' = Whnf.cnormPattern (pat,  Whnf.mcomp t1 t') in
    let _    = dprint (fun () -> "cnormPat done ... ") in
      (t0, t', cD1', pat')
  with exn -> raise exn (* raise (Error.Error (loc, Error.ConstraintsLeft))*)
 end

and elBranch caseTyp cD cG branch (i, tau_s) (tau, theta) = match branch with
  | Apx.Comp.EmptyBranch(loc, delta, (Apx.Comp.PatEmpty (loc', cpsi) as pat)) ->
      let cD'    = elMCtx  Lfrecon.Pibox delta in
      let ((l_cd1', l_delta) , cD1', _cG1,  pat1, tau1)  =  recPatObj loc cD' pat  (cD, tau_s)  in
      let _ = dprint (fun () -> "[elBranch] - EmptyBranch " ^
                        "cD1' = " ^ P.mctxToString cD1' ^
                        "pat = " ^ P.patternToString cD1' _cG1 pat1) in
      let tau_s' = Whnf.cnormCTyp (tau_s, Int.LF.MShift l_cd1') in
        (* cD |- tau_s and cD, cD1 |- tau_s' *)
        (* cD1 |- tau1 *)
      let _ = dprint (fun () -> "[Reconstructed pattern] " ^ P.patternToString cD1' _cG1 pat1 ) in
      let (t', t1, cD1'', pat1') = synPatRefine loc DataObj (cD, cD1') pat1 (tau_s', tau1) in
            (*  cD1'' |- t' : cD    and   cD1'' |- t1 : cD, cD1' *)
        Int.Comp.EmptyBranch (loc, cD1'', pat1', t')


   | Apx.Comp.Branch (loc, _omega, delta, Apx.Comp.PatMetaObj(loc',mO), e) ->
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern ... ") in
        begin match tau_s with
          | Int.Comp.TypBox (_, mT0) ->
              let typAnn = (cD, mtypeSkelet loc mT0) in
              let cD'    = elMCtx  Lfrecon.Pibox delta in
		(* ***************  RECONSTRUCT PATTERN BEGIN *************** *)
              let ((l_cd1', l_delta), cD1', mO', mT1') = recMObj loc' cD' mO typAnn in
		(* ***************  RECONSTRUCT PATTERN DONE  *************** *)
              let mT =  Whnf.cnormMetaTyp (mT0, Int.LF.MShift l_cd1') in
		(* NOW: cD , cD1 |- mO : mT   and  cD1 |- mO' : mT1'          *)
		(* ***************                            *************** *)
              let caseT'  = normCaseType (caseTyp, Int.LF.MShift l_cd1') in
		(* *************** Synthesize Refinement Substitution *********)
              let (t', t1, cD1'', mO'') = synRefine loc' caseT' (cD, cD1') mO' mT mT1' in
		(*   cD1''|-  t' : cD   and   cD1''  |- mO'' :  [t']mT
                     cD1''|- t1  : cD, cD1'
		*)
		(* *************** Synthesize Refinement Substitution *************************)
		(* Note: e is in the scope of cD, cD'; however, cD1' = cD1, cD' !!   *)
		(*     and e must make sense in cD, cD1, cD'                         *)
              let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
              let cD'      = Context.append cD cD1' in
              let e1       = Apxnorm.fmvApxExp [] cD' (l_cd1, l_delta, 0) e in

              let _        = dprint (fun () -> "Refinement (from cD): " ^  P.mctxToString cD1'' ^
                                       "\n |- \n " ^ P.msubToString cD1'' t' ^
                                       " \n <= " ^ P.mctxToString cD ^ "\n") in
              let _        = dprint (fun () -> "Refinement (from cD'): " ^  P.mctxToString cD1'' ^
                                       "\n |- \n " ^ P.msubToString cD1'' t1 ^
                                       " \n<= " ^ P.mctxToString cD' ^ "\n") in

              let _ = dprint (fun () -> "\nChecking refinement substitution") in
              let _ = dprint (fun () -> "    " ^  P.mctxToString cD1'' ^
                                "\n |- \n " ^ P.msubToString cD1'' t' ^
                                " \n<= " ^ P.mctxToString cD ^ "\n") in
              let _ = Check.LF.checkMSub loc cD1'' t' cD in
              let _ = dprint (fun () -> "\nChecking refinement substitution :      DONE\n") in

              (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0
                  then cD, cD1' |- e1 apx_exp
              *)
              (* if   cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
		 then cD1'' |- e' apx_exp
              *)
              let e'      =  Apxnorm.cnormApxExp cD' Apx.LF.Empty e1  (cD1'', t1) in
		(* Note: e' is in the scope of cD1''  *)
              let cG   = Whnf.normCtx cG in
              let cG'  = Whnf.cnormCtx (cG, t') in
              let _ = (dprint (fun () -> "Target type tau' = " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta))) ;
                       dprint (fun () -> "t'   = " ^ P.msubToString cD1'' t' )) in

              let tau'    = Whnf.cnormCTyp (tau, Whnf.mcomp theta t') in

              let _       = dprint (fun () -> "[elBranch] Elaborate branch \n" ^
                                      P.mctxToString cD1'' ^ "  ;  " ^
                                      P.gctxToString cD1'' cG' ^ "\n      |-\n" ^
                                      "against type " ^ P.compTypToString cD1'' tau' ^ "\n") in
		(*                             "against type " ^ P.compTypToString cD1'' (C.cnormCTyp ttau') ^ "\n") *)

              let eE'      = elExp cD1'' cG'  e' (tau', Whnf.m_id) in
              let _ = FCVar.clear() in
              let _ = dprint (fun () -> "[elBranch] Pattern " ^
				P.patternToString cD1'' Int.LF.Empty (Int.Comp.PatMetaObj (loc',mO''))) in
              let _ = dprint (fun () -> "[elBranch] Body : \n") in
              let _ = dprint (fun () -> "        " ^ P.expChkToString cD1'' cG' eE') in
		Int.Comp.Branch (loc, cD1'', Int.LF.Empty,
				 Int.Comp.PatAnn (loc',
				   Int.Comp.PatMetaObj (loc', mO''),
				   Int.Comp.TypBox (loc', Whnf.cnormMTyp (mT0,t') )), t', eE')

          | _ ->  raise (Error (loc, (IllegalCase (cD, cG, i, (tau_s, Whnf.m_id)))))
        end

 | Apx.Comp.Branch (loc, _omega, delta, pat, e) ->
     let _  = dprint (fun () -> "[elBranch] Reconstruction of general pattern of type "
                       ^ P.compTypToString cD tau_s) in
    let cD' = elMCtx Lfrecon.Pibox delta in
    let _ = dprint (fun () -> "[recPatObj] reconstruction of delta done : cD_p  (explicit) = " ^ P.mctxToString cD') in

    let ((l_cd1', l_delta), cD1', cG1,  pat1, tau1)  =  recPatObj loc cD' pat (cD, tau_s) in
    let _ = dprint (fun () -> "[recPatObj] done") in
    let _ = dprint (fun () -> "           " ^ P.mctxToString cD1' ^ " ; " ^
                      P.gctxToString cD1' cG1 ^ "\n    |- " ^
                      P.patternToString cD1' cG1 pat1 ^ " : " ^
                      P.compTypToString cD1' tau1) in
    let tau_s' = Whnf.cnormCTyp (tau_s, Int.LF.MShift l_cd1') in
    (* ***************                            *************** *)
    let caseT'  = begin match caseTyp with
                  | IndexObj (l, Int.LF.ClObj (phat, Int.LF.MObj tR')) ->
                      IndexObj (l, Int.LF.ClObj(phat, Int.LF.MObj (Whnf.cnorm (tR', Int.LF.MShift l_cd1'))))
                  | DataObj -> DataObj
                  end in
    (* cD |- tau_s and cD, cD1 |- tau_s' *)
    (* cD1 |- tau1 *)

    let (t', t1, cD1'', pat1') = synPatRefine loc caseT' (cD, cD1') pat1 (tau_s', tau1) in
    (*  cD1'' |- t' : cD    and   cD1'' |- t1 : cD, cD1' *)
    let _ = dprint (fun () -> "[after synPatRefine] cD1'' = " ^ P.mctxToString cD1'' ) in
    let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
    (*   cD1' |- cG1     cD1'' |- t1 : cD, cD1'    cD, cD1' |- ?   cD1' *)
    let cD'      = Context.append cD cD1' in
    let _ = dprint (fun () -> "cD' = " ^ P.mctxToString cD') in
    let _ = dprint (fun () -> "\n     |- cG1 = " ^ P.gctxToString cD' cG1 ) in
    let _ = dprint (fun () -> " \n t1 : cD' = " ^ P.msubToString cD1'' t1) in
    let cG1'    = Whnf.cnormCtx (Whnf.normCtx cG1, t1) in
    let _ = dprint (fun () -> " cD1'' |- cG1 = " ^ P.gctxToString cD1''  cG1') in

    let cG'     = Whnf.cnormCtx (Whnf.normCtx cG, t') in
    let cG_ext  = Context.append cG' cG1' in

    let e1       = Apxnorm.fmvApxExp [] cD'  (l_cd1, l_delta, 0) e in

    let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cD1'' ^
                               "\n |- \n " ^ P.msubToString cD1'' t' ^
                               " \n <= " ^ P.mctxToString cD ^ "\n") in
    let _        = dprint (fun () -> "Refinement: " ^  P.mctxToString cD1'' ^
                               "\n |- \n " ^ P.msubToString cD1'' t1 ^
                               " \n<= " ^ P.mctxToString cD' ^ "\n") in
      (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0
          then cD, cD1' |- e1 apx_exp
      *)
      (* if   cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
                 then cD1'' |- e' apx_exp
      *)
    let e'      =  Apxnorm.cnormApxExp cD' Apx.LF.Empty e1  (cD1'', t1) in
      (* Note: e' is in the scope of cD1''  *)
    let _       = dprint (fun () -> "[Apx.cnormApxExp ] done ") in

    let _ = (dprint (fun () -> "Target type tau' = " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta))) ;
             dprint (fun () -> "t'   = " ^ P.msubToString cD1'' t' )) in
    let tau'    = Whnf.cnormCTyp (tau, Whnf.mcomp theta t') in

    let _       = dprint (fun () -> "[elBranch] Elaborate branch \n" ^
                              P.mctxToString cD1'' ^ "  ;  " ^
                              P.gctxToString cD1'' cG_ext ^ "\n      |-\n" ^
                              "against type " ^ P.compTypToString cD1'' tau' ^
                              "\n") in
    let eE'      = elExp cD1'' cG_ext  e' (tau', Whnf.m_id) in
    let _        = dprint (fun () -> "[elBranch] Body done (general pattern) \n") in
    let _       = FCVar.clear() in
    Int.Comp.Branch (loc, cD1'', cG1', pat1', t', eE')

(* ******************************************************************************* *)
(* TOP LEVEL                                                                       *)


let solve_fvarCnstr = Lfrecon.solve_fvarCnstr
let reset_fvarCnstr = Lfrecon.reset_fvarCnstr

let kind = Lfrecon.elKind Int.LF.Empty Int.LF.Null

let typ rectyp apxT = Lfrecon.elTyp rectyp Int.LF.Empty Int.LF.Null apxT

let schema = elSchema

let compkind = elCompKind Int.LF.Empty

let comptyp tau =
  let tau' = elCompTyp Int.LF.Empty tau in
  let _ = Lfrecon.solve_constraints Int.LF.Empty in
  let _ = dprint (fun () -> "[elCompTyp] " ^ P.compTypToString Int.LF.Empty tau' ^ " done \n") in
  tau'

let comptypdef loc a (tau, cK) =
  let cK = elCompKind Int.LF.Empty cK in
  let _  = (solve_fvarCnstr Lfrecon.Pibox;
            Unify.forceGlobalCnstr (!Unify.globalCnstrs)) in
  let (cK,i) = Abstract.compkind cK in
  let _  = (reset_fvarCnstr ();
	    Unify.resetGlobalCnstrs ()) in
  let rec unroll cD cK = begin match cK with
    | Int.Comp.Ctype _ -> cD
    | Int.Comp.PiKind (_, cdecl, cK) -> unroll (Int.LF.Dec(cD, cdecl)) cK
  end in
  let cD  = unroll Int.LF.Empty cK in
  let tau = elCompTyp cD tau in
  let _   = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
  let (tau, k) =  Abstract.comptyp  tau in
   let _   = if k = 0 then () else
                raise (Error(loc, TypeAbbrev a)) in

    ((cD, tau), i, cK)


let exp  = elExp  Int.LF.Empty

let exp' = elExp' Int.LF.Empty
