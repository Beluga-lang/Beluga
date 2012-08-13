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


let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

type error =
  | EtaExpandFMV        of Id.name * Int.LF.mctx * Int.LF.dctx * Int.LF.tclo
  | ValueRestriction    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | IllegalCase         of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | CompScrutineeTyp    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.LF.tclo * Int.LF.dctx
  | MetaObjContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.dctx
  | PatternContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | ContextSchemaClash  of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | MetaObjectClash     of Int.LF.mctx * (Int.Comp.meta_typ * Int.LF.msub)
  | MissingMetaObj
  | TooManyMetaObj

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | EtaExpandFMV (offset, cD, cPsi, sA) ->
          Format.fprintf ppf
            "meta-variable %s to has type %a \n and should be eta-expanded\n"
            (R.render_name offset)
            (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)

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
            "Type %a[%a]@.\
             of scrutinee %a@.\
             is not closed@ or requires that some meta-variables@ introduced in the pattern@ \
             are further restricted,@ i.e. some variable dependencies cannot happen.@ \
             This error may indicate@ that some implicit arguments that are reconstructed@ \
             should be restricted.@."
            (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sP)
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi
            (P.fmt_ppr_cmp_exp_syn cD cG Pretty.std_lvl) i

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

       | MetaObjectClash (cD, (mC, theta)) ->
           Format.fprintf ppf
             "Meta-object type clash.@ \
              Expected meta-object of type: %a"
             (P.fmt_ppr_meta_typ cD Pretty.std_lvl) (Whnf.cnormMetaTyp (mC, theta));

       | MissingMetaObj      ->
           Format.fprintf ppf
             "Too few meta-objects supplied to data-constructor"

       | TooManyMetaObj      ->
           Format.fprintf ppf
             "Too many meta-objects supplied to data-constructor"
))




let rec get_ctxvar cPsi  = match cPsi with
  | Int.LF.Null -> None
  | Int.LF.CtxVar (psi_name) -> Some psi_name
  | Int.LF.DDec (cPsi, _ ) -> get_ctxvar cPsi


(* etaExpandMVstr cPsi sA  = tN
 *
 *  cPsi   |- [s]A <= typ
 *  cPsi   |- ss  <= cPsi'
 *  cPsi'  |- tN   <= [s'][s]A
 *)

let rec etaExpandMVstr loc cO cPsi sA  = etaExpandMVstr' loc cO cPsi (Whnf.whnfTyp sA)

and etaExpandMVstr' loc cO cPsi sA  = match sA with
  | (Int.LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = ConvSigma.flattenDCtx cPsi in
      let s_proj = ConvSigma.gen_conv_sub conv_list in
      let tQ    = ConvSigma.strans_typ (tP, s) conv_list in
      (*  cPsi |- s_proj : cPhi
          cPhi |- tQ   where  cPsi |- tP   and [s_proj]^-1([s]tP) = tQ  *)

      let (ss', cPhi') = Subord.thin' cO a cPhi in
      (* cPhi |- ss' : cPhi' *)
      let ssi' = LF.invert ss' in
      (* cPhi' |- ssi : cPhi *)
      (* cPhi' |- [ssi]tQ    *)
      let u = Whnf.newMVar None (cPhi', Int.LF.TClo(tQ,ssi')) in
      (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
      let ss_proj = LF.comp ss' s_proj in
        Int.LF.Root (loc, Int.LF.MVar (u, ss_proj), Int.LF.Nil)

  | (Int.LF.PiTyp ((Int.LF.TypDecl (x, _tA) as decl, _ ), tB), s) ->
      Int.LF.Lam (loc, x, etaExpandMVstr loc cO (Int.LF.DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) )




(* etaExpandMMV loc cO cD cPsi sA  = tN
 *
 *  cO ; cD ; cPsi   |- [s]A <= typ
 *
 *  cO ; cD ; cPsi   |- tN   <= [s]A
 *)
let rec etaExpandMMVstr loc cO cD cPsi sA  = etaExpandMMVstr' loc cO cD cPsi (Whnf.whnfTyp sA)

and etaExpandMMVstr' loc cO cD cPsi sA  = match sA with
  | (Int.LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = ConvSigma.flattenDCtx cPsi in
      let s_proj = ConvSigma.gen_conv_sub conv_list in
      let tQ    = ConvSigma.strans_typ (tP, s) conv_list in
      (*  cPsi |- s_proj : cPhi
          cPhi |- tQ   where  cPsi |- tP   and [s_proj]^-1([s]tP) = tQ  *)

      let (ss', cPhi') = Subord.thin' cO a cPhi in
      (* cPhi |- ss' : cPhi' *)
      let ssi' = LF.invert ss' in
      (* cPhi' |- ssi : cPhi *)
      (* cPhi' |- [ssi]tQ    *)
      let u = Whnf.newMMVar None (cD, cPhi', Int.LF.TClo(tQ,ssi')) in
      (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
      let ss_proj = LF.comp ss' s_proj in
        Int.LF.Root (loc, Int.LF.MMVar (u, (Whnf.m_id, ss_proj)), Int.LF.Nil)

  | (Int.LF.PiTyp ((Int.LF.TypDecl (x, _tA) as decl, _ ), tB), s) ->
      Int.LF.Lam (loc, x, etaExpandMMVstr loc cO cD (Int.LF.DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) )


type caseType  = IndexObj of Int.LF.psi_hat * Int.LF.normal | DataObj

type typAnn    = FullTyp of Apx.LF.typ | PartialTyp of cid_typ

(** This function does the same thing as unifyDCtx in unify.ml, but in
    addition records new names for variables left free by the user
    when they are instantiated. *)
let rec unifyDCtxWithFCVar cD cPsi1 cPsi2 =
  let rec loop cD cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
    | (Int.LF.Null , Int.LF.Null) -> ()

    | (Int.LF.CtxVar (Int.LF.CInst (_n1, ({contents = None} as cvar_ref1), _schema1, _cO1, _cD1)),
       Int.LF.CtxVar (Int.LF.CInst (_n2, ({contents = None} as cvar_ref2), _schema2, _cO2, _cD2))) ->
      if cvar_ref1 != cvar_ref2 then
        Unify.instantiateCtxVar (cvar_ref1, cPsi2)

    | (Int.LF.CtxVar (Int.LF.CInst (_n, ({contents = None} as cvar_ref), s_cid, _cO, _cD)) , cPsi) ->
      begin
        Unify.instantiateCtxVar (cvar_ref, cPsi);
        match Context.ctxVar cPsi with
          | None -> ()
          | Some (Int.LF.CtxName psi) ->
            FCVar.add psi (cD, Int.LF.CDecl (psi, s_cid, Int.LF.No))
          | _ -> ()
      end

    | (cPsi, Int.LF.CtxVar (Int.LF.CInst (_n, ({contents = None} as cvar_ref), s_cid, _cO, _cD))) ->
      begin
        Unify.instantiateCtxVar (cvar_ref, cPsi);
        match Context.ctxVar cPsi with
          | None -> ()
          | Some (Int.LF.CtxName psi) ->
            FCVar.add psi (cD, Int.LF.CDecl (psi, s_cid, Int.LF.No))
          | _ -> ()
      end

    | (Int.LF.CtxVar  psi1_var , Int.LF.CtxVar psi2_var) when psi1_var = psi2_var -> ()

    | (Int.LF.DDec (cPsi1, Int.LF.TypDecl(_ , tA1)) ,
       Int.LF.DDec (cPsi2, Int.LF.TypDecl(_ , tA2))) ->
      loop cD cPsi1 cPsi2;
      Unify.unifyTyp cD cPsi1 (tA1, LF.id) (tA2, LF.id)

    | (Int.LF.DDec (cPsi1, Int.LF.TypDeclOpt _),
       Int.LF.DDec (cPsi2, Int.LF.TypDeclOpt _ )) ->
      loop cD cPsi1 cPsi2

    | _ -> raise (Unify.Failure "context clash")

  in loop cD (Whnf.normDCtx cPsi1)  (Whnf.normDCtx cPsi2)

let rec raiseType cPsi tA = match cPsi with
  | Int.LF.Null -> tA
  | Int.LF.DDec (cPsi', decl) ->
    raiseType cPsi' (Int.LF.PiTyp ((decl, Int.LF.Maybe), tA))


(* -------------------------------------------------------------*)

let rec apxget_ctxvar psi  = match psi with
  | Apx.LF.Null -> None
  | Apx.LF.CtxVar (psi_name) -> Some psi_name
  | Apx.LF.DDec (psi, _ ) -> apxget_ctxvar psi

let rec apx_length_typ_rec t_rec = match t_rec with
  | Apx.LF.SigmaLast _ -> 1
  | Apx.LF.SigmaElem (x, _ , rest ) ->
      (print_string (R.render_name x ^ "  ");
      1 + apx_length_typ_rec rest )

let rec getctxvarFromHat phat = match phat with
  | (None, _ ) -> None
  | (Some (Int.LF.CtxName n), _ ) -> Some(Apx.LF.CtxName n)
  | (Some (Int.LF.CtxOffset n), _ ) -> Some(Apx.LF.CtxOffset n)

let rec apxget_ctxvar_mobj mO = match mO with
  | Apx.Comp.MetaCtx (_, cPsi) -> apxget_ctxvar cPsi
  | Apx.Comp.MetaObjAnn (_, cPsi, _tM) -> apxget_ctxvar cPsi
  | Apx.Comp.MetaObj (_, phat, _tM) ->
      getctxvarFromHat phat
  | Apx.Comp.MetaParam (_, phat, _h) ->
      getctxvarFromHat phat

let rec lookup cG k = match cG, k with
  | Int.LF.Dec (_cG', Int.Comp.CTypDecl (_, tau)), 1 -> tau
  | Int.LF.Dec ( cG', Int.Comp.CTypDecl (_, _tau)), k -> lookup cG' (k-1)

(* -------------------------------------------------------------*)

(* Solve free variable constraints *)


(* ******************************************************************* *)

let rec elCCtx omega = match omega with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (omega, Apx.LF.CDecl(g,schema_cid)) ->
      let cO    = elCCtx omega in
        Int.LF.Dec (cO, Int.LF.CDecl (g, schema_cid, Int.LF.No))

let rec elTypDeclCtx cD  = function
  | Apx.LF.Empty ->
      Int.LF.Empty

  | Apx.LF.Dec (ctx, Apx.LF.TypDecl (name, typ)) ->
      let ctx'     = elTypDeclCtx cD ctx in
      let tA       = Lfrecon.elTyp Lfrecon.Pi cD (Context.projectCtxIntoDctx ctx') typ in
      let typDecl' = Int.LF.TypDecl (name, tA) in
        Int.LF.Dec (ctx', typDecl')

let rec elSchElem (Apx.LF.SchElem (ctx, typRec)) =
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

let rec elSchema (Apx.LF.Schema el_list) =
   Int.LF.Schema (List.map elSchElem el_list)

let rec elDCtxAgainstSchema loc recT cD psi s_cid = match psi with
  | Apx.LF.Null -> Int.LF.Null

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
        let (_ , Int.LF.CDecl (_, s_cid', _ )) = FCVar.get psi in
          if s_cid = s_cid' then Int.LF.CtxVar (Int.LF.CtxName psi)
          else
            (let schema = Schema.get_schema s_cid in
             let c_var' = Int.LF.CtxName psi in
               raise (Check.LF.Error (Syntax.Loc.ghost, Check.LF.CtxVarMismatch (cD, c_var', schema))))
      with Not_found ->
        (FCVar.add psi (cD, Int.LF.CDecl (psi, s_cid, Int.LF.No));
         Int.LF.CtxVar (Int.LF.CtxName psi))
      end
  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtxAgainstSchema loc recT cD psi' s_cid in
      let tA   = Lfrecon.elTyp recT cD cPsi a in
      (* let _ = Check.LF.checkTypeAgainstSchema cO cD cPsi' tA elements in          *)
      let _ = dprint (fun () -> "[elDCtxAgainstSchema] " ^ R.render_name x ^ ":" ^
                        P.typToString cD cPsi (tA, LF.id)) in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))

let rec elCDecl recT cD cdecl = match cdecl with
  | Apx.LF.MDecl (u, a, psi) ->
      let cPsi = Lfrecon.elDCtx recT cD psi in
      let tA   = Lfrecon.elTyp recT cD cPsi a in
        Int.LF.MDecl (u, tA, cPsi)
  | Apx.LF.PDecl (u, a, psi) ->
      let cPsi = Lfrecon.elDCtx recT cD psi in
      let tA   = Lfrecon.elTyp recT cD cPsi a in
        Int.LF.PDecl (u, tA, cPsi)

  | Apx.LF.SDecl (u, phi, psi) ->
      let cPsi = Lfrecon.elDCtx recT cD psi in
      let cPhi = Lfrecon.elDCtx recT cD phi in
        Int.LF.SDecl (u, cPhi, cPsi)

  | Apx.LF.CDecl (g, schema_cid) ->
      Int.LF.CDecl (g, schema_cid, Int.LF.No)

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
let mgTyp cD cPsi a kK =
  let (flat_cPsi, conv_list) = flattenDCtx cPsi in
    let s_proj   = gen_conv_sub conv_list in

  let rec genSpine sK = match sK with
    | (Int.LF.Typ, _s) ->
        Int.LF.Nil

(*    | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA1), _ ), kK), s) ->
        let u  = Whnf.newMMVar (cD, cPsi , Int.LF.TClo (tA1,s)) in
        let h  = Int.LF.MMVar (u, (Whnf.m_id, LF.id)) in
        let tR = Int.LF.Root (Syntax.Loc.ghost, h, Int.LF.Nil) in  (* -bp needs to be eta-expanded *)
        let _ = dprint (fun () -> "Generated meta^2-variable " ^
                          P.normalToString cD cPsi (tR, LF.id)) in
        let _ = dprint (fun () -> "of type : " ^ P.dctxToString cD cPsi ^
                          " |- " ^ P.typToString cD cPsi (tA1,s)) in
        let tS = genSpine (kK, Int.LF.Dot (Int.LF.Head h, s)) in
        (* let tS = genSpine (kK, Int.LF.Dot (Int.LF.Obj tR , s)) in  (* -bp would not work if h is functional type *) *)
          Int.LF.App (tR, tS)
*)

    | (Int.LF.PiKind ((Int.LF.TypDecl (n, tA1), _ ), kK), s) ->
        let tA1' = strans_typ (tA1, s) conv_list in
        let u  = Whnf.newMMVar (Some n) (cD, flat_cPsi , tA1') in
        let h  = Int.LF.MMVar (u, (Whnf.m_id, s_proj)) in
        let tR = Int.LF.Root (Syntax.Loc.ghost, h, Int.LF.Nil) in  (* -bp needs to be
          eta-expanded *)

        (* let tR = etaExpandMMVstr None cD cPsi (tA1, s) in  *)

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

let rec genMApp loc cD (i, tau_t) = genMAppW loc cD (i, Whnf.cwhnfCTyp tau_t)

and genMAppW loc cD (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox ((Int.LF.MDecl(n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let psihat  = Context.dctxToHat cPsi' in
      let tA'   = C.cnormTyp (tA, theta) in

      let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
      (* let tM'   = etaExpandMMVstr loc cD  cPsi' (tA', LF.id) in *)
        let _   = dprint (fun () -> "[genMApp] Generated meta^2-variable " ^
                            P.dctxToString cD cPsi' ^ " . " ^
                            P.normalToString cD cPsi' (tM', LF.id)) in
        let _   = dprint (fun () -> "          of type : " ^
                          P.dctxToString cD cPsi' ^ " |- " ^
                          P.typToString cD cPsi' (tA',LF.id)) in
        let _ = dprint (fun () -> "[genMApp] tau = " ^
                          P.compTypToString cD (Whnf.cnormCTyp (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)))) in
        genMApp loc cD ((Int.Comp.MApp (loc, i, (psihat, Int.Comp.NormObj tM'))),
                        (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)))


  | (Int.Comp.TypPiBox ((Int.LF.PDecl(n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let psihat  = Context.dctxToHat cPsi' in
      let tA'   = C.cnormTyp (tA, theta) in

      let p     = Whnf.newMPVar (Some n) (cD, cPsi', tA') in
      let h     = Int.LF.MPVar (p, (Whnf.m_id, LF.id)) in
      (* let tM'   = etaExpandMMVstr loc cD  cPsi' (tA', LF.id) in *)
        let _   = dprint (fun () -> "[genMApp] Generated #meta^2-variable ") in
        let _   = dprint (fun () -> "          of type : " ^
                          P.dctxToString cD cPsi' ^ " |- " ^
                          P.typToString cD cPsi' (tA',LF.id)) in
        let _ = dprint (fun () -> "[genMApp] tau = " ^
                          P.compTypToString cD (Whnf.cnormCTyp (tau, Int.LF.MDot (Int.LF.PObj (psihat, h), theta)))) in
        genMApp loc cD ((Int.Comp.MApp (loc, i, (psihat, Int.Comp.NeutObj h))),
                        (tau, Int.LF.MDot (Int.LF.PObj (psihat, h), theta)))

  | (Int.Comp.TypCtxPi ((psi_name, schema_cid, Int.Comp.Implicit), tau), theta)
    ->
      let cPsi = Int.LF.CtxVar (Int.LF.CInst (psi_name, ref None, schema_cid, Int.LF.Empty, cD)) in
      let _   = dprint (fun () -> "[genMApp] Generated ctx-variable " ^
                          P.dctxToString cD cPsi) in
      let _ = dprint (fun () -> "[genMApp] Show tau : " ^
                        P.compTypToString cD
                        (Whnf.cnormCTyp (tau, Int.LF.MDot (Int.LF.CObj (cPsi), theta)))) in
        genMApp loc cD  ((Int.Comp.CtxApp (loc, i, cPsi)),
                         (tau, Int.LF.MDot (Int.LF.CObj (cPsi), theta)))

  | _ ->
      let _ = dprint (fun () -> "[genMAppp]  done " ^
                                P.mctxToString cD ^ " \n   |- " ^
                                P.compTypToString cD (Whnf.cnormCTyp tau_t)) in
        (i, tau_t)


(* elCompKind  cPsi k = K *)
let rec elCompKind cD k = match k with
  | Apx.Comp.Ctype loc ->
      Int.Comp.Ctype loc

  | Apx.Comp.PiKind (loc, (cdecl, dep), k') ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl   in
      let tK     = elCompKind  (Int.LF.Dec (cD, cdecl')) k' in
      let dep' = match dep with
                   | Apx.Comp.Explicit -> Int.Comp.Explicit
                   |Apx.Comp.Implicit -> Int.Comp.Implicit in
        Int.Comp.PiKind (loc, (cdecl', dep'), tK)

let rec elMetaObj cD cM cTt = match  (cM, cTt) with
  | (Apx.Comp.MetaCtx (loc, psi), (Int.Comp.MetaSchema  w, _)) ->
      let cPsi' = elDCtxAgainstSchema loc Lfrecon.Pibox cD psi w in
        Int.Comp.MetaCtx (loc, cPsi')

  | (Apx.Comp.MetaObj (loc, phat, tM), (Int.Comp.MetaTyp (tA, cPsi), theta)) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      if Lfrecon.unify_phat cD phat (Context.dctxToHat cPsi') then
        let tM' = Lfrecon.elTerm (Lfrecon.Pibox) cD cPsi' tM (C.cnormTyp (tA, theta), LF.id) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _        = Unify.resetGlobalCnstrs () in
        let _        = dprint (fun () -> "[elMetaObj] tA = " ^ P.typToString cD cPsi (tA, LF.id) ) in
        let _        = dprint (fun () -> "[elMetaObj] tM = " ^ P.normalToString cD cPsi (tM', LF.id) ) in
          Int.Comp.MetaObj (loc, phat, tM')
      else
         raise (Error.Violation ("Contexts do not match - MetaObj not of the appropriate meta-type"
                                ^ P.typToString cD cPsi (tA, LF.id)))

  | (Apx.Comp.MetaObjAnn (loc, cPhi, tM), (Int.Comp.MetaTyp (tA, cPsi), theta)) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let cPhi = Lfrecon.elDCtx (Lfrecon.Pibox) cD cPhi in
      let _ = dprint (fun () -> "[elMetaObjAnn] cPsi = " ^ P.dctxToString cD  cPsi') in
      let _ = dprint (fun () -> "[elMetaObjAnn] cPhi = " ^ P.dctxToString cD  cPhi) in
      (* let _    = inferCtxSchema (cD, cPsi') (cD, cPhi) in  *)
      let _ =
        (* unifying two contexts AND inferring schema for psi in
           cPhi, if psi is not in cD *)
        try unifyDCtxWithFCVar cD cPsi' cPhi
        with Unify.Failure _ -> raise (Error (loc, MetaObjContextClash (cD, cPsi', cPhi))) in
      let phat = Context.dctxToHat cPhi  in
      let _ = dprint (fun () -> "[elMetaObjAnn] unfied contexts") in
      let tA' = C.cnormTyp (tA, theta) in
      let _        = dprint (fun () -> "[elMetaObj] tA = " ^ P.typToString cD cPsi' (tA',LF.id) ) in
      let tM' = Lfrecon.elTerm (Lfrecon.Pibox) cD cPsi' tM (tA', LF.id) in
      let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
      let _        = Unify.resetGlobalCnstrs () in
        (* RETURN POSSIBLY A PARAMETER OBJECT *)
      let _        = dprint (fun () -> "[elMetaObj] tM = " ^ P.normalToString cD cPsi' (tM', LF.id) ) in
        Int.Comp.MetaObj (loc, phat, tM')

  | (Apx.Comp.MetaObjAnn (loc, cPhi, tM), (Int.Comp.MetaParamTyp (tA, cPsi), theta)) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let cPhi = Lfrecon.elDCtx (Lfrecon.Pibox) cD cPhi in
      let _ = dprint (fun () -> "[elMetaObjAnn] cPsi = " ^ P.dctxToString cD  cPsi') in
      let _ = dprint (fun () -> "[elMetaObjAnn] cPhi = " ^ P.dctxToString cD  cPhi) in
      let _ =
        (* unifying two contexts AND inferring schema for psi in
           cPhi, if psi is not in cD *)
        try unifyDCtxWithFCVar cD cPsi' cPhi
        with Unify.Failure _ -> raise (Error (loc, MetaObjContextClash (cD, cPsi', cPhi))) in
      let phat = Context.dctxToHat cPhi  in
      let _ = dprint (fun () -> "[elMetaObjAnn] unfied contexts") in
      let tA' = C.cnormTyp (tA, theta) in
      let _   = dprint (fun () -> "[elMetaObj] tA = " ^ P.typToString cD cPsi' (tA',LF.id) ) in
      let tM' = Lfrecon.elTerm (Lfrecon.Pibox) cD cPsi' tM (tA', LF.id) in
      let h   = begin match tM' with
                  | Int.LF.Root(_, ((Int.LF.FPVar (p,s)) as h), Int.LF.Nil) -> h
                  | Int.LF.Root(_, ((Int.LF.PVar (p,s)) as h), Int.LF.Nil) -> h
                  | Int.LF.Root (_, ((Int.LF.BVar k) as h), Int.LF.Nil) -> h
                  | Int.LF.Root (_, (Int.LF.Proj (_, _ ) as h), Int.LF.Nil) -> h
                end in
      let _   = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
      let _   = Unify.resetGlobalCnstrs () in
      let _   = dprint (fun () -> "[elMetaObj] h = " ^ P.headToString cD cPsi' h) in
        Int.Comp.MetaParam (loc, phat, h)


  | (Apx.Comp.MetaObj (loc, phat, tM), (Int.Comp.MetaParamTyp (tA, cPsi), theta)) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let tA'   = C.cnormTyp (tA, theta) in
      if Lfrecon.unify_phat cD phat (Context.dctxToHat cPsi') then
        let _ = dprint (fun () -> "[elMetaObj/Param] cPsi = " ^ P.dctxToString cD  cPsi') in
        let _   = dprint (fun () -> "[elMetaObj]/Param tA = " ^ P.typToString cD cPsi' (tA',LF.id) ) in
        let tM' = Lfrecon.elTerm (Lfrecon.Pibox) cD cPsi' tM (tA', LF.id) in
        let h   = begin match tM' with
          | Int.LF.Root(_, ((Int.LF.FPVar (p,s)) as h), Int.LF.Nil) -> h
          | Int.LF.Root(_, ((Int.LF.PVar (p,s)) as h), Int.LF.Nil) -> h
          | Int.LF.Root (_, ((Int.LF.BVar k) as h), Int.LF.Nil) -> h
          | Int.LF.Root (_, (Int.LF.Proj (_, _ ) as h), Int.LF.Nil) -> h
        end in
        let _   = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _   = Unify.resetGlobalCnstrs () in
        let _   = dprint (fun () -> "[elMetaObj] h = " ^ P.headToString cD cPsi' h) in
          Int.Comp.MetaParam (loc, phat, h)
      else
        raise (Error.Violation ("ParamObj not of the appropriate meta-type"
                                ^ P.typToString cD cPsi (tA, LF.id)))

  | (Apx.Comp.MetaParam (loc, phat, h), (Int.Comp.MetaParamTyp (tA, cPsi), theta)) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let tA'   = C.cnormTyp (tA, theta) in
      if Lfrecon.unify_phat cD phat (Context.dctxToHat cPsi') then
        let tM = Apx.LF.Root (loc, h, Apx.LF.Nil) in
        let Int.LF.Root (_, h, Int.LF.Nil) = Lfrecon.elTerm  (Lfrecon.Pibox) cD cPsi' tM (tA', LF.id) in
        let _  = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _  = Unify.resetGlobalCnstrs () in
        let _  = dprint (fun () -> "[elMetaObj] expected tA = " ^ P.typToString cD cPsi' (tA', LF.id) ) in
        let _  = dprint (fun () -> "[elMetaObj] h = " ^ P.headToString cD cPsi' h) in
          Int.Comp.MetaParam (loc, phat, h)
      else
        raise (Error.Violation ("MetaParameter not of the appropriate meta-type"
                                ^ P.typToString cD cPsi (tA, LF.id)))

  | (Apx.Comp.MetaCtx(loc, _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
  | (Apx.Comp.MetaObj(loc, _ , _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
  | (Apx.Comp.MetaParam(loc, _ , _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
  | (Apx.Comp.MetaObjAnn(loc, _ , _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
    (* The case for parameter types should be handled separately, for better error messages -bp *)


and elMetaSpine loc cD s cKt  = match (s, cKt) with
  | (Apx.Comp.MetaNil , (Int.Comp.Ctype _ , _ )) -> Int.Comp.MetaNil

  | (Apx.Comp.MetaNil , (Int.Comp.PiKind (_, (cdecl, _ ) , _cK), theta )) ->
       raise (Error (loc, MissingMetaObj))

  | (Apx.Comp.MetaApp (m, s), (Int.Comp.Ctype _ , _ )) ->
       raise (Error (loc, TooManyMetaObj))

  | (s, (Int.Comp.PiKind (_ , (Int.LF.CDecl (psi_name , schema_cid, _ ), Int.Comp.Implicit ), cK), theta )) ->
      let cPsi = Int.LF.CtxVar (Int.LF.CInst (psi_name, ref None, schema_cid, Int.LF.Empty, cD)) in
      let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.CObj(cPsi), theta)) in
        Int.Comp.MetaApp (Int.Comp.MetaCtx (loc, cPsi), cS)

  | (s, (Int.Comp.PiKind (_loc, (Int.LF.MDecl (n , tA, cPsi), Int.Comp.Implicit), cK), theta )) ->
      let psihat  = Context.dctxToHat cPsi in
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let tA'   = C.cnormTyp (tA, theta) in

      let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
      let mS    = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)) in
        Int.Comp.MetaApp (Int.Comp.MetaObj (loc, psihat, tM'), mS)

  | (s, (Int.Comp.PiKind (_loc, (Int.LF.PDecl (n , tA, cPsi), Int.Comp.Implicit), cK), theta )) ->
      let psihat  = Context.dctxToHat cPsi in
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let tA'   = C.cnormTyp (tA, theta) in

      let p     = Whnf.newMPVar (Some n) (cD, cPsi', tA') in
      let h     = Int.LF.MPVar (p, (Whnf.m_id, LF.id)) in

      let mS    = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.PObj (psihat, h), theta)) in
        Int.Comp.MetaApp (Int.Comp.MetaParam (loc, psihat, h), mS)


  | (Apx.Comp.MetaApp (m, s), (Int.Comp.PiKind (_, (cdecl, Int.Comp.Explicit), cK) , theta)) ->
      begin match cdecl with
        | Int.LF.CDecl (_psi, schema_cid, _) ->
            let Int.Comp.MetaCtx (loc, cPsi')  = elMetaObj cD m ((Int.Comp.MetaSchema schema_cid), theta)  in
            let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.CObj(cPsi'), theta)) in
              Int.Comp.MetaApp (Int.Comp.MetaCtx (loc, cPsi'), cS)

        | Int.LF.MDecl (_u, tA, cPsi) ->
            let (Int.Comp.MetaObj (loc, psihat, tM) as cM) = elMetaObj cD m (Int.Comp.MetaTyp (tA, cPsi), theta)  in
            let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.MObj(psihat, tM), theta)) in
              Int.Comp.MetaApp (cM, cS)


        | Int.LF.PDecl (_u, tA, cPsi) ->
            let (Int.Comp.MetaParam (_, psihat, h) as cM) = elMetaObj cD m (Int.Comp.MetaParamTyp (tA, cPsi), theta)  in
            let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.PObj(psihat, h), theta)) in
              Int.Comp.MetaApp (cM, cS)

      end

(* and elMetaSpineI loc cD s cKt =
(*  if i = 0 then
    elMetaSpine loc cD s cKt
  else *)
  begin match cKt with
    |
    | (Int.Comp.PiKind (_ , (Int.LF.CDecl (psi_name , schema_cid, _ ), Int.Comp.Implicit ), cK), theta ) ->
          let cPsi = Int.LF.CtxVar (Int.LF.CInst (psi_name, ref None, schema_cid, Int.LF.Empty, cD)) in
          let cS = elMetaSpineI loc cD s (i-1) (cK, Int.LF.MDot (Int.LF.CObj(cPsi), theta)) in
              Int.Comp.MetaApp (Int.Comp.MetaCtx (loc, cPsi), cS)
(*          raise (Error.Violation "Contexts cannot be supplied implicitly; they must be passed explicitly)\n")*)
      | (Int.Comp.PiKind (_loc, (Int.LF.MDecl (n , tA, cPsi), _implicit), cK), theta ) ->
          let psihat  = Context.dctxToHat cPsi in
          let cPsi' = C.cnormDCtx (cPsi, theta) in
          let tA'   = C.cnormTyp (tA, theta) in

          let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
          let mS    = elMetaSpineI loc cD s (i-1) (cK, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)) in
           Int.Comp.MetaApp (Int.Comp.MetaObj (loc, psihat, tM'), mS)


(*      | (I.Comp.PiKind (_, (I.LF.PDecl (_ , tA, cPsi), I.Comp.Implicit), tK), theta ) ->  *)

    end
*)

let rec elCompTyp cD tau = match tau with
  | Apx.Comp.TypBase (loc, a, cS) ->
      let _ = dprint (fun () -> "[elCompTyp] Base : " ^ R.render_cid_comp_typ a) in
      let tK = (CompTyp.get a).CompTyp.kind in
      let _ = dprint (fun () -> "[elCompTyp] of kind : " ^ P.compKindToString cD tK) in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypBase (loc, a ,cS')

  | Apx.Comp.TypBox (loc, a, psi) ->
      let _ = dprint (fun () -> "[elCompTyp] TypBox" ) in
      let cPsi = Lfrecon.elDCtx (Lfrecon.Pibox) cD psi in
      let _ = dprint (fun () -> "[elCompTyp] TypBox - cPsi = " ^ P.dctxToString cD cPsi) in
      let tA   = Lfrecon.elTyp (Lfrecon.Pibox) cD cPsi a in
      let tT = Int.Comp.TypBox (loc, tA, cPsi) in
        (dprint (fun () -> "[elCompTyp] " ^ P.compTypToString cD tT);
         tT)

  | Apx.Comp.TypSub (loc, psi, phi) ->
      let cPsi = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
      let cPhi = Lfrecon.elDCtx Lfrecon.Pibox cD phi in
        Int.Comp.TypSub (loc, cPsi, cPhi)

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cD tau1 in
      let tau2' = elCompTyp cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCross (tau1, tau2) ->
      let tau1' = elCompTyp cD tau1 in
      let tau2' = elCompTyp cD tau2 in
        Int.Comp.TypCross (tau1', tau2')

  | Apx.Comp.TypCtxPi ((x, schema_cid, apx_dep) , tau) ->
      let cdep = match apx_dep with
          Apx.Comp.Explicit -> Int.LF.No
        | Apx.Comp.Implicit -> Int.LF.Maybe in
      let dep = match apx_dep with
          Apx.Comp.Explicit -> Int.Comp.Explicit
        | Apx.Comp.Implicit -> Int.Comp.Implicit in
      let tau' = elCompTyp (Int.LF.Dec (cD, Int.LF.CDecl (x, schema_cid, cdep))) tau in
        Int.Comp.TypCtxPi ((x, schema_cid, dep), tau')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl  in
      let tau'   = elCompTyp (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox ((cdecl', Int.Comp.Explicit), tau')

  | Apx.Comp.TypBool -> Int.Comp.TypBool

(* *******************************************************************************)

let genMetaVar loc' cD (loc, cdecl, t) = match cdecl with
  | Int.LF.MDecl (n, tA, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      let psihat  = Context.dctxToHat cPsi' in
      let tA'   = C.cnormTyp (tA, t) in
      let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
        (Int.Comp.MetaObj (loc', psihat, tM') ,
         Int.LF.MObj (psihat, tM'))

  | Int.LF.CDecl (n, schema_cid, _ ) ->
      let cPsi = Int.LF.CtxVar (Int.LF.CInst (n, ref None, schema_cid,
                                              Int.LF.Empty, cD)) in
        (Int.Comp.MetaCtx (loc', cPsi),
         Int.LF.CObj cPsi)

let rec mgCompTyp cD (loc, c) =
  let cK = (CompTyp.get c).CompTyp.kind in
  let rec genMetaSpine (cK, t) = match (cK, t) with
    | (Int.Comp.Ctype _, _t) -> Int.Comp.MetaNil
    | (Int.Comp.PiKind (loc', (cdecl, _ ), cK), t) ->
        let (mO, mF) = genMetaVar loc cD (loc', cdecl, t) in
        let mS = genMetaSpine (cK, Int.LF.MDot (mF, t)) in
          Int.Comp.MetaApp (mO, mS)
  in
    Int.Comp.TypBase (loc, c, genMetaSpine (cK, Whnf.m_id))


let rec inferPatTyp' cD' tau = match tau with
  | Int.Comp.TypBool -> Int.Comp.TypBool
  | Int.Comp.TypCross (tau1, tau2) ->
      let tau1' = inferPatTyp' cD' tau1 in
      let tau2' = inferPatTyp' cD' tau2 in
        Int.Comp.TypCross (tau1', tau2')
  | Int.Comp.TypBase (loc, c, _ )  ->
      mgCompTyp cD' (loc, c)
  | Int.Comp.TypArr _  ->
      raise (Error.Violation "Patterns cannot have function type")
(*  | _ -> raise Error.NotImplemented*)
  | Int.Comp.TypBox (loc, (Int.LF.Atom(_, a, _) as _tP) , cPsi)  ->
      let tP' = mgTyp cD' cPsi a (Typ.get a).Typ.kind  in
        Int.Comp.TypBox (loc, tP', cPsi)


let rec inferPatTyp cD' tau = inferPatTyp' cD' (Whnf.cnormCTyp (tau, Whnf.m_id))

(* *******************************************************************************)

let rec elExp cD cG e theta_tau = elExpW cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Fun (loc, x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
      let e' = elExp cD (Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo
                                                              (tau1, theta)))) e
        (tau2, theta) in
      let e'' =  Whnf.cnormExp (Int.Comp.Fun (loc, x, e'), Whnf.m_id) in
      let _ = dprint (fun () -> "[elExp] Fun " ^ R.render_name x ^ " done ") in
      let _ = dprint (fun () -> "[elExp] " ^ P.expChkToString cD cG e'' ) in
      let _ = dprint (fun () -> "[elExp] has type " ^
                        P.compTypToString cD (Whnf.cnormCTyp theta_tau)) in
        e''


  | (Apx.Comp.CtxFun (loc, psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid, Int.Comp.Explicit), tau), theta)) ->
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = Int.LF.Dec (cD, Int.LF.CDecl (psi_name, schema_cid, Int.LF.No))  in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
      let _ = dprint (fun () -> "[elExp] ctx-mlam " ^ R.render_name psi_name ^ "
      done ") in
      let _ = dprint (fun () -> "[elExp] ctx-mlam e' = " ^ P.expChkToString cD' cG' e')
      in
      let e'' =  Int.Comp.CtxFun (loc, psi_name, e') in
      let _ = dprint (fun () -> "[elExp] ctx-mlam : cG = " ^ P.gctxToString cD cG) in
      let _ = dprint (fun () -> "[elExp] ctx-mlam result ") in
      let _ = dprint (fun () -> "        " ^ P.expChkToString cD cG e'' ) in
      let _ = dprint (fun () -> "[elExp] has type " ^
                        P.compTypToString cD (Whnf.cnormCTyp theta_tau)) in
        e''

  (* Allow uniform abstractions for all meta-objects *)
  | (Apx.Comp.MLam (loc, psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid, Int.Comp.Explicit), tau), theta)) ->
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = Int.LF.Dec (cD, Int.LF.CDecl (psi_name, schema_cid, Int.LF.No)) in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.CtxFun (loc, psi_name, e')

  | (Apx.Comp.MLam (loc, u, e) , (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let cD' = Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))) in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (loc, u, e')

  | (Apx.Comp.MLam (loc, p, e) , (Int.Comp.TypPiBox((Int.LF.PDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let cD' = Int.LF.Dec (cD, Int.LF.PDecl (p, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))) in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (loc, p, e')


  | (Apx.Comp.MLam (loc, s, e) , (Int.Comp.TypPiBox((Int.LF.SDecl(_u, cPhi, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let cD' = Int.LF.Dec (cD, Int.LF.SDecl (s, C.cnormDCtx (cPhi, theta), C.cnormDCtx (cPsi, theta))) in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
         Int.Comp.MLam (loc, s, e')


  | (e, (Int.Comp.TypCtxPi((psi_name, schema_cid, Int.Comp.Implicit), tau), theta))  ->
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = Int.LF.Dec (cD, Int.LF.CDecl (psi_name, schema_cid, Int.LF.Maybe)) in
      let e' = Apxnorm.cnormApxExp cD (Apx.LF.Empty) e (cD', Int.LF.MShift 1) in
      let e' = elExp cD' cG'  e' (tau, C.mvar_dot1 theta) in
        Int.Comp.CtxFun (Syntax.Loc.ghost, psi_name, e')

  | (e, (Int.Comp.TypPiBox((Int.LF.MDecl(u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      (* let u' = Id.mk_name (Id.MVarName (Typ.gen_mvar_name tA)) in *)
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))) in
      let e' = Apxnorm.cnormApxExp cD (Apx.LF.Empty) e (cD', Int.LF.MShift 1) in
      let e' = elExp cD' cG' e' (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (Syntax.Loc.ghost, u , e')

  | (e, (Int.Comp.TypPiBox((Int.LF.PDecl(_u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      let u' = Id.mk_name (Id.PVarName None) in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = Int.LF.Dec (cD, Int.LF.PDecl (u', C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))) in
      let e' = Apxnorm.cnormApxExp cD (Apx.LF.Empty) e (cD', Int.LF.MShift 1) in
      let e' = elExp cD' cG' e' (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (Syntax.Loc.ghost, u' , e')


  | (Apx.Comp.Syn (loc, i), (tau,t)) ->
      let _ = dprint (fun () -> "[elExp] Syn") in
      let _ = dprint (fun () -> "[elExp] cG = " ^
                        P.mctxToString cD ^ " |- " ^ P.gctxToString cD cG) in
      let (i1,tau1) = elExp' cD cG i in
      let _ = dprint (fun () -> "[elExp] Syn i = " ^ P.expSynToString cD cG i1) in
      let _ = dprint (fun () -> "[elExp] Syn done: " ^
                        P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau1))  in
      let (i', tau_t') = genMApp loc cD (i1, tau1) in
      let _ = dprint (fun () -> "[elExp] Unify computation-level types: \n" ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t') ^ " == "
                        ^
                        P.compTypToString cD (Whnf.cnormCTyp (tau,t) )) in
        begin try
          dprint (fun () -> "Unifying computation-level types\n") ;
          Unify.unifyCompTyp cD (tau, t) (tau_t');
          dprint (fun () -> "Unified computation-level types\n") ;
          dprint (fun () -> "     " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t') ^ "\n         == \n"
                        ^
                        P.compTypToString cD (Whnf.cnormCTyp (tau,t)) ^ "\n") ;
          Int.Comp.Syn (loc, i')
        with _ ->
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
              let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Int.Comp.TypClo (tau1, t))) in
              let cG2 = Int.LF.Dec (cG1, Int.Comp.CTypDecl (y, Int.Comp.TypClo (tau2, t))) in
              let e'  =  elExp cD cG2 e (tau, theta) in
                Int.Comp.LetPair (loc, i', (x, y, e'))

          | _ -> raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantCross, tau_theta')))
              (* TODO postpone to reconstruction *)
        end

  | (Apx.Comp.Let (loc, i, (x, e)), (tau, theta)) ->
      let (i', (tau',theta')) = elExp' cD cG i in
      let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Int.Comp.TypClo (tau',theta'))) in
      let e'  =  elExp cD cG1 e (tau, theta) in
        Int.Comp.Let (loc, i', (x,  e'))

  | (Apx.Comp.Box (loc, psihat, tM), ((Int.Comp.TypBox (_loc, tA, cPsi), theta) as tau_theta)) ->
   (* if psihat = Context.dctxToHat cPsi then *)
      let _ = dprint (fun () -> "[elExp] BOX\n") in
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      if Lfrecon.unify_phat cD psihat (Context.dctxToHat cPsi') then
        let tM' = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (C.cnormTyp (tA, theta), LF.id) in
        let _   = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _   = Unify.resetGlobalCnstrs () in
        let e   = Int.Comp.Box (loc, psihat, tM') in
        let _   = (dprint (fun () -> "[elExp] Box : " ^ P.expChkToString cD cG e ) ;
                   dprint (fun () -> "[elExp] Box checked against "  ^
                             P.typToString cD cPsi' (C.cnormTyp (tA, theta), LF.id) ^ "[" ^
                             P.dctxToString cD cPsi' ^ "]")) in

          Int.Comp.Box (loc, psihat, tM')
      else
        (* raise (Error.Error (loc, Error.CompBoxCtxMismatch (cD, cPsi, (psihat, tM')))) *)
        (begin match psihat with
           | (Some (Int.LF.CtxOffset psi), k) ->
               (dprint (fun () ->
                         "[elExp] phat = " ^ R.render_ctx_var cD psi  ^
                           "   k  = " ^ string_of_int k ^ "\n");
                dprint (fun () -> "[elExp] cPsi = " ^ P.dctxToString cD cPsi  ))
           | ( None , k ) ->
               dprint (fun () -> "[elExp] cPsi = " ^ P.dctxToString cD cPsi  ^
                     "\n psihat  = None " ^ string_of_int k ^ "\n")
           | ( Some (Int.LF.CtxName psi) , k ) ->
               dprint (fun () -> "[elExp] cPsi = " ^ P.dctxToString cD cPsi  ^
                     "\n psihat  = " ^ R.render_name psi ^ " , " ^ string_of_int k ^ "\n")
         end;
         raise (Check.Comp.Error (loc, Check.Comp.BoxMismatch (cD, cG, tau_theta))) )


  | (Apx.Comp.SBox (loc, psihat, sigma), ((Int.Comp.TypSub (_loc, cPhi, cPsi), theta))) ->
   (* if psihat = Context.dctxToHat cPsi then *)
      if Lfrecon.unify_phat cD psihat (Context.dctxToHat cPsi) then
        let sigma' = Lfrecon.elSub loc Lfrecon.Pibox cD (C.cnormDCtx (cPsi, theta)) sigma (C.cnormDCtx (cPhi, theta)) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _        = Unify.resetGlobalCnstrs () in
          Int.Comp.SBox (loc, psihat, sigma')
      else
        (* raise (Error (loc, Check.Comp.BoxCtxMismatch (cD, cPsi, (psihat, tM')))) *)
        (let (_ , k) = psihat in
           dprint (fun () -> "cPsi = " ^ P.dctxToString cD (C.cnormDCtx (cPsi, theta))  ^ "\n psihat  = " ^ string_of_int k ^ "\n") ;
           raise (Check.Comp.Error (loc, Check.Comp.SBoxMismatch (cD, cG, (C.cnormDCtx (cPhi, theta)), (C.cnormDCtx (cPsi, theta)))) ))


  | (Apx.Comp.Case (loc, prag, i, branches), ((tau, theta) as tau_theta)) ->
      let _ = dprint (fun () -> "[elExp] case ") in
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp] case on " ^ P.expSynToString cD cG i') in
      begin match (i', C.cwhnfCTyp tau_theta') with
        | (Int.Comp.Ann (Int.Comp.Box (_ , phat,tR), _ ) as i,
           (Int.Comp.TypBox (_, tP, cPsi) as tau_s, t (* m_id *))) ->
          let _ = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          let _ = Unify.resetGlobalCnstrs () in
          if Whnf.closed (tR, LF.id) then
            let rec recBranch b =
              let _ = dprint (fun () -> "[elBranch - IndexObj] in context cPsi = "
                ^ P.dctxToString cD cPsi ^ "\n") in
              let b = elBranch (IndexObj(phat, tR)) cD cG b tau_s tau_theta in
              let _ = Gensym.MVarData.reset () in
              b in
            let branches' = List.map recBranch branches in
            Int.Comp.Case (loc, prag, i, branches')
          else
            raise (Error (loc, ValueRestriction (cD, cG, i, (tau_s,t))))

        | (Int.Comp.Ann (Int.Comp.Box (_ , phat,tR), _ ) as i, (tau_s, t)) ->
          raise (Error (loc, (IllegalCase (cD, cG, i, (tau_s, t)))))

        | (i, (Int.Comp.TypBox (_, tP, cPsi) as tau_s, _mid)) ->
          let _      = dprint (fun () -> "[elExp]"
            ^ "Contexts cD  = " ^ P.mctxToString cD ^ "\n"
            ^ "cG = " ^ P.gctxToString cD cG ^ "\n"
            ^ "Expected Pattern has type :" ^
            P.typToString cD cPsi (tP, LF.id)
            ^  "\n Context of expected pattern type : "
            ^  P.dctxToString cD cPsi
            ^ "\n Checking closedness ... ") in
          if Whnf.closedTyp (tP, LF.id) && Whnf.closedDCtx cPsi && Whnf.closedGCtx cG then
            let rec recBranch b =
              let _ = dprint (fun () -> "[elBranch - DataObj] " ^
                P.expSynToString cD cG i ^
                " of type "
                ^ P.compTypToString cD tau_s
                ^ "\n") in
              let b = elBranch DataObj cD cG b tau_s tau_theta in
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

        | (i, ((Int.Comp.TypBool | Int.Comp.TypCross (_, _) | Int.Comp.TypBase (_, _, _)) as tau_s, _mid)) ->
          let rec recBranch b =
            let _ = dprint (fun () -> "[elBranch - PatObj] has type " ) in
            let _ = dprint (fun () -> "         " ^ P.compTypToString cD tau_s ^ "\n") in
            let b = elBranch DataObj cD cG b tau_s tau_theta in
            Gensym.MVarData.reset () ; b in

          let branches' = List.map recBranch branches in
          let _ = dprint (fun () -> "[elBranch - PatObj] of type " ) in
          let _ = dprint (fun () ->  P.compTypToString cD tau_s
            ^ " done \n") in
          Int.Comp.Case (loc, prag, i, branches')

        | (i, (tau_s, t)) ->
          raise (Error (loc, (IllegalCase (cD, cG, i, (tau_s, t)))))
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
    Int.Comp.Hole (loc)

  (* TODO postpone to reconstruction *)
  (* Error handling cases *)
  | (Apx.Comp.Fun (loc, _x, _e),  tau_theta ) ->
      raise (Check.Comp.Error (loc, Check.Comp.FunMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.CtxFun (loc, _psi_name, _e), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.CtxFunMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.MLam (loc, _u, _e), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.MLamMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.Pair(loc, _ , _ ), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.PairMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.Box (loc, _, _ ) , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BoxMismatch (cD, cG, tau_theta)))

and elExp' cD cG i = match i with
  | Apx.Comp.Var offset ->
      (Int.Comp.Var offset, (lookup cG offset, C.m_id))

  | Apx.Comp.DataConst c ->
      let _ = dprint (fun () -> "[elExp'] DataConst " ^ R.render_cid_comp_const  c ^
                        "\n has type " ^ P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD ((CompConst.get c).CompConst.typ)) in
     (Int.Comp.DataConst c, ((CompConst.get c).CompConst.typ, C.m_id))

  | Apx.Comp.Const prog ->
     (Int.Comp.Const prog, ((Comp.get prog).Comp.typ, C.m_id))

  | Apx.Comp.Apply (loc, i, e) ->
      let _ = dprint (fun () -> "[elExp'] Apply") in
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] Apply - generated implicit arguments") in
        begin match tau_theta' with
          | (Int.Comp.TypArr (tau2, tau), theta) ->
              let _ = dprint (fun () -> "[elExp'] Inferred type for i' = " ^
                                P.expSynToString cD cG i' ^ "\n      " ^
                                P.compTypToString cD (Whnf.cnormCTyp (Int.Comp.TypArr (tau2,tau), theta))
                                ^ "\n") in
              let _ = dprint (fun () -> "[elExp'] Check argument has type " ^
                                P.compTypToString cD (Whnf.cnormCTyp (tau2,theta))) in
              let e' = elExp cD cG e (tau2, theta) in
              let i'' = Int.Comp.Apply (loc, i', e') in
              let _ = dprint (fun () -> "[elExp'] Apply done : " ) in
              let _ = dprint (fun () -> "         " ^
                                P.expSynToString cD cG i'') in
                (i'', (tau, theta))

          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantArrow, tau_theta')))
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.CtxApp (loc, i, cPsi) ->
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
        begin match tau_theta' with
          | ((Int.Comp.TypCtxPi ((_psi, _sW, _explicit ), tau), theta) as tt)->
              let cPsi'  = Lfrecon.elDCtx Lfrecon.Pibox cD cPsi in
              let theta' = Int.LF.MDot (Int.LF.CObj (cPsi'), theta) in
              let _ = (dprint (fun () -> "[elExp'] CtxApp : tau = " ^
                                 P.compTypToString cD (Whnf.cnormCTyp tt) );
                       dprint (fun () -> "[elExp'] cPsi' = " ^ P.dctxToString cD cPsi' )) in
              let _ = dprint (fun () -> "[elExp'] CtxApp : [cPsi/psi]tau' = " ^
                                 P.compTypToString cD (Whnf.cnormCTyp (tau,theta')) ) in
                (Int.Comp.CtxApp (loc, i', cPsi'), (tau, theta'))

          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantCtxPi, tau_theta')))
                (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.MApp (loc, i, mC) ->
      let _ = dprint (fun () -> "Elaborating MApp.\n") in
      let (i0, tau_t) = (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] MApp : " ^
                        P.expSynToString cD cG i0 ^ " : " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t) ) in
      let (i', tau_theta') = genMApp loc cD (i0, tau_t) in
      let _ = dprint (fun () -> "\n MApp - Generated implicit args.\n") in
        begin match tau_theta' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
              let cPsi' = C.cnormDCtx (cPsi, theta) in
              let psihat' = Context.dctxToHat cPsi'  in
                begin match mC with
                  | Apx.Comp.MetaObj (_loc', psihat, m) ->
                      begin try
                        let _      = dprint (fun () -> "[elExp']  MApp -  MetaObj") in
                        let _      = dprint (fun () -> "[elExp'] elaborate"^
                                               " MetaObj against type " ^
                                               P.typToString cD cPsi' (C.cnormTyp (tA, theta),
                                                                       LF.id)) in
                        let tM'    = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m (C.cnormTyp (tA, theta), LF.id) in
                        let theta' = Int.LF.MDot (Int.LF.MObj (psihat', tM'), theta) in
                          (dprint (fun () -> "[elSyn] MApp : tau = " ^
                                     P.compTypToString cD (Whnf.cnormCTyp tau_theta' ));
                           dprint (fun () -> "[elSyn] tM  = " ^ P.normalToString cD cPsi' (tM', LF.id) );
                           dprint (fun () -> "[elSyn] tau_theta = " ^
                                     P.compTypToString cD (Whnf.cnormCTyp (tau, theta'))) ;
                           (Int.Comp.MApp (loc, i', (psihat', Int.Comp.NormObj tM')), (tau, theta')))
                      with Error.Violation msg ->
                        dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
                        raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn))
                      end
                  | _ -> raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaTyp (tA, cPsi), theta))))
                end
            | (Int.Comp.TypPiBox ((Int.LF.PDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
              (* m = PVar or BVar of Proj *)
              (* tM' really is a head ... if we would allow  Root (_, PVar _ , Nil) then this wouldn't be normal. *)
               begin try
                 begin match mC with
                   | Apx.Comp.MetaObj (_loc', psihat , Apx.LF.Root (_, h, Apx.LF.Nil)) ->
                       let _ = dprint (fun () -> "[elExp'] Mapp case : PDecl ") in
                       let cPsi' = C.cnormDCtx (cPsi, theta) in
                       let (h', sB) = Lfrecon.elHead loc Lfrecon.Pibox cD cPsi' h  in
                       let theta' = Int.LF.MDot (Int.LF.PObj (psihat, h'), theta) in
                       let sA' = (C.cnormTyp (tA, theta), LF.id) in
                         begin try
                           (Unify.unifyTyp cD cPsi' sB  sA' ;
                            dprint (fun () -> "[elExp'] unification of PDecl with inferred type done");
                          (Int.Comp.MApp (loc, i', (psihat, Int.Comp.NeutObj h')), (tau, theta')))
                         with Unify.Failure msg ->
                           (Printf.printf "%s\n" msg;
                            raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
                         end
                  | _ ->
                       (dprint (fun () -> "[elTerm] Error.Violation: Not a head");
                      raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaTyp (tA, cPsi), theta)))))
                 end
               with Error.Violation msg ->
                 dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
                 raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn))
               end

         (* Allow uniform applications for all meta-objects *)
          | ((Int.Comp.TypCtxPi ((_psi, sW, _explicit ), tau), theta) as tt)->
              begin match mC with
                | Apx.Comp.MetaCtx (loc, cPsi) ->
                    let cPsi'  = Lfrecon.elDCtx Lfrecon.Pibox cD cPsi in
                    let _ = (dprint (fun () -> "[elExp'] CtxApp : tau = " ^
                                       P.compTypToString cD (Whnf.cnormCTyp tt) );
                             dprint (fun () -> "[elExp'] cPsi' = " ^ P.dctxToString cD cPsi' )) in

                    let _ = dprint (fun () -> "[elExp'] CtxApp : [cPsi/psi]tau' = " ^
                                      P.compTypToString cD (Whnf.cnormCTyp (tau,theta)) ) in

                      (Int.Comp.CtxApp (loc, i', cPsi'), (tau, theta))
                | _ ->  raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaSchema sW, theta))))
              end

          | (Int.Comp.TypArr (Int.Comp.TypBox(_, tP, cPsi), tau), theta) ->
              begin match mC with
                | Apx.Comp.MetaObj (loc, psihat, m) ->
                  begin
                    try
                      let cPsi' = C.cnormDCtx (cPsi, theta) in
                      let _     = dprint (fun () -> "[elExp']  MApp -  MetaObj") in
                      let _     = dprint (fun () -> "[elExp'] elaborate" ^
                        " MetaObj against type " ^
                        P.typToString cD cPsi' (C.cnormTyp (tP, theta), LF.id)) in
                      let tM'   = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m  (C.cnormTyp (tP, theta), LF.id) in
                      let i     = Int.Comp.Apply (loc, i', Int.Comp.Box(loc, psihat, tM')) in
                      dprint (fun () -> "[elExp] MApp Reconstructed: " ^
                        P.expSynToString cD cG i); (i , (tau, theta))
                    with Error.Violation msg ->
                      dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
                      raise (Check.Comp.Error (loc, Check.Comp.AppMismatch (cD, (Int.Comp.MetaTyp (tP, cPsi), theta))))
                  end
                | _ -> raise (Check.Comp.Error (loc, Check.Comp.AppMismatch (cD, (Int.Comp.MetaTyp (tP, cPsi), theta))))
              end

          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantPiBox, tau_theta')))
                (* TODO postpone to reconstruction *)

        end

  | Apx.Comp.MAnnApp (loc, i, (psi, m)) ->
      let _ = dprint (fun () -> "Reconstructing MAnnApp\n") in
      let (i0, tau_t) = (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] MApp : " ^
                        P.expSynToString cD cG i0 ^ " : " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t) ) in

      let (i', tau_theta') = genMApp loc cD  (i0, tau_t) in
      let _ = dprint (fun () -> "[elExp'] MAnnApp - generated implicit args.\n") in
      let _ = dprint (fun () -> "[elExp] MAnnApp  : " ^
                                P.mctxToString cD ^ "\n |- " ^
                                P.compTypToString cD (Whnf.cnormCTyp tau_theta')) in
      begin match tau_theta' with
        | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
          let cPsi    = C.cnormDCtx (cPsi, theta) in
          begin
            try
              let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
              let _     = Unify.unifyDCtx cD cPsi cPsi' in
              let psihat' = Context.dctxToHat cPsi'  in
              let tM'    = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m (C.cnormTyp (tA, theta), LF.id) in
              let theta' = Int.LF.MDot (Int.LF.MObj (psihat', tM'), theta) in
              (Int.Comp.MApp (loc, i', (psihat', Int.Comp.NormObj tM')), (tau, theta'))
            with Error.Violation msg ->
              dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
              raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn ))
          end
        | (Int.Comp.TypPiBox ((Int.LF.PDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
          let cPsi    = C.cnormDCtx (cPsi, theta) in
          begin
            try
              let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
              let _     = Unify.unifyDCtx cD cPsi cPsi' in
              let cPsi' = Whnf.normDCtx cPsi' in 
              let psihat' = Context.dctxToHat cPsi'  in
              begin match m with
                | Apx.LF.Root (_, h, Apx.LF.Nil) ->
                  let _ = dprint (fun () -> "[elExp'] Mapp case :  PDecl ") in
                  let (h', sB) = Lfrecon.elHead loc Lfrecon.Pibox cD cPsi' h  in
                  let theta' = Int.LF.MDot (Int.LF.PObj (psihat', h'), theta)  in
                  let sA' = (C.cnormTyp (tA, theta), LF.id) in
                  begin
                    try
                      (Unify.unifyTyp cD cPsi' sB  sA' ;
                       dprint (fun () -> "[elExp'] unification of PDecl with inferred type done");
                       (Int.Comp.MApp (loc, i', (psihat', Int.Comp.NeutObj h')), (tau, theta')))
                    with Unify.Failure msg ->
                      (Printf.printf "%s\n" msg;
                       raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
                  end
                | _ ->
                  (dprint (fun () -> "[elTerm] Violation: Not a head");
                   raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaTyp (tA, cPsi), theta)))))
              end
            with Error.Violation msg ->
              dprint (fun () -> "[elTerm] Violation: " ^ msg);
              raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn))
          end
        | (Int.Comp.TypArr (Int.Comp.TypBox(_, tP, cPsi), tau), theta) ->
          let cPsi = C.cnormDCtx (cPsi, theta) in
          let _ = dprint (fun () -> "Encountered Boxed arg") in
          let _ = dprint (fun () -> "[elExp] MAnnApp - TypArr : " ^
            P.mctxToString cD ^ " |- " ^
            P.compTypToString cD (Whnf.cnormCTyp tau_theta')) in
          let _ = dprint (fun () -> "cnormDctx done") in
          let _ = dprint (fun () -> "Projected type of argument : " ^
            (P.dctxToString cD cPsi) ^ " |- " ^
            P.typToString cD cPsi (C.cnormTyp (tP, theta), LF.id)) in
          begin
            try
              let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
              let _ = dprint (fun () -> "reconstruction of explicit psi done") in
              let _ = dprint (fun () -> "BEFORE unifyDCtx cPsi' = " ^ P.dctxToString cD  cPsi') in
              let _ = dprint (fun () -> "                 cPsi = " ^ P.dctxToString cD  cPsi) in
              let _     = Unify.unifyDCtx cD cPsi cPsi' in
              let _ = dprint (fun () -> "Infer omitted context argument using unification") in
              let psihat' = Context.dctxToHat cPsi'  in
              let tM' = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m (C.cnormTyp (tP, theta), LF.id) in
              let _   = dprint (fun () -> "[elTerm] for m against type : " ^
                P.dctxToString cD cPsi' ^ " |- " ^
                P.typToString cD cPsi' (C.cnormTyp (tP, theta), LF.id)) in
              let i = Int.Comp.Apply (loc, i',
                                      Int.Comp.Box(loc, psihat', tM')) in
              dprint (fun () -> "[elExp] MAnnApp Reconstructed: " ^
                P.expSynToString cD cG i ^ "\n"); (i , (tau, theta))

            with Unify.Failure msg ->
              raise (Check.Comp.Error (loc, Check.Comp.AppMismatch (cD, (Int.Comp.MetaTyp (tP, cPsi), theta))))
          end
        | _ ->
          raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantPiBox, tau_theta')))
          (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.BoxVal (loc, psi, r) ->
      let _ = dprint (fun () -> "[elExp'] BoxVal dctx ") in
      let cPsi     = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
      let _ = dprint (fun () -> "[elExp'] BoxVal dctx done: " ^ P.dctxToString cD cPsi ) in
      let (tR, sP) = Lfrecon.elClosedTerm' Lfrecon.Pibox cD cPsi r  in
      let _ = dprint (fun () -> "[elExp'] BoxVal tR done ") in
      (* let sP    = synTerm Lfrecon.Pibox cD cPsi (tR, LF.id) in *)
      let phat     = Context.dctxToHat cPsi in
      let tau      = Int.Comp.TypBox (Syntax.Loc.ghost, Int.LF.TClo sP, cPsi) in
        (Int.Comp.Ann (Int.Comp.Box (loc, phat, tR), tau), (tau, C.m_id))

  | Apx.Comp.PairVal (loc, i1, i2) ->
      let (i1', (tau1,t1)) = genMApp loc cD (elExp' cD cG i1) in
      let (i2', (tau2,t2)) = genMApp loc cD (elExp' cD cG i2) in
        (Int.Comp.PairVal (loc, i1', i2'),
         (Int.Comp.TypCross (Int.Comp.TypClo (tau1,t1), Int.Comp.TypClo (tau2,t2)), C.m_id))


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
 *  the same type as the expression we analyze.
 *
 *)
(*

  recPattern cD cPsi omega delta psi m tPopt =

  Assumptions:
      cO ; cD ; cPsi |- tPopt
      omega ; delta ; psi |- m


* recMObj cD cPsi omega delta mO tPopt =
  based on recPattern.

* recPattern becomes redundant when we adopt the new parser as default.

*)
and recMObj cD' mO (cD, tAnn, cPsi) = match mO with
  | Apx.Comp.MetaObjAnn (loc, psi, m) ->
  let cPsi'   = Lfrecon.elDCtx  Lfrecon.Pibox cD' psi in
  let _       = dprint (fun () -> "[recMObj] inferCtxSchema ... ") in
  let _       = dprint (fun () ->  "Scrutinee's context " ^ P.mctxToString cD ^ " |- " ^
                          P.dctxToString cD cPsi) in
  let _       = dprint (fun () ->  "Pattern's context  " ^ P.mctxToString cD' ^ " |- " ^
                          P.dctxToString cD' cPsi') in
  let _       = inferCtxSchema loc (cD, cPsi) (cD', cPsi') in
  let _       = dprint (fun () -> "[recMObj] inferCtxSchema done") in
  let tP'     = begin match tAnn with
                | FullTyp  a    ->
                    let tP' = Lfrecon.elTyp Lfrecon.Pibox cD' cPsi' a  in
                      (* recTyp Lfrecon.Pibox cD' cPsi' (tP', LF.id) ;*) tP'
                | PartialTyp a  ->
                    let _ = dprint (fun () -> "[mgTyp] Generate mg type in context " ^
                                      P.dctxToString cD' cPsi' ) in
                      mgTyp cD' cPsi' a (Typ.get a).Typ.kind
                end in
  let _ = dprint (fun () -> "[recMObj] Reconstruction of pattern of type  " ^
                    P.typToString cD' cPsi' (tP', LF.id)) in
  let tR = Lfrecon.elTerm' Lfrecon.Pibox cD' cPsi' m (tP', LF.id) in
  let _  = Lfrecon.solve_constraints  cD' in
  let _   = dprint (fun () -> "recMObj: Elaborated pattern...\n" ^ P.mctxToString cD' ^ "  ;   " ^
                      P.dctxToString cD' cPsi' ^ "\n   |-\n    "  ^ P.normalToString cD' cPsi' (tR, LF.id) ^
                      "\n has type " ^ P.typToString cD' cPsi' (tP', LF.id) ^ "\n") in

  let phat = Context.dctxToHat cPsi' in
  let (cD1', cPsi1', (_phat, tR1'), tP1') =
    Abstract.abstrPattern cD' cPsi' (phat, tR) tP' in

  let _   = dprint (fun () -> "recMObj: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                      P.mctxToString cD1' ^ "  ;   " ^ P.dctxToString cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.normalToString cD1' cPsi1' (tR1', LF.id) ^ "\n has type \n " ^
                      P.typToString cD1' cPsi1'  (tP1', LF.id)) in
  let l_cd1'    = Context.length cD1'  in
  let l_delta   = Context.length cD'  in
    ((l_cd1', l_delta), cD1', cPsi1', Some tR1', tP1')

(* inferCtxSchema loc (cD, cPsi) (cD', cPsi') = ()

   if cD |- cPsi  ctx  and  cPsi is the context of the scrutinee
      cD'|- cPsi' ctx  and  cPsi' is the context of the pattern
      cPsi ~ cPsi'   (i.e. they can be made equal during unification)
   then
      return unit
   otherwise
      raise exception
*)
and inferCtxSchema loc (cD,cPsi) (cD', cPsi') = match (cPsi , cPsi') with
      | (Int.LF.Null , Int.LF.Null) -> ()
      | (Int.LF.CtxVar (Int.LF.CtxOffset psi1_var), cPsi') ->
          let _ = dprint (fun () -> "[inferSchema] outside context cD = " ^ P.mctxToString cD )
          in
          let _ = dprint (fun () -> "[inferSchema] local context in branch : cD' " ^ P.mctxToString cD' ) in
          let _ = dprint (fun () -> "[inferSchema] looking up psi = " ^
                            P.dctxToString cD cPsi) in
          let (_ , s_cid) = Whnf.mctxCDec cD psi1_var in
          begin match get_ctxvar cPsi' with
               | None -> ()
               | Some (Int.LF.CtxOffset psi) ->
                   let _ = dprint (fun () -> "[inferSchema] looking up psi' = " ^
                            P.dctxToString cD' cPsi') in
                   let (_ , s_cid') = Whnf.mctxCDec cD' psi in
              if s_cid != s_cid' then raise (Error (loc, ContextSchemaClash (cD, cPsi, cD', cPsi')))
               | Some (Int.LF.CtxName psi) ->
                   (dprint (fun () -> "[inferCtxSchema] Added free context variable "
                              ^ R.render_name psi ^ " with schema " ^
                              R.render_cid_schema s_cid ^
                              " to FCVar");
                   FCVar.add psi (cD, Int.LF.CDecl (psi, s_cid, Int.LF.No)))
          end

      | (Int.LF.DDec (cPsi1, Int.LF.TypDecl(_ , _tA1)) , Int.LF.DDec (cPsi2, Int.LF.TypDecl(_ , _tA2))) ->
          inferCtxSchema loc (cD, cPsi1) (cD',cPsi2)
      | _ -> raise (Error (loc, PatternContextClash (cD, cPsi, cD', cPsi')))

(* ********************************************************************************)
(* Elaborate computation-level patterns *)

and elPatMetaObj cD pat (cdecl, theta) = match pat with
  | (Apx.Comp.PatMetaObj (loc, cM)) ->
    (match cdecl with
       | Int.LF.MDecl (_, tA, cPsi) ->
           (match  elMetaObj cD cM (Int.Comp.MetaTyp (tA, cPsi), theta)  with
              | (Int.Comp.MetaObj (loc, phat, tM) as cM') ->
                  (Int.Comp.PatMetaObj (loc, cM'),
                   Int.LF.MDot (Int.LF.MObj (phat, tM), theta))
           )
       | Int.LF.PDecl (_, tA, cPsi) ->
           (match elMetaObj cD cM (Int.Comp.MetaParamTyp (tA, cPsi), theta)  with
              | (Int.Comp.MetaParam (loc, phat, h) as cM') ->
                  (Int.Comp.PatMetaObj (loc, cM'),
                   Int.LF.MDot (Int.LF.PObj (phat, h), theta))
           )

       | Int.LF.CDecl (_, w, _dep)        ->
           let (Int.Comp.MetaCtx (loc, cPsi) as cM') = elMetaObj cD cM (Int.Comp.MetaSchema w, theta) in
             (Int.Comp.PatMetaObj (loc, cM'),
              Int.LF.MDot (Int.LF.CObj (cPsi), theta))
    )
  | pat -> raise (Error.Violation "Expected a meta-object; Found a computation-level pattern")

and elPatChk (cD:Int.LF.mctx) (cG:Int.Comp.gctx) pat ttau = match (pat, ttau) with
  | (Apx.Comp.PatEmpty (loc, cpsi), (tau, theta)) ->
      let cPsi' = Lfrecon.elDCtx (Lfrecon.Pibox) cD cpsi in
      let Int.Comp.TypBox (_ , _tQ, cPsi_s) = Whnf.cnormCTyp ttau  in
        begin try
          Unify.unifyDCtx (Int.LF.Empty) cPsi' cPsi_s;
          (Int.LF.Empty, Int.Comp.PatEmpty (loc, cPsi'))
        with Unify.Failure _msg ->
          raise (Error.Violation "Context mismatch in pattern")
        end
  | (Apx.Comp.PatVar (loc, name, x) , (tau, theta)) ->
      (Int.LF.Dec(cG, Int.Comp.CTypDecl (name, Int.Comp.TypClo (tau, theta))),
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

  | (Apx.Comp.PatPair (loc, pat1, pat2) , (Int.Comp.TypCross (tau1, tau2),
                                           theta)) ->
      let (cG1, pat1') = elPatChk cD cG pat1 (tau1, theta) in
      let (cG2, pat2') = elPatChk cD cG1 pat2 (tau2, theta) in
        (cG2, Int.Comp.PatPair (loc, pat1', pat2'))

  | (Apx.Comp.PatMetaObj (loc, cM), (Int.Comp.TypBox (_loc, tA, cPsi), theta)) ->
      (* cM = MetaObj or MetaObjAnn *)
      let cM' = elMetaObj cD cM (Int.Comp.MetaTyp (tA, cPsi), theta) in
        (cG, Int.Comp.PatMetaObj (loc, cM'))
  (* Error handling cases *)
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
         | (Int.Comp.TypPiBox ((Int.LF.MDecl (n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
             let cPsi' = C.cnormDCtx (cPsi, theta) in
             let tA'   = C.cnormTyp (tA, theta) in
             let psihat  = Context.dctxToHat cPsi' in

             let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
             let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaObj (loc, psihat, tM')) in
             let ttau' = (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)) in
             let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
               (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

           | (Int.Comp.TypPiBox ((Int.LF.PDecl (n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypPiBox #p implicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let cPsi' = C.cnormDCtx (cPsi, theta) in
             let tA'   = C.cnormTyp (tA, theta) in
             let psihat  = Context.dctxToHat cPsi' in

             let p   =  Int.LF.MPVar(Whnf.newMPVar (Some n) (cD, cPsi', tA'), (Whnf.m_id, LF.id)) in
              let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaParam (loc, psihat, p)) in
             let ttau' = (tau, Int.LF.MDot (Int.LF.PObj (psihat, p), theta)) in
             let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
               (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

          | (Int.Comp.TypCtxPi ((n, w, Int.Comp.Implicit), tau), theta) ->
               let cPsi  = Int.LF.CtxVar (Int.LF.CInst (n, ref None, w, Int.LF.Empty, cD)) in
               let ttau' = (tau, Int.LF.MDot (Int.LF.CObj (cPsi), theta)) in
               let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaCtx (loc, cPsi)) in
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
         | (Int.Comp.TypPiBox ((cdecl, Int.Comp.Explicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypPiBox explicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let (pat, theta') = elPatMetaObj cD pat' (cdecl, theta) in
             let _ = dprint (fun () -> "[elPatSpine] pat = " ^ P.patternToString cD cG pat ) in
             let _ = dprint (fun () -> "[elPatSpine] remaining pattern spine must have type : " ) in
             let _ = dprint (fun () -> "              " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta'))) in
             let (cG1, pat_spine, ttau2) = elPatSpine cD cG pat_spine' (tau, theta') in
               (cG1, Int.Comp.PatApp (loc, pat, pat_spine), ttau2)
         | (Int.Comp.TypCtxPi ((x, w, Int.Comp.Explicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypCtxPi Explicit - ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let (pat, theta') = elPatMetaObj cD pat' (Int.LF.CDecl(x,w, Int.LF.No), theta) in
             let (cG1, pat_spine, ttau2) = elPatSpine cD cG pat_spine' (tau, theta') in
               (cG1, Int.Comp.PatApp (loc, pat, pat_spine), ttau2)
         | (Int.Comp.TypPiBox ((Int.LF.MDecl (n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypPiBox implicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let cPsi' = C.cnormDCtx (cPsi, theta) in
             let tA'   = C.cnormTyp (tA, theta) in
             let psihat  = Context.dctxToHat cPsi' in

             let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
             let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaObj (loc, psihat, tM')) in
             let ttau' = (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)) in
             let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
               (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

           | (Int.Comp.TypPiBox ((Int.LF.PDecl (n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypPiBox #p implicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
             let cPsi' = C.cnormDCtx (cPsi, theta) in
             let tA'   = C.cnormTyp (tA, theta) in
             let psihat  = Context.dctxToHat cPsi' in

             let p   =  Int.LF.MPVar(Whnf.newMPVar (Some n) (cD, cPsi', tA'), (Whnf.m_id, LF.id)) in
             let _   = dprint (fun () -> "[elPatSpine] new MPVar #p = " ^ P.headToString cD cPsi' p ^ "\n") in
              let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaParam (loc, psihat, p)) in
             let ttau' = (tau, Int.LF.MDot (Int.LF.PObj (psihat, p), theta)) in
             let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
               (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)


          | (Int.Comp.TypCtxPi ((n, w, Int.Comp.Implicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypCtxPi implicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
               let cPsi  = Int.LF.CtxVar (Int.LF.CInst (n, ref None, w, Int.LF.Empty, cD)) in
               let ttau' = (tau, Int.LF.MDot (Int.LF.CObj (cPsi), theta)) in
               let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaCtx (loc, cPsi)) in
               let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
                 (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)
          | _ ->  raise (Error (loc, TooManyMetaObj))
      )

and recPatObj' cD pat (cD_s, tau_s) = match pat with
  | Apx.Comp.PatAnn (_ , (Apx.Comp.PatMetaObj (loc, _) as pat') , Apx.Comp.TypBox (loc', a, psi) ) ->
      let _ = dprint (fun () -> "[recPatObj' - PatMetaObj] scrutinee has type tau = " ^ P.compTypToString cD_s  tau_s) in
      let cPsi = Lfrecon.elDCtx (Lfrecon.Pibox) cD psi in
      let tP   = Lfrecon.elTyp (Lfrecon.Pibox) cD cPsi a in
      let Int.Comp.TypBox (_ , _tQ, cPsi_s) = tau_s  in
      let _       = inferCtxSchema loc (cD_s, cPsi_s) (cD, cPsi) in
            (* as a side effect we will update FCVAR with the schema for the
               context variable occurring in cPsi' *)
      let ttau' = (Int.Comp.TypBox(loc',tP, cPsi), Whnf.m_id) in
      let (cG', pat') = elPatChk cD Int.LF.Empty pat'  ttau' in
              (cG', pat', ttau')

  | Apx.Comp.PatEmpty (loc, cpsi) ->
      let cPsi = Lfrecon.elDCtx (Lfrecon.Pibox) cD cpsi in
      let Int.Comp.TypBox (_ , (Int.LF.Atom(_, a, _) as _tQ), cPsi_s) = tau_s  in
      let _       = inferCtxSchema loc (cD_s, cPsi_s) (cD, cPsi) in
      let tP     =  mgTyp cD cPsi a (Typ.get a).Typ.kind in
      let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of empty type  " ^
                        P.typToString cD cPsi (tP, LF.id)) in
      let ttau' = (Int.Comp.TypBox (loc, tP, cPsi), Whnf.m_id) in
        (Int.LF.Empty, Int.Comp.PatEmpty (loc, cPsi), ttau')

  | Apx.Comp.PatAnn (_ , pat, tau) ->
      let _ = dprint (fun () -> "[recPatObj' PatAnn] scrutinee has type tau = " ^ P.compTypToString cD_s  tau_s) in
      let tau' = elCompTyp cD tau in
      let ttau' = (tau', Whnf.m_id) in
      let (cG', pat') = elPatChk cD Int.LF.Empty pat ttau' in
        (cG', pat', ttau')

  | _ ->
      let tau_p = inferPatTyp cD tau_s in
      let _ = dprint (fun () -> "[inferPatTyp] : tau_p = " ^ P.compTypToString cD  tau_p) in
      let ttau' = (tau_p, Whnf.m_id) in
      let (cG', pat')  = elPatChk cD Int.LF.Empty pat ttau' in
        (cG', pat', ttau')


and recPatObj cD pat (cD_s, tau_s) =
  let _ = dprint (fun () -> "[recPatObj] scrutinee has type tau = " ^ P.compTypToString cD_s  tau_s) in
  let (cG', pat', ttau') = recPatObj' cD pat (cD_s, tau_s) in
  (* cD' ; cG' |- pat' => tau' (may contain free contextual variables) *)
  (* where cD' = cD1, cD and cD1 are the free contextual variables in pat'
           cG' contains the free computation-level variables in pat'
     cG' and cD' are handled destructively via FVar and FCVar store
  *)
  let _                      = Lfrecon.solve_constraints cD in
  let _ = dprint (fun () -> "[recPatObj] pat (before abstraction) = " ^
                    P.patternToString cD cG' pat' ) in
  let _ = dprint (fun () -> "[recPatObj] Abstract over pattern and its type") in
  let (cD1, cG1, pat1, tau1) = Abstract.abstrPatObj cD (Whnf.cnormCtx (cG', Whnf.m_id)) pat' (Whnf.cnormCTyp ttau') in
  (* cD1 ; cG1 |- pat1 => tau1 (contains no free contextual variables) *)
  let l_cd1                  = Context.length cD1 in
  let l_delta                = Context.length cD  in
    ((l_cd1, l_delta), cD1, cG1,  pat1, tau1)

(* ********************************************************************************)
(* recPattern will become obsolete when we switch to the new syntax *)
 and recPattern (cD, cPsi) delta psi m tPopt =
  let cD'     = elMCtx  Lfrecon.Pibox delta in
  let cPsi'   = Lfrecon.elDCtx  Lfrecon.Pibox cD' psi in
  let _       = inferCtxSchema Syntax.Loc.ghost (cD, cPsi) (cD', cPsi') in

  let _ = dprint (fun () -> "[recPattern] (specified pattern) cPsi' = " ^
                    P.dctxToString cD'  cPsi' ) in
  let _ = (dprint (fun () -> "[recPattern] " ^ P.mctxToString cD' ^ " [ " ^ P.dctxToString cD' cPsi' ^ "]")) in
  let tP'     = begin match tPopt with
                  | FullTyp  a    ->
                      let tP' = Lfrecon.elTyp Lfrecon.Pibox cD' cPsi' a  in
                        (* recTyp Lfrecon.Pibox cD' cPsi' (tP', LF.id) ;*) tP'
                  | PartialTyp a  ->
                      let _ = dprint (fun () -> "[mgTyp] Generate mg type in context " ^
                                        P.dctxToString cD' cPsi' ) in
                      mgTyp cD' cPsi' a (Typ.get a).Typ.kind
                end in

  let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of type  " ^
                               P.typToString cD' cPsi' (tP', LF.id)) in

  let m' = Apxnorm.cnormApxTerm cD' Apx.LF.Empty m (cD', Int.LF.MShift 0) in
  let tR = Lfrecon.elTerm' Lfrecon.Pibox cD' cPsi' m' (tP', LF.id) in

  let _  = Lfrecon.solve_constraints cD'  in

  let _   = dprint (fun () -> "recPattern: Elaborated pattern...\n" ^ P.mctxToString cD' ^ "  ;   " ^
                      P.dctxToString cD' cPsi' ^ "\n   |-\n    "  ^ P.normalToString cD' cPsi' (tR, LF.id) ^
                      "\n has type " ^ P.typToString  cD' cPsi' (tP', LF.id) ^ "\n") in

  let phat = Context.dctxToHat cPsi' in

  let (cD1', cPsi1', (_phat, tR1'), tP1') =  Abstract.abstrPattern cD' cPsi' (phat, tR) tP' in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.mctxToString cD1' ^ "  ;   " ^ P.dctxToString cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.normalToString cD1' cPsi1' (tR1', LF.id) ^ "\n has type \n " ^
                          P.typToString cD1' cPsi1'  (tP1', LF.id)) in
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in
    ((n,k), cD1', cPsi1', Some tR1', tP1')


(* and recEmptyPattern (cD, cPsi) delta psi tPopt =
  let cD'     = elMCtx  Lfrecon.Pibox delta in
  let cPsi'   = Lfrecon.elDCtx  Lfrecon.Pibox cD' psi in
  let _ = dprint (fun () -> "[recPattern] cPsi' = " ^ P.dctxToString cD' cPsi' ) in

  let _ = (dprint (fun () -> "[recPattern] " ^ P.mctxToString cD' ^ " [ " ^ P.dctxToString cD' cPsi' ^ "]")) in

  let tP'     = begin match tPopt with
                  | FullTyp  a    ->
                      let tP' = Lfrecon.elTyp Lfrecon.Pibox cD' cPsi' a  in
                        (* recTyp Lfrecon.Pibox cD' cPsi' (tP', LF.id) ;*) tP'
                  | PartialTyp a  ->
                      let _ = dprint (fun () -> "[mgTyp] Generate mg type in context " ^
                                        P.dctxToString cD' cPsi' ) in
                      mgTyp cD' cPsi' a (Typ.get a).Typ.kind
                end in

  let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of type  " ^
                               P.typToString cD' cPsi' (tP', LF.id)) in

  let _  = Lfrecon.solve_constraints cD'  in
  let (cD1', cPsi1', tP1') =  (cD', cPsi', tP') in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.mctxToString cD1' ^ "  ;   " ^ P.dctxToString cD1' cPsi1' ) in
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in
    ((n,k), cD1', cPsi1', None, tP1')

*)

(* synRefine caseT (cD, cD1) (Some tR1) (cPsi, tP) (cPsi1, tP1) = (t, cD1')

   if  cD, cD1 ; cPsi  |- tP  <= type
       cD1; cPsi1 |- tP1 <= type
       cD, cD1 ; cPsi  |- tR1 <= tP

   then
       cD1' |- t <= cD, cD1    and

       cD1' |- |[t]|(|[r]|cPsi)  =   |[t]|(|[r1]|cPsi1)
       cD1' ; |[t]|(|[r]|cPsi) |- |[t]|(|[r]|cP)  =   |[t]|(|[r1]|tP1)
*)
and synRefine loc caseT (cD, cD1) pattern1 (cPsi, tP) (cPsi1, tP1) =
    let cD'    = Context.append cD cD1 in  (*         cD'  = cD, cD1     *)
    let _      = dprint (fun () -> "[synRefine] cD' = " ^ P.mctxToString cD') in
    let t      = Ctxsub.mctxToMSub cD'  in  (*         .  |- t   <= cD'   *)
    let _      = dprint (fun () -> "[synRefine] mctxToMSub .  |- t <= cD' ") in
    let _ = dprint (fun () -> "                      " ^
                             P.msubToString  Int.LF.Empty (Whnf.cnormMSub t)) in
    let n      = Context.length cD1 in
    let m      = Context.length cD in

    let t1     = Whnf.mvar_dot (Int.LF.MShift m) cD1 in
      (* cD, cD1 |- t1 <= cD1 *)
    let mt1    = Whnf.mcomp t1 t in        (*         .  |- mt1 <= cD1   *)

    let cPsi'  = Whnf.cnormDCtx (cPsi, t) (* t *) in        (*      .  |- cPsi' ctx    *)
    let cPsi1' = Whnf.cnormDCtx (cPsi1, mt1) in             (*      .  |- cPsi1 ctx    *)

    let tP'    = Whnf.cnormTyp (tP, t) (* t *) in           (*  . ; cPsi'  |- tP'  <= type *)
    let tP1'   = Whnf.cnormTyp (tP1, mt1) in                (*  . ; cPsi1' |- tP1' <= type *)

    let _  = begin try
          Unify.unifyDCtx (Int.LF.Empty) cPsi' cPsi1';
          Unify.unifyTyp   (Int.LF.Empty) cPsi' (tP', LF.id) (tP1', LF.id);
          dprint (fun () -> "Unify successful: \n" ^  "  Inferred pattern type: "
                    ^  P.dctxToString Int.LF.Empty cPsi1' ^ "    |-    "
                    ^ P.typToString Int.LF.Empty cPsi1' (tP1', LF.id)
                    ^ "\n  Expected pattern type: "
                    ^ P.dctxToString Int.LF.Empty  cPsi1' ^ "    |-    "
                    ^ P.typToString Int.LF.Empty cPsi1' (tP', LF.id))
        with Unify.Failure msg ->
          dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n" ^  "  Inferred pattern type: "
                   ^  P.dctxToString Int.LF.Empty cPsi1' ^ "    |-    "
                   ^ P.typToString Int.LF.Empty cPsi1' (tP1', LF.id)
                   ^ "\n  Expected pattern type: "
                   ^ P.dctxToString Int.LF.Empty cPsi' ^ "    |-    "
                   ^ P.typToString Int.LF.Empty cPsi' (tP', LF.id));
          dprint (fun () -> "cD' = " ^ P.mctxToString cD');
          raise (Check.Comp.Error (loc, Check.Comp.PattMismatch ((cD1, cPsi1, pattern1, (tP1, LF.id)),
                                                                 (cD', cPsi, (tP, LF.id)))))
        end
    in
    let _  = begin match (caseT, pattern1) with
               | (_, None) -> ()
               | (IndexObj (_phat, tR'), Some tR1) ->
                   begin try
                     (dprint (fun () -> "Pattern matching on index object...unify scrutinee with pattern");
                        Unify.unify Int.LF.Empty (Whnf.normDCtx cPsi') (C.cnorm (tR',  t),  LF.id)
                                                       (C.cnorm (tR1, mt1), LF.id))
                   with Unify.Failure msg ->
                     (dprint (fun () -> "Unify ERROR: " ^ msg);
                      raise (Error.Violation "Pattern matching on index argument failed"))
                   end
               | (DataObj, _) -> ()
             end
    in
    let _ = dprnt "AbstractMSub..." in
      (* cD1' |- t' <= cD' *)
    let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub t) in

    let rec drop t l_delta1 = match (l_delta1, t) with
        | (0, t) -> t
        | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

    let t0   = drop t' n in  (* cD1' |- t0 <= cD *)
    let cPsi1_new = Whnf.cnormDCtx (cPsi1, Whnf.mcomp t1 t') in
        (* cD1' |- cPsi1_new ctx *)
    let outputPattern = match pattern1 with
                   | Some tR1 -> Some (Whnf.cnorm (tR1, Whnf.mcomp t1 t'))
                   | None -> None in
        (* cD1' ; cPsi1_new |- tR1 <= tP1' *)
    let _ = dprint (fun () -> "synRefine [Substitution] t': " ^ P.mctxToString cD1' ^
                        "\n|-\n" ^ P.msubToString cD1' t' ^ "\n <= " ^ P.mctxToString cD' ^ "\n") in
      (t0, t', cD1', cPsi1_new, outputPattern)

and synPatRefine loc caseT (cD, cD_p) pat (tau_s, tau_p) =
 begin try
   let cD'  = Context.append cD cD_p in   (* cD'  = cD, cD_p   *)
    let _   = dprint (fun () -> "[synPatRefine] cD' = "
                           ^ P.mctxToString cD') in
    let t   = Ctxsub.mctxToMSub cD'  in  (* .  |- t   <= cD'  *)
    let _   = dprint (fun () -> "[synPatRefine] mctxToMSub .  |- t <= cD' ") in
    let _ = dprint (fun () -> "                        " ^
                      P.msubToString  Int.LF.Empty (Whnf.cnormMSub t)) in
    let n   = Context.length cD_p in
    let m   = Context.length cD in
    let t1  = Whnf.mvar_dot (Int.LF.MShift m) cD_p in
      (* cD, cD_p |- t1 <= cD_p *)
    let mt1 = Whnf.mcomp t1 t in         (* .  |- mt1 <= cD1   *)
    let tau_s' = Whnf.cnormCTyp (tau_s, t) in
    let tau_p' = Whnf.cnormCTyp (tau_p, mt1) in
    let _  = begin match (caseT, pat) with
               | (DataObj, _) -> ()
               | (IndexObj (phat, tR'), Int.Comp.PatMetaObj(_, Int.Comp.MetaObj (_, _, tR1))) ->
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
    let (t', cD1') = Abstract.abstractMSub (Whnf.cnormMSub t) in
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

and elBranch caseTyp cD cG branch tau_s (tau, theta) = match branch with
  | Apx.Comp.EmptyBranch(loc, delta, (Apx.Comp.PatEmpty (loc', cpsi) as pat)) ->
      let cD'    = elMCtx  Lfrecon.Pibox delta in
      let ((l_cd1', l_delta) , cD1', _cG1,  pat1, tau1)  =  recPatObj cD' pat  (cD, tau_s)  in
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
      let Int.Comp.TypBox (_, (Int.LF.Atom(_, a, _) as tP) , cPsi) = tau_s in
      let _ = dprint (fun () -> "[elBranch] Reconstruction of pattern ... ") in
      let typAnn = (cD, PartialTyp a, cPsi) in
      let cD'    = elMCtx  Lfrecon.Pibox delta in
      (* ***************  RECONSTRUCT PATTERN BEGIN *************** *)
      let ((l_cd1', l_delta),
           cD1', cPsi1', pattern', tP1') = recMObj cD' mO typAnn in
      (* ***************  RECONSTRUCT PATTERN DONE  *************** *)
      let (cPsi, tP) =  (Whnf.cnormDCtx (cPsi, Int.LF.MShift l_cd1') ,
                         Whnf.cnormTyp (tP, Int.LF.MShift l_cd1')) in
      (* NOW: cD , cD1 |- cPsi  and    cD, cD1' ; cPsi |- tP        *)
      (*      cD1 ; cPsi1' |- tM1' <= tP1'                          *)
      (* ***************                            *************** *)
      let caseT'  = begin match caseTyp with
                      | IndexObj (phat, tR') ->
                          IndexObj (phat, Whnf.cnorm (tR', Int.LF.MShift l_cd1'))
                      | DataObj -> DataObj
                    end in
      (* *************** Synthesize Refinement Substitution *********)
      let (t', t1, cD1'', cPsi1'', tR1') =
        synRefine loc caseT' (cD, cD1') pattern' (cPsi, tP) (cPsi1', tP1') in
      (*   cD1''|-  t' : cD   and   cD1'' ; [t']cPsi |- tR1 <= [t']tP
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

      (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0
          then cD, cD1' |- e1 apx_exp
      *)
      (* if   cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
                 then cD1'' |- e' apx_exp
      *)
      let e'      =  Apxnorm.cnormApxExp cD' Apx.LF.Empty e1  (cD1'', t1) in
        (* Note: e' is in the scope of cD1''  *)
 (*     let _       = dprint (fun () -> "[Apx.cnormApxExp ] done ") in
      let _ = dprint (fun () -> "[cnormCtx] cD = " ^ P.mctxToString cD) in
      let _ = dprint (fun () -> "[cnormCtx] cG = " ^ P.gctxToString cD cG) in
      let _ = dprint (fun () -> "t' = " ^ P.msubToString cD1'' t') in
 *)
      let cG   = Whnf.normCtx cG in
      let cG'  = Whnf.cnormCtx (cG, t') in
(*    let _ = (dprint (fun () -> "tau' = " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta))) ;
               dprint (fun () -> "t'   = " ^ P.msubToString cD1'' t' )) in
*)
      let tau'    = Whnf.cnormCTyp (tau, Whnf.mcomp theta t') in

      let _       = dprint (fun () -> "[elBranch] Elaborate branch \n" ^
                              P.mctxToString cD1'' ^ "  ;  " ^
                              P.gctxToString cD1'' cG' ^ "\n      |-\n" ^
                              "against type " ^ P.compTypToString cD1'' tau' ^ "\n") in
        (*                             "against type " ^ P.compTypToString cD1'' (C.cnormCTyp ttau') ^ "\n") *)

      let eE'      = elExp cD1'' cG'  e' (tau', Whnf.m_id) in
      let Some tR1' = tR1' in
      let pat = Int.Comp.MetaObjAnn (loc', cPsi1'', tR1') in
      let _       = FCVar.clear() in
      let _ = dprint (fun () -> "[elBranch] Pattern " ^
                        P.patternToString cD1'' Int.LF.Empty (Int.Comp.PatMetaObj (loc',pat))) in
      let _        = dprint (fun () -> "[elBranch] Body done \n") in
      let _ = dprint (fun () -> "        " ^ P.expChkToString cD1'' cG' eE') in
      let b = Int.Comp.Branch (loc, cD1'', Int.LF.Empty,
                               Int.Comp.PatMetaObj (loc', pat), t', eE')
      in
        b


 | Apx.Comp.Branch (loc, _omega, delta, pat, e) ->
     let _ = dprint (fun () -> "[elBranch] Reconstruction of general pattern of type "
                       ^ P.compTypToString cD tau_s) in
    let cD'    = elMCtx  Lfrecon.Pibox delta in
    let ((l_cd1', l_delta), cD1', cG1,  pat1, tau1)  =  recPatObj cD' pat (cD, tau_s)
     in
    let _ = dprint (fun () -> "[rePatObj] done") in
    let _ = dprint (fun () -> "           " ^ P.mctxToString cD1' ^ " ; " ^
                      P.gctxToString cD1' cG1 ^ "\n    |- " ^
                      P.patternToString cD1' cG1 pat1 ^ " : " ^
                      P.compTypToString cD1' tau1) in
    let tau_s' = Whnf.cnormCTyp (tau_s, Int.LF.MShift l_cd1') in
    (* ***************                            *************** *)
    let caseT'  = begin match caseTyp with
                  | IndexObj (phat, tR') ->
                      IndexObj (phat, Whnf.cnorm (tR', Int.LF.MShift l_cd1'))
                  | DataObj -> DataObj
                  end in
    (* cD |- tau_s and cD, cD1 |- tau_s' *)
    (* cD1 |- tau1 *)

    let (t', t1, cD1'', pat1') = synPatRefine loc caseT' (cD, cD1') pat1 (tau_s', tau1) in
    (*  cD1'' |- t' : cD    and   cD1'' |- t1 : cD, cD1' *)
    let _ = dprint (fun () -> " cD1'' = " ^ P.mctxToString cD1'' ) in
    let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
    (*   cD1' |- cG1     cD1'' |- t1 : cD, cD1'    cD, cD1' |- ?   cD1' *)
    let cD'      = Context.append cD cD1' in
    let _ = dprint (fun () -> "cD' = " ^ P.mctxToString cD') in
    let _ = dprint (fun () -> "    ' |- cG1 = " ^ P.gctxToString cD' cG1 ) in
    let _ = dprint (fun () -> " t1 : cD' = " ^ P.msubToString cD1'' t1) in
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

    let _ = (dprint (fun () -> "tau' = " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta))) ;
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

type reconType = Lfrecon.reconType

let kind = Lfrecon.elKind Int.LF.Empty Int.LF.Null

let typ rectyp apxT = Lfrecon.elTyp rectyp Int.LF.Empty Int.LF.Null apxT

let schema = elSchema

let compkind = elCompKind Int.LF.Empty

let comptyp tau =
  let tau' = elCompTyp Int.LF.Empty tau in
  let _ = dprint (fun () -> "[elCompTyp] " ^ P.compTypToString Int.LF.Empty tau' ^ " done \n") in
  tau'

let exp  = elExp  Int.LF.Empty

let exp' = elExp' Int.LF.Empty
