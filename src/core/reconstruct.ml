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


let strengthen : bool ref =  Lfrecon.strengthen

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

type error =
  | ValueRestriction    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | IllegalCase         of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | CompScrutineeTyp    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.LF.tclo * Int.LF.dctx
  | MetaObjContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.dctx
  | PatternContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | ContextSchemaClash  of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | MetaObjectClash     of Int.LF.mctx * (Int.Comp.meta_typ * Int.LF.msub)
  | MissingMetaObj
  | TooManyMetaObj
  | CompTypEmpty       of Int.LF.mctx * Int.Comp.tclo
  | TypeAbbrev         of Id.name
  | CtxMismatch        of Int.LF.mctx * Int.Comp.typ * Int.LF.dctx
  | PatternMobj
  | PatAnn
  | PatIndexMatch  of Int.LF.mctx * Int.LF.dctx * Int.LF.normal
  | MCtxIllformed of Int.LF.mctx
  | TypMismatch        of Int.LF.mctx * Int.Comp.tclo * Int.Comp.tclo


exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | MCtxIllformed cD ->
            Format.fprintf ppf "Unable to abstract over the free meta-variables due to dependency on the specified meta-variables. The following meta-context was reconstructed, but is ill-formed: %a"
              (P.fmt_ppr_lf_mctx Pretty.std_lvl) cD
        | PatIndexMatch (cD, cPsi, tR) ->
            Format.fprintf ppf "Pattern matching on index argument %a fails. @@
  Note that unification is conservative and will fail if it cannot handle a case."
              (P.fmt_ppr_lf_normal cD cPsi Pretty.std_lvl) tR
        | PatAnn     ->
            Format.fprintf ppf
              "Type annotations on context variables and parameter variables not supported at this point."
        | PatternMobj ->
            Format.fprintf ppf
              "Expected a meta-object; Found a computation-level pattern"
        | CtxMismatch (cD, tau, cPsi) ->
            Format.fprintf ppf
              "Context mismatch@.\
               @ @ expected: %a@.\
               @ @ found object in context %a"
            (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) tau
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
        | TypeAbbrev a ->
          Format.fprintf ppf
            "Type definition %s cannot contain any free meta-variables in its type."
            (R.render_name a)
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

       | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
           Error.report_mismatch ppf
             "Type of destructor did not match the type it was expected to have."
             "Type of destructor" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
             (Whnf.cnormCTyp (tau1, theta1))
             "Expected type" (P.fmt_ppr_cmp_typ cD Pretty.std_lvl)
             (Whnf.cnormCTyp (tau2, theta2))
))



let rec get_ctxvar cPsi  = match cPsi with
  | Int.LF.Null -> None
  | Int.LF.CtxVar (psi_name) -> Some psi_name
  | Int.LF.DDec (cPsi, _ ) -> get_ctxvar cPsi


let rec extend_mctx cD (x, (cdecl, dep), t) = match cdecl with
  | Int.LF.CDecl(_psi, schema,_ ) ->
      let dep' = match dep with Int.Comp.Explicit -> Int.LF.No | Int.Comp.Implicit -> Int.LF.Maybe in
        Int.LF.Dec(cD, Int.LF.CDecl(x, schema, dep'))
  | Int.LF.MDecl(_u, tA, cPsi) ->
      Int.LF.Dec(cD, Int.LF.MDecl(x, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t)))
  | Int.LF.PDecl(_u, tA, cPsi) ->
      Int.LF.Dec(cD, Int.LF.PDecl(x, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t)))
  | Int.LF.SDecl (_s, cPhi, cPsi) ->
      Int.LF.Dec(cD, Int.LF.SDecl(x, C.cnormDCtx (cPhi, t), C.cnormDCtx (cPsi, t)))


let mk_name_cdec cdec = match cdec with
  | Int.LF.MDecl (u, tA, cPsi) -> mk_name (SomeName u) (* mk_name (MVarName (Typ.gen_mvar_name tA)) *)
  | Int.LF.PDecl (p, tA, cPsi) -> mk_name (PVarName None)
  | Int.LF.CDecl (psi_name, schema_cid, _ ) -> mk_name (SomeName (psi_name))
  | Int.LF.SDecl (s, cPsi, cPhi) -> mk_name (SomeName s)

(* etaExpandMMV loc cD cPsi sA  = tN
 *
 *  cD ; cPsi   |- [s]A <= typ
 *
 *  cD ; cPsi   |- tN   <= [s]A
 *)
let rec etaExpandMMVstr loc cD cPsi sA  n =
  etaExpandMMVstr' loc cD cPsi (Whnf.whnfTyp sA) n

and etaExpandMMVstr' loc cD cPsi sA  n = match sA with
  | (Int.LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
      let s_proj = ConvSigma.gen_conv_sub conv_list in
      let tQ    = ConvSigma.strans_typ cD (tP, s) conv_list in
      (*  cPsi |- s_proj : cPhi
          cPhi |- tQ   where  cPsi |- tP   and [s_proj]^-1([s]tP) = tQ  *)

      let (ss', cPhi') = Subord.thin' cD a cPhi in
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
      Int.LF.Lam (loc, x,
                  etaExpandMMVstr loc cD (Int.LF.DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) x )


type caseType  = IndexObj of Int.LF.psi_hat * Int.LF.normal | DataObj

type typAnn    = FullTyp of Apx.LF.typ | PartialTyp of cid_typ

(** This function does the same thing as unifyDCtx in unify.ml, but in
    addition records new names for variables left free by the user
    when they are instantiated. *)
let unifyDCtxWithFCVar cD cPsi1 cPsi2 =
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

(* -------------------------------------------------------------*)

let rec apx_length_typ_rec t_rec = match t_rec with
  | Apx.LF.SigmaLast _ -> 1
  | Apx.LF.SigmaElem (x, _ , rest ) ->
      (print_string (R.render_name x ^ "  ");
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

let elCDecl recT cD cdecl = match cdecl with
  | Apx.LF.MDecl (u, a, psi) ->
      let cPsi = Lfrecon.elDCtx recT cD psi in
      let tA   = Lfrecon.elTyp recT cD cPsi a in
        Int.LF.MDecl (u, tA, cPsi)

  | Apx.LF.PDecl (u, a, psi) ->
      let cPsi = Lfrecon.elDCtx recT cD psi in
      let tA   = Lfrecon.elTyp recT cD cPsi a in
      (* The type tA is valid, if it either is part of the context schema
         or if it is an instance of a concrete declaration in cPsi.
         This is postponed to checking, since we may not have the
         schema of the context yet.

         let elems =
         let _ = Check.LF.checkTypeAgainstSchema (Syntax.ghost.loc) cD cPsi tA elems
      *)
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

let mgAtomicTyp cD cPsi a kK =
  let (flat_cPsi, conv_list) = flattenDCtx cD cPsi in
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
        let tA1' = strans_typ cD (tA1, s) conv_list in
        let h    = if !strengthen then
                    (let (ss', cPhi') = Subord.thin' cD a flat_cPsi in
                       (* cPhi |- ss' : cPhi' *)
                     let ssi' = LF.invert ss' in
                       (* cPhi' |- ssi : cPhi *)
                       (* cPhi' |- [ssi]tQ    *)
                     let u  = Whnf.newMMVar (Some n) (cD, cPhi' , Int.LF.TClo (tA1', ssi')) in
                     let ss_proj = LF.comp ss' s_proj in
                       Int.LF.MMVar (u, (Whnf.m_id, ss_proj)))
                   else
                     let u  = Whnf.newMMVar (Some n) (cD, flat_cPsi , tA1') in
                     Int.LF.MMVar (u, (Whnf.m_id, s_proj))
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
   | Int.LF.SigmaLast tA -> Int.LF.SigmaLast (mgTyp cD cPsi tA)
   | Int.LF.SigmaElem (x, tA, trec) ->
       let tA' = mgTyp cD cPsi tA in
       let trec' = mgTypRec cD (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA'))) trec in
	 Int.LF.SigmaElem (x, tA', trec')
 end


let rec genMApp loc cD (i, tau_t) = genMAppW loc cD (i, Whnf.cwhnfCTyp tau_t)

and genMAppW loc cD (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox ((Int.LF.MDecl(n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let psihat  = Context.dctxToHat cPsi' in
      let tA'   = C.cnormTyp (tA, theta) in

      (* let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in *)
      let tM'   =  if !strengthen then  etaExpandMMVstr loc cD  cPsi' (tA', LF.id) n
                   else Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
      let _   = dprint (fun () -> "[genMApp] Generated meta^2-variable " ^
                            P.dctxToString cD cPsi' ^ " . " ^
                            P.normalToString cD cPsi' (tM', LF.id)) in
        let _   = dprint (fun () -> "          of type : " ^
                          P.dctxToString cD cPsi' ^ " |- " ^
                          P.typToString cD cPsi' (tA',LF.id) ^ "\n") in
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


  | (Int.Comp.TypPiBox ((Int.LF.SDecl(n, cPhi, cPsi), Int.Comp.Implicit), tau), theta) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let psihat  = Context.dctxToHat cPsi' in
      let cPhi' = C.cnormDCtx (cPhi, theta) in
      let s     =  Whnf.newMSVar (Some n) (cD, cPsi', cPhi') in
      let sigma = Int.LF.MSVar (s, (Int.LF.NoCtxShift, 0), (Whnf.m_id, LF.id)) in
      let _   = dprint (fun () -> "[genMApp] Generated meta^2-variable " ^
                            P.dctxToString cD cPsi' ^ " . " ^
                            P.subToString cD cPsi' sigma) in
        let _   = dprint (fun () -> "          of domain : " ^
                          P.dctxToString cD cPhi' ^ "\n") in
        genMApp loc cD ((Int.Comp.MApp (loc, i, (psihat, Int.Comp.SubstObj sigma))),
                        (tau, Int.LF.MDot (Int.LF.SObj (psihat, sigma), theta)))



  | (Int.Comp.TypPiBox ((Int.LF.CDecl(psi_name, schema_cid, _), Int.Comp.Implicit), tau), theta)
    ->
      let cPsi = Int.LF.CtxVar (Int.LF.CInst (psi_name, ref None, schema_cid, cD, Whnf.m_id)) in
      let _   = dprint (fun () -> "\n[genMApp] Generated ctx-variable " ^
                          P.dctxToString cD cPsi) in
      let _ = dprint (fun () -> "[genMApp] Show tau : " ^
                        P.compTypToString cD
                        (Whnf.cnormCTyp (tau, Int.LF.MDot (Int.LF.CObj (cPsi), theta)))) in
        genMApp loc cD  ((Int.Comp.CtxApp (loc, i, cPsi)),
                         (tau, Int.LF.MDot (Int.LF.CObj (cPsi), theta)))
  | _ ->
      let _ = dprint (fun () -> "[genMApp]  done " ^
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
        let _   = begin try Unify.forceGlobalCnstr (!Unify.globalCnstrs)
                        with _ -> raise (Error.Violation ("Unresolved constraints - MetaObj cannot be reconstructed"))
                  end  in
        let _   = dprint (fun () -> "[elMetaObj] tA = " ^ P.typToString cD cPsi (tA, LF.id) ) in
        let _   = dprint (fun () -> "[elMetaObj] tM = " ^ P.normalToString cD cPsi (tM', LF.id) ) in
          Int.Comp.MetaObj (loc, phat, tM')
      else
         raise (Error.Violation ("Contexts do not match - MetaObj not of the appropriate meta-type"
                                ^ P.typToString cD cPsi (tA, LF.id)))
  | (Apx.Comp.MetaSub (loc, phat, s), (Int.Comp.MetaSubTyp (cPhi, cPsi), theta)) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let cPhi' = C.cnormDCtx (cPhi, theta) in
      if Lfrecon.unify_phat cD phat (Context.dctxToHat cPsi') then
        let s' = Lfrecon.elSub loc (Lfrecon.Pibox) cD cPsi' s cPhi' in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _        = Unify.resetGlobalCnstrs () in
        let _        = dprint (fun () -> "[elMetaSObj] cPhi = " ^ P.dctxToString cD cPhi) in
        let _        = dprint (fun () -> "[elMetaSObj] cPsi = " ^ P.dctxToString cD cPsi) in
        let _        = dprint (fun () -> "[elMetaSObj] cPsi |- s : cPhi = " ^ P.subToString cD cPsi s' ) in
          Int.Comp.MetaSObj (loc, phat, s')
      else
         raise (Error.Violation ("Contexts do not match - MetaSObj not of the appropriate meta-type" ))

  | (Apx.Comp.MetaSubAnn (loc, cPhi, s), (Int.Comp.MetaSubTyp (cPsi0, cPsi), theta)) ->
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
      let cPsi0' = C.cnormDCtx (cPsi0, theta) in
      let _        = dprint (fun () -> "[elMetaSObj] (domain) cPsi0 = " ^ P.dctxToString cD cPsi0' ) in
      let s' = Lfrecon.elSub loc (Lfrecon.Pibox) cD cPsi' s cPsi0' in
      let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
      let _        = Unify.resetGlobalCnstrs () in
        (* RETURN POSSIBLY A PARAMETER OBJECT *)
      let _        = dprint (fun () -> "[elMetaSObj] s = " ^ P.subToString cD cPsi' s') in
        Int.Comp.MetaSObj (loc, phat, s')

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
      let _   = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        (* RETURN POSSIBLY A PARAMETER OBJECT *)
      let _   = dprint (fun () -> "[elMetaObj] tM = " ^ P.normalToString cD cPsi' (tM', LF.id) ) in
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
        let _  = dprint (fun () -> "[elMetaObj] expected tA = " ^ P.typToString cD cPsi' (tA', LF.id) ) in
        let _  = dprint (fun () -> "[elMetaObj] h = " ^ P.headToString cD cPsi' h) in
          Int.Comp.MetaParam (loc, phat, h)
      else
        raise (Error.Violation ("MetaParameter not of the appropriate meta-type"
                                ^ P.typToString cD cPsi (tA, LF.id)))

  | (Apx.Comp.MetaCtx(loc, _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
  | (Apx.Comp.MetaObj(loc, _ , _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
 | (Apx.Comp.MetaSub(loc, _ , _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
 | (Apx.Comp.MetaSubAnn(loc, _ , _ ) , (mC, theta)) -> raise (Error (loc,  MetaObjectClash (cD, (mC,theta))))
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
      let cPsi = Int.LF.CtxVar (Int.LF.CInst (psi_name, ref None, schema_cid, cD, Whnf.m_id)) in
      let _ = dprint (fun () -> "[elMetaSpine] Implicit context quantification K = " ) in
      let _ = dprint (fun () ->  P.compKindToString cD (Whnf.cnormCKind (cK, Int.LF.MDot (Int.LF.CObj(cPsi), theta)))) in
      let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.CObj(cPsi), theta))
      in
        Int.Comp.MetaApp (Int.Comp.MetaCtx (loc, cPsi), cS)

  | (s, (Int.Comp.PiKind (_loc, (Int.LF.MDecl (n , tA, cPsi), Int.Comp.Implicit), cK), theta )) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let tA'   = C.cnormTyp (tA, theta) in
      let psihat  = Context.dctxToHat cPsi' in
      (* let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in *)
      let tM'   = if !strengthen then etaExpandMMVstr loc cD  cPsi' (tA', LF.id) n
                  else Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
      let mO    = Int.Comp.MetaObj (loc, psihat, tM') in
      let mS    = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)) in
      let _     = dprint (fun () -> "[elMetaSpine] Insert MMVar for implicit  argument " ^ P.metaObjToString cD mO) in
        Int.Comp.MetaApp (mO, mS)

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
            if Unify.isVar h then
              let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.PObj(psihat, h), theta)) in
              Int.Comp.MetaApp (cM, cS)
            else
              raise (Error (loc,  MetaObjectClash (cD, (Int.Comp.MetaParamTyp (tA, cPsi), theta))))

        | Int.LF.SDecl (_u, cPhi, cPsi) ->
            let (Int.Comp.MetaSObj (loc, psihat, tM) as cM) = elMetaObj cD m (Int.Comp.MetaSubTyp (cPhi, cPsi), theta)  in
            let cS = elMetaSpine loc cD s (cK, Int.LF.MDot (Int.LF.SObj(psihat, tM), theta)) in
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

| Apx.Comp.TypCobase (loc, a, cS) ->
      let _ = dprint (fun () -> "[elCompCotyp] Cobase : " ^ R.render_cid_comp_cotyp a) in
      let tK = (CompCotyp.get a).CompCotyp.kind in
      let _ = dprint (fun () -> "[elCompCotyp] of kind : " ^ P.compKindToString cD tK) in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypCobase (loc, a ,cS')

  | Apx.Comp.TypDef (loc, a, cS) ->
      let tK = (CompTypDef.get a).CompTypDef.kind in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
      let rec spineToMSub cS' ms = match cS' with
        | Int.Comp.MetaNil -> ms
        | Int.Comp.MetaApp (mO, mS) ->
            let mf = begin match mO with
              | Int.Comp.MetaObj (loc, phat, tM) -> Int.LF.MObj (phat, tM)
              | Int.Comp.MetaObjAnn (loc, cPsi, tM) -> Int.LF.MObj (Context.dctxToHat cPsi, tM)
              | Int.Comp.MetaParam (loc, phat, h) -> Int.LF.PObj (phat, h)
              | Int.Comp.MetaCtx (loc, cPsi) -> Int.LF.CObj (cPsi)
            end in
              spineToMSub mS (Int.LF.MDot(mf, ms))
      in
      let tau = (CompTypDef.get a).CompTypDef.typ in
        (* eager expansion of type definitions - to make things simple for now
           -bp *)
      let ms = spineToMSub cS' (Int.LF.MShift 0) in
        Whnf.cnormCTyp (tau, ms)
        (* Int.Comp.TypDef (loc, a, cS') *)

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

  | Apx.Comp.TypPiBox ((cdecl, apx_dep), tau) ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl  in
      let tau'   = elCompTyp (Int.LF.Dec (cD, cdecl')) tau in
      let dep = match apx_dep with
          Apx.Comp.Explicit -> Int.Comp.Explicit
        | Apx.Comp.Implicit -> Int.Comp.Implicit in
        Int.Comp.TypPiBox ((cdecl', dep), tau')

  | Apx.Comp.TypBool -> Int.Comp.TypBool

(* *******************************************************************************)

let genMetaVar loc' cD (loc, cdecl, t) = match cdecl with
  | Int.LF.MDecl (n, tA, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      let psihat  = Context.dctxToHat cPsi' in
      let tA'   = C.cnormTyp (tA, t) in
      let tM'   = if !strengthen then etaExpandMMVstr loc cD  cPsi' (tA', LF.id) n
                  else Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
        (Int.Comp.MetaObj (loc', psihat, tM') ,
         Int.LF.MObj (psihat, tM'))

  | Int.LF.PDecl (n, tA, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      let psihat  = Context.dctxToHat cPsi' in
      let tA'   = C.cnormTyp (tA, t) in
      let p     = Whnf.newMPVar (Some n) (cD, cPsi', tA') in
      let h     = Int.LF.MPVar (p, (Whnf.m_id, LF.id)) in
        (Int.Comp.MetaParam (loc', psihat, h) ,
         Int.LF.PObj (psihat, h))

  | Int.LF.CDecl (n, schema_cid, _ ) ->
      let cPsi = Int.LF.CtxVar (Int.LF.CInst (n, ref None, schema_cid, cD, Whnf.m_id)) in
        (Int.Comp.MetaCtx (loc', cPsi),
         Int.LF.CObj cPsi)

  | Int.LF.SDecl (n, cPhi, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, t) in
      let psihat  = Context.dctxToHat cPsi' in
      let cPhi'   = C.cnormDCtx (cPhi, t) in
      let s = Whnf.newMSVar None (cD, cPsi', cPhi') in
      let s' = Int.LF.MSVar (s, (Int.LF.NoCtxShift,0),
                             (Whnf.m_id, LF.id)) in (* Probably LF.id is  wrong *)
      let s' = Whnf.normSub s' in
        (Int.Comp.MetaSObj (loc', psihat, s') ,
         Int.LF.SObj (psihat, s'))

let mgCompTyp cD (loc, c) =
  let cK = (CompTyp.get c).CompTyp.kind in
  let _ = dprint (fun () -> "[mgCompTyp] kind of constant " ^
              (R.render_cid_comp_typ c)) in
  let _ = dprint (fun () -> "               " ^
                    P.compKindToString Int.LF.Empty cK) in
  let rec genMetaSpine (cK, t) = match (cK, t) with
    | (Int.Comp.Ctype _, _t) -> Int.Comp.MetaNil
    | (Int.Comp.PiKind (loc', (cdecl, _ ), cK), t) ->
        let (mO, mF) = genMetaVar loc cD (loc', cdecl, t) in
        let mS = genMetaSpine (cK, Int.LF.MDot (mF, t)) in
          Int.Comp.MetaApp (mO, mS) in
  let mS = genMetaSpine (cK, Whnf.m_id) in
    Int.Comp.TypBase (loc, c, mS)

let rec mgCtx cD' (cD, cPsi) = begin match cPsi with
  | Int.LF.CtxVar (Int.LF.CtxOffset psi_var) ->
      let (n , sW) = Whnf.mctxCDec cD psi_var in
	Int.LF.CtxVar (Int.LF.CInst (n, ref None, sW,
                                      cD, Whnf.m_id))
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

  | Int.Comp.TypPiBox ((Int.LF.MDecl (x, (Int.LF.Atom (_, a, _ ) as tP), cPsi), dep), tau) ->
      let cPsi' = mgCtx cD' (cD_s, cPsi) in
      let tP'   = mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind  in
      let tau'  = inferPatTyp' (Int.LF.Dec (cD', Int.LF.MDecl(x,tP', cPsi')))
                               (Int.LF.Dec (cD_s, Int.LF.MDecl(x,tP, cPsi)), tau) in
        Int.Comp.TypPiBox ((Int.LF.MDecl (x, tP', cPsi'), dep), tau')

  | Int.Comp.TypPiBox ((Int.LF.PDecl (x, tA, cPsi), dep), tau) ->
      let cPsi' = mgCtx cD' (cD_s, cPsi) in
      let tA'   = mgTyp cD' cPsi' tA in
      let tau'  = inferPatTyp' (Int.LF.Dec (cD', Int.LF.MDecl(x,tA', cPsi')))
                               (Int.LF.Dec (cD_s, Int.LF.MDecl(x,tA, cPsi)), tau) in
        Int.Comp.TypPiBox ((Int.LF.PDecl (x, tA', cPsi'), dep), tau')


  | Int.Comp.TypPiBox((Int.LF.CDecl(name, sW, dep), Int.Comp.Implicit), tau) ->
      let tau' = inferPatTyp' (Int.LF.Dec (cD', Int.LF.CDecl (name, sW, Int.LF.Maybe)))
                              (Int.LF.Dec (cD_s, Int.LF.CDecl (name, sW, Int.LF.Maybe)),  tau) in
        Int.Comp.TypPiBox((Int.LF.CDecl(name, sW, dep), Int.Comp.Implicit), tau')

  | Int.Comp.TypPiBox((Int.LF.CDecl(name, sW, dep), Int.Comp.Explicit), tau) ->
      let tau' = inferPatTyp' (Int.LF.Dec (cD', Int.LF.CDecl (name, sW, Int.LF.No)))
                              (Int.LF.Dec (cD_s, Int.LF.CDecl (name, sW, Int.LF.No)),  tau) in
        Int.Comp.TypPiBox((Int.LF.CDecl(name, sW, dep), Int.Comp.Explicit), tau')

  | Int.Comp.TypPiBox ((Int.LF.SDecl (x, cPhi, cPsi), dep), tau) ->
      let cPsi' = mgCtx cD' (cD_s, cPsi) in
      let cPhi' = mgCtx cD' (cD_s, cPhi) in
      let tau'  = inferPatTyp' (Int.LF.Dec (cD', Int.LF.SDecl(x,cPhi', cPsi')))
                               (Int.LF.Dec (cD_s, Int.LF.SDecl(x,cPhi, cPsi)), tau) in
        Int.Comp.TypPiBox ((Int.LF.SDecl (x, cPhi', cPsi'), dep), tau')

  | Int.Comp.TypBox (loc, (Int.LF.Atom(_, a, _) as _tP) , cPsi)  ->
      let cPsi' = mgCtx cD' (cD_s, cPsi) in
      let tP' = mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind  in
        Int.Comp.TypBox (loc, tP', cPsi')


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

let elApply cD (loc, i, mobj) (mdec, tau) theta depend = match mobj , mdec with
  | Apx.Comp.MetaObj (_loc', psihat, m) , Int.LF.MDecl (_, tA, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
        begin try
          let tM'    = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m (C.cnormTyp (tA, theta), LF.id) in
          if depend then
            let  theta' =  Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta) in
            (Int.Comp.MApp (loc, i, (psihat, Int.Comp.NormObj tM')), (tau, theta'))
          else
            (Int.Comp.Apply (loc, i, Int.Comp.Box (loc,psihat, tM')), (tau, theta))
        with Error.Violation msg ->
          dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
          raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn))
        end
  | Apx.Comp.MetaObjAnn (_loc', psi, m) , Int.LF.MDecl (_, tA, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let cPhi =  Lfrecon.elDCtx Lfrecon.Pibox cD psi in
        (begin try
           Unify.unifyDCtx cD cPsi' cPhi
         with
           | Unify.Failure "Context clash" ->
               let expected_tau = Int.Comp.TypBox (Syntax.Loc.ghost,Whnf.cnormTyp (tA, theta),
                                                   Whnf.cnormDCtx (cPsi, theta))   in
                 raise (Error (loc, CtxMismatch (cD, expected_tau, cPhi)))
         end;
         begin try
           let cPhi' = Whnf.normDCtx cPhi in
           let phihat' = Context.dctxToHat cPhi'  in
           let i_norm = Whnf.cnormExp' (i, Whnf.m_id) in
           let tM'    = Lfrecon.elTerm Lfrecon.Pibox cD cPhi' m (C.cnormTyp (tA, theta), LF.id) in
             if depend then
               let theta' = Int.LF.MDot (Int.LF.MObj (phihat', tM'), theta) in
               let tau'' = Whnf.cnormCTyp (tau, theta') in
                 (Int.Comp.MApp (loc, i_norm, (phihat', Int.Comp.NormObj tM')), (tau'', Whnf.m_id))
             else
               (Int.Comp.Apply (loc, i_norm, Int.Comp.Box (loc, phihat', tM')), (tau, theta))
         with Error.Violation msg ->
           dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
           raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn))
         end)

  | Apx.Comp.MetaObj (_loc', psihat , Apx.LF.Root (_, h, Apx.LF.Nil)) ,
      Int.LF.PDecl (_, tA, cPsi) ->
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      let (h', sB) = Lfrecon.elHead loc Lfrecon.Pibox cD cPsi' h  in
      let theta' = Int.LF.MDot (Int.LF.PObj (psihat, h'), theta) in
      let sA' = (C.cnormTyp (tA, theta), LF.id) in
        begin try
          (Unify.unifyTyp cD cPsi' sB  sA' ;
           dprint (fun () -> "[elExp'] unification of PDecl with inferred type done");
           (Int.Comp.MApp (loc, i, (psihat, Int.Comp.NeutObj h')), (tau, theta')))
        with Unify.Failure msg ->
          (Printf.printf "%s\n" msg;
           raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
        end

  | Apx.Comp.MetaObjAnn (_loc', psi , Apx.LF.Root (_, h, Apx.LF.Nil)) ,
        Int.LF.PDecl (_, tA, cPsi) ->
      let cPsi  = C.cnormDCtx (cPsi, theta) in
      let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
        (begin try
           Unify.unifyDCtx cD cPsi cPsi'
         with
           | Unify.Failure "Context clash" ->
               let expected_tau = Int.Comp.TypBox (Syntax.Loc.ghost,Whnf.cnormTyp (tA, theta),
                                                   Whnf.cnormDCtx (cPsi, theta))   in
                 raise (Error (loc, CtxMismatch (cD, expected_tau, cPsi')))
         end ;

         let cPsi' = Whnf.normDCtx cPsi' in
         let psihat' = Context.dctxToHat cPsi'  in
         let _ = dprint (fun () -> "[elExp'] Mapp case :  PDecl ") in
         let (h', sB) = Lfrecon.elHead loc Lfrecon.Pibox cD cPsi' h  in
         let _ = dprint (fun () -> "\n[elExp'] PDecl instantiated with " ^ P.headToString cD cPsi' h') in
         let theta' = Int.LF.MDot (Int.LF.PObj (psihat', h'), theta)  in
         let sA' = (C.cnormTyp (tA, theta), LF.id) in
         let i_norm = Whnf.cnormExp' (i, Whnf.m_id) in
           (if Unify.isVar h' then
              begin
                try
                  (Unify.unifyTyp cD cPsi' sB  sA' ;
                   dprint (fun () -> "[elExp'] unification of PDecl with inferred type done");
                   (Int.Comp.MApp (loc, i_norm, (psihat', Int.Comp.NeutObj h')), (tau, theta')))
                with Unify.Failure msg ->
                  (Printf.printf "%s\n" msg;
                   raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
              end
            else
              raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
        )


  |  Apx.Comp.MetaSub (loc', psihat, s) , Int.LF.SDecl (_, cPhi, cPsi) ->
       begin try
         let cPsi' = C.cnormDCtx (cPsi, theta) in
         let s'    = Lfrecon.elSub loc' Lfrecon.Pibox cD cPsi' s (C.cnormDCtx (cPhi, theta)) in
         let theta' = Int.LF.MDot (Int.LF.SObj (psihat, s'), theta) in
           (Int.Comp.MApp (loc, i, (psihat, Int.Comp.SubstObj s')), (tau, theta'))
       with Error.Violation msg ->
         dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
                 raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaSubTyp (cPhi,cPsi), theta))))
       end
  |  Apx.Comp.MetaSubAnn (loc', psi, s) , Int.LF.SDecl (_, cPhi, cPsi) ->
      let cPsi  = C.cnormDCtx (cPsi, theta) in
      let cPhi' = C.cnormDCtx (cPhi, theta) in
      let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
        (begin try
           Unify.unifyDCtx cD cPsi cPsi'
         with
           | Unify.Failure "Context clash" ->
                 raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaSubTyp (cPhi,cPsi), theta))))
         end ;
       begin try
         let cPsi' = Whnf.normDCtx cPsi' in
         let psihat' = Context.dctxToHat cPsi'  in
         let cPhi' = Whnf.normDCtx cPhi' in
         let s'    = Lfrecon.elSub loc' Lfrecon.Pibox cD cPsi' s cPhi' in
         let theta' = Int.LF.MDot (Int.LF.SObj (psihat', s'), theta) in
           (Int.Comp.MApp (loc, i, (psihat', Int.Comp.SubstObj s')), (tau, theta'))
       with Error.Violation msg ->
         dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
         raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaSubTyp (cPhi,cPsi), theta))))
       end)
  | Apx.Comp.MetaCtx (loc, cPsi) , Int.LF.CDecl(_psi, sW, _dep) ->
      let cPsi'  = Lfrecon.elDCtx Lfrecon.Pibox cD cPsi in
        let theta' = Int.LF.MDot (Int.LF.CObj (cPsi'), theta) in
        (Int.Comp.CtxApp (loc, i, cPsi'), (tau, theta'))
  | _ , Int.LF.CDecl(_psi, sW, _dep) ->
      raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaSchema sW, theta))))
  | _ , Int.LF.PDecl (_, tA, cPsi) ->
      raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaTyp (tA, cPsi), theta))))
  | _ , Int.LF.MDecl (_, tA, cPsi) ->
      raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaTyp (tA, cPsi), theta))))
  | _ , Int.LF.SDecl (_, tA, cPsi) ->
      raise (Check.Comp.Error (loc, Check.Comp.MAppMismatch (cD, (Int.Comp.MetaSubTyp (tA, cPsi), theta))))


let rec elExp cD cG e theta_tau = elExpW cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Fun (loc, x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
      (* let cG' = Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo (tau1, theta))) in *)
      let cG' = Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Whnf.cnormCTyp (tau1, theta))) in
      let e' = elExp cD cG' e (tau2, theta) in
      let e'' =  Whnf.cnormExp (Int.Comp.Fun (loc, x, e'), Whnf.m_id) in
      let _ = dprint (fun () -> "[elExp] Fun " ^ R.render_name x ^ " done ") in
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
  | (Apx.Comp.MLam (loc, u, e) , (Int.Comp.TypPiBox((cdec, Int.Comp.Explicit), tau), theta))  ->
      let cD' = extend_mctx cD (u, (cdec, Int.Comp.Explicit), theta) in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (loc, u, e')

  | (e, (Int.Comp.TypPiBox((cdec, Int.Comp.Implicit), tau), theta))  ->
      let u = mk_name_cdec cdec in
      let cG' = Whnf.cnormCtx (cG, Int.LF.MShift 1) in
      let cD' = extend_mctx cD (u, (cdec, Int.Comp.Implicit), theta) in
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

  | (Apx.Comp.Box (loc, psihat, tM), ((Int.Comp.TypBox (_loc, tA, cPsi), theta) as tau_theta)) ->
   (* if psihat = Context.dctxToHat cPsi then *)
      let _ = dprint (fun () -> "[elExp] BOX\n") in
      let cPsi' = C.cnormDCtx (cPsi, theta) in
      if Lfrecon.unify_phat cD psihat (Context.dctxToHat cPsi') then
        let tM' = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (C.cnormTyp (tA, theta), LF.id) in
        let _   = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
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
          Int.Comp.SBox (loc, psihat, sigma')
      else
        (* raise (Error (loc, Check.Comp.BoxCtxMismatch (cD, cPsi, (psihat, tM')))) *)
        (let (_ , k) = psihat in
           dprint (fun () -> "cPsi = " ^ P.dctxToString cD (C.cnormDCtx (cPsi, theta))  ^ "\n psihat  = " ^ string_of_int k ^ "\n") ;
           raise (Check.Comp.Error (loc, Check.Comp.SBoxMismatch (cD, cG, (C.cnormDCtx (cPhi, theta)), (C.cnormDCtx (cPsi, theta)))) ))


  | (Apx.Comp.Case (loc, prag, i, branches), ((tau, theta) as tau_theta)) ->
      let _ = dprint (fun () -> "[elExp] case ") in
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp] case on " ^ P.expSynToString cD cG (Whnf.cnormExp' (i', Whnf.m_id))) in
      begin match (i', C.cwhnfCTyp tau_theta') with
        | (Int.Comp.Ann (Int.Comp.Box (_ , phat,tR), _ ) as i,
           (Int.Comp.TypBox (_, tP, cPsi) as tau_s, t (* m_id *))) ->
          let _ = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          if Whnf.closed (tR, LF.id) then
            let recBranch b =
              let _ = dprint (fun () -> "[elBranch - IndexObj] in context cPsi = "
                ^ P.dctxToString cD cPsi ^ "\n") in
              let b = elBranch (IndexObj(phat, tR)) cD cG b (i, tau_s) tau_theta in
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

(*        | (i, ((Int.Comp.TypBool | Int.Comp.TypCross (_, _) | Int.Comp.TypBase  (_, _, _)) as tau_s, _mid)) -> *)
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

(*        | (i, (tau_s, t)) ->
          raise (Error (loc, (IllegalCase (cD, cG, i, (tau_s, t)))))*)
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
  | (Apx.Comp.MLam (loc, _u, _e), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.MLamMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.Pair(loc, _ , _ ), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.PairMismatch (cD, cG, tau_theta)))
  | (Apx.Comp.Box (loc, _, _ ) , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BoxMismatch (cD, cG, tau_theta)))

and elExp' cD cG i = match i with
  | Apx.Comp.Var offset ->
      let tau = lookup cG offset in
      let _ = dprint (fun () -> "[elExp'] Variable " ^ R.render_var cG offset
                        ^ " has type " ^
                        P.compTypToString cD tau) in
      (Int.Comp.Var offset, (tau, C.m_id))

  | Apx.Comp.DataConst c ->
      let _ = dprint (fun () -> "[elExp'] DataConst " ^ R.render_cid_comp_const  c ^
                        "\n has type " ^ P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD ((CompConst.get c).CompConst.typ)) in
     (Int.Comp.DataConst c, ((CompConst.get c).CompConst.typ, C.m_id))

  | Apx.Comp.DataDest c ->
      let _ = dprint (fun () -> "[elExp'] DataDest " ^ R.render_cid_comp_dest  c ^
                        "\n has type " ^ P.mctxToString cD ^ " |- " ^
                        P.compTypToString cD ((CompDest.get c).CompDest.typ)) in
     (Int.Comp.DataDest c, ((CompDest.get c).CompDest.typ, C.m_id))

  | Apx.Comp.Const prog ->
     (Int.Comp.Const prog, ((Comp.get prog).Comp.typ, C.m_id))

  | Apx.Comp.Apply (loc, i, e) ->
      let _ = dprint (fun () -> "[elExp'] Apply") in
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] Apply - generated implicit arguments") in
        begin match tau_theta' with
          | (Int.Comp.TypArr (tau2, tau), theta) ->
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

          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantArrow, tau_theta')))
                (* TODO postpone to reconstruction *)
        end

(*  | Apx.Comp.CtxApp (loc, i, cPsi) ->
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
        begin match tau_theta' with
          | ((Int.Comp.TypPiBox ((Int.LF.CDecl(_psi, _sW, _), _explicit ), tau), theta) as tt)->
              let cPsi'  = Lfrecon.elDCtx Lfrecon.Pibox cD cPsi in
              let theta' = Int.LF.MDot (Int.LF.CObj (cPsi'), theta) in
              let _ = (dprint (fun () -> "[elExp'] CtxApp : tau = " ^
                                 P.compTypToString cD (Whnf.cnormCTyp tt) );
                       dprint (fun () -> "[elExp'] cPsi' = " ^ P.dctxToString cD cPsi' )) in
              let _ = dprint (fun () -> "[elExp'] CtxApp : [cPsi/psi]tau' = " ^
                                 P.compTypToString cD (Whnf.cnormCTyp   (tau,theta')) ) in
                (Int.Comp.CtxApp (loc, i', cPsi'), (tau, theta'))



          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantCtxPi, tau_theta')))
                (* TODO postpone to reconstruction *)
        end
*)
  | Apx.Comp.MApp (loc, i, mC) ->
      let _ = dprint (fun () -> "Elaborating MApp.\n") in
      let (i0, tau_t) = (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] MApp : " ^
                        P.expSynToString cD cG (Whnf.cnormExp' (i0, Whnf.m_id)) ^ " : " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t) ) in
      let (i', tau_theta') = genMApp loc cD (i0, tau_t) in
        begin match tau_theta' with
          | (Int.Comp.TypPiBox ((cdec, Int.Comp.Explicit), tau), theta) ->
              elApply cD (loc, i', mC) (cdec, tau) theta true

          | (Int.Comp.TypArr (tau1, tau), theta) -> begin match tau1 with
              | Int.Comp.TypBox(_, tP, cPsi) ->
                  elApply cD (loc, i', mC) (Int.LF.MDecl (Id.mk_name (Id.MVarName None), tP, cPsi), tau) theta false
                | _ ->
                    raise (Check.Comp.Error (loc, Check.Comp.BoxMismatch (cD, cG, (tau1, theta))))
            end
          | _ ->
              raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantPiBox, tau_theta')))
        end


  (*| Apx.Comp.MAnnApp (loc, i, (psi, m)) ->
      let _ = dprint (fun () -> "Reconstructing MAnnApp\n") in
      let (i0, tau_t) = (elExp' cD cG i) in
      let _ = (dprint (fun () -> ("[elExp'] MAnnApp : " ^
                                     P.mctxToString cD ^ "\n |- " ^
                                     P.expSynToString cD cG (Whnf.cnormExp' (i0, Whnf.m_id)))) ;
              dprint (fun () -> "             : " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t) )) in

      let (i', tau_theta') = genMApp loc cD  (i0, tau_t) in
      let _ = dprint (fun () -> "[elExp'] MAnnApp - generated implicit args.\n") in
      let _ = dprint (fun () -> "[elExp] MAnnApp  : " ^
                                P.mctxToString cD ^ "\n |- " ^
                                P.compTypToString cD (Whnf.cnormCTyp  tau_theta')) in
              dprint (fun () -> "[elExp] MAnnApp Reconstructed (partially) AFTER GENERATING IMPLICIT ARGS:\n      " ^
                P.expSynToString cD cG (Whnf.cnormExp' (i', Whnf.m_id)) ^ "\n");
      begin match tau_theta' with
        | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau0), theta) ->
          let cPsi    = C.cnormDCtx (cPsi, theta) in
          begin
            try
              let _ = dprint (fun () -> "... PiBox MDecl case ...") in
              let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
              let _ = dprint (fun () -> "[elDCtx] done... ]") in
              let _     = begin try
                           Unify.unifyDCtx cD cPsi cPsi'
                          with
                            | Unify.Failure "Context clash" ->
                                let expected_tau = Int.Comp.TypBox (Syntax.Loc.ghost,Whnf.cnormTyp (tA, theta),
                                                                Whnf.cnormDCtx (cPsi, theta))   in
                                  raise (Error (loc, CtxMismatch (cD, expected_tau, cPsi')))
                          end
              in
              let _ = dprint (fun () -> "[unifyDCtx] done... ]") in
              let cPsi' = Whnf.normDCtx cPsi' in
              let psihat' = Context.dctxToHat cPsi'  in
              let i_norm = Whnf.cnormExp' (i', Whnf.m_id) in
              let tM'    = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m (C.cnormTyp (tA, theta), LF.id) in
              let _ = dprint (fun () -> "[elTerm] done... ]") in
              let theta' = Int.LF.MDot (Int.LF.MObj (psihat', tM'), theta) in
              let i'' = Int.Comp.MApp (loc, i_norm, (psihat', Int.Comp.NormObj tM'))  in
              let tau'' = Whnf.cnormCTyp (tau0, theta') in
                (dprint (fun () -> "[elExp] MAnnApp Reconstructed EXPLICIT ARG:\n      " ^
                           P.expSynToString cD cG (Whnf.cnormExp' (i'',  Whnf.m_id)) ^ "\n");
                 dprint (fun () -> "[elExp] MAnnApp tau " ^ P.compTypToString cD (Whnf.cnormCTyp  tau_theta'));
                 dprint (fun () -> "[elExp] MAnnApp theta' = " ^ P.msubToString cD theta');
                 dprint (fun () -> "[elExp] MAnnApp of type tau'' :\n      " ^ P.compTypToString cD tau'');
                   (i'', (tau'', Whnf.m_id)))
            with Error.Violation msg ->
              dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
              raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn ))
          end
        | (Int.Comp.TypPiBox ((Int.LF.PDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
          let cPsi    = C.cnormDCtx (cPsi, theta) in
          begin
            try
              let _ = dprint (fun () -> "... PiBox PDecl case ...") in
              let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
              let _ = dprint (fun () -> "[elDCtx] done... ]") in
              let _     = Unify.unifyDCtx cD cPsi cPsi' in
              let cPsi' = Whnf.normDCtx cPsi' in
              let psihat' = Context.dctxToHat cPsi'  in
              begin match m with
                | Apx.LF.Root (_, h, Apx.LF.Nil) ->
                  let _ = dprint (fun () -> "[elExp'] Mapp case :  PDecl ") in
                  let (h', sB) = Lfrecon.elHead loc Lfrecon.Pibox cD cPsi' h  in
                  let _ = dprint (fun () -> "\n[elExp'] PDecl instantiated with " ^ P.headToString cD cPsi' h') in
                    let theta' = Int.LF.MDot (Int.LF.PObj (psihat', h'), theta)  in
                    let sA' = (C.cnormTyp (tA, theta), LF.id) in
                    let i_norm = Whnf.cnormExp' (i', Whnf.m_id) in
                    (if Unify.isVar h' then
                        begin
                          try
                            (Unify.unifyTyp cD cPsi' sB  sA' ;
                             dprint (fun () -> "[elExp'] unification of PDecl with inferred type done");
                             (Int.Comp.MApp (loc, i_norm, (psihat', Int.Comp.NeutObj h')), (tau, theta')))
                          with Unify.Failure msg ->
                            (Printf.printf "%s\n" msg;
                             raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
                        end
                     else
                        raise (Lfrecon.Error (loc, Lfrecon.TypMismatchElab (cD, cPsi', sA', sB))))
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
              let _ = dprint (fun () -> "AFTER unifyDCtx cPsi' = " ^ P.dctxToString cD  cPsi') in
              let _ = dprint (fun () -> "                 cPsi = " ^ P.dctxToString cD  cPsi) in
              let _ = dprint (fun () -> "Infer omitted context argument using  unification") in
              let i_norm = Whnf.cnormExp' (i', Whnf.m_id) in
              dprint (fun () -> "[elExp] MAnnApp Reconstructed (partially): " ^
                P.expSynToString cD cG i_norm ^ "\n");
              let cPsi' = Whnf.normDCtx cPsi' in

              let _   = dprint (fun () -> "[elTerm] for m against type (BEFORE): " ^
                P.dctxToString cD cPsi' ^ " \n  |- \n  " ^
                P.typToString cD cPsi' (C.cnormTyp (tP, theta), LF.id)) in
              let tM' = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' m (C.cnormTyp (tP, theta), LF.id) in
              let _   = dprint (fun () -> "[elTerm] for m against type (AFTER): " ^
                P.dctxToString cD cPsi' ^ " \n  |- \n " ^
                P.typToString cD cPsi' (C.cnormTyp (tP, theta), LF.id)) in
              let psihat' = Context.dctxToHat (Whnf.normDCtx cPsi')  in
              let i = Int.Comp.Apply (loc, i_norm,
                                      Int.Comp.Box(loc, psihat', tM')) in
              dprint (fun () -> "[elExp] MAnnApp Reconstructed: " ^
                P.expSynToString cD cG (Whnf.cnormExp' (i_norm, Whnf.m_id)) ^ "\n"); (i , (tau, theta))

            with Unify.Failure msg ->
              raise (Check.Comp.Error (loc, Check.Comp.AppMismatch (cD, (Int.Comp.MetaTyp (tP, cPsi), theta))))
          end
        | _ ->
          raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantPiBox, tau_theta')))
          (* TODO postpone to reconstruction *)
      end
   | Apx.Comp.MAnnSApp (loc, i, (psi, m)) ->
      let _ = dprint (fun () -> "Reconstructing MAnnSApp\n") in
      let (i0, tau_t) = (elExp' cD cG i) in
      let _ = (dprint (fun () -> "[elExp'] MApp : " ^
                        P.expSynToString cD cG (Whnf.cnormExp' (i0, Whnf.m_id))) ;
              dprint (fun () -> "             : " ^
                        P.compTypToString cD (Whnf.cnormCTyp tau_t) )) in

      let (i', tau_theta') = genMApp loc cD  (i0, tau_t) in
      let _ = dprint (fun () -> "[elExp'] MAnnSApp - generated implicit args.\n") in
      let _ = dprint (fun () -> "[elExp] MAnnSApp  : " ^
                                P.mctxToString cD ^ "\n |- " ^
                                P.compTypToString cD (Whnf.cnormCTyp  tau_theta')) in
              dprint (fun () -> "[elExp] MAnnSApp Reconstructed (partially) AFTER GENERATING IMPLICIT ARGS:\n      " ^
                P.expSynToString cD cG (Whnf.cnormExp' (i', Whnf.m_id)) ^ "\n");
      begin match tau_theta' with
        | (Int.Comp.TypPiBox ((Int.LF.SDecl (_, tA, cPsi), Int.Comp.Explicit), tau0), theta) ->
          let cPsi    = C.cnormDCtx (cPsi, theta) in
          begin
            try
              let _ = dprint (fun () -> "... PiBox SDecl case ...") in
              let cPsi' = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
              let _ = dprint (fun () -> "[elDCtx] done... ]") in
              let _     = begin try
                           Unify.unifyDCtx cD cPsi cPsi'
                          with
                            | Unify.Failure "Context clash" ->
                                let expected_tau = Int.Comp.TypSub (Syntax.Loc.ghost,Whnf.cnormDCtx (tA, theta),
                                                                Whnf.cnormDCtx (cPsi, theta))   in
                                  raise (Error (loc, CtxMismatch (cD, expected_tau, cPsi')))
                          end
              in
              let _ = dprint (fun () -> "[unifyDCtx] done... ]") in
              let cPsi' = Whnf.normDCtx cPsi' in
              let psihat' = Context.dctxToHat cPsi'  in
              let i_norm = Whnf.cnormExp' (i', Whnf.m_id) in
              let tM'    = Lfrecon.elSub loc Lfrecon.Pibox cD cPsi' m (C.cnormDCtx (tA, theta)) in
              let _ = dprint (fun () -> "[elTerm] done... ]") in
              let theta' = Int.LF.MDot (Int.LF.SObj (psihat', tM'), theta) in
              let i'' = Int.Comp.MApp (loc, i_norm, (psihat', Int.Comp.SubstObj tM'))  in
              let tau'' = Whnf.cnormCTyp (tau0, theta') in
                (dprint (fun () -> "[elExp] MAnnApp Reconstructed EXPLICIT ARG:\n      " ^
                           P.expSynToString cD cG (Whnf.cnormExp' (i'', Whnf.m_id)) ^ "\n");
                   (i'', (tau'', Whnf.m_id)))
            with Error.Violation msg ->
              dprint (fun () -> "[elTerm] Error.Violation: " ^ msg);
              raise (Lfrecon.Error (loc, Lfrecon.CompTypAnn ))
          end
        | _ ->
          raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantPiBox, tau_theta')))
          (* TODO postpone to reconstruction *)
        end
  *)

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
                    let _ = dprint (fun () -> "[mgAtomicTyp] Generate mg type in context " ^
                                      P.dctxToString cD' cPsi' ) in
                      mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind
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
    Abstract.pattern cD' cPsi' (phat, tR) tP' in
    begin try
      let _   = dprint (fun () -> "recMObj: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.mctxToString cD1' ^ "  ;   " ^ P.dctxToString cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.normalToString cD1' cPsi1' (tR1', LF.id) ^ "\n has type \n " ^
                          P.typToString cD1' cPsi1'  (tP1', LF.id)) in
      let l_cd1'    = Context.length cD1'  in
      let l_delta   = Context.length cD'  in
      Check.Comp.wf_mctx cD1' ;
        ((l_cd1', l_delta), cD1', cPsi1', Some tR1', tP1')
      with
        | Check.Comp.Error (_ , msg) -> raise (Check.Comp.Error (loc, msg))
        |  _ -> raise (Error (loc,MCtxIllformed cD1'))
    end

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

and elPatMetaObj cD pat (cdecl, theta) = begin match pat with
  | Apx.Comp.PatMetaObj (loc, cM) ->
    (match cdecl with
       | Int.LF.MDecl (_, tA, cPsi) ->
           (match  elMetaObj cD cM (Int.Comp.MetaTyp (tA, cPsi), theta)  with
              | (Int.Comp.MetaObj (loc, phat, tM) as cM') ->
                  (Int.Comp.PatMetaObj (loc, cM'),
                   Int.LF.MDot (Int.LF.MObj (phat, tM), theta))
           )
       | Int.LF.SDecl (_, cPhi, cPsi) ->
           (match  elMetaObj cD cM (Int.Comp.MetaSubTyp (cPhi, cPsi), theta)  with
              | (Int.Comp.MetaSObj (loc, phat, s) as sigma') ->
                  (Int.Comp.PatMetaObj (loc, sigma'),
                   Int.LF.MDot (Int.LF.SObj (phat, s), theta))
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

  | Apx.Comp.PatEmpty (loc, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatConst (loc, _, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatFVar (loc, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatVar (loc, _ , _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatPair (loc, _ , _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatTrue loc -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatFalse loc -> raise (Error (loc, PatternMobj))
(*  | Apx.Comp.PatAnn (loc, (Apx.Comp.PatMetaObj (_, _ ) as pat), tau) ->
      (let tau' = elCompTyp cD tau in
      let (_cG', pat') = elPatChk cD (Int.LF.Empty) pat (tau', Whnf.m_id) in
        begin match pat' , cdecl with
          |  (Int.Comp.MetaObj (loc, phat, tM) as cM') , Int.LF.MDecl (_, tA, cPsi) ->
               let ttau = (Int.Comp.TypBox (Syntax.Loc.ghost, tA, cPsi), theta) in
               let ttau' = (tau', Whnf.m_id) in
                 begin try
                   Unify.unifyCompTyp cD ttau ttau' ;
                   (Int.Comp.PatMetaObj (loc, cM'),
                    Int.LF.MDot (Int.LF.MObj (phat, tM), theta))
                 with Unify.Failure msg ->
                   dprint (fun () -> "Unify Error: " ^ msg) ;
                   raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, ttau, ttau')))
                 end
          | _ -> raise (Error (loc, PattAnn))
          (* Other type annotations on MetaCtx or MetaParam not supported *)
        end)
*)
(*
      (let tau'   =  elCompTyp cD tau in
       let cdecl' = (match tau' with
         | Int.Comp.TypBox (_, tA', cPsi') ->
             Int.LF.MDecl (Id.mk_name (Id.MVar_name None) , tA', cPsi')
         | Int.Comp.TypParam (_, tA', cPsi') ->
             Int.LF.PDecl (Id.mk_name (Id.PVar_name None) , tA', cPsi')) in

      let (pat', _) = elPatMetaObj cD pat (cdecl', Whnf.m_id) in
        begin try
          (match cdecl , cdecl' with
             | Int.LF.MDecl (_, tA, cPsi) , Int.LF.MDecl (_, tA', cPsi') ->
                 let cPsi0 = Whnf.cnormDCtx (cPsi, theta) in
                 let tA0   = Whnf.cnormTyp (tA, theta) in
                   (Unify.unifyDCtx cD cPsi0 cPsi';
                    Unify.unifyTyp cD cPsi0 (tA0, LF.id) (tA', LF.id);
                    (pat,
             | Int.LF.PDecl (_, tA, cPsi) , Int.LF.PDecl (_, tA', cPsi') ->
                 let cPsi0 = Whnf.cnormDCtx (cPsi, theta) in
                 let tA0   = Whnf.cnormTyp (tA, theta) in
                   (Unify.unifyDCtx cD cPsi0 cPsi';
                    Unify.unifyTyp cD cPsi0 (tA0, LF.id) (tA', LF.id))
          );
          match pat'  with
          |  (Int.Comp.MetaObj (loc, phat, tM) as cM') ,  ->
               (Int.Comp.PatMetaObj (loc, cM'),
                Int.LF.MDot (Int.LF.MObj (phat, tM), theta))
          |  (Int.Comp.MetaParam (loc, phat, h) as cM') , Int.LF.PDecl (_, tA, cPsi) ->
               let ttau = (Int.Comp.TypParam (Syntax.Loc.ghost, tA, cPsi), theta) in
               let ttau' = (tau', Whnf.m_id) in
                 begin try
                   Unify.unifyCompTyp cD ttau ttau' ;
                   (Int.Comp.PatMetaObj (loc, cM'),
                    Int.LF.MDot (Int.LF.MObj (phat, tM), theta))
                 with Unify.Failure msg ->
                   dprint (fun () -> "Unify Error: " ^ msg) ;
                   raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, ttau, ttau')))
                 end
        with Unify.Failure msg ->
         let tau0 = (match cdecl of
         |  Int.LF.MDecl (_, tA, cPsi)  ->Int.Comp.TypBox   (Syntax.Loc.ghost, tA, cPsi)
         |  Int.LF.PDecl (_, tA, cPsi)  -> Int.Comp.TypParam (Syntax.Loc.ghost, tA, cPsi)
                    ) in
         dprint (fun () -> "Unify Error: " ^ msg) ;
         raise (Check.Comp.Error (loc,
                                  Check.Comp.SynMismatch (cD, (tau', Whnf.m_id), (tau0, Whnf.m_id))))
         | _ -> raise (Error (loc, PatternMobj))
          (* Other type annotations on MetaCtx not supported *)
        end)
*)
  | Apx.Comp.PatAnn (loc, _, _) -> raise (Error (loc, PatAnn))

end

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
      let tau' = Whnf.cnormCTyp (tau, theta) in
      let _  = dprint (fun () -> "Inferred type of pat var " ^ R.render_name name )  in
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

  | (Apx.Comp.PatMetaObj (loc, cM), (Int.Comp.TypBox (_loc, tA, cPsi), theta)) ->
      (* cM = MetaObj or MetaObjAnn *)
      let cM' = elMetaObj cD cM (Int.Comp.MetaTyp (tA, cPsi), theta) in
        (cG, Int.Comp.PatMetaObj (loc, cM'))
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
         | (Int.Comp.TypPiBox ((Int.LF.MDecl (n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
             let cPsi' = C.cnormDCtx (cPsi, theta) in
             let tA'   = C.cnormTyp (tA, theta) in
             let psihat  = Context.dctxToHat cPsi' in

             let tM'   = if !strengthen then etaExpandMMVstr loc cD  cPsi' (tA', LF.id) n
                         else Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
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

           | (Int.Comp.TypPiBox ((Int.LF.SDecl(n, cPhi, cPsi), Int.Comp.Implicit), tau), theta) ->
               let cPsi' = C.cnormDCtx (cPsi, theta) in
               let psihat  = Context.dctxToHat cPsi' in
               let cPhi' = C.cnormDCtx (cPhi, theta) in
               let s     =  Whnf.newMSVar (Some n) (cD, cPsi', cPhi') in
               let sigma = Int.LF.MSVar (s, (Int.LF.NoCtxShift, 0), (Whnf.m_id, LF.id)) in
               let ttau'  = (tau, Int.LF.MDot (Int.LF.SObj (psihat, sigma), theta)) in
               let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaSObj (loc, psihat, sigma)) in
               let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
                 (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

          | (Int.Comp.TypPiBox ((Int.LF.CDecl(n, w, _ ), Int.Comp.Implicit), tau), theta) ->
               let cPsi  = Int.LF.CtxVar (Int.LF.CInst (n, ref None, w,  cD, Whnf.m_id)) in
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

         | (Int.Comp.TypPiBox ((Int.LF.MDecl (n, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
             let _ = (dprint (fun () -> "[elPatSpine] TypPiBox implicit ttau = ");
                      dprint (fun () -> "       " ^ P.compTypToString cD (Whnf.cnormCTyp ttau))) in
             let cPsi' = Whnf.normDCtx (C.cnormDCtx (cPsi, theta)) in
             let _ = dprint (fun () -> "cnormDCtx done .... cPsi' = " ^
                               P.dctxToString cD cPsi') in
             let tA'   = Whnf.normTyp (C.cnormTyp (tA, theta), LF.id) in
             let _ = dprint (fun () -> "cnormTyp done ... tA' = " ^
                               P.typToString cD cPsi' (tA', LF.id)) in
             let psihat  = Context.dctxToHat cPsi' in
             let _ = dprint (fun () -> "call etaExpandMMV ... ") in
             (* let tM'   = Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in *)
             let tM'   = if !strengthen then etaExpandMMVstr loc cD  cPsi' (tA', LF.id) n
                         else Whnf.etaExpandMMV loc cD  cPsi' (tA', LF.id) n LF.id in
             let _ = dprint (fun () -> "...generated MMVar " ^ P.normalToString cD cPsi' (tM', LF.id)) in
             let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaObj (loc, psihat, tM')) in
             let ttau' = (tau, Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta))
             in
             let _ = (dprint (fun() -> "[elPatSpine] elaborate spine against " );
                      dprint (fun () -> "theta = " ^ P.msubToString cD (Int.LF.MDot (Int.LF.MObj (psihat, tM'), theta)));
                      dprint (fun () -> "ttau'   " ^ P.compTypToString cD (Whnf.cnormCTyp ttau'))) in
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
             let _ = (dprint (fun () -> "theta = " ^ P.msubToString cD (Int.LF.MDot (Int.LF.PObj (psihat, p), theta)));
                      dprint (fun () -> "ttau'   " ^ P.compTypToString cD (Whnf.cnormCTyp ttau'))) in
             let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
               (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

           | (Int.Comp.TypPiBox ((Int.LF.SDecl(n, cPhi, cPsi), Int.Comp.Implicit), tau), theta) ->
               let cPsi' = C.cnormDCtx (cPsi, theta) in
               let psihat  = Context.dctxToHat cPsi' in
               let cPhi' = C.cnormDCtx (cPhi, theta) in
               let s     =  Whnf.newMSVar (Some n) (cD, cPsi', cPhi') in
               let sigma = Int.LF.MSVar (s, (Int.LF.NoCtxShift, 0), (Whnf.m_id, LF.id)) in
               let ttau'  = (tau, Int.LF.MDot (Int.LF.SObj (psihat, sigma), theta)) in
               let pat'  = Int.Comp.PatMetaObj (loc, Int.Comp.MetaSObj (loc, psihat, sigma)) in
               let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
                 (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

          | (Int.Comp.TypPiBox ((Int.LF.CDecl(n, w, _ ), Int.Comp.Implicit), tau), theta) ->
             let _ = dprint (fun () -> "[elPatSpine] TypPiBox CDecl implicit ttau = " ^
                               P.compTypToString cD (Whnf.cnormCTyp ttau)) in
               let cPsi  = Int.LF.CtxVar (Int.LF.CInst (n, ref None, w, cD, Whnf.m_id)) in
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
        begin try
          let Int.Comp.TypBox (_ , _tQ, cPsi_s) = tau_s  in
          let _       = inferCtxSchema loc (cD_s, cPsi_s) (cD, cPsi) in
            (* as a side effect we will update FCVAR with the schema for the
               context variable occurring in cPsi' *)
          let ttau' = (Int.Comp.TypBox(loc',tP, cPsi), Whnf.m_id) in
          let (cG', pat') = elPatChk cD Int.LF.Empty pat'  ttau' in
            (cG', pat', ttau')
        with
            _ -> raise (Error (loc, PatternMobj))
        end

  | Apx.Comp.PatEmpty (loc, cpsi) ->
      let cPsi = Lfrecon.elDCtx (Lfrecon.Pibox) cD cpsi in
      begin match tau_s with
       | Int.Comp.TypBox (_ , (Int.LF.Atom(_, a, _) as _tQ), cPsi_s) ->
         let _       = inferCtxSchema loc (cD_s, cPsi_s) (cD, cPsi) in
         let tP     =  mgAtomicTyp cD cPsi a (Typ.get a).Typ.kind in
         let _ = dprint (fun () -> "[recPattern] Reconstruction of pattern of empty type  " ^
                        P.typToString cD cPsi (tP, LF.id)) in
         let ttau' = (Int.Comp.TypBox (loc, tP, cPsi), Whnf.m_id) in
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

(* ********************************************************************************)
(* recPattern will become obsolete when we switch to the new syntax *)
(*  and recPattern (cD, cPsi) delta psi m tPopt =
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
                      let _ = dprint (fun () -> "[mgAtomicTyp] Generate mg type in context " ^
                                        P.dctxToString cD' cPsi' ) in
                      mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind
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

  let (cD1', cPsi1', (_phat, tR1'), tP1') =  Abstract.pattern cD' cPsi' (phat, tR) tP' in

  let _       = dprint (fun () -> "recPattern: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                          P.mctxToString cD1' ^ "  ;   " ^ P.dctxToString cD1' cPsi1' ^ "\n   |-\n    "  ^
                          P.normalToString cD1' cPsi1' (tR1', LF.id) ^ "\n has type \n " ^
                          P.typToString cD1' cPsi1'  (tP1', LF.id)) in
  let n       = Context.length cD1' in
  let k       = Context.length cD'  in
    ((n,k), cD1', cPsi1', Some tR1', tP1')

*)
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
                      let _ = dprint (fun () -> "[mgAtomicTyp] Generate mg type in context " ^
                                        P.dctxToString cD' cPsi' ) in
                      mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind
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
  let _ = dprint (fun () -> "\n Expected Pattern type : " ^ P.dctxToString cD' cPsi ^ " . " ^
    P.typToString cD' cPsi (tP, Substitution.LF.id) ^ "\n") in
  let _ = dprint (fun () -> "\n Inferred Pattern type : " ^ P.dctxToString cD1 cPsi1 ^ " . " ^
    P.typToString cD' cPsi1 (tP1, Substitution.LF.id) ^ "\n") in

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
                      raise (Error (loc, PatIndexMatch (cD, Whnf.normDCtx cPsi',
                                                        C.cnorm (tR',  t)))))
(*                      raise (Error.Violation "Pattern matching on index
                        argument failed")*)
                   end
               | (DataObj, _) -> ()
             end
    in
    let _ = dprnt "AbstractMSub..." in
      (* cD1' |- t' <= cD' *)
    let (t', cD1') = Abstract.msub (Whnf.cnormMSub t) in

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
          | Int.Comp.TypBox (_, (Int.LF.Atom(_, a, _) as tP) , cPsi) ->
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

          let _ = dprint (fun () -> "\nChecking refinement substitution") in
          let _        = dprint (fun () -> "    " ^  P.mctxToString cD1'' ^
                                   "\n |- \n " ^ P.msubToString cD1'' t' ^
                                   " \n<= " ^ P.mctxToString cD ^ "\n") in
          let _     = Check.LF.checkMSub loc cD1'' t' cD in
          let _ = dprint (fun () -> "\nChecking refinement substitution :      DONE\n") in

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
            let _ = (dprint (fun () -> "Target type tau' = " ^ P.compTypToString cD (Whnf.cnormCTyp (tau, theta))) ;
                     dprint (fun () -> "t'   = " ^ P.msubToString cD1'' t' )) in

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
            let _        = dprint (fun () -> "[elBranch] Body : \n") in
            let _ = dprint (fun () -> "        " ^ P.expChkToString cD1'' cG' eE') in
            let b = Int.Comp.Branch (loc, cD1'', Int.LF.Empty,
                                     Int.Comp.PatMetaObj (loc', pat), t', eE')
            in
              b
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
                  | IndexObj (phat, tR') ->
                      IndexObj (phat, Whnf.cnorm (tR', Int.LF.MShift l_cd1'))
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
    | Int.Comp.PiKind (_, (cdecl, dep), cK) -> unroll (Int.LF.Dec(cD, cdecl)) cK
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
