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

let strengthen : bool ref =  Lfrecon.strengthen

let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

type error =
  | ValueRestriction    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | IllegalCase         of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.tclo
  | CompScrutineeTyp    of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.LF.tclo * Int.LF.dctx
  | MetaObjContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.dctx
  | PatternContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | MetaObjectClash     of Int.LF.mctx * (Int.Comp.meta_typ)
  | MissingMetaObj
  | TooManyMetaObj
  | TypeAbbrev         of Id.name
  | PatternMobj
  | PatAnn
  | MCtxIllformed of Int.LF.mctx
  | TypMismatch        of Int.LF.mctx * Int.Comp.tclo * Int.Comp.tclo
  | IllegalSubstMatch
  | ErrorMsg of string

exception Error of Syntax.Loc.t * error
let throw loc e = raise (Error (loc, e))

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | ErrorMsg str -> Format.fprintf ppf "NOT IMPLEMENTED: %s" str
        | MCtxIllformed cD ->
            Format.fprintf ppf "Unable to abstract over the free meta-variables due to dependency on the specified meta-variables. The following meta-context was reconstructed, but is ill-formed: %a"
              (P.fmt_ppr_lf_mctx P.l0) cD
        | PatAnn     ->
            Format.fprintf ppf
              "Type annotations on context variables and parameter variables not supported at this point."
        | PatternMobj ->
            Format.fprintf ppf
              "Expected a meta-object; Found a computation-level pattern"
        | TypeAbbrev a ->
          Format.fprintf ppf
            "Type definition %s cannot contain any free meta-variables in its type."
            (Id.render_name a)
        | ValueRestriction (cD, cG, i, theta_tau) ->
          Format.fprintf ppf
            "@[<v 2>value restriction [pattern matching]@,\
             expected: closed boxed type@,\
             inferred: @[%a@]@,\
             for expression:@ @[%a@]@,\
             in context:   @[%a@]@]"
            (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
            (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
            (P.fmt_ppr_cmp_gctx cD P.l0) cG

        | IllegalCase (cD, cG, i, theta_tau) ->
          Format.fprintf ppf
            "Cannot pattern-match on values of this type.@.";
          Format.fprintf ppf
            "  @[<v>Scrutinee: %a@;\
                    Type: %a@]"
            (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
            (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)

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
            (P.fmt_ppr_lf_dctx cD P.l0) cPsi
            (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sP)
            (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
            (P.fmt_ppr_lf_mctx P.l0) (Whnf.normMCtx cD)
            (P.fmt_ppr_cmp_gctx cD P.l0) (Whnf.cnormCtx (cG, Whnf.m_id))


        | MetaObjContextClash (cD, cPsi, cPhi) ->
          Error.report_mismatch ppf
            "Context of meta-object does not match expected context."
            "Expected context"    (P.fmt_ppr_lf_dctx cD P.l0) cPsi
            "Encountered context" (P.fmt_ppr_lf_dctx cD P.l0) cPhi;

        | PatternContextClash (cD, cPsi, cD', cPsi') ->
          Error.report_mismatch ppf
            "Context clash in pattern."
            "Pattern's context"   (P.fmt_ppr_lf_dctx cD P.l0)  cPsi
            "Scrutinee's context" (P.fmt_ppr_lf_dctx cD' P.l0) cPsi';
          Format.fprintf ppf
            "Note that we do not allow the context in the pattern@ \
             to be more general than the context in the scrutinee."

       | MetaObjectClash (cD, mC) ->
           Format.fprintf ppf
             "Meta-object type clash.@ \
              Expected meta-object of type: %a"
             (P.fmt_ppr_cmp_meta_typ cD P.l0) mC;

       | MissingMetaObj      ->
           Format.fprintf ppf
             "Too few meta-objects supplied to data-constructor"

       | TooManyMetaObj      ->
           Format.fprintf ppf
             "Too many meta-objects supplied to data-constructor"

       | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
           Error.report_mismatch ppf
             "Type of destructor did not match the type it was expected to have."
             "Type of destructor" (P.fmt_ppr_cmp_typ cD P.l0)
             (Whnf.cnormCTyp (tau1, theta1))
             "Expected type" (P.fmt_ppr_cmp_typ cD P.l0)
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


type case_type  = (* IndexObj of Int.LF.psi_hat * Int.LF.normal *)
  | IndexObj of Int.Comp.meta_obj
  | DataObj

let case_type i =
  match i with
  | Int.Comp.AnnBox (mC, _) -> IndexObj mC
  | _ -> DataObj

let rec elDCtxAgainstSchema loc recT cD psi s_cid = match psi with
  | Apx.LF.Null ->
     dprintf
       begin fun p ->
       p.fmt "[elDCtxAgainstSchema] Null"
       end;
     Int.LF.Null
  | Apx.LF.CtxHole ->
    Int.LF.CtxVar (Whnf.newCVar None cD (Some s_cid) Int.LF.Maybe)

  | Apx.LF.CtxVar ((Apx.LF.CtxOffset _ ) as c_var) ->
      let schema = Schema.get_schema s_cid in
      let c_var = Lfrecon.elCtxVar c_var in
      let cPsi' = Int.LF.CtxVar (c_var) in
      begin
        try
          Check.LF.checkSchema loc cD cPsi' schema;
          cPsi'
        with
          _ -> raise (Check.LF.Error (loc, Check.LF.CtxVarMismatch (cD, c_var, schema)))
      end

  | Apx.LF.CtxVar (Apx.LF.CtxName psi ) ->
      (* This case should only be executed when c_var occurs in a pattern *)
     begin
       try
         let (_ , Int.LF.Decl (_, Int.LF.CTyp (Some s_cid'), _)) = FCVar.get psi in
         if s_cid = s_cid'
         then Int.LF.CtxVar (Int.LF.CtxName psi)
         else
           let schema = Schema.get_schema s_cid in
           let c_var' = Int.LF.CtxName psi in
           raise (Check.LF.Error (Syntax.Loc.ghost, Check.LF.CtxVarMismatch (cD, c_var', schema)))
       with Not_found ->
         FCVar.add psi (cD, Int.LF.Decl (psi, Int.LF.CTyp (Some s_cid), Int.LF.Maybe));
         Int.LF.CtxVar (Int.LF.CtxName psi)
     end

  | Apx.LF.DDec (psi', decl) ->
     match decl with
     | Apx.LF.TypDecl (x, a) ->
        let cPsi = elDCtxAgainstSchema loc recT cD psi' s_cid in
        let tA   = Lfrecon.elTyp recT cD cPsi a in
        (* let _ = Check.LF.checkTypeAgainstSchema cO cD cPsi' tA elements in          *)
        dprintf
          begin fun p ->
          p.fmt "[elDCtxAgainstSchema] %a : %a"
            Id.print x
            (P.fmt_ppr_lf_typ cD cPsi P.l0) tA
          end;
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))
     | Apx.LF.TypDeclOpt x ->
        raise (Check.LF.Error (loc, Check.LF.MissingType (Id.string_of_name x)))

(* performs reconstruction of cPsi2 while comparing it with cPsi1
   this is (apparently) necessary to get the right schema for context holes? *)
let unifyDCtxWithFCVar loc cD cPsi1 cPsi2 =
  dprintf
    (fun p ->
      p.fmt "[unifyDCtxWithFCVar] at %a" Loc.print_short loc);

  let rec loop cD cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
    | (Int.LF.Null , Apx.LF.Null) -> ()

    | (Int.LF.CtxVar (Int.LF.CInst (mmvar (*(_n, ({contents = None} as cvar_ref), _cO, Int.LF.CTyp (Some s_cid), _, dep)*), _cD)) , cPsi) ->
       let Int.LF.CTyp (Some s_cid) = Int.LF.(mmvar.typ) in
      begin
        let cPsi = elDCtxAgainstSchema loc Lfrecon.Pibox cD cPsi s_cid in
        Unify.instantiateCtxVar (Int.LF.(mmvar.instantiation), cPsi);
        match Context.ctxVar cPsi with
          | None -> ()
          | Some (Int.LF.CtxName psi) ->
            FCVar.add psi (cD, Int.LF.(Decl (psi, CTyp (Some s_cid), mmvar.depend)))
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

  in
  loop cD (Whnf.normDCtx cPsi1)  cPsi2

(* -------------------------------------------------------------*)

let rec apx_length_typ_rec t_rec = match t_rec with
  | Apx.LF.SigmaLast _ -> 1
  | Apx.LF.SigmaElem (x, _ , rest ) ->
      (print_string (Id.render_name x ^ "  ");
      1 + apx_length_typ_rec rest )

let rec lookup cG k = match cG, k with
  | Int.LF.Dec (_cG', Int.Comp.CTypDecl (_, tau, _ )), 1 -> Whnf.cnormCTyp (tau, Whnf.m_id)
  | Int.LF.Dec ( cG', Int.Comp.CTypDecl (_, _tau, _ )), k -> lookup cG' (k-1)

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
   dprintf
     begin fun p ->
     p.fmt "[elSchElem] @[<v>some context = %a@,apx nblock has length %d@]"
       (P.fmt_ppr_lf_dctx Int.LF.Empty P.l0) dctx
       (apx_length_typ_rec typRec)
     end;
   let typRec' = Lfrecon.elTypRec Lfrecon.Pi cD dctx typRec in
   let s_elem   = Int.LF.SchElem(el_ctx, typRec') in
   dprintf
     begin fun p ->
     p.fmt "[elSchElem] %a"
       (P.fmt_ppr_lf_sch_elem P.l0) s_elem
     end;
   s_elem

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

    | (Int.LF.PiKind ((Int.LF.TypDecl (_n, tA1), dep ), kK), s) ->
        let tA1' = strans_typ cD cPsi (tA1, s) conv_list in
        let tR    = if !strengthen then
                         (let (ss', cPhi') = Subord.thin' cD a flat_cPsi in
                       (* cPhi |- ss' : cPhi' *)
                     let ssi' = LF.invert ss' in
                       (* cPhi' |- ssi : cPhi *)
                       (* cPhi' |- [ssi]tQ    *)
                     let ss_proj = LF.comp ss' s_proj in
                     Whnf.etaExpandMMV Syntax.Loc.ghost cD cPhi' (tA1', ssi') _n ss_proj dep)
                   else
                     Whnf.etaExpandMMV Syntax.Loc.ghost cD flat_cPsi (tA1', Substitution.LF.id) _n s_proj dep
        in

        dprintf
          begin fun p ->
          p.fmt "Generated mg Term (meta2) @[<v>tR = %a@,of type %a |- %a@,orig type %a |- %a@]"
            (P.fmt_ppr_lf_normal cD cPsi P.l0) tR
            (P.fmt_ppr_lf_dctx cD P.l0) flat_cPsi
            (P.fmt_ppr_lf_typ cD flat_cPsi P.l0) tA1'
            (P.fmt_ppr_lf_dctx cD P.l0) cPsi
            (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tA1,s))
          end;
         let tS = genSpine (kK, Int.LF.Dot (Int.LF.Obj tR , s)) in
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
  | Int.LF.MTyp tA   -> (dprint (fun () -> "genMetaVar' [mmVarToCMetaObj]: MObj - MMV \n") ;
                         Int.LF.MObj (Int.LF.Root(loc', Int.LF.MMVar ((mV, Whnf.m_id), LF.id), Int.LF.Nil)))
  | Int.LF.PTyp tA   -> (dprint (fun () ->  "genMetaVar' [mmVarToCMetaObj]: PObj - PVar\n");
                         Int.LF.PObj (Int.LF.MPVar ((mV, Whnf.m_id), LF.id)))
  | Int.LF.STyp (_, cPhi) -> (dprint (fun () ->  "genMetaVar' [mmVarToCMetaObj]: PObj - PVar\n");
                             Int.LF.SObj (Int.LF.MSVar (0, ((mV, Whnf.m_id), LF.id))))

let mmVarToMetaObj loc' mV = function
  | Int.LF.ClTyp (mt, cPsi) ->
    Int.LF.ClObj (Context.dctxToHat cPsi, mmVarToCMetaObj loc' mV mt)
  | Int.LF.CTyp schema_cid ->
    Int.LF.CObj(Int.LF.CtxVar (Int.LF.CInst (mV, Whnf.m_id)))

let genMetaVar' loc' cD (loc, n , ctyp, t) =
  let ctyp' = C.cnormMTyp (ctyp, t) in
  dprintf
    begin fun p ->
    p.fmt "[genMetaVar'] Type : %a"
      (P.fmt_ppr_cmp_meta_typ cD P.l0) ctyp
    end;
  let mO = mmVarToMetaObj loc' (Whnf.newMMVar' (Some n) (cD, ctyp') Int.LF.Maybe) ctyp' in
  ((loc',mO), Int.LF.MDot(mO,t))

let rec genMApp loc cD (i, tau_t) = genMAppW loc cD (i, Whnf.cwhnfCTyp tau_t)

and genMAppW loc cD (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox (Int.LF.Decl(n, ctyp, Int.LF.Maybe), tau), theta) ->
    let (cM,t') = genMetaVar' loc cD (loc, n, ctyp, theta) in
    genMApp loc cD (Int.Comp.MApp (loc, i, cM), (tau, t'))
  | _ ->
     dprintf
       begin fun p ->
       p.fmt "[genMApp] done: %a |- %a"
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp tau_t)
       end;
     (i, tau_t)


(* elCompKind  cPsi k = K *)
let rec elCompKind cD k = match k with
  | Apx.Comp.Ctype loc ->
      Int.Comp.Ctype loc

  | Apx.Comp.PiKind (loc, cdecl, k') ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl   in
      let tK     = elCompKind  (Int.LF.Dec (cD, cdecl')) k' in
        Int.Comp.PiKind (loc, cdecl', tK)

let elClObj cD loc cPsi' clobj mtyp =
  match clobj, mtyp with
  (* the case for a substitution that's actually representing an ordinary term *)
  (* not sure if we should require Obj here or if Head makes sense too *)
  | Apx.LF.Dot (Apx.LF.Obj tM, Apx.LF.EmptySub)
  , Int.LF.MTyp tA ->
     dprintf
       (fun p ->
         p.fmt "[elClObj] disambiguating substitution to term at %a"
           Loc.print loc);
     let r = Int.LF.MObj (Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA, LF.id)) in
     dprint (fun () -> "̱\n[ElClObj] ELABORATION MObj DONE\n");
     r

  (* proper substitution elaboration *)
  | s
  , Int.LF.STyp (cl, cPhi') ->
     Int.LF.SObj
       (Lfrecon.elSub loc Lfrecon.Pibox cD cPsi' (Some s) cl cPhi')

  (* substitution actually representing a parameter variable hole *)
  | Apx.LF.Dot (Apx.LF.Obj (Apx.LF.Root (_, Apx.LF.Hole, Apx.LF.Nil)), Apx.LF.EmptySub)
  , Int.LF.PTyp _tA' ->
     let mV = Whnf.newMMVar' (None) (cD, Int.LF.ClTyp (mtyp, cPsi')) Int.LF.Maybe in
     mmVarToCMetaObj loc mV mtyp

  (* ordinary parameter variable elaboration *)
  | Apx.LF.Dot (Apx.LF.Obj (Apx.LF.Root (_, h, Apx.LF.Nil) as tM), Apx.LF.EmptySub)
  , Int.LF.PTyp tA' ->
     let Int.LF.Root (_, h, Int.LF.Nil) = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA', LF.id) in
     Int.LF.PObj h

  (* ordinary parameter variable elaboration *)
  | Apx.LF.Dot (Apx.LF.Head h, Apx.LF.EmptySub)
  , Int.LF.PTyp tA' ->
     let tM = Apx.LF.Root (Loc.ghost, h, Apx.LF.Nil) in
     let Int.LF.Root (_, h, Int.LF.Nil) = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA', LF.id) in
     Int.LF.PObj h
  | Apx.LF.Dot (Apx.LF.Head h, Apx.LF.EmptySub)
  , Int.LF.MTyp tA' ->
     let tM = Apx.LF.Root (Loc.ghost, h, Apx.LF.Nil) in
     let m = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA', LF.id) in
     Int.LF.MObj m

  | _, _ ->
     let x = match mtyp with
       | Int.LF.PTyp _  -> true
       | _ -> false
     in
     dprintf (fun p -> p.fmt "[elClObj] failure. Is ptyp? %b" x);
     throw loc (MetaObjectClash (cD, Int.LF.ClTyp (mtyp, cPsi')))

let rec elMetaObj' cD loc cM cTt = match cM , cTt with
  | (Apx.Comp.CObj psi, (Int.LF.CTyp (Some w))) ->
      let cPsi' = elDCtxAgainstSchema loc Lfrecon.Pibox cD psi w in
        Int.LF.CObj cPsi'

  | (Apx.Comp.ClObj (cPhi, clobj), (Int.LF.ClTyp (mtyp, cPsi'))) ->
     begin
       try unifyDCtxWithFCVar loc cD cPsi' cPhi
       with Unify.Failure _ ->
         let cPhi = Lfrecon.elDCtx Lfrecon.Pibox cD cPhi in
         raise (Error (loc, MetaObjContextClash (cD, cPsi', cPhi)))
     end;
     let _ = dprint (fun () -> "\n[elMetaObj'] ==> elCloObj \n") in
     let o = elClObj cD loc cPsi' clobj mtyp in
     Int.LF.ClObj
       ( Context.dctxToHat cPsi'
       , o
       )

  | (_ , _) -> raise (Error (loc,  MetaObjectClash (cD, cTt)))

and elMetaObj cD (loc,cM) cTt =
  let ctyp = C.cnormMTyp cTt in
  let r = elMetaObj' cD loc cM ctyp in
  try
    Unify.forceGlobalCnstr (!Unify.globalCnstrs);
    dprintf
      begin fun p ->
      p.fmt "[elMetaObj] @[<v>type = %a@,term = %a@]"
        (P.fmt_ppr_cmp_meta_typ cD P.l0) ctyp
        (P.fmt_ppr_cmp_meta_obj cD P.l0) (loc,r)
      end;
    loc, r
  with Unify.GlobalCnstrFailure (loc,cnstr)  ->
          raise (Check.Comp.Error (loc, Check.Comp.UnsolvableConstraints (None, cnstr)))

and elMetaObjCTyp loc cD m theta ctyp =
  let cM = elMetaObj cD m (ctyp, theta) in
  (cM, Int.LF.MDot (metaObjToFt cM, theta))

and elMetaSpine loc cD s cKt  =
  match (s, cKt) with
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
      dprintf
        begin fun p ->
        p.fmt "[elCompTyp] of kind: %a"
          (P.fmt_ppr_cmp_kind cD P.l0) tK
        end;
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypBase (loc, a ,cS')

| Apx.Comp.TypCobase (loc, a, cS) ->
      let _ = dprint (fun () -> "[elCompCotyp] Cobase : " ^ R.render_cid_comp_cotyp a) in
      let tK = (CompCotyp.get a).CompCotyp.kind in
      dprintf
        begin fun p ->
        p.fmt "[elCompCotyp] of kind: %a"
          (P.fmt_ppr_cmp_kind cD P.l0) tK
        end;
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
      dprintf
        begin fun p ->
        p.fmt "[elCompTyp] TypBox - cPsi = %a"
          (P.fmt_ppr_lf_dctx cD P.l0) cPsi
        end;
      let tA   = Lfrecon.elTyp (Lfrecon.Pibox) cD cPsi a in
      let tT = Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp tA, cPsi)) in
      dprintf
        begin fun p ->
        p.fmt "[elCompTyp] %a"
          (P.fmt_ppr_cmp_typ cD P.l0) tT
        end;
      tT

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

  | Apx.Comp.TypInd tau -> Int.Comp.TypInd (elCompTyp cD tau)

(* *******************************************************************************)

let mgCompTypSpine cD (loc, cK) =
  let rec genMetaSpine (cK, t) = match (cK, t) with
    | (Int.Comp.Ctype _, _t) -> Int.Comp.MetaNil
    | (Int.Comp.PiKind (loc', Int.LF.Decl(n,ctyp,_), cK), t) ->
        let (mO, t') = genMetaVar' loc cD (loc', n , ctyp, t) in
        let mS = genMetaSpine (cK, t') in
          Int.Comp.MetaApp (mO, mS) in
  genMetaSpine (cK, Whnf.m_id)

let mgCompCotyp cD (loc, c) =
  let cK = (CompCotyp.get c).CompCotyp.kind in
  let mS = mgCompTypSpine cD (loc, cK) in
  dprintf
    begin fun p ->
    p.fmt "[mgCompTyp] @[<v>kind of constant %s@,%a@]"
      (R.render_cid_comp_cotyp c)
      (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK
    end;
  Int.Comp.TypCobase (loc, c, mS)

let mgCompTyp cD (loc, c) =
  let cK = (CompTyp.get c).CompTyp.kind in
  let mS = mgCompTypSpine cD (loc, cK) in
  dprintf
    begin fun p ->
    p.fmt "[mgCompTyp] @[<v>kind of constant %s@,%a@]"
      (R.render_cid_comp_typ c)
      (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK
    end;
  Int.Comp.TypBase (loc, c, mS)

let rec mgCtx cD' (cD, cPsi) = begin match cPsi with
    | Int.LF.CtxVar (Int.LF.CtxOffset psi_var) ->
        let (n , sW) = Whnf.mctxCDec cD psi_var in
        let mmvar =
          let open Int.LF in
          { name = n
          ; instantiation = ref None
          ; cD = cD'
          ; typ = CTyp (Some sW)
          ; constraints = ref []
          ; depend = Maybe
          }
        in
        Int.LF.(CtxVar (CInst (mmvar, Whnf.m_id)))
    | Int.LF.Null -> Int.LF.Null
    | Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA)) ->
        let cPsi' = mgCtx cD' (cD, cPsi) in
        let tA'   = mgTyp cD' cPsi' tA in
          Int.LF.DDec (cPsi', Int.LF.TypDecl (x, tA'))
  end


let rec mgClTyp cD' cD_s cPsi' = function
  | Int.LF.MTyp tA -> Int.LF.MTyp (mgTyp cD' cPsi' tA)
  | Int.LF.PTyp tA -> Int.LF.PTyp (mgTyp cD' cPsi' tA)
  | Int.LF.STyp (cl, cPhi) -> Int.LF.STyp (cl, mgCtx cD' (cD_s, cPhi))
and mgCTyp cD' cD_s = function
  | Int.LF.ClTyp (t, cPsi) ->
    let cPsi' = mgCtx cD' (cD_s, cPsi) in
    Int.LF.ClTyp (mgClTyp cD' cD_s cPsi' t, cPsi')
  | Int.LF.CTyp sW -> Int.LF.CTyp sW



let rec inferPatTyp' cD' (cD_s, tau_s) = match tau_s with
  | Int.Comp.TypCross (tau1, tau2) ->
     let tau1' = inferPatTyp' cD' (cD_s, tau1) in
     let tau2' = inferPatTyp' cD' (cD_s, tau2) in
     Int.Comp.TypCross (tau1', tau2')

  | Int.Comp.TypBase (loc, c, _ )  -> mgCompTyp cD' (loc, c)

  | Int.Comp.TypCobase (loc, c, _ )  ->
     dprintf (fun p -> p.fmt "[inferPatTyp'] inferring type of cobase");
     mgCompCotyp cD' (loc, c)

  | Int.Comp.TypArr (tau1, tau2)  ->
     let tau1' = inferPatTyp' cD' (cD_s, tau1) in
     let tau2' = inferPatTyp' cD' (cD_s, tau2) in
     Int.Comp.TypArr (tau1', tau2')

  | Int.Comp.TypPiBox ((Int.LF.Decl (x, mtyp,dep)), tau) ->
     let mtyp' = mgCTyp cD' cD_s mtyp in
     let tau'  = inferPatTyp' (Int.LF.Dec (cD', Int.LF.Decl(x, mtyp',dep)))
                   (Int.LF.Dec (cD_s, Int.LF.Decl(x, mtyp,dep)), tau) in
     Int.Comp.TypPiBox (Int.LF.Decl (x, mtyp',dep), tau')

  | Int.Comp.TypBox (loc, mtyp)  ->
     let mtyp' = mgCTyp cD' cD_s mtyp in
     Int.Comp.TypBox (loc, mtyp')

(*  | Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp (Int.LF.Atom(_, a, _) as _tP) , cPsi))  ->
      let cPsi' = mgCtx cD' (cD_s, cPsi) in
      let tP' = mgAtomicTyp cD' cPsi' a (Typ.get a).Typ.kind  in
        Int.Comp.TypBox (loc, Int.LF.ClTyp (Int.LF.MTyp tP', cPsi'))

*)

let inferPatTyp cD' (cD_s, tau_s) = inferPatTyp' cD' (cD_s, Whnf.cnormCTyp (tau_s, Whnf.m_id))

(* *******************************************************************************)

(* (\* cD |- csp : theta_tau1 => theta_tau2 *\) *)
(* let rec elCofunExp cD csp theta_tau1 theta_tau2 = *)
(*   match (csp, theta_tau1, theta_tau2) with *)
(*     | (Apx.Comp.CopatNil loc, (Int.Comp.TypArr (tau1, tau2), theta), (tau', theta')) -> *)
(*         if Whnf.convCTyp (tau1, theta) (tau', theta') then *)
(*           (Int.Comp.CopatNil loc, (tau2, theta)) *)
(*         else raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta')))) *)
(*     | (Apx.Comp.CopatApp (loc, dest, csp'), *)
(*        (Int.Comp.TypArr (tau1, tau2), theta), (tau', theta')) -> *)
(*         if Whnf.convCTyp (tau1, theta) (tau', theta') then *)
(*           let (csp'', theta_tau') = elCofunExp cD csp' *)
(*             ((CompDest.get dest).CompDest.typ,Whnf.m_id) (tau2, theta) in *)
(*             (Int.Comp.CopatApp (loc, dest, csp''), theta_tau') *)
(*         else raise (Error (loc, TypMismatch (cD, (tau1, theta), (tau',theta')))) *)
(*           (\*  | (Apx.Comp.CopatMeta (loc, mo, csp'), (Int.Comp.*\) *)

let rec elExp cD cG e theta_tau = elExpW cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Fn (loc, x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
     (* let cG' = Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo (tau1, theta))) in *)
     let cG' = Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Whnf.cnormCTyp (tau1, theta), false)) in
     let e' = elExp cD cG' e (tau2, theta) in
     let e'' =  Whnf.cnormExp (Int.Comp.Fn (loc, x, e'), Whnf.m_id) in
     dprintf
       begin fun p ->
       p.fmt "[elExp] @[<v>Fn %a done@,cD = %a@,cG = %a@,expression %a@,has type %a@]"
         Id.print x
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_cmp_gctx cD P.l0) cG'
         (P.fmt_ppr_cmp_exp_chk cD cG' P.l0) e''
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp theta_tau)
       end;
     e''

  | (Apx.Comp.Fun (loc, fbr), ttau) ->
    Int.Comp.Fun (loc, elFBranch cD cG fbr theta_tau)

  (* | (Apx.Comp.Cofun (loc, bs), (Int.Comp.TypCobase (_, a, sp), theta)) -> *)
  (*     let copatMap = function (Apx.Comp.CopatApp (loc, dest, csp), e')  -> *)
  (*         let (csp', theta_tau') = *)
  (*           elCofunExp cD csp ((CompDest.get dest).CompDest.typ, Whnf.m_id) theta_tau *)
  (*         in (Int.Comp.CopatApp (loc, dest, csp'), elExpW cD cG e' theta_tau') *)
  (*     in let bs' = List.map copatMap bs *)
  (*     in Int.Comp.Cofun (loc, bs') *)

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
     dprintf
       begin fun p ->
       p.fmt "[elExp] @[<v>Syn@,expected type: %a@,cG = %a@]"
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau,t))
         P.fmt_ppr_cmp_gctx_typing (cD, cG)
       end;
    let (i1,tau1) = elExp' cD cG i in
    dprintf
      begin fun p ->
      p.fmt "[elExp] @[<v>Syn i = %a@,done: %a@]"
        (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i1, Whnf.m_id))
        P.fmt_ppr_cmp_typ_typing (cD, Whnf.cnormCTyp tau1)
      end;
    let (i', tau_t') = genMApp loc cD (i1, tau1) in
    dprintf
      begin fun p ->
      p.fmt "[elExp] @[<v>Unify computation-level types:@,%a == %a@]"
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp tau_t')
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau,t))
      end;
    let tau0 = Whnf.cnormCTyp (tau,t) in
    let tau1 = Whnf.cnormCTyp tau_t' in
    begin
      try
        Unify.unifyCompTyp cD (tau0, Whnf.m_id) (tau1, Whnf.m_id);
        dprintf
          begin fun p ->
          p.fmt "[elExp] @[<v>Unified computation-level types@,%a == %a@]"
            (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp tau_t')
            (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau,t))
          end;
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
              let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Whnf.cnormCTyp (tau1, t), false)) in
              let cG2 = Int.LF.Dec (cG1, Int.Comp.CTypDecl (y, Whnf.cnormCTyp (tau2, t), false)) in
              let e'  =  elExp cD cG2 e (tau, theta) in
                Int.Comp.LetPair (loc, i', (x, y, e'))

          | _ -> raise (Check.Comp.Error (loc, Check.Comp.MismatchSyn (cD, cG, i', Check.Comp.VariantCross, tau_theta')))
              (* TODO postpone to reconstruction *)
        end

  | (Apx.Comp.Let (loc, i, (x, e)), (tau, theta)) ->
      let (i', (tau',theta')) = elExp' cD cG i in
      let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Whnf.cnormCTyp (tau',theta'), false)) in
      let e'  =  elExp cD cG1 e (tau, theta) in
        Int.Comp.Let (loc, i', (x,  e'))


  | (Apx.Comp.Box (loc, cM), (Int.Comp.TypBox (_loc, cT), theta)) ->
     Int.Comp.Box (loc, elMetaObj cD cM (cT, theta))

  | Apx.Comp.Impossible (loc, i), (tau, theta) ->
     let i', ttau' = elExp' cD cG i in
     let i', _ = genMApp loc cD (i', ttau') in
     (* Not sure if we need to work any harder at this point, since we
        don't have any branches to elaborate. *)
     Int.Comp.Impossible (loc, i')

  | (Apx.Comp.Case (loc, prag, i, branches), ((tau, theta) as tau_theta)) ->
     dprintf (fun p -> p.fmt "[elExp] case at %a" Loc.print_short loc);
     dprintf (fun p -> p.fmt "[elExp] elaborating scrutinee");
     let (i', tau_theta') =  (elExp' cD cG i) in
     dprintf
       begin fun p ->
       p.fmt "[elExp] @[<v>case on @[@[%a@]@ @[%a@]@]@,cD = @[%a@]@,cG = @[%a@]@]"
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i', Whnf.m_id))
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp tau_theta')
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_cmp_gctx cD P.l0) cG
       end;
     let (i, tau_theta') = genMApp loc cD (i', tau_theta') in
     let tau_s = Whnf.cnormCTyp tau_theta' in
     let ct = case_type i in
     begin
       match (i, tau_s) with
             (* Not only the object but also its type must be closed *)
       | (Int.Comp.AnnBox (mC, _) as i, Int.Comp.TypBox (_, mT)) ->
          let _ = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          if Whnf.closedMetaObj mC && Whnf.closedCTyp tau_s then
            let recBranch b =
              let b = elBranch ct cD cG b tau_s tau_theta in
              let _ = Gensym.MVarData.reset () in
              b in
            let branches' = List.map recBranch branches in
            Int.Comp.Case (loc, prag, i, branches')
          else
            raise (Error (loc, ValueRestriction (cD, cG, i, (tau_s, Whnf.m_id))))

       | (Int.Comp.AnnBox (_, _) as i, _ ) ->
          raise (Error (loc, (IllegalCase (cD, cG, i, (tau_s, Whnf.m_id)))))

       | (i, Int.Comp.TypBox (_, Int.LF.ClTyp (Int.LF.MTyp tP, cPsi))) ->
          dprintf
            begin fun p ->
            p.fmt "[elExp] @[<v>Contexts @[<v>cD = @[%a@]@,cG = @[%a@]@]@,\
                   expected pattern has type: @[%a@]@,\
                   context of expected pattern type: @[%a@]@,\
                   checking closedness...@]"
              (P.fmt_ppr_lf_mctx P.l0) cD
              (P.fmt_ppr_cmp_gctx cD P.l0) cG
              (P.fmt_ppr_lf_typ cD cPsi P.l0) tP
              (P.fmt_ppr_lf_dctx cD P.l0) cPsi
            end;
          let tP = Whnf.normTyp (Whnf.cnormTyp (tP, Whnf.m_id), LF.id) in
          let cPsi = Whnf.normDCtx (Whnf.cnormDCtx (cPsi, Whnf.m_id)) in
          let cG = Whnf.cnormCtx (cG, Whnf.m_id) in
          if Whnf.closedTyp (tP, LF.id) &&
               Whnf.closedDCtx cPsi
               && Whnf.closedGCtx cG
          then
            let recBranch b =
              dprintf
                begin fun p ->
                p.fmt "[elBranch - DataObj] @[<v>@[%a@]@ of type@ @[%a@]@]"
                  (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i, Whnf.m_id))
                  (P.fmt_ppr_cmp_typ cD P.l0) tau_s
                end;
              let b = elBranch ct cD cG b tau_s tau_theta in
              let _ = Gensym.MVarData.reset () in
              b
            in
            let branches' = List.map recBranch branches in
            let b = Int.Comp.Case (loc, prag, i, branches') in
            dprintf
              begin fun p ->
              p.fmt "[elBranch - DataObj] @[<v>of type @[%a@]@ done@,\
                     cG = @[%a@]@,\
                     reconstructed branch:@,\
                     @[%a@]@]"
                (P.fmt_ppr_cmp_typ cD P.l0) tau_s
                (P.fmt_ppr_cmp_gctx cD P.l0) cG
                (P.fmt_ppr_cmp_exp_chk cD cG P.l0) b
              end;
            b
          else raise (Error (loc, CompScrutineeTyp (cD, cG, i', (tP, LF.id), cPsi)))

       | (i, _ ) ->
          let recBranch b =
            dprintf
              begin fun p ->
              p.fmt "[elBranch - PatObj] has type @[%a@]"
                (P.fmt_ppr_cmp_typ cD P.l0) tau_s
              end;
            let b = elBranch ct cD cG b tau_s tau_theta in
            Gensym.MVarData.reset () ; b in

          let branches' = List.map recBranch branches in
          dprintf
            begin fun p ->
            p.fmt "[elBranch - PatObj] @[<v>of type@,@[%a]@]"
              (P.fmt_ppr_cmp_typ cD P.l0) tau_s
            end;
          Int.Comp.Case (loc, prag, i, branches')
     end

  | (Apx.Comp.Hole (loc, name), (tau, theta)) ->
     dprintf
       begin fun p ->
       p.fmt "[elExp] @[<v>Expected Type (Hole):@,@[%a@]@] "
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau,theta))
       end;
     let id = Holes.allocate () in
     let name = HoleId.name_of_option name in
     Int.Comp.Hole (loc, id, name)

  (* TODO postpone to reconstruction *)
  (* Error handling cases *)
  | (Apx.Comp.Fn (loc, _x, _e),  tau_theta ) ->
      raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`fn, cD, cG, tau_theta)))
  | (Apx.Comp.MLam (loc, _u, _e), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`mlam, cD, cG, tau_theta)))
  | (Apx.Comp.Pair(loc, _ , _ ), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`pair, cD, cG, tau_theta)))
  | (Apx.Comp.Box (loc, _ ) , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`box, cD, cG, tau_theta)))

and elExp' cD cG i =
  let elBoxVal loc loc' psi r =
    let cPsi = Lfrecon.elDCtx Lfrecon.Pibox cD psi in
    let (tR, sP) = Lfrecon.elClosedTerm' Lfrecon.Pibox cD cPsi r in
    (* maybe we should detect whether tR is actually a parameter variable
       and generate a PObj instead of an MObj?
       Currently this is detected during typechecking, only to make
       sure we generate the appropriate cases during coverage
       checking.
       -je
     *)
    let phat = Context.dctxToHat cPsi in
    let cT = Int.LF.ClTyp (Int.LF.MTyp (Int.LF.TClo sP), cPsi) in
    let tau = Int.Comp.TypBox (Loc.ghost, cT) in
    let cM = (loc, Int.LF.ClObj (phat, Int.LF.MObj tR)) in
    (Int.Comp.AnnBox (cM, cT), (tau, C.m_id))
  in
  match i with
  | Apx.Comp.Var (loc, offset) ->
      let tau = lookup cG offset in
      dprintf
        begin fun p ->
        p.fmt "[elExp'] Variable %s has type @[%a@]"
          (R.render_var cG offset)
          (P.fmt_ppr_cmp_typ cD P.l0) tau
        end;
      (Int.Comp.Var (loc, offset), (tau, C.m_id))

  | Apx.Comp.DataConst (loc, c) ->
     let tau = (CompConst.get c).CompConst.typ in
     dprintf
       begin fun p ->
       p.fmt "[elExp'] @[<v>DataConst %s has type@,@[%a@]@]"
         (R.render_cid_comp_const c)
         P.fmt_ppr_cmp_typ_typing (cD, tau)
       end;
     (Int.Comp.DataConst (loc, c), (tau, C.m_id))

  | Apx.Comp.Obs (loc, e, obs) ->
    let cD' = (CompDest.get obs).CompDest.mctx in
    let t    = Ctxsub.mctxToMMSub cD cD' in
    let tau0 = (CompDest.get obs).CompDest.obs_type in
    let tau1 = (CompDest.get obs).CompDest.return_type in
    dprintf
      begin fun p ->
      p.fmt "[Obs] @[<v>tau0 = @[%a@]@,tau1 = @[%a@]@,t (before) = @[%a@]@]"
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau0, t))
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau1, t))
        (P.fmt_ppr_lf_msub cD P.l0) t
      end;
    let e' = elExp cD cG e (tau0, t) in
    dprintf
      begin fun p ->
      p.fmt "[Obs] @[<v>tau1 = @[%a@]@,t (after) = @[%a@]@]"
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau1, t))
        (P.fmt_ppr_lf_msub cD P.l0) t
      end;
    (Int.Comp.Obs (loc, e', t, obs), (tau1, t))

  (* | Apx.Comp.DataDest (loc, c) -> *)
  (*     let _ = dprint (fun () -> "[elExp'] DataDest " ^ R.render_cid_comp_dest  c ^ *)
  (*                       "\n has type " ^ P.mctxToString cD ^ " |- " ^ *)
  (*                       P.compTypToString cD ((CompDest.get c).CompDest.typ)) in *)
  (*    (Int.Comp.DataDest (loc, c), ((CompDest.get c).CompDest.typ, C.m_id)) *)

  | Apx.Comp.Const (loc,prog) ->
     (Int.Comp.Const (loc,prog), ((Comp.get prog).Comp.typ, C.m_id))

  | Apx.Comp.Apply (loc, i, e) ->
     dprintf
       (fun p ->
         p.fmt "[elExp'] Apply at %a" Loc.print_short loc);
      let (i', tau_theta') = genMApp loc cD (elExp' cD cG i) in
      let _ = dprint (fun () -> "[elExp'] Apply - generated implicit arguments") in
        begin match e , tau_theta' with
          | e , (Int.Comp.TypArr (tau2, tau), theta) ->
             dprintf
               begin fun p ->
               p.fmt "[elExp'] @[<v>i' = @[%a@]@,inferred type: @[%a@]@,\
                      check argument has type: @[%a@]@,\
                      result has type: @[%a@]@]"
                 (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i', Whnf.m_id))
                 (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (Int.Comp.TypArr (tau2,tau), theta))
                 (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau2,theta))
                 (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau,theta))
               end;
              let tau' = Whnf.cnormCTyp (tau, theta) in

              let e' = elExp cD cG e (tau2, theta) in

              let i'' = Int.Comp.Apply (loc, i', e') in

              (* let tau'' = Whnf.cnormCTyp (tau', Whnf.m_id) in *)
              dprintf
                begin fun p ->
                p.fmt "[elExp'] @[<v>Apply done:@,\
                       cD = @[%a@]@,\
                       i'' = @[%a@]@,\
                       has type: @[%a@]@]"
                  (P.fmt_ppr_lf_mctx P.l0) cD
                  (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i'', Whnf.m_id))
                  (P.fmt_ppr_cmp_typ cD P.l0) tau'
                end;
               (*  (i'', (tau, theta))  - not returnig the type in normal form
      leads to subsequent whnf failure and the fact that indices for context in
      MetaObj are off *)
                (i'', (tau', Whnf.m_id))
          | Apx.Comp.Box (_,mC) , (Int.Comp.TypPiBox (Int.LF.Decl(_,ctyp,_), tau), theta) ->
                let cM = elMetaObj cD mC (ctyp, theta) in
                (Int.Comp.MApp (loc, i', cM), (tau, Int.LF.MDot (metaObjToFt cM, theta)))
          | _ ->
             raise
               ( Check.Comp.Error
                   ( loc
                   , Check.Comp.MismatchSyn
                       (cD, cG, i', Check.Comp.VariantArrow, tau_theta')
                   )
               )
                (* TODO postpone to reconstruction *)
        end

  (* In the following two cases, the substitution is possibly
     representing a *term*. In fact, it must, because afaik BoxVal is
     only for when we case-analyze on a box, and matching on
     substitutions in general is not allowed (only matching on
     substitution variables is), so we can safely disambiguate this to
     a boxed *term*. -je *)
  | Apx.Comp.BoxVal (loc, (loc', Apx.Comp.ClObj (psi, Apx.LF.Dot (Apx.LF.Head h, Apx.LF.EmptySub)))) ->
     (* package the head into a full term *)
     elBoxVal loc loc' psi (Apx.LF.Root (Loc.ghost, h, Apx.LF.Nil))

  | Apx.Comp.BoxVal (loc, (loc', Apx.Comp.ClObj (psi, Apx.LF.Dot (Apx.LF.Obj r, Apx.LF.EmptySub)))) ->
     elBoxVal loc loc' psi r

     (* old elaboration
  | Apx.Comp.BoxVal (loc, (loc', Apx.Comp.ClObj (psi, Comp.MObj r))) ->
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
      *)

  | Apx.Comp.BoxVal (loc, (_loc',Apx.Comp.ClObj (phi, Apx.LF.SVar (Apx.LF.Offset k, id)))) ->
     dprint (fun () -> "Case Analysis on SubstVar");
     let isId =
       match id with
       | None -> true
       | Some Apx.LF.Id -> true
       | Some Apx.LF.EmptySub ->
          let (_ ,  cPsi, _ , cPhi) = Whnf.mctxSDec cD k in
          match cPhi, cPsi with
          | Int.LF.Null, Int.LF.Null -> true
          | _ -> false
     in
     if isId then
       let sv = Int.LF.SVar (k, 0, Int.LF.Shift 0) in
       let cPhi     = Lfrecon.elDCtx Lfrecon.Pibox cD phi in
       let (_ , cPsi, cl , _cPhi) = Whnf.mctxSDec cD k in (* cD; cPhi |- svar: cPsi  *)
       let phat     = Context.dctxToHat cPhi in
       let cT       = Int.LF.ClTyp (Int.LF.STyp (cl, cPsi), cPhi) in
       let tau      = Int.Comp.TypBox (Syntax.Loc.ghost, cT) in
       let cM       = (loc, Int.LF.ClObj(phat, Int.LF.SObj sv)) in
       (Int.Comp.AnnBox (cM, cT), (tau, C.m_id))
     else
       throw loc IllegalSubstMatch
  (* (ErrorMsg "Found a Substitution – Only Pattern Matching on Substitution Variables is supported") *)

  | Apx.Comp.BoxVal (loc, (_loc',Apx.Comp.ClObj (phi2, Apx.LF.SVar (s , s' )))) ->
      let Apx.LF.MInst (Int.LF.SObj s0, Int.LF.ClTyp (Int.LF.STyp (cl, cPsi), cPhi)) = s in
      let cPhi2     = Lfrecon.elDCtx Lfrecon.Pibox cD phi2 in
      let s'        = Lfrecon.elSub loc Lfrecon.Pibox cD cPhi2 s' cl cPhi in
      let s0' = Substitution.LF.comp s0 s' in
      begin match s0'  with
      | Int.LF.SVar (k, 0, id) ->
         (*               let isId = (match id with
                          | Int.LF.EmptySub ->
                          let (_ ,  cPsi, _ , cPhi) = Whnf.mctxSDec cD k in
                          (match cPhi, cPsi with
                          | Int.LF.Null, Int.LF.Null -> true
                          | _ -> false)
                          | s -> Substitution.LF.isId s ) in *)
         if Substitution.LF.isId id then
           let phat     = Context.dctxToHat cPhi in
           let cT       = Int.LF.ClTyp (Int.LF.STyp (cl, cPsi), cPhi2) in
           let tau      = Int.Comp.TypBox (Syntax.Loc.ghost, cT) in
           let cM       = (loc, Int.LF.ClObj(phat, Int.LF.SObj s0')) in
           (Int.Comp.AnnBox (cM, cT), (tau, C.m_id))
         else
           throw loc IllegalSubstMatch
      | _  -> throw loc IllegalSubstMatch
      end


  | Apx.Comp.BoxVal (loc, (loc', Apx.Comp.CObj (cpsi))) ->
     dprintf (fun p -> p.fmt "[elExp'] BoxVal");
     begin
       match cpsi with
       | Apx.LF.CtxVar (ctxvar) ->
          let c_var = Lfrecon.elCtxVar ctxvar in
          let cM = (loc', Int.LF.CObj (Int.LF.CtxVar c_var)) in
          begin
            match c_var with
            | (Int.LF.CtxOffset offset) as phi ->
               let sW  = Context.lookupCtxVarSchema cD  phi in
               let cT  = Int.LF.CTyp (Some sW) in
               let tau = Int.Comp.TypBox (Syntax.Loc.ghost, cT) in
               (Int.Comp.AnnBox (cM, cT), (tau, C.m_id))
            | _ ->
               throw loc (ErrorMsg "In general the schema of the given context cannot be uniquely inferred")
          end
     end

  | Apx.Comp.PairVal (loc, i1, i2) ->
     let (i1', (tau1,t1)) = genMApp loc cD (elExp' cD cG i1) in
     let (i2', (tau2,t2)) = genMApp loc cD (elExp' cD cG i2) in
     (Int.Comp.PairVal (loc, i1', i2'),
      (Int.Comp.TypCross (Whnf.cnormCTyp (tau1,t1), Whnf.cnormCTyp (tau2,t2)), C.m_id))

  | _ -> failwith "uh oh"

(*

  recPattern cD delta psi m tPopt =

  Assumptions:
      cO ; cD ; cPsi |- tPopt
      omega ; delta ; psi |- m


* recPattern becomes redundant when we adopt the new parser as default.

*)

(* inferCtxSchema loc (cD, cPsi) (cD', cPsi') = ()
    cPsi is the context of the scrutinee
    cPsi' is the context of the pattern
    return elaborated cPsi'
    or raise exception
   TODO: This is very similar to unifyDCtxWithFCVar
*)
and inferCtxSchema loc (cD,cPsi) (cD', cPsi') = match (cPsi , cPsi') with
  | (Int.LF.Null , Apx.LF.Null) ->
     Int.LF.Null

  | (Int.LF.CtxVar (Int.LF.CtxOffset psi1_var), cPsi') ->
     dprintf
       begin fun p ->
       p.fmt "[inferCtxSchema] @[<v>outside context cD = @[%a@]@,\
              local context in branch: cD' = @[%a@]@,\
              looking up psi = @[%a@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_lf_mctx P.l0) cD'
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
       end;
     (* lookup the schema of the context variable on the RHS *)
     let (_ , s_cid) = Whnf.mctxCDec cD psi1_var in
     (* and then elaborate the given context against that schema *)
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

and elPatMetaObj cD pat (cdecl, theta) = match pat with
  | Apx.Comp.PatMetaObj (loc, cM) ->
    let (mO,t') = elMetaObjCTyp loc cD cM theta cdecl in
    (Int.Comp.PatMetaObj (loc, mO), t')
  | Apx.Comp.PatConst (loc, _, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatFVar (loc, _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatVar (loc, _ , _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatPair (loc, _ , _ ) -> raise (Error (loc, PatternMobj))
  | Apx.Comp.PatAnn (loc, _, _) -> raise (Error (loc, PatAnn))

and elPatChk (cD:Int.LF.mctx) (cG:Int.Comp.gctx) pat ttau = match (pat, ttau) with
  | (Apx.Comp.PatVar (loc, name, x) , (tau, theta)) ->
      let tau' = Whnf.cnormCTyp (tau, theta) in
      dprintf
        begin fun p ->
        p.fmt "[elPatChk] @[<v>Inferred type of pat var %a as@,@[%a@]@]"
          Id.print name
          (P.fmt_ppr_cmp_typ cD P.l0) tau'
        end;
      ( Int.LF.Dec(cG, Int.Comp.CTypDecl (name, tau', false))
      , Int.Comp.PatVar (loc, x)
      )
(*  | (Apx.Comp.PatFVar (loc, x) , ttau) ->
       (FPatVar.add x (Whnf.cnormCTyp ttau);
        (* indexing guarantees that all pattern variables occur uniquely *)
       Int.Comp.PatFVar (loc, x))
*)
  | (Apx.Comp.PatConst (loc, _c, _), ttau) ->
      let (cG', pat', ttau') = elPatSyn cD cG pat in
      dprintf
        begin fun p ->
        p.fmt "[elPatChk] @[<v>expected tau = @[%a@]@,expected tau' = @[%a@]@]"
          (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
          (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau')
        end;
      begin
        try
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
  | (Apx.Comp.PatPair(loc, _ , _ ), tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`pair, cD, Int.LF.Empty, tau_theta)))
  | (Apx.Comp.PatMetaObj (loc, _) , tau_theta) ->
      raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`box, cD, Int.LF.Empty, tau_theta)))
  | (Apx.Comp.PatAnn (loc, _, _ ) , ttau) ->
      let (cG', pat', ttau') = elPatSyn cD cG pat in
      dprintf
        begin fun p ->
        p.fmt "[elPatChk] @[<v>expected tau = @[%a@]@,inferred tau' = @[%a@]@]"
          (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
          (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau')
        end;
      begin
        try
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
      begin match ttau with
      | (Int.Comp.TypArr (tau1, tau2), theta) ->
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>ttau = @[%a@]@,ttau1 = @[%a@]@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau1, theta))
           end;
         let (cG', pat) = elPatChk cD cG pat' (tau1, theta) in
         let (cG'', pat_spine, ttau2) = elPatSpine cD cG' pat_spine' (tau2, theta) in
         (cG'', Int.Comp.PatApp (loc, pat, pat_spine), ttau2)
      | (Int.Comp.TypPiBox ((Int.LF.Decl (n, ctyp, Int.LF.Maybe)), tau), theta) ->
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>TypPiBox implicit ttau =@,@[%a@]@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
           end;
         let (mO,t') = genMetaVar' loc cD (loc, n, ctyp, theta) in
         let pat'  = Int.Comp.PatMetaObj (loc, mO) in
         let ttau' = (tau, t')
         in
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>elaborate spine against@,theta = @[%a]@,ttau' = @[%a@]@]"
             (P.fmt_ppr_lf_msub cD P.l0) t'
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau')
           end;
         let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
         (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)

      | (Int.Comp.TypPiBox (Int.LF.Decl (_,ctyp,dep), tau), theta) ->
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>TypPiBox explicit ttau = @[%a@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
           end;
         let (pat, theta') = elPatMetaObj cD pat' (ctyp, theta) in
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>pat = @[%a@]@,theta = @[%a@]@,\
                  remaining spine must have type:@,@[%a@]@]"
             (P.fmt_ppr_cmp_pattern cD cG P.l0) pat
             (P.fmt_ppr_lf_msub cD P.l0) theta'
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau, theta'))
           end;
         let (cG1, pat_spine, ttau2) = elPatSpine cD cG pat_spine' (tau, theta') in
         (cG1, Int.Comp.PatApp (loc, pat, pat_spine), ttau2)

      | _ ->
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] fall through - ttau = @[%a@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
           end;
         raise (Error (loc, TooManyMetaObj))
      end
  | Apx.Comp.PatObs (loc, obs, pat_spine') ->
    begin match ttau with
    | (Int.Comp.TypCobase (loc', cid, mspine), theta) ->
      let cD' = (CompDest.get obs).CompDest.mctx in
       dprintf
         begin fun p ->
         let name = (CompDest.get obs).CompDest.name in
         p.fmt "[elPatSpine] @[<v>Observation: %a@,cD = @[%a@]@,cD' = @[%a@]@]"
           Id.print name
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_lf_mctx P.l0) cD'
         end;
      let tau0 = (CompDest.get obs).CompDest.obs_type in
      let tau1 = (CompDest.get obs).CompDest.return_type in
      let t    = Ctxsub.mctxToMMSub cD cD' in
      dprintf
        begin fun p ->
        p.fmt "[elPatSpine] @[<v>t = @[%a@]@,inst. type: @[%a@]@]"
          (P.fmt_ppr_lf_msub cD P.l0) t
          (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau0,t))
        end;
      begin try
        Unify.unifyCompTyp cD ttau (tau0, t);
        dprintf
          begin fun p ->
          p.fmt "[elPatSpine] New type: @[%a@]"
            (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau1,t))
          end;
        let (cG1, pat_spine, ttau2) = elPatSpine cD cG pat_spine' (tau1, t) in
        (cG1, Int.Comp.PatObs (loc, obs, Whnf.cnormMSub t, pat_spine), ttau2)
      with
      | Unify.Failure _ ->
        raise (Error (loc, TypMismatch (cD, ttau, (tau0, t))))
      end
    | (Int.Comp.TypPiBox (Int.LF.Decl (n, ctyp, Int.LF.Maybe), tau), theta) ->
     let (mO,t') = genMetaVar' loc cD (loc, n, ctyp, theta) in
     let pat'  = Int.Comp.PatMetaObj (loc, mO) in
     let ttau' = (tau, t') in
     let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
     (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)
    (* | _ -> raise (Error (loc, TypMismatch (cD, ttau, (tau1, Whnf.m_id)))) *)
 end



and recPatObj' cD pat (cD_s, tau_s) = match pat with
  | Apx.Comp.PatAnn (l, (Apx.Comp.PatMetaObj (loc, _) as pat') ,
                          Apx.Comp.TypBox (loc', (_,Apx.LF.ClTyp(Apx.LF.MTyp a, psi)))) ->
     dprintf
       begin fun p ->
       p.fmt "[recPatObj' - PatMetaObj] scrutinee has type tau = @[%a@]"
         (P.fmt_ppr_cmp_typ cD_s P.l0) tau_s
       end;
     let Int.Comp.TypBox (_ , Int.LF.ClTyp (Int.LF.MTyp _tQ, cPsi_s)) = tau_s  in
     let cPsi = inferCtxSchema loc (cD_s, cPsi_s) (cD, psi) in
     let tP   = Lfrecon.elTyp (Lfrecon.Pibox) cD cPsi a in
     let tau' = Int.Comp.TypBox(loc', Int.LF.ClTyp (Int.LF.MTyp tP, cPsi)) in
     let ttau' = (tau', Whnf.m_id) in
     let (cG', pat') = elPatChk cD Int.LF.Empty pat'  ttau' in
     (* Return annotated pattern? Int.Comp.PatAnn (l, pat', tau') *)
     (cG',Int.Comp.PatAnn(l, pat', tau'), ttau')

  | Apx.Comp.PatAnn (_ , pat, tau) ->
     dprintf
       begin fun p ->
       p.fmt "[recPatObj' PatAnn] scrutinee has type tau = @[%a@]"
         (P.fmt_ppr_cmp_typ cD_s P.l0) tau_s
       end;
     let tau' = elCompTyp cD tau in
     let ttau' = (tau', Whnf.m_id) in
     let (cG', pat') = elPatChk cD Int.LF.Empty pat ttau' in
     (cG', pat', ttau')

  | Apx.Comp.PatMetaObj (loc, (_ , Apx.Comp.ClObj (psi, _ ))) ->
      (* Factor out the case for PatMetaObj, since the context associated
         with the MetaObj is used in generating the mg type of pattern;
         this is useful, if the context psi contains Sigma-types,
         as existential variables can be generated in a flattened context.
      *)
      let inferClTyp cD psi (cD_s, tau_s) =
        begin match tau_s with
        | Int.Comp.TypBox (loc', Int.LF.ClTyp (mT, cPsi)) ->
          (match mT with
             | Int.LF.MTyp (Int.LF.Atom(_, a, _)) ->
                 let cPsi' = inferCtxSchema loc (cD_s, cPsi) (cD, psi) in
                 let tP'   = mgAtomicTyp cD cPsi' a (Typ.get a).Typ.kind in
                   loc', Int.LF.ClTyp (Int.LF.MTyp tP', cPsi')
             | Int.LF.STyp (sv_class, cPhi) ->
                 let cPsi' = mgCtx cD (cD_s, cPsi) in
                 let cPhi' = mgCtx cD (cD_s, cPhi) in
                   loc', Int.LF.ClTyp (Int.LF.STyp (sv_class, cPhi'), cPsi')
            )
        | Int.Comp.TypBox (loc', mT) -> raise (Error (loc, MetaObjectClash (cD, mT)))
        | _ ->  raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`box, cD_s, Int.LF.Empty, (tau_s, Whnf.m_id))))
        end
      in
      let (loc', clTyp) = inferClTyp cD psi (cD_s, tau_s) in
        let tau_p = Int.Comp.TypBox (loc', clTyp) in
        let ttau' = (tau_p, Whnf.m_id) in
        let (cG', pat')  = elPatChk cD Int.LF.Empty pat ttau' in
          (cG', Int.Comp.PatAnn(loc, pat', tau_p), ttau')

  | _ ->
     dprintf
       begin fun p ->
       p.fmt "[recPatObj'] @[<v>-~~> inferPatTyp@,tau_s = @[%a@]@]"
         (P.fmt_ppr_cmp_typ cD_s P.l0) tau_s
       end;
      let tau_p = inferPatTyp cD (cD_s, tau_s) in
      dprintf
        begin fun p ->
        p.fmt "[inferPatTyp] tau_p = @[%a@]"
          (P.fmt_ppr_cmp_typ cD P.l0) tau_p
        end;
      let ttau' = (tau_p, Whnf.m_id) in
      let (cG', pat')  = elPatChk cD Int.LF.Empty pat ttau' in
        (cG', pat', ttau')


and recPatObj loc cD pat (cD_s, tau_s) =
  dprintf
    begin fun p ->
    p.fmt "[recPatObj] @[<v>scrutinee has type @[tau =@ @[%a@]@]@,\
           scrutinee cD = @[%a@]@,
           pattern cD = @[%a@]@]"
      (P.fmt_ppr_cmp_typ cD_s P.l0) tau_s
      (P.fmt_ppr_lf_mctx P.l0) cD_s
      (P.fmt_ppr_lf_mctx P.l0) cD
    end;
  let (cG', pat', ttau') = recPatObj' cD pat (cD_s, tau_s) in
    (* cD' ; cG' |- pat' => tau' (may contain free contextual variables) *)
    (* where cD' = cD1, cD and cD1 are the free contextual variables in pat'
       cG' contains the free computation-level variables in pat'
       cG' and cD' are handled destructively via FVar and FCVar store
      *)
  dprintf (fun p -> p.fmt "[recPatObj] solving constraints %a" Loc.print_short loc);
  Lfrecon.solve_constraints cD;
  dprintf
    begin fun p ->
    p.fmt "[recPatObj] @[<v>pat (before abstraction) =@,\
           @[@[%a@] |-@ @[%a@]@]@]"
      (P.fmt_ppr_cmp_gctx cD P.l0) cG'
      (P.fmt_ppr_cmp_pattern cD cG' P.l0) pat'
    end;
  dprint (fun () -> "[recPatObj] Abstract over pattern and its type");
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

and synPatRefine loc caseT (cD, cD_p) pat (tau_s, tau_p) =
  let cD'  = Context.append cD cD_p in   (* cD'  = cD, cD_p   *)
  dprintf
    begin fun p ->
    p.fmt "[synPatRefine] @[<v>cD' = @[%a@]@,cD' |- tau_s = @[%a@]"
      (P.fmt_ppr_lf_mctx P.l0) cD'
      (P.fmt_ppr_cmp_typ cD' P.l0) tau_s
    end;
  let t   = Ctxsub.mctxToMSub cD'  in  (* .  |- t   <= cD'  *)
  dprintf
    begin fun p ->
    p.fmt "[synPatRefine] @[<v>mctxToMSub .  |- t <= cD'@,@[%a@]@] "
      (P.fmt_ppr_lf_msub Int.LF.Empty P.l0) (Whnf.cnormMSub t)
    end;
  let n   = Context.length cD_p in
  let m   = Context.length cD in
  let t1  = Whnf.mvar_dot (Int.LF.MShift m) cD_p in
  (* cD, cD_p |- t1 <= cD_p *)
  let mt1 = Whnf.mcomp t1 t in         (* .  |- mt1 <= cD1   *)
  dprintf
    begin fun p ->
    p.fmt "[synPatRefine] @[<v>. |- [t]tau_s = @,@[%a@]@]"
      (P.fmt_ppr_cmp_typ cD' P.l0) (Whnf.cnormCTyp (tau_s,t))
    end;
  let tau_s' = Whnf.cnormCTyp (Whnf.cnormCTyp (tau_s, Whnf.m_id), t) in
  let _ = dprint (fun () -> ".... [t]tau_s done ") in
  let tau_p' = Whnf.cnormCTyp (tau_p, mt1) in
  dprintf
    begin fun p ->
    p.fmt "[synPatRefine] @[<v>Unify : Inferred pattern type@,\
           tau_p' = @[%a@]@,\
           expected pattern type tau_s' = @[%a@]@]"
      (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau_p'
      (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau_s'
    end;
  begin
    try
      Unify.unifyCompTyp (Int.LF.Empty) (tau_s', Whnf.m_id) (tau_p', Whnf.m_id)
    with Unify.Failure msg ->
      dprintf
        begin fun p ->
        p.fmt "@[<v>Unify ERROR: %s@,\
               inferred pattern type: @[%a@]@,\
               expected pattern type: @[%a@]@]"
          msg
          (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau_p'
          (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau_s'
        end;
      raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, (tau_s', Whnf.m_id), (tau_p', Whnf.m_id))))
  end;
  begin match (caseT, pat) with
  | (DataObj, _) -> ()
  | (IndexObj mO, Int.Comp.PatMetaObj (_, mO1)) |
      (IndexObj mO, Int.Comp.PatAnn (_ , Int.Comp.PatMetaObj (_ , mO1), _ ))->
     let Int.Comp.TypBox (_ , mT) =  tau_p' in
     begin
       try
         dprint (fun () -> "Pattern matching on index object...");
         Unify.unifyMetaObj Int.LF.Empty  (mO,  t)
           (mO1, mt1) (mT, Whnf.m_id)
       with Unify.Failure msg ->
         (dprint (fun () -> "Unify ERROR: " ^ msg);
          raise (Error.Violation "Pattern matching on index argument failed"))
     end
  end;
  dprnt "[synPatRefine] AbstractMSub...";
  (* cD1' |- t' <= cD' where cD' = cD, cD_p *)
  let (t', cD1') = Abstract.msub (Whnf.cnormMSub t) in
  dprintf
    begin fun p ->
    p.fmt "@[<v>[synPatRefine] AbstractMSub... done:@,\
           @[@[%a@] |-@ @[%a@]@]@]"
      (P.fmt_ppr_lf_mctx P.l0) cD1'
      (P.fmt_ppr_lf_msub cD1' P.l0) t'
    end;
  let rec drop t l_delta1 = match (l_delta1, t) with
    | (0, t) -> t
    | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

  let t0   = drop t' n in  (* cD1' |- t0 <= cD *)

  let pat' = Whnf.cnormPattern (pat,  Whnf.mcomp t1 t') in
  let _    = dprint (fun () -> "cnormPat done ... ") in
  (t0, t', cD1', pat')

and elBranch caseTyp cD cG branch tau_s (tau, theta) =
  match branch with
  | Apx.Comp.Branch (loc, _omega, delta, pat, e) ->
     dprintf
       begin fun p ->
         p.fmt "[elBranch] @[<v>Reconstruction of general pattern of type@,@[%a@]@]"
           (P.fmt_ppr_cmp_typ cD P.l0) tau_s
       end;
     let cD' = elMCtx Lfrecon.Pibox delta in
     dprintf
       begin fun p ->
       p.fmt "[recPatObj] @[<v>reconstruction of delta done : cD_p  (explicit) =@,@[%a@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD'
       end;
     let ((l_cd1', l_delta), cD1', cG1,  pat1, tau1)  =  recPatObj loc cD' pat (cD, tau_s) in
     dprintf
       begin fun p ->
       p.fmt "[recPatObj] @[<v>done@,\
              @[@[%a@] ; @[%a@] |-@ @[@[%a@]@ : @[%a@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD1'
         (P.fmt_ppr_cmp_gctx cD1' P.l0) cG1
         (P.fmt_ppr_cmp_pattern cD1' cG1 P.l0) pat1
         (P.fmt_ppr_cmp_typ cD1' P.l0) tau1
       end;
     let tau_s' = Whnf.cnormCTyp (tau_s, Int.LF.MShift l_cd1') in
           (* ***************                            *************** *)
     let caseT'  =
       match caseTyp with
       | IndexObj mO -> IndexObj (Whnf.cnormMetaObj (mO, Int.LF.MShift l_cd1'))

       (*                  | IndexObj (l, Int.LF.ClObj (phat, Int.LF.MObj tR')) ->
                           IndexObj (l, Int.LF.ClObj(phat, Int.LF.MObj (Whnf.cnorm (tR', Int.LF.MShift l_cd1'))))
                           | IndexObj (l, Int.LF.ClObj (phat, Int.LF.SObj s)) ->
                           IndexObj (l, Int.LF.ClObj(phat, Int.LF.SObj (Whnf.cnormSub (s, Int.LF.MShift l_cd1'))))
        *)
       | DataObj -> DataObj
     in
     (* cD |- tau_s and cD, cD1' |- tau_s' *)
     (* cD1' |- tau1 *)

     let (t', t1, cD1'', pat1') = synPatRefine loc caseT' (cD, cD1') pat1 (tau_s', tau1) in
     (*  cD1'' |- t' : cD    and   cD1'' |- t1 : cD, cD1' *)
     let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
     (*   cD1' |- cG1     cD1'' |- t1 : cD, cD1'    cD, cD1' |- ?   cD1' *)
     let cD'      = Context.append cD cD1' in
     dprintf
       begin fun p ->
       p.fmt "[elBranch] @[<v>after synPatRefine@,cD1'' = @[%a@]@,\
              cD' = @[%a@]@,\
              and cG1 = @[%a@]@,\
              t1 : cD' = @[%a@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD1''
         (P.fmt_ppr_lf_mctx P.l0) cD'
         (P.fmt_ppr_cmp_gctx cD' P.l0) cG1
         (P.fmt_ppr_lf_msub cD1'' P.l0) t1
       end;
     let cG1'    = Whnf.cnormCtx (Whnf.normCtx cG1, t1) in
     dprintf
       begin fun p ->
       p.fmt "[elBranch] cD1'' |- cG1 = @[%a@]"
         (P.fmt_ppr_cmp_gctx cD1'' P.l0) cG1'
       end;
     let cG'     = Whnf.cnormCtx (Whnf.normCtx cG, t') in
     let cG_ext  = Context.append cG' cG1' in

     let e1       = Apxnorm.fmvApxExp [] cD'  (l_cd1, l_delta, 0) e in

     dprintf
       begin fun p ->
       p.fmt "[after synPatRefine]: @[<v>t': @[%a@]@,refinement: @[%a@]@]"
         P.fmt_ppr_lf_msub_typing (cD1'', t', cD)
         P.fmt_ppr_lf_msub_typing (cD1'', t1, cD')
       end;
     (*  if cD,cD0     |- e apx_exp   and  cD1' = cD1, cD0
         then cD, cD1' |- e1 apx_exp
      *)
     (* if   cD1'' |- t' <= cD, cD1'   and cD,cD1' |- e1 apx_exp
        then cD1'' |- e' apx_exp
      *)
     let e'      =  Apxnorm.cnormApxExp cD' Apx.LF.Empty e1  (cD1'', t1) in
     (* Note: e' is in the scope of cD1''  *)
     dprintf
       begin fun p ->
       p.fmt "[Apx.cnormApxExp ] @[<v>done@,target type tau' = @[%a@]@,t' = @[%a@]@]"
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau, theta))
         (P.fmt_ppr_lf_msub cD1'' P.l0) t'
       end;
     let tau'    = Whnf.cnormCTyp (tau, Whnf.mcomp theta t') in

     dprintf
       begin fun p ->
       p.fmt "[elBranch] @[<v>Elaborate branch against@,@[%a@]@,in cG = @[%a@]"
         P.fmt_ppr_cmp_typ_typing (cD1'', tau')
         (P.fmt_ppr_cmp_gctx cD1'' P.l0) cG_ext
       end;
     let eE'      = elExp cD1'' cG_ext  e' (tau', Whnf.m_id) in
     let _        = dprint (fun () -> "[elBranch] Body done (general pattern) \n") in
     let _       = FCVar.clear() in
     Int.Comp.Branch (loc, cD1'', cG1', pat1', t', eE')


and elFBranch cD cG fbr theta_tau = match fbr with
  | Apx.Comp.NilFBranch loc -> Int.Comp.NilFBranch loc
  | Apx.Comp.ConsFBranch (loc, (ps, e), fbr') ->
    let (cG', ps', ttau2) = elPatSpine cD cG ps theta_tau in
    let _ = Lfrecon.solve_constraints cD in
    let (cD1, cG1, ps1, tau1) = Abstract.pattern_spine loc cD (Whnf.cnormCtx (cG', Whnf.m_id)) ps' (Whnf.cnormCTyp ttau2) in
    let _ = try Check.Comp.wf_mctx cD1 (* Double Check that cD1 is well-formed *)
            with _ -> raise (Error (loc,MCtxIllformed cD1)) in
      (* cD1 ; cG1 |- pat1 => tau1 (contains no free contextual variables) *)
    let l_cd1    = Context.length cD1 in
    let cD'     = Context.append cD cD1 in
    let e'      = Apxnorm.fmvApxExp [] cD' (l_cd1, 0, 0) e in
    let cG_ext  = Context.append cG cG1 in
    dprintf
      begin fun p ->
      p.fmt "[elExp] @[<v>Fun: In progress@,cD' = @[%a@]@,cG' = @[%a@]@,tau1 = @[%a@]@]"
        (P.fmt_ppr_lf_mctx P.l0) cD1
        (P.fmt_ppr_cmp_gctx cD1 P.l0) cG1
        (P.fmt_ppr_cmp_typ cD1 P.l0) tau1
      end;
    let e''     = elExp cD1 cG1  e' (tau1, Whnf.m_id) in
    let _       = FCVar.clear() in
    dprintf
      begin fun p ->
      p.fmt "[elExp] @[<v>Fun: Done@,expression @[%a@]@,has type @[%a@]@]"
        (P.fmt_ppr_cmp_exp_chk cD1 cG_ext P.l0) e''
        (P.fmt_ppr_cmp_typ cD1 P.l0) (Whnf.cnormCTyp (tau1, Whnf.m_id))
      end;
    Int.Comp.ConsFBranch (loc, (cD1, cG1, ps1, e''), elFBranch cD cG fbr' theta_tau)

(* ******************************************************************************* *)
(* TOP LEVEL                                                                       *)


let solve_fvarCnstr = Lfrecon.solve_fvarCnstr
let reset_fvarCnstr = Lfrecon.reset_fvarCnstr

let kind = Lfrecon.elKind Int.LF.Empty Int.LF.Null

let typ rectyp apxT = Lfrecon.elTyp rectyp Int.LF.Empty Int.LF.Null apxT

let schema = elSchema

let mctx = elMCtx Lfrecon.Pibox

let compkind = elCompKind Int.LF.Empty

let comptyp_cD cD tau =
  let tau' = elCompTyp cD tau in
  let _ = Lfrecon.solve_constraints cD in
  dprintf
    begin fun p ->
    p.fmt "[elCompTyp] @[%a@]"
      (P.fmt_ppr_cmp_typ cD P.l0) tau'
    end;
  tau'

let comptyp tau = comptyp_cD Int.LF.Empty tau

let comptypdef loc a (tau, cK) =
  let cK = elCompKind Int.LF.Empty cK in
  let _  = (solve_fvarCnstr Lfrecon.Pibox;
            Unify.forceGlobalCnstr (!Unify.globalCnstrs)) in
  let (cK,i) = Abstract.compkind cK in
  reset_fvarCnstr ();
  Unify.resetGlobalCnstrs ();
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
