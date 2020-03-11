open Support.Equality
(**

   @author Brigitte Pientka
*)

open Support
open Store
open Store.Cid
open Syntax
open Substitution
open Id
open ConvSigma

module F = Misc.Function

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail
module C     = Whnf

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

module A = Syntax.Apx.Comp
module I = Syntax.Int.Comp

let strengthen : bool ref =  Lfrecon.strengthen

let dprintf, dprint, dprnt = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

type case_label_variant = [ `named | `context | `pvar | `bvar ]

type error =
  | IllegalCase         of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.typ
  | ClosedTermRequired  of Int.LF.mctx * Int.Comp.gctx * Int.Comp.exp_syn * Int.Comp.typ
  | MetaObjContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.dctx
  | PatternContextClash of Int.LF.mctx * Int.LF.dctx * Int.LF.mctx * Int.LF.dctx
  | MetaObjectClash     of Int.LF.mctx * (Int.Comp.meta_typ)
  | MissingMetaObj
  | TooManyMetaObj
  | TypeAbbrev         of Id.name
  | PatternMobj
  | UnsupportedTypeAnnotation
  | MCtxIllformed of Int.LF.mctx
  | TypMismatch        of Int.LF.mctx * Int.Comp.tclo * Int.Comp.tclo
  | IllegalSubstMatch
  | InvalidHypotheses  of Int.Comp.hypotheses (* expected *)
                          * Int.Comp.hypotheses (* actual *)
  | InvalidSchemaElementIndex of int * Id.cid_schema
  | UnboundCaseLabel of [ `comp | `meta ] * Id.name * Int.LF.mctx * Int.Comp.typ
  | CaseLabelMismatch of case_label_variant (* expected *)
                         * case_label_variant (* actual *)
  | NotImplemented of (Format.formatter -> unit -> unit)

exception Error of Syntax.Loc.t * error
let throw loc e = raise (Error (loc, e))

let _ = Error.register_printer
  begin fun (Error (loc, err)) ->
  Error.print_with_location loc
    begin fun ppf ->
    let open Format in
    fprintf ppf "Type reconstruction error.@.";
    match err with
    | NotImplemented f ->
       fprintf ppf "@[<v 2>Not implemented:@,@[%a@]@]"
         f ()
    | MCtxIllformed cD ->
       fprintf ppf "Unable to abstract over the free meta-variables due to dependency on the specified meta-variables. The following meta-context was reconstructed, but is ill-formed: %a"
         (P.fmt_ppr_lf_mctx P.l0) cD
    | UnsupportedTypeAnnotation ->
       fprintf ppf
         "Type annotations on context variables and parameter variables not supported at this point."
    | PatternMobj ->
       fprintf ppf
         "Expected a meta-object; Found a computation-level pattern"
    | TypeAbbrev a ->
       fprintf ppf
         "Type definition %s cannot contain any free meta-variables in its type."
         (Id.render_name a)

    | IllegalCase (cD, cG, i, tau) ->
       fprintf ppf
         "@[<v>Illegal case analysis.\
          @,Cannot pattern-match on expression\
          @,  @[%a@]\
          @,of type\
          @,  @[%a@]\
          @]"
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
         (P.fmt_ppr_cmp_typ cD P.l0) tau

    | ClosedTermRequired (cD, cG, i, tau) ->
       fprintf ppf
         "Expression is not closed.\
          @,The expression\
          @,  @[%a@]\
          @,has type\
          @,  @[%a@]\
          @,@[%a@]\
          @,Meta-context:\
          @,  @[%a@]\
          @,Computation context:\
          @,  @[%a@]\
          @]"
         P.(fmt_ppr_cmp_exp_syn cD cG l0) i
         P.(fmt_ppr_cmp_typ cD l0) tau
         pp_print_string
         "which is not closed, or which requires that some \
          metavariables are futher \
          restricted, i.e. some variable dependencies cannot happen.
          This error may indicate that some reconstructed implicit
          arguments should be restricted."
         P.(fmt_ppr_lf_mctx l0) cD
         P.(fmt_ppr_cmp_gctx cD l0) cG

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
       fprintf ppf
         "Note that we do not allow the context in the pattern@ \
          to be more general than the context in the scrutinee."

    | MetaObjectClash (cD, mC) ->
       fprintf ppf
         "Meta-object type clash.@ \
          Expected meta-object of type: %a"
         (P.fmt_ppr_cmp_meta_typ cD) mC;

    | MissingMetaObj      ->
       fprintf ppf
         "Too few meta-objects supplied to data-constructor"

    | TooManyMetaObj      ->
       fprintf ppf
         "Too many meta-objects supplied to data-constructor"

    | TypMismatch (cD, (tau1, theta1), (tau2, theta2)) ->
       Error.report_mismatch ppf
         "Type of destructor did not match the type it was expected to have."
         "Type of destructor" (P.fmt_ppr_cmp_typ cD P.l0)
         (Whnf.cnormCTyp (tau1, theta1))
         "Expected type" (P.fmt_ppr_cmp_typ cD P.l0)
         (Whnf.cnormCTyp (tau2, theta2))

    | CaseLabelMismatch (expected, actual) ->
       let print_case_label_kind ppf = function
         | `named -> fprintf ppf "named"
         | `context -> fprintf ppf "context"
         | `pvar -> fprintf ppf "parameter variable"
         | `bvar -> fprintf ppf "head bound variable"
       in
       fprintf ppf
         "@[<v>Case label mismatch.\
          @,Expected case label type: %a\
          @,Actual case label type: %a\
          @,@]"
         print_case_label_kind expected
         print_case_label_kind actual

    | UnboundCaseLabel (kind, name, cD, tau) ->
       let print_case_label_kind ppf = function
         | `meta -> fprintf ppf "LF"
         | `comp -> fprintf ppf "computational"
       in
       fprintf ppf
         "@[<v>Unbound constructor @[%a@].\
          @,@[A %a constructor is expected, due to the type of the scrutinee, namely@]\
          @,  @[%a@]
          @]"
         Id.print name
         print_case_label_kind kind
         P.(fmt_ppr_cmp_typ cD l0) tau

    | InvalidHypotheses (exp, act) ->
       fprintf ppf
         "@[<v>Invalid hypotheses.\
          @,Expected hypotheses:\
          @,  @[%a@]
          @,Actual hypotheses:\
          @,  @[%a@]
          @]"
         P.fmt_ppr_cmp_hypotheses_listing exp
         P.fmt_ppr_cmp_hypotheses_listing act

    | InvalidSchemaElementIndex (n, w) ->
       let Int.LF.Schema elems as schema = Store.Cid.Schema.get_schema w in
       fprintf ppf
         "@[<v>The 1-based index %d is invalid for the schema\
          @,  @[%a@]\
          @,which consists of %d only elements.
          @]"
         n
         P.(fmt_ppr_lf_schema ~useName: false l0) schema
         (List.length elems)
    end
  end


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
  | IndexObj of Int.Comp.pattern * Int.Comp.meta_obj
  | DataObj

(** Decides what the case type is. *)
let case_type pat i =
  match i with
  | Int.Comp.AnnBox (mC, _) ->
     IndexObj (Lazy.force pat, mC)
  | _ -> DataObj

let map_case_type f = function
  | DataObj -> DataObj
  | IndexObj (pat, mC) ->
     let (pat', mC') = f (pat, mC) in
     IndexObj (pat', mC')

(** Elaborates the given numeric induction order by skipping implicit
    parameters in the given type.
 *)
let elNumericOrder (tau : I.typ) (order : Ext.Comp.numeric_order)
    : I.order =
  (** skip tau n uses n units of fuel to travel through the type tau.
      A fuel unit is spent to cross an explicit function type, but
      crossing an implicit pi-type costs nothing.
      The returned integer is the argument number we end up at,
      counting implicits too.
   *)
  let rec skip tau n =
    match tau, n with
    | _, 0 -> 0
    | I.TypPiBox (_, Int.LF.Decl (u, cU, dep), tau), n ->
       begin match dep with
       | Int.LF.Inductive ->
          Error.violation "[elaborate_numeric_order] impossible LF.Inductive"
       | Int.LF.Maybe ->
          1 + skip tau n (* implicits are free *)
       | Int.LF.No ->
          1 + skip tau (n - 1) (* explicits pi-types cost 1 *)
       end
    | I.TypArr (_, _, tau), n ->
       1 + skip tau (n - 1) (* simple functions cost 1 *)
  in
  Ext.Comp.map_order (skip tau) order
  |> Order.of_numeric_order

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
      let { Schema.Entry.name; schema } = Schema.get s_cid in
      let c_var = Lfrecon.elCtxVar c_var in
      Int.LF.CtxVar (c_var)
      |> F.through (fun cPsi' -> Check.LF.checkSchema loc cD cPsi' name schema)

  | Apx.LF.CtxVar (Apx.LF.CtxName psi ) ->
      (* This case should only be executed when c_var occurs in a pattern *)
     begin
       try
         let (_ , Int.LF.Decl (_, Int.LF.CTyp (Some s_cid'), _)) = FCVar.get psi in
         if Id.cid_equals s_cid s_cid' then
           Int.LF.CtxVar (Int.LF.CtxName psi)
         else
           let { Schema.Entry.name; schema } = Schema.get s_cid in
           let c_var' = Int.LF.CtxName psi in
           Check.LF.(CtxVarMismatch (cD, c_var', name, schema) |> throw (Id.loc_of_name psi))
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
    | (Int.LF.CtxVar (Int.LF.CtxName g) , Apx.LF.CtxVar (Apx.LF.CtxName h))
         when Id.equals g h -> ()

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
  dprintf begin fun p ->
    p.fmt "[mgAtomicTyp] @[<v>flat cPsi = @[%a@]\
           @,s_proj = @[%a@]@]"
      P.(fmt_ppr_lf_dctx cD l0) flat_cPsi
      P.(fmt_ppr_lf_sub cD cPsi l0) s_proj
    end;
  let thinned =
    lazy
      begin
        let (ss', cPhi') = Subord.thin' cD a flat_cPsi in
        (* cPhi |- ss' : cPhi' *)
        dprintf begin fun p ->
          p.fmt "[mgAtomicTyp] @[<v>thinning constructed weakening\
                 @,@[%a@]\
                 @,for type %a@]"
            P.fmt_ppr_lf_sub_typing (cD, flat_cPsi, ss', cPhi')
            (P.fmt_ppr_lf_typ Int.LF.Empty Int.LF.Null P.l0) Int.LF.(Atom (Loc.ghost, a, Nil))
          end;
        let ssi' = LF.invert ss' in
        (* cPhi' |- ssi : cPhi *)
        (* cPhi' |- [ssi]tQ    *)
        let ss_proj = LF.comp ss' s_proj in
        (cPhi', ssi', ss_proj)
      end
  in

  let rec genSpine sK = match sK with
    | (Int.LF.Typ, _s) ->
        Int.LF.Nil

    | (Int.LF.PiKind ((Int.LF.TypDecl (_n, tA1), dep ), kK), s) ->
        let tA1' = strans_typ cD cPsi (tA1, s) conv_list in
        let tR    =
          if !strengthen then
            let lazy (cPhi', ssi', ss_proj) = thinned in
            dprintf begin fun p ->
              p.fmt "[mgAtomicTyp] PiKind ssi' = @[%a@]"
                P.(fmt_ppr_lf_sub cD cPhi' l0) ssi'
              end;
            Whnf.etaExpandMMV Syntax.Loc.ghost cD cPhi' (tA1', ssi') _n ss_proj dep
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
      mgAtomicTyp cD cPsi a (Typ.get a).Typ.Entry.kind

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
     dprint (fun () -> "[ElClObj] ELABORATION MObj DONE");
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
     Whnf.mmVarToClObj loc mV mtyp

  (* ordinary parameter variable elaboration *)
  | Apx.LF.Dot (Apx.LF.Obj (Apx.LF.Root (_, h, Apx.LF.Nil) as tM), Apx.LF.EmptySub)
  , Int.LF.PTyp tA' ->
     let Int.LF.Root (_, h, Int.LF.Nil, _) =
       Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA', LF.id)
     in
     Int.LF.PObj h

  (* ordinary parameter variable elaboration *)
  | Apx.LF.Dot (Apx.LF.Head h, Apx.LF.EmptySub)
  , Int.LF.PTyp tA' ->
     let tM = Apx.LF.Root (Loc.ghost, h, Apx.LF.Nil) in
     let Int.LF.Root (_, h, Int.LF.Nil, _) =
       Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA', LF.id)
     in
     Int.LF.PObj h
  | Apx.LF.Dot (Apx.LF.Head h, Apx.LF.EmptySub)
  , Int.LF.MTyp tA' ->
     let tM = Apx.LF.Root (Loc.ghost, h, Apx.LF.Nil) in
     let m = Lfrecon.elTerm Lfrecon.Pibox cD cPsi' tM (tA', LF.id) in
     Int.LF.MObj m

  | _, _ ->
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
        (P.fmt_ppr_cmp_meta_typ cD) ctyp
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

  | (s, (Int.Comp.PiKind (loc', Int.LF.Decl (u, cU, Int.LF.Maybe), cK), t)) ->
    let (mO,t') = Whnf.dotMMVar loc cD t (u, cU, Int.LF.Maybe) in
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
      let tK = (CompTyp.get a).CompTyp.Entry.kind in
      dprintf
        begin fun p ->
        p.fmt "[elCompTyp] of kind: %a"
          (P.fmt_ppr_cmp_kind cD P.l0) tK
        end;
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypBase (loc, a ,cS')

| Apx.Comp.TypCobase (loc, a, cS) ->
      let _ = dprint (fun () -> "[elCompCotyp] Cobase : " ^ R.render_cid_comp_cotyp a) in
      let tK = (CompCotyp.get a).CompCotyp.Entry.kind in
      dprintf
        begin fun p ->
        p.fmt "[elCompCotyp] of kind: %a"
          (P.fmt_ppr_cmp_kind cD P.l0) tK
        end;
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
        Int.Comp.TypCobase (loc, a ,cS')

  | Apx.Comp.TypDef (loc, a, cS) ->
      let tK = (CompTypDef.get a).CompTypDef.Entry.kind in
      let cS' = elMetaSpine loc cD cS (tK, C.m_id) in
      let tau = (CompTypDef.get a).CompTypDef.Entry.typ in
        (* eager expansion of type definitions - to make things simple for now
           -bp *)
      let ms = spineToMSub cS' (Int.LF.MShift 0) in
        Whnf.cnormCTyp (tau, ms)
        (* Int.Comp.TypDef (loc, a, cS') *)

  | Apx.Comp.TypBox (loc, (_, cU)) ->
     dprintf
       begin fun p ->
       p.fmt "[elCompTyp] TypBox at %a" Loc.print_short loc
       end;
     let cU = elCTyp Lfrecon.Pibox cD cU in
     I.TypBox (loc, cU)

  | Apx.Comp.TypArr (loc, tau1, tau2) ->
      let tau1' = elCompTyp cD tau1 in
      let tau2' = elCompTyp cD tau2 in
        Int.Comp.TypArr (loc, tau1', tau2')

  | Apx.Comp.TypCross (loc, tau1, tau2) ->
      let tau1' = elCompTyp cD tau1 in
      let tau2' = elCompTyp cD tau2 in
        Int.Comp.TypCross (loc, tau1', tau2')

  | Apx.Comp.TypPiBox (loc, cdecl, tau) ->
      let cdecl' = elCDecl Lfrecon.Pibox cD cdecl  in
      let tau'   = elCompTyp (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox (loc, cdecl', tau')

  | Apx.Comp.TypInd tau -> Int.Comp.TypInd (elCompTyp cD tau)

(* *******************************************************************************)

let mgCompTypSpine cD (loc, cK) =
  let rec genMetaSpine (cK, t) = match (cK, t) with
    | (Int.Comp.Ctype _, _t) -> Int.Comp.MetaNil
    | (Int.Comp.PiKind (loc', Int.LF.Decl(u, cU, dep), cK), t) ->
       let (mO, t') = Whnf.dotMMVar loc cD t (u, cU, dep) in
       let mS = genMetaSpine (cK, t') in
       Int.Comp.MetaApp (mO, mS)
  in
  genMetaSpine (cK, Whnf.m_id)

let mgCompCotyp cD (loc, c) =
  let cK = (CompCotyp.get c).CompCotyp.Entry.kind in
  let mS = mgCompTypSpine cD (loc, cK) in
  dprintf
    begin fun p ->
    p.fmt "[mgCompTyp] @[<v>kind of constant %s@,%a@]"
      (R.render_cid_comp_cotyp c)
      (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK
    end;
  Int.Comp.TypCobase (loc, c, mS)

let mgCompTyp cD (loc, c) =
  let cK = (CompTyp.get c).CompTyp.Entry.kind in
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
  | Int.Comp.TypCross (loc, tau1, tau2) ->
     let tau1' = inferPatTyp' cD' (cD_s, tau1) in
     let tau2' = inferPatTyp' cD' (cD_s, tau2) in
     Int.Comp.TypCross (loc, tau1', tau2')

  | Int.Comp.TypBase (loc, c, _ )  -> mgCompTyp cD' (loc, c)

  | Int.Comp.TypCobase (loc, c, _ )  ->
     dprintf (fun p -> p.fmt "[inferPatTyp'] inferring type of cobase");
     mgCompCotyp cD' (loc, c)

  | Int.Comp.TypArr (loc, tau1, tau2)  ->
     let tau1' = inferPatTyp' cD' (cD_s, tau1) in
     let tau2' = inferPatTyp' cD' (cD_s, tau2) in
     Int.Comp.TypArr (loc, tau1', tau2')

  | Int.Comp.TypPiBox (loc, (Int.LF.Decl (x, mtyp,dep)), tau) ->
     let mtyp' = mgCTyp cD' cD_s mtyp in
     let tau'  = inferPatTyp' (Int.LF.Dec (cD', Int.LF.Decl(x, mtyp',dep)))
                   (Int.LF.Dec (cD_s, Int.LF.Decl(x, mtyp,dep)), tau) in
     Int.Comp.TypPiBox (loc, Int.LF.Decl (x, mtyp',dep), tau')

  | Int.Comp.TypBox (loc, mtyp)  ->
     let mtyp' = mgCTyp cD' cD_s mtyp in
     Int.Comp.TypBox (loc, mtyp')

  | Int.Comp.TypInd typ -> inferPatTyp' cD' (cD_s, typ)

  | _ ->
     let s = Support.Fmt.stringify (P.fmt_ppr_cmp_typ cD_s P.l0) tau_s in
     Error.violation ("uninferrable pattern type for: " ^ s)

let inferPatTyp cD' (cD_s, tau_s) = inferPatTyp' cD' (cD_s, Whnf.cnormCTyp (tau_s, Whnf.m_id))

(** See documentation in reconstruct.mli *)
let synPatRefine loc caseT (cD, cD') t (tau_s, tau_p) =
  let unifyPatternType tau_s' tau_p' =
    dprintf
      begin fun p ->
      p.fmt "[synPatRefine] @[<v>unifying scrutinee and pattern types:@,\
             @[<v>@[%a@]@,===@,@[%a@]@]@]"
        (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau_s'
        (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau_p'
      end;
    try
      Unify.unifyCompTyp Int.LF.Empty (tau_s', Whnf.m_id) (tau_p', Whnf.m_id)
    with
      Unify.Failure msg ->
       (* XXX there's no way this error is formatted correctly -je *)
       raise (Check.Comp.Error (loc, Check.Comp.SynMismatch (cD, (tau_s', Whnf.m_id), (tau_p', Whnf.m_id))))
  in
  let unifyScrutinee tau_p' t1 t1t =
    match caseT with
    | DataObj -> () (* not dependent pattern matching; nothing to do *)
    | IndexObj (Int.Comp.(PatMetaObj (_, mC_p) | PatAnn (_, PatMetaObj (_, mC_p), _, _)), mC) ->
       let mC_p = Whnf.(cnormMetaObj (mC_p, m_id)) in
       (* tau_p' _has_ to be a box type if caseT is an IndexObj  *)
       let Int.Comp.TypBox (_, mT) = tau_p' in
       dprintf
         begin fun p ->
         p.fmt "[synPatRefine] @[<v>unifying scrutinee and pattern:\
                @,mC    = @[%a@]\
                @,mC_p  = @[%a@]\
                @,cD    = @[%a@]@]"
           (P.fmt_ppr_cmp_meta_obj cD P.l0) mC
           (P.fmt_ppr_cmp_meta_obj cD' P.l0) mC_p
           P.(fmt_ppr_lf_mctx l0) cD
         end;
       try
         Unify.unifyMetaObj Int.LF.Empty
           (Whnf.cnormMetaObj (mC, t), t1)
           (mC_p, t1t)
           (mT, Whnf.m_id)
       with
         Unify.Failure msg ->
         Error.violation
           ("Dependent pattern matching failed at "
            ^ Fmt.stringify Loc.print_short loc ^ ": " ^ msg)
  in
  let t1 = Ctxsub.mctxToMSub cD' in (* . |- t1 : cD' *)
  let t1t = Whnf.mcomp t t1 in (* . |- t1t : cD  since  cD' |- t : cD  and  t1t = t mcomp t1 *)
  let tau_s' = Whnf.cnormCTyp (tau_s, t1t) in (* . |- tau_s' <= type *)
  let tau_p' = Whnf.cnormCTyp (tau_p, t1) in (* . |- tau_p' <= type *)
  unifyPatternType tau_s' tau_p'; (* . |- tau_s' === tau_p' <= type *)
  unifyScrutinee tau_p' t1 t1t;
  let t1', cD'' = Abstract.msub (Whnf.cnormMSub t1) in
  let t' = Whnf.mcomp t t1' in
  (* let pat' = Whnf.cnormPattern (pat, t1') in *)
  (t', t1', cD'')

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
  | (Apx.Comp.Fn (loc, x, e), (Int.Comp.TypArr (_, tau1, tau2), theta)) ->
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
  | ( Apx.Comp.MLam (loc, u, e)
    , (Int.Comp.TypPiBox(_, (Int.LF.Decl (_,_,Int.LF.No) as cdec), tau), theta)
    ) ->
     let cD' = extend_mctx cD (u, cdec, theta) in
     let cG' = Whnf.cnormGCtx (cG, Int.LF.MShift 1) in
     let e' = elExp cD' cG' e (tau, C.mvar_dot1 theta) in
     Int.Comp.MLam (loc, u, e', `explicit)

  | ( e
    , (Int.Comp.TypPiBox(_, (Int.LF.Decl(_,_,Int.LF.Maybe) as cdec), tau), theta)
    ) ->
     let u = mk_name_cdec cdec in
     let cG' = Whnf.cnormGCtx (cG, Int.LF.MShift 1) in
     let cD' = extend_mctx cD (u, cdec, theta) in
     let e' = Apxnorm.cnormApxExp cD (Apx.LF.Empty) e (cD', Int.LF.MShift 1) in
     let e' = elExp cD' cG' e' (tau, C.mvar_dot1 theta) in
     Int.Comp.MLam (Syntax.Loc.ghost, u , e', `implicit)

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
      p.fmt "[elExp] @[<v>Syn i = @[%a@]@,done: @[%a@]@]"
        (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i1, Whnf.m_id))
        P.fmt_ppr_cmp_typ_typing (cD, Whnf.cnormCTyp tau1)
      end;
    let (_, (i', tau_t')) =
      Check.Comp.genMApp loc F.(not ++ Int.LF.is_explicit) cD (i1, tau1)
    in
    dprintf
      begin fun p ->
      p.fmt "[elExp] @[<v>Unify computation-level types:@,  @[@[%a@]@ ==@ @[%a@]@]@]"
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


  | (Apx.Comp.Pair(loc, e1, e2), (Int.Comp.TypCross (_, tau1, tau2), theta)) ->
      let e1' = elExp cD cG e1 (tau1, theta) in
      let e2' = elExp cD cG e2 (tau2, theta) in
        Int.Comp.Pair (loc, e1', e2')

  | (Apx.Comp.LetPair (loc, i, (x, y, e)), (tau, theta)) ->
      let (i', tau_theta') = elExp' cD cG i in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypCross (_, tau1, tau2), t) ->
             let cG' =
               Int.LF.Dec
                 ( Int.LF.Dec
                     ( cG
                     , Int.Comp.CTypDecl (x,  Whnf.cnormCTyp (tau1, t), false)
                     )
                 , Int.Comp.CTypDecl (y, Whnf.cnormCTyp (tau2, t), false)
                 )
             in
             let e' = elExp cD cG' e (tau, theta) in
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
     let cM = elMetaObj cD cM (cT, theta) in
     let cU = Whnf.cnormMTyp (cT, theta) in
     Int.Comp.Box (loc, cM, cU)

  | Apx.Comp.Impossible (loc, i), (tau, theta) ->
     let i', ttau' = elExp' cD cG i in
     let _, (i', _) =
       Check.Comp.genMApp loc F.(not ++ Int.LF.is_explicit) cD (i', ttau')
     in
     (* Not sure if we need to work any harder at this point, since we
        don't have any branches to elaborate. *)
     Int.Comp.Impossible (loc, i')

  | (Apx.Comp.Case (loc, prag, i, branches), ttau) ->
     dprintf (fun p -> p.fmt "[elExp] case at %a" Loc.print_short loc);
     dprintf (fun p -> p.fmt "[elExp] elaborating scrutinee");
     let (i', ttau') =  (elExp' cD cG i) in
     dprintf
       begin fun p ->
       p.fmt "[elExp] @[<v>case on @[@[%a@]@ @[%a@]@]@,cD = @[%a@]@,cG = @[%a@]@]"
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) (Whnf.cnormExp' (i', Whnf.m_id))
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau')
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_cmp_gctx cD P.l0) cG
       end;
     let _, (i, ttau') =
       Check.Comp.genMApp loc F.(not ++ Int.LF.is_explicit) cD (i', ttau')
     in
     let i = Whnf.(cnormExp' (i, m_id)) in
     let tau_s = Whnf.cnormCTyp ttau' in
     let ct = fun pat -> case_type pat i in

     if not Whnf.(closedExp' i && closedCTyp tau_s && closedGCtx cG) then
       raise (Error (loc, ClosedTermRequired (cD, cG, i, tau_s)));

     let branches' =
       List.map
         begin fun b ->
         elBranch ct cD cG b tau_s ttau
         |> F.after Gensym.MVarData.reset
         end
         branches
     in
     Int.Comp.Case (loc, prag, i, branches')

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
       and generate a PObj/PTyp instead of an MObj/MTyp?
       Currently this is detected during typechecking, only to make
       sure we generate the appropriate cases during coverage
       checking.
       -je
       EDIT: generating a PTyp here will cause unification failures
       later because PTyp cannot unify with MTyp. It's not clear
       whether such failure is _really_ necessary, but it would be
       suspect if unification didn't make its inputs equal on success.
       It depends on whether one considers PTyp/MTyp distinction as
       metadata or whether it's morally part of the type.
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
     let tau = (CompConst.get c).CompConst.Entry.typ in
     dprintf
       begin fun p ->
       p.fmt "[elExp'] @[<v>DataConst %s has type@,@[%a@]@]"
         (R.render_cid_comp_const c)
         P.fmt_ppr_cmp_typ_typing (cD, tau)
       end;
     (Int.Comp.DataConst (loc, c), (tau, C.m_id))

  | Apx.Comp.Obs (loc, e, obs) ->
    let cD' = (CompDest.get obs).CompDest.Entry.mctx in
    let t    = Ctxsub.mctxToMMSub cD cD' in
    let tau0 = (CompDest.get obs).CompDest.Entry.obs_type in
    let tau1 = (CompDest.get obs).CompDest.Entry.return_type in
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
     (Int.Comp.Const (loc,prog), ((Comp.get prog).Comp.Entry.typ, C.m_id))

  | Apx.Comp.Apply (loc, i, e) ->
     dprintf
       (fun p ->
         p.fmt "[elExp'] Apply at @[%a@]" Loc.print_short loc);
     let i' = elExp' cD cG i in
     dprintf begin fun p ->
       p.fmt "[elExp'] @[<v>genMApp for@,@[<hv 2>i' =@ @[%a@]@]@]"
         P.(fmt_ppr_cmp_exp_syn cD cG l0) (fst i')
       end;
     let k, (i', tau_theta') =
       Check.Comp.genMApp loc F.(not ++ Int.LF.is_explicit) cD i'
     in
     dprintf
       begin fun p ->
       p.fmt "[elExp'] @[<v>Apply - generated %d implicit arguments:@,\
              i' = @[%a@]@]"
         k
         P.(fmt_ppr_cmp_exp_syn cD cG l0) i'
       end;
     begin match e , tau_theta' with
     | e , (Int.Comp.TypArr (loc', tau2, tau), theta) ->
        dprintf
          begin fun p ->
          p.fmt "[elExp'] @[<v>i' = @[%a@]@,inferred type: @[%a@]@,\
                 check argument has type: @[%a@]@,\
                 result has type: @[%a@]@]"
            (P.fmt_ppr_cmp_exp_syn cD cG P.l0)
            (Whnf.cnormExp' (i', Whnf.m_id))
            (P.fmt_ppr_cmp_typ cD P.l0)
            (Whnf.cnormCTyp (Int.Comp.TypArr (loc', tau2, tau), theta))
            (P.fmt_ppr_cmp_typ cD P.l0)
            (Whnf.cnormCTyp (tau2,theta))
            (P.fmt_ppr_cmp_typ cD P.l0)
            (Whnf.cnormCTyp (tau,theta))
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

     | Apx.Comp.Box (_,mC) , (Int.Comp.TypPiBox (_, Int.LF.Decl(_,ctyp,_), tau), theta) ->
        dprintf begin fun p ->
          p.fmt "[elExp'] @[<v>Apply -> elMetaObj at type\
                 @,@[%a@]@]"
            P.(fmt_ppr_cmp_meta_typ cD) (Whnf.cnormMTyp (ctyp, theta))
          end;
        let cM = elMetaObj cD mC (ctyp, theta) in
        ( Int.Comp.MApp (loc, i', cM, Whnf.cnormMTyp (ctyp, theta), `explicit)
        , (tau, Int.LF.MDot (metaObjToFt cM, theta)))
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
               NotImplemented
                 begin fun ppf _ ->
                 Format.fprintf ppf
                   "@[<v>More sophisticated inference for context schemas.\
                    @,In general, schemas cannot be uniquely inferred.@]"
                 end
               |> throw loc
          end
     end

  | Apx.Comp.PairVal (loc, i1, i2) ->
     let f = F.(not ++ Int.LF.is_explicit) in
     let _, (i1', (tau1,t1)) = Check.Comp.genMApp loc f cD (elExp' cD cG i1) in
     let _, (i2', (tau2,t2)) = Check.Comp.genMApp loc f cD (elExp' cD cG i2) in
     ( Int.Comp.PairVal (loc, i1', i2')
     , ( Int.Comp.TypCross (loc, Whnf.cnormCTyp (tau1,t1), Whnf.cnormCTyp (tau2,t2)),
         C.m_id
       )
     )

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
     raise (Error (loc, PatternContextClash (cD', cPsi', cD, cPsi)))

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
  | Apx.Comp.PatAnn (loc, _, _) -> raise (Error (loc, UnsupportedTypeAnnotation))

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

  | (Apx.Comp.PatPair (loc, pat1, pat2) , (Int.Comp.TypCross (_, tau1, tau2), theta)) ->
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
        (cG', Int.Comp.PatAnn (loc, pat', tau', `explicit), (tau', Whnf.m_id))

  | Apx.Comp.PatConst (loc, c, pat_spine) ->
      let tau = (CompConst.get c).CompConst.Entry.typ in
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
        | (Int.Comp.TypPiBox (_, Int.LF.Decl (u, cU, Int.LF.Maybe), tau), t) ->
          let (mO,t') = Whnf.dotMMVar loc cD t (u, cU, Int.LF.Maybe) in
          let pat'  = Int.Comp.PatMetaObj (loc, mO) in
          let ttau' = (tau, t') in
          let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
              (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)
          | _ ->   (cG, Int.Comp.PatNil, ttau))

  | Apx.Comp.PatApp (loc, pat', pat_spine')  ->
      begin match ttau with
      | (Int.Comp.TypArr (_, tau1, tau2), theta) ->
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>ttau = @[%a@]@,ttau1 = @[%a@]@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp (tau1, theta))
           end;
         let (cG', pat) = elPatChk cD cG pat' (tau1, theta) in
         let (cG'', pat_spine, ttau2) = elPatSpine cD cG' pat_spine' (tau2, theta) in
         (cG'', Int.Comp.PatApp (loc, pat, pat_spine), ttau2)
      | (Int.Comp.TypPiBox (_, (Int.LF.Decl (u, cU, Int.LF.Maybe)), tau), theta) ->
         dprintf
           begin fun p ->
           p.fmt "[elPatSpine] @[<v>TypPiBox implicit ttau =@,@[%a@]@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
           end;
         let (mO,t') = Whnf.dotMMVar loc cD theta (u, cU, Int.LF.Maybe) in
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

      | (Int.Comp.TypPiBox (_, Int.LF.Decl (_,ctyp,dep), tau), theta) ->
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
      let cD' = (CompDest.get obs).CompDest.Entry.mctx in
       dprintf
         begin fun p ->
         let name = (CompDest.get obs).CompDest.Entry.name in
         p.fmt "[elPatSpine] @[<v>Observation: %a@,cD = @[%a@]@,cD' = @[%a@]@]"
           Id.print name
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_lf_mctx P.l0) cD'
         end;
      let tau0 = (CompDest.get obs).CompDest.Entry.obs_type in
      let tau1 = (CompDest.get obs).CompDest.Entry.return_type in
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
    | (Int.Comp.TypPiBox (_, Int.LF.Decl (u, cU, Int.LF.Maybe), tau), theta) ->
     let (mO,t') = Whnf.dotMMVar loc cD theta (u, cU, Int.LF.Maybe) in
     let pat'  = Int.Comp.PatMetaObj (loc, mO) in
     let ttau' = (tau, t') in
     let (cG', pat_spine', ttau2) = elPatSpine cD cG pat_spine ttau' in
     (cG', Int.Comp.PatApp (loc, pat', pat_spine' ), ttau2)
    (* | _ -> raise (Error (loc, TypMismatch (cD, ttau, (tau1, Whnf.m_id)))) *)
 end



and recPatObj' cD pat (cD_s, tau_s) = match pat with
  | Apx.Comp.PatAnn
    ( l
    , (Apx.Comp.PatMetaObj (loc, _) as pat')
    , Apx.Comp.TypBox (loc', (_,Apx.LF.ClTyp(Apx.LF.MTyp a, psi)))
    ) ->
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
     (cG', Int.Comp.PatAnn (l, pat', tau', `explicit), ttau')

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
      let (loc', clTyp) =
        (* infer the cltyp *)
        match tau_s with
        | Int.Comp.TypBox (loc', Int.LF.ClTyp (mT, cPsi)) ->
           begin match mT with
           | Int.LF.(MTyp (Atom _ | Sigma _ as tA))->
              let cPsi' = inferCtxSchema loc (cD_s, cPsi) (cD, psi) in
              let tP'   = mgTyp cD cPsi' tA in
              loc', Int.LF.ClTyp (Int.LF.MTyp tP', cPsi')
           | Int.LF.(MTyp (PiTyp _)) ->
              Error.violation "[recPatObj'] scrutinee PiTyp is forbidden"
           | Int.LF.STyp (sv_class, cPhi) ->
              let cPsi' = mgCtx cD (cD_s, cPsi) in
              let cPhi' = mgCtx cD (cD_s, cPhi) in
              loc', Int.LF.ClTyp (Int.LF.STyp (sv_class, cPhi'), cPsi')
              (* Are the other cases (PTyp, or MTyp of a non-atomic
                 type) impossible?
                 Or can a user somehow write such a pattern, and we
                 should generate an error?
                 -je
               *)
           | Int.LF.PTyp _ ->
              Error.violation "[recPatObj'] scrutinee PTyp should be impossible"
           end
        | Int.Comp.TypBox (loc', mT) -> raise (Error (loc, MetaObjectClash (cD, mT)))
        | _ ->  raise (Check.Comp.Error (loc, Check.Comp.BasicMismatch (`box, cD_s, Int.LF.Empty, (tau_s, Whnf.m_id))))
        (* inferClTyp cD psi (cD_s, tau_s) *)
      in
      let tau_p = Int.Comp.TypBox (loc', clTyp) in
      let ttau' = (tau_p, Whnf.m_id) in
      let (cG', pat')  = elPatChk cD Int.LF.Empty pat ttau' in
      (* here the annotation is implicit because it did not appear in
         the user-supplied syntax; we just reconstructed it. *)
      (cG', Int.Comp.PatAnn(loc, pat', tau_p, `implicit), ttau')

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

(* cD is the explicitly given user-context on the branch *)
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
  let (cD1, cG1, pat1, tau1) =
    Abstract.patobj loc cD (Whnf.cnormGCtx (cG', Whnf.m_id))
      pat'
      (Context.names_of_mctx cD_s)
      (Whnf.cnormCTyp ttau')
  in
  begin try
      Check.Comp.wf_mctx cD1 ;
      (* cD1 ; cG1 |- pat1 => tau1 (contains no free contextual variables) *)
      let l_cd1                  = Context.length cD1 in
      let l_delta                = Context.length cD  in
      ((l_cd1, l_delta), cD1, cG1,  pat1, tau1)
    with
      _ -> raise (Error (loc,MCtxIllformed cD1))
  end

and elBranch caseTyp cD cG branch tau_s (tau, theta) =
  match branch with
  | Apx.Comp.Branch (loc, delta, pat, e) ->
     dprintf
       begin fun p ->
         p.fmt "[elBranch] @[<v>type@,@[%a@]@,at %a@]"
           (P.fmt_ppr_cmp_typ cD P.l0) tau_s
           Loc.print_short loc
       end;
     let cD_prefix = elMCtx Lfrecon.Pibox delta in
     dprintf
       begin fun p ->
       p.fmt "[elBranch] @[<v>reconstruction of delta done : cD' (explicit) =@,@[%a@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD_prefix
       end;
     let ((l_cd1', l_delta), cD1', cG1,  pat1, tau1) =
       recPatObj loc cD_prefix pat (cD, tau_s)
     in
     dprintf
       begin fun p ->
       p.fmt "[recPatObj] @[<v>done@,\
              @[@[%a@] ; @[%a@] |-@ @[@[%a@]@ : @[%a@]@]@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD1'
         (P.fmt_ppr_cmp_gctx cD1' P.l0) cG1
         (P.fmt_ppr_cmp_pattern cD1' cG1 P.l0) pat1
         (P.fmt_ppr_cmp_typ cD1' P.l0) tau1
       end;
           (* ***************                            *************** *)
     (* cD |- tau_s and cD, cD1' |- tau_s' *)
     (* cD1' |- tau1 *)

     let cD' = Context.append cD cD1' in
     dprintf begin fun p ->
       p.fmt "[elBranch] @[<v>cD' =\
              @,@[<hv 2>cD =@ @[<hv>%a@]@]\
              @,PLUS\
              @,@[<hv 2>CD' =@ @[<hv>%a@]@]@]"
         P.(fmt_ppr_lf_mctx l0) cD
         P.(fmt_ppr_lf_mctx l0) cD1'
       end;

     let (t', t1, cD1'') =
       let t = Int.LF.MShift l_cd1' in
       (* since tau1 and pat1 make sense in cD1', they also make sense in cD'
          because cD' is obtained from cD by putting stuff *on the
          left*, so the indices are still valid. *)
       dprintf
         begin fun p ->
         p.fmt "[elBranch] @[<v>before synPatRefine:@,\
                cD = @[%a@]@,\
                cD' = @[%a@]@,\
                cD' |- t : cD = @[%a@]@,\
                pat1 = @[%a@]@,\
                tau_s = @[%a@]@,\
                tau1 = @[%a@]@]"
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_lf_mctx P.l0) cD'
           (P.fmt_ppr_lf_msub cD' P.l0) t
           (P.fmt_ppr_cmp_pattern cD' cG1 P.l0) pat1
           (P.fmt_ppr_cmp_typ cD P.l0) tau_s
           (P.fmt_ppr_cmp_typ cD' P.l0) tau1
         end;
       synPatRefine loc (caseTyp (lazy pat1)) (cD, cD') t (tau_s, tau1)
     in
     let pat1' = Whnf.cnormPattern (pat1, t1) in
     (*  cD1'' |- t' : cD    and   cD1'' |- t1 : cD, cD1' *)
     let l_cd1    = l_cd1' - l_delta  in   (* l_cd1 is the length of cD1 *)
     (*   cD1' |- cG1     cD1'' |- t1 : cD, cD1'    cD, cD1' |- ?   cD1' *)
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
     let cG1'    = Whnf.cnormGCtx ( (* Whnf.normGCtx *) cG1, t1) in
     dprintf
       begin fun p ->
       p.fmt "[elBranch] cD1'' |- cG1 = @[%a@]"
         (P.fmt_ppr_cmp_gctx cD1'' P.l0) cG1'
       end;
     let cG'     = Whnf.cnormGCtx ( (* Whnf.normGCtx *) cG, t') in
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
     Int.Comp.Branch (loc, cD_prefix, (cD1'', cG1'), pat1', t', eE')


and elFBranch cD cG fbr theta_tau = match fbr with
  | Apx.Comp.NilFBranch loc -> Int.Comp.NilFBranch loc
  | Apx.Comp.ConsFBranch (loc, (ps, e), fbr') ->
    let (cG', ps', ttau2) = elPatSpine cD cG ps theta_tau in
    let _ = Lfrecon.solve_constraints cD in
    let (cD1, cG1, ps1, tau1) =
      Abstract.pattern_spine loc cD (Whnf.cnormGCtx (cG', Whnf.m_id)) ps'
        (Context.names_of_mctx cD)
        (Whnf.cnormCTyp ttau2)
    in
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

(* elaborate gamma contexts *)
let rec elGCtx (delta : Int.LF.mctx) gamma =
  match gamma with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (gamma', Apx.Comp.CTypDecl (name, tau)) ->
     let cG = elGCtx delta gamma' in
     let tau' = elCompTyp delta tau in
     Int.LF.Dec (cG, Int.Comp.CTypDecl (name, tau', false))

let variant_of_case_label = function
  | A.NamedCase _ -> `named
  | A.ContextCase _ -> `context
  | A.PVarCase (_, _, _) -> `pvar
  | A.BVarCase _ -> `bvar

(* elaborate hypotheses *)
let elHypotheses { A.cD; cG } =
  let cD = elMCtx Lfrecon.Pibox cD in
  let cG = elGCtx cD cG in
  { I.cD ; cG ; cIH = Int.LF.Empty }

(** Verifies that the pairs of contexts are convertible. *)
let validateContexts loc (cD, cD') (cG, cG') : unit =
  if not Whnf.(convMCtx cD cD' && convGCtx (cG, m_id) (cG', m_id)) then
    let open I in
    InvalidHypotheses
      ( { cD; cG; cIH = Int.LF.Empty }
      , { cD = cD'; cG = cG'; cIH = Int.LF.Empty }
      )
    |> throw loc

(* elaborate hypothetical *)
let rec elHypothetical cD cG label hyp ttau =
  let { A.hypotheses = h; proof = p; hypothetical_loc = loc } = hyp in
  let { I.cD = cD'; cG = cG'; cIH = Int.LF.Empty } as h' =
    elHypotheses h
  in
  dprintf begin fun p ->
    let tau = Whnf.cnormCTyp ttau in
    p.fmt "[elHypothetical] @[<v>outside ttau = @[%a@]\
           @,inside ttau  = @[%a@]\
           @,@[<v 2>outside cD =@ @[<v>%a@]@]\
           @,@[<v 2>inside cD  =@ @[<v>%a@]@]@]"
      P.(fmt_ppr_cmp_typ cD l0) tau
      P.(fmt_ppr_cmp_typ cD' l0) tau
      P.(fmt_ppr_lf_mctx l0) cD
      P.(fmt_ppr_lf_mctx l0) cD'
    end;

  validateContexts loc (cD, cD') (cG, cG');
  I.Hypothetical
    ( h'
    , elProof cD' cG' label p ttau
    )

and elCommand cD cG =
  function
  | A.Unbox (loc, i, x) ->
     let (i, ttau_i) = elExp' cD cG i in
     let cU =
       Check.Comp.require_syn_typbox cD cG loc i ttau_i
       |> Whnf.cnormMTyp
     in
     let d = Int.LF.(Decl (x, cU, No)) in
     let t = Int.LF.MShift 1 in
     (* No need to check for shadowing since that already happened
        during indexing. *)
     ( Int.LF.Dec (cD, d)
     , Whnf.cnormGCtx (cG, t)
     , t
     , I.Unbox (i, x, cU)
     )

  | A.By (loc, i, x) ->
     let (i, tau_i) = elExp' cD cG i |> Pair.rmap Whnf.cnormCTyp in
     let i = Whnf.(cnormExp' (i, m_id)) in
     let tau_i = Whnf.(cnormCTyp (tau_i, m_id)) in
     if not Whnf.(closedExp' i && closedCTyp tau_i) then
       throw loc (ClosedTermRequired (cD, cG, i, tau_i));
     let c = I.By (i, x, tau_i) in
     (cD, Int.LF.Dec (cG, I.CTypDecl (x, tau_i, false)), Whnf.m_id, c)

(* elaborate Harpoon proofs *)
and elProof cD cG (pb : I.SubgoalPath.builder) (p : Apx.Comp.proof) ttau =
  match p with
  | A.Incomplete (loc, str_opt) ->
     let context = I. ({ cD; cG; cIH = Int.LF.Empty }) in
     let label = pb in
     I.(Incomplete (loc, { context; goal = ttau; solution = ref None; label }))
  | A.Directive (loc, d) ->
     I.Directive (elDirective cD cG pb d ttau)
  | A.Command (loc, cmd, p) ->
     dprnt "[elProof] --> elCommand @[%a@]";
     let (cD', cG', t, cmd) = elCommand cD cG cmd in
     let ttau' = Pair.rmap (Whnf.mcomp' t) ttau in
     dprintf begin fun p ->
       p.fmt "[elProof] @[<v>elCommand done.\
              @,cmd = @[%a@]\
              @,goal before: @[%a@]\
              @,goal after: @[%a@]@]"
         P.(fmt_ppr_cmp_command cD cG) cmd
         P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp ttau)
         P.(fmt_ppr_cmp_typ cD' l0) (Whnf.cnormCTyp ttau')
       end;
     let p = elProof cD' cG' pb p ttau' in
     I.Command (cmd, p)

and elSplit loc cD cG pb i tau_i bs ttau =
  let make_ctx_branch w { A.case_label = l; branch_body = hyp; split_branch_loc = loc } =
    match l with
    | A.ContextCase (A.EmptyContext loc) ->
       let pb' =
         I.SubgoalPath.(append pb (build_context_split i I.(EmptyContext loc)))
       in
       let pat =
         let mC = (Loc.ghost, Int.LF.(CObj Null)) in
         I.PatMetaObj (Loc.ghost, mC)
       in
       let (t', t1, cD_b) =
         synPatRefine loc (case_type (lazy pat) i) (cD, cD) Whnf.m_id
           (tau_i, tau_i)
       in
       let cG_b = Whnf.cnormGCtx (cG, t') in
       let hyp' = elHypothetical cD_b cG_b pb' hyp ttau in
       (* No need to apply the msub to pat, since pat is closed. *)
       I.SplitBranch (I.EmptyContext loc, (Int.LF.Empty, pat), t', hyp')

    | A.ContextCase (A.ExtendedBy (loc, n)) ->
       begin match Coverage.genNthSchemaElemGoal cD n w with
       | None ->
          throw loc (InvalidSchemaElementIndex (n, w))
       | Some (cD', cPsi, t) ->
          (* cD' |- t : cD
             cD' |- cPsi dctx is the pattern *)
          let pat =
            I.PatMetaObj (Loc.ghost, (Loc.ghost, Int.LF.CObj cPsi))
          in
          let (t', t1, cD_b) =
            synPatRefine loc (case_type (lazy pat) i) (cD, cD') t
              (tau_i, Whnf.cnormCTyp (tau_i, t))
            (* pretty sure [t]tau_i = tau_i because it should just be
               a typbox of a ctyp of a schema, which is unaffected by
               substitution. -je *)
          in
          let cG_b = Whnf.cnormGCtx (cG, t') in
          let ttau_b = Pair.rmap (Whnf.mcomp' t') ttau in
          let pat' = Whnf.cnormPattern (pat, t1) in
          let l' = I.ExtendedBy (loc, n) in
          let pb' = I.SubgoalPath.(append pb (build_context_split i l')) in
          let hyp' = elHypothetical cD_b cG_b pb' hyp ttau_b in
          I.SplitBranch (l', (Int.LF.Empty, pat'), t', hyp')
       end

    | _ ->
       CaseLabelMismatch (`context, variant_of_case_label l)
       |> throw loc
  in
  let make_meta_branch (cU, cPsi) { A.case_label = l; branch_body = hyp; split_branch_loc = loc } =
    match l with
    | A.PVarCase (loc, n, k) ->
       (* Generate the preliminary branch context cD'
          cD'; cPsi' |- h : tA'
          cD' |- t : cD
        *)
       let (cD', (cPsi', h, tA'), t) =
         let psi, e =
           match Context.ctxVar cPsi with
           (* TODO raise appropriate error
              Parameter variable cases are impossible for this split.
              The split's scrutinee
              i
              of type
              tau_i
              does not involve a context variable.
            *)
           | None -> assert false
           | Some psi ->
              let Int.LF.Schema es =
                Context.lookupCtxVarSchema cD psi
                |> Store.Cid.Schema.get_schema
              in
              (* Subtract 1 here because the user specifies schema
                 elements 1-based but lists are 0-based *)
              match List.nth_opt es (n - 1) with
              | Some e -> (psi, e)
              (* TODO raise appropriate error
                 Parameter variable case #n.k is invalid for the schema
                 ctx
                 Schema element n is out of bounds.
               *)
              | None -> assert false
         in
         Coverage.genPVarGoal e cD cPsi psi
       in

       (* Construct the pattern, appropriately projected. *)
       (* XXX need to eta-expand parameter variables ? -je
          If we do, then pattern and type construction will need to
          take place at the same time, or pattern construction will
          need to return some kind of function that can accept the
          necessary spine generated by type construction.
        *)
       (* cD' |- pat <== tau_p
          (tau_p is constructed below.)
        *)
       let pat =
         I.PatMetaObj
           ( Loc.ghost
           , ( Loc.ghost
             , let open Int.LF in
               ClObj
                 ( Context.dctxToHat cPsi'
                 , MObj (Root (Loc.ghost, (proj_maybe h k), Nil, `explicit))
                 )
             )
           )
       in

       (* Compute the type of the pattern *)
       (* cD' |- tau_p <== type
          because we build tau_p using tA'
          and cD'; cPsi' |- tA' <== type
        *)
       let tau_p =
         let tA' =
           match k, tA' with
           | Some k, Int.LF.Sigma tRec ->
              (* Compute the type of the kth projection of tRec. *)
              Int.LF.getType h (tRec, LF.id) k 1
              |> Whnf.normTyp

           | None, Int.LF.Sigma _ ->
              (* TODO raise proper error
                 Parameter variable case #n is invalid for schema
                   ctx
                 A projected case #n.k is required.
               *)
              assert false
           | None, tA' -> tA'
         in
         I.TypBox
           ( Loc.ghost
           , Int.LF.(ClTyp (MTyp tA', cPsi'))
           )
         (* We generate an MTyp here despite this being a _parameter_
            variable because unification (used in synPatRefine) will
            otherwise fail to unify the PTyp here with the MTyp of the
            scrutinee.
            Consequently, during typechecking, we will need to use the
            PTyp hack.
          *)
       in

       let (t', t1, cD_b) =
         synPatRefine loc (case_type (lazy pat) i) (cD, cD') t
           (tau_i, tau_p)
       in
       let pat' = Whnf.cnormPattern (pat, t1) in
       let cG_b = Whnf.cnormGCtx (cG, t') in

       (* Compute the goal type inside the branch. *)
       (* cD_b |- ttau_b <== type *)
       let ttau_b = Pair.rmap (Whnf.mcomp' t') ttau in

       let l' = `pvar k in
       let pb' = I.SubgoalPath.(append pb (build_meta_split i l')) in

       let hyp' = elHypothetical cD_b cG_b pb' hyp ttau_b in

       I.SplitBranch (l', (Int.LF.Empty, pat'), t', hyp')

    | A.NamedCase (loc, name) ->
       let cid, tA, k =
         try
           let open Store.Cid.Term in
           let cid = index_of_name name in
           let { Entry.typ; implicit_arguments; _ } = get cid in
           (cid, typ, implicit_arguments)
         with
         | Not_found ->
            UnboundCaseLabel (`meta, name, cD, tau_i)
            |> throw loc
       in
       (* XXX Is this always going to be MTyp?
          Need to think about how this will interact with parameter variables.
        *)
       let Int.LF.MTyp tP = cU in
       let (cD', (cPsi', tR_p, tA_p), t) =
         match Coverage.genObj (cD, cPsi, tP) (Int.LF.Const cid, tA, k) with
         | None ->
            assert false
         (* XXX throw an appropriate error
            Normally this would be a type mismatch, because the user
            types the full pattern, but here since the user only
            types the constructor.
            I'm thinking an error that looks like
            Impossible constructor.
            The constructor %a, of type
            %a
            is not a possible case for the split scrutinee type
            %a
          *)
         | Some p -> p
       in
       let pat =
         I.PatMetaObj
           ( Loc.ghost
           , let open Int.LF in
             ( Loc.ghost
             , ClObj
                 ( Context.dctxToHat cPsi'
                 , MObj tR_p
                 )
             )
           )
       in
       let tau_p =
         I.TypBox
           ( Loc.ghost
           , Int.LF.(ClTyp (MTyp (Whnf.normTyp tA_p), cPsi'))
           )
       in
       dprintf begin fun p ->
         p.fmt "[elSplit] @[<v>generated pattern:\
                @,@[<hv 2>@[%a@]; . |-@ @[%a@] :@ @[%a@]@]@]"
           P.(fmt_ppr_lf_mctx ~all: true l0) cD'
           P.(fmt_ppr_cmp_pattern cD' Int.LF.Empty l0) pat
           P.(fmt_ppr_cmp_typ cD' l0) tau_p
         end;
       (* cD' ; cPsi' |- tR_p <= tA_p
          cD' |- t : cD
        *)
       let (t', t1, cD_b) =
         synPatRefine loc (case_type (lazy pat) i) (cD, cD') t
           (tau_i, tau_p)
       in
       let pat = Whnf.cnormPattern (pat, t1) in
       (* cD_b |- t' : cD
          cD_b |- t1 : cD'
        *)
       let cG_b = Whnf.cnormGCtx (cG, t') in
       let ttau_b = Pair.rmap (Whnf.mcomp' t') ttau in
       dprintf begin fun p ->
         p.fmt "[elSplit] @[<v>goal outside: @[%a@]\
                @,goal inside: @[%a@]\
                @,msub typing:\
                @,  @[%a@]\
                @]"
           P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp ttau)
           P.(fmt_ppr_cmp_typ cD_b l0) (Whnf.cnormCTyp ttau_b)
           P.fmt_ppr_lf_msub_typing (cD_b, t', cD)
         end;

       let l' = `ctor cid in
       let pb' = I.SubgoalPath.(append pb (build_meta_split i l')) in
       let hyp' = elHypothetical cD_b cG_b pb' hyp ttau_b
       (*
         ttau = (t, tau)
         such that
         cD |- [t]tau <= type

         ttau_b = (t o t', tau)
         such that
         cD_b |- [t o t']tau <= type
        *)
       in
       I.SplitBranch (l', (Int.LF.Empty, pat), t', hyp')

    | A.BVarCase loc ->
       if Context.dctxLength cPsi <> 1 then
         Error.not_implemented loc
           "Parameter variable matching is supported only if the LF \
            context has exactly 1 binder.";
       let Int.LF.MTyp tA = cU in
       let (cD', (cPsi', tM, sA), t) =
         match Coverage.genBVar (cD, cPsi, tA) 1 with
         | [x] -> x
         | _ ->
            Error.violation "[make_meta_branch] genBVar did not generate 1 case"
       in
       let pat =
         I.PatMetaObj
           ( Loc.ghost
           , let open Int.LF in
             ( Loc.ghost
             , ClObj
                 ( Context.dctxToHat cPsi'
                 , MObj tM
                 )
             )
           )
       in
       let tau_p =
         I.TypBox
           ( Loc.ghost
           , Int.LF.(ClTyp (MTyp (Whnf.normTyp sA), cPsi'))
           )
       in
       let (t', t1, cD_b) =
         synPatRefine loc (case_type (lazy pat) i) (cD, cD') t
           (tau_i, tau_p)
       in
       let pat' = Whnf.cnormPattern (pat, t1) in
       let cG_b = Whnf.cnormGCtx (cG, t') in
       let ttau_b = Pair.rmap (Whnf.mcomp' t') ttau in
       let l' = `bvar in
       let pb' = I.SubgoalPath.(append pb (build_meta_split i l')) in
       let hyp' = elHypothetical cD_b cG_b pb' hyp ttau_b in
       I.SplitBranch (l', (Int.LF.Empty, pat'), t', hyp')

    | _ ->
       CaseLabelMismatch (`named, variant_of_case_label l)
       |> throw loc
  in
  let make_comp_branch { A.case_label = l; branch_body = hyp; split_branch_loc = loc } =
    match l with
    | A.NamedCase (loc, name) ->
       let cid =
         try
           CompConst.index_of_name name
         with
         | Not_found ->
            UnboundCaseLabel (`comp, name, cD, tau_i)
            |> throw loc
       in
       let e = CompConst.get cid in
       let tau_c = CompConst.Entry.(e.typ) in

       dprintf begin fun p ->
         p.fmt "[make_comp_branch] @[<v>--> genPatt with scrutinee type\
                @,tau_i = @[%a@]@]"
           P.(fmt_ppr_cmp_typ cD l0) tau_i
         end;
       let (cD', (cG', pat, ttau_p), t) =
         (* only consider gctx names here since the generated
            variables are computational only.
          *)
         let names = Context.(names_of_gctx cG) in
         match Coverage.(genPatt names withPatVar (cD, tau_i) (cid, tau_c)) with
         | None -> assert false (* TODO throw error *)
         | Some p -> p
       in
       let tau_p = Whnf.cnormCTyp ttau_p in

       dprintf begin fun p ->
         p.fmt "@[<v 2>[make_comp_branch] for @[%a@]@,\
                @[<hv 2>@[<hv>%a@] |-@ @[%a@] :@ @[%a@]@]\
                @,current goal = @[%a@]\
                @,cG' = @[%a@]@]"
           Id.print name
           P.(fmt_ppr_lf_mctx l0) cD'
           P.(fmt_ppr_cmp_pattern cD' cG' l0) pat
           P.(fmt_ppr_cmp_typ cD' l0) tau_p
           P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp ttau)
           P.(fmt_ppr_cmp_gctx cD' l0) cG'
         end;

       (* cD' |- t : cD
          cD' |- cG' ctx
          cD', cG' |- pat <= tau_p
        *)
       let (t', t1, cD_b) =
         synPatRefine loc (case_type (lazy pat) i) (cD, cD') t (tau_i, tau_p)
       in
       let pat = Whnf.cnormPattern (pat, t1) in
       (* cD_b |- t' : cD
          cD_b |- t1 : cD'
        *)
       let cG_pat = (Whnf.cnormGCtx (cG', t1)) in
       let cG_b =
         Context.append
           (Whnf.cnormGCtx (cG, t))
           cG_pat
       in

       let ttau_b = Pair.rmap (Whnf.mcomp' t') ttau in

       dprintf begin fun p ->
         p.fmt "[make_comp_branch] @[<v>ttau =   @[%a@]\
                @,ttau_b = @[%a@]@,\
                @,@[<hv 2>msub:@ @[%a@]@]@]"
           P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp ttau)
           P.(fmt_ppr_cmp_typ cD_b l0) (Whnf.cnormCTyp ttau_b)
           P.(fmt_ppr_lf_msub_typing) (cD_b, t', cD)
         end;

       let pb' = I.SubgoalPath.(append pb (build_comp_split i cid)) in
       let hyp' =
         elHypothetical cD_b cG_b pb' hyp ttau_b
       in

       I.SplitBranch (cid, (cG_pat, pat), t', hyp')

    | _ ->
       CaseLabelMismatch (`named, variant_of_case_label l)
       |> throw loc
  in
  match tau_i with
  | I.TypBox (_, (Int.LF.CTyp w)) ->
     let Some w = w in
     let ctx_branches = List.map (make_ctx_branch w) bs in
     I.ContextSplit (i, tau_i, ctx_branches)
  | I.TypBox (loc, (Int.LF.ClTyp (cl, psi))) ->
     let meta_branches = List.map (make_meta_branch (cl, psi)) bs in
     I.MetaSplit (i, tau_i, meta_branches)
  | I.TypBase _ | I.TypCross _ ->
     let comp_branches = List.map make_comp_branch bs in
     I.CompSplit (i, tau_i, comp_branches)
  | _ ->
     (* TODO throw proper error see; see what elab does for Case, if anything? *)
     throw loc (IllegalCase (cD, cG, i, tau_i))

(* elaborate Harpoon directives *)
and elDirective cD cG pb (d : Apx.Comp.directive) ttau : Int.Comp.directive =
  match d with
  | A.Intros (loc, hyp) ->
     let (cD', cG', tau', _) =
       Check.Comp.unroll cD cG (Whnf.cnormCTyp ttau)
     in
     let hyp =
       elHypothetical cD' cG' I.SubgoalPath.(append pb build_intros) hyp (tau', Whnf.m_id)
     in
     I.Intros hyp

  | A.Solve (loc, e) ->
     let e = elExp cD cG e ttau in
     dprintf begin fun p ->
       p.fmt "[elDirective] [solve] @[<v>elExp done.\
              @,@[@[%a@] :@ @[%a@]@]@]"
         P.(fmt_ppr_cmp_exp_chk cD cG l0) e
         P.(fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp ttau)
       end;
     I.Solve e

  | A.Split (loc, i, bs) ->
     let (i, tau_i) = elExp' cD cG i |> Pair.rmap Whnf.cnormCTyp in
     dprintf begin fun p ->
       p.fmt "[elDirective] @[<v>split @[%a@] as...\
              @,tau_i = @[%a@]@]"
         P.(fmt_ppr_cmp_exp_syn cD cG l0) i
         P.(fmt_ppr_cmp_typ cD l0) tau_i
       end;
     elSplit loc cD cG pb i tau_i bs ttau

  | A.Suffices (loc, i, ps) ->
     let (i, tau_i) = elExp' cD cG i |> Pair.rmap Whnf.cnormCTyp in
     let ps =
       List.map (fun (loc, tau, p) -> (loc, elCompTyp cD tau, p)) ps
     in
     Check.Comp.unify_suffices cD tau_i
       (List.map (fun (_, tau, _) -> tau) ps)
       (Whnf.cnormCTyp ttau);
     let ps =
       let i_head = I.head_of_application i in
       List.mapi
         begin fun k (loc, tau, p) ->
         ( loc
         , tau
         , elProof cD cG
             I.SubgoalPath.(append pb (build_suffices i_head k))
             p (tau, Whnf.m_id)
         )
         end
         ps
     in
     I.Suffices (i, ps)

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

let thm cG t ttau = match t with
  | Apx.Comp.Program e -> Int.Comp.Program (elExp Int.LF.Empty cG e ttau)
  | Apx.Comp.Proof p ->
     Int.Comp.(Proof (elProof Int.LF.Empty cG SubgoalPath.start p ttau))

let numeric_order = elNumericOrder
