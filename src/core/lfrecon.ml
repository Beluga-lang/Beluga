open Store
open Store.Cid
open Syntax
open Id

(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail
module C     = Whnf

(* **********************************************************************)
(* Pretty printing                                                      *)
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer

let strengthen : bool ref = ref true


let (dprint, _dprnt) = Debug.makeFunctions (Debug.toFlags [11])

type typeVariant = VariantAtom | VariantPi | VariantSigma

type error =
  | ProjBVarImpossible of Int.LF.mctx * Int.LF.dctx * Id.offset * Apx.LF.proj
  | BVarTypMissing  of Int.LF.mctx * Int.LF.dctx * Int.LF.head
  | IdCtxsub
  | SubstTyp
  | MissingInformationCtx of Int.LF.mctx * Int.LF.dctx
  | TypMismatchElab of Int.LF.mctx * Int.LF.dctx * Int.LF.tclo * Int.LF.tclo
  | IllTypedElab    of Int.LF.mctx * Int.LF.dctx * Int.LF.tclo * typeVariant
  | IllTypedSub     of Int.LF.mctx * Int.LF.dctx * Apx.LF.sub * Int.LF.dctx
  | LeftoverConstraints of Id.name
  | PruningFailed
  | CompTypAnn
  | InvalidLFHole
  | CompTypAnnSub
  | NotPatternSpine
  | MissingSchemaForCtxVar of Id.name
  | ProjNotValid of Int.LF.mctx * Int.LF.dctx * int * Int.LF.tclo
  | ProjNotFound of Int.LF.mctx * Int.LF.dctx * name * Int.LF.tclo
  | HolesFunction
  | ParamFun
  | CtxVarSchema of Id.name
  | SigmaTypImpos of Int.LF.mctx * Int.LF.dctx * Int.LF.tclo
  | SpineLengthMisMatch
  | IllTypedSubVar of Int.LF.mctx * Int.LF.dctx * Int.LF.dctx
  | NotPatSub
  | IncompatibleSchemaForCtxVar of Int.LF.mctx * Int.LF.ctx_var * Id.cid_schema * Id.cid_schema
  | TermWhenVar of Int.LF.mctx * Int.LF.dctx * Apx.LF.normal
  | SubWhenRen of Int.LF.mctx * Int.LF.dctx * Apx.LF.sub
  | HOMVarNotSupported
  | SubstVarConflict of Id.name

exception Error of Syntax.Loc.t * error

let string_of_typeVariant = function
  | VariantAtom -> "atomic type"
  | VariantPi -> "Pi type"
  | VariantSigma -> "Sigma type"

let string_of_proj = function
  | Apx.LF.ByPos k -> string_of_int k
  | Apx.LF.ByName n -> Id.render_name n

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | ProjBVarImpossible (cD, cPsi, x, proj) ->
            Format.fprintf ppf
              "%a.%s is illegal; there is no block declaration in %a."
              (P.fmt_ppr_lf_head cD cPsi Pretty.std_lvl) (Int.LF.BVar x)
	      (string_of_proj proj)
              (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)
        | BVarTypMissing (cD, cPsi, _h) ->
            Format.fprintf ppf
              "Missing type information for bound variable. Provide a fully annotated context."
(*              (P.fmt_ppr_lf_head cD cPsi Pretty.std_lvl) h *)
        | SubstTyp ->
            Format.fprintf ppf
              "We currently only support substitution variables which either map a context\
\n variable to another context variable or to an empty context."
        | MissingInformationCtx (_cD, _cPsi) ->
            Format.fprintf ppf
              "The domain of the substitution cannot be inferred; please provide\
\n it explicitly.\n"
        | NotPatSub ->
          Format.fprintf ppf
            "Substitution associated with substitution variable is not a pattern substitution;\
\nPlease provide the type of the substitution variable."
        | SpineLengthMisMatch ->
            Format.fprintf ppf
              "Too few or to many arguments supplied to a type family."
        | CtxVarSchema psi ->
            Format.fprintf ppf
              "Reconstruction cannot infer the schema for context %s."
            (Id.render_name psi)
        | SigmaTypImpos (cD, cPsi, sA) ->
            Format.fprintf ppf
              "Ill-typed expression. @ @ The head of a spine has type %a. "
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)
        | ParamFun ->
            Format.fprintf ppf "Projection on a parameter variable has a functional type which type reconstruction cannot infer - please specify the type of the parameter variable"
        | HolesFunction ->
            Format.fprintf ppf
              "Underscores occurring inside LF objects must be of atomic type."

        | ProjNotValid (cD, cPsi, k, sA) ->
            Format.fprintf ppf
              "Cannot get the %s. projection from type %a."
              (string_of_int k)
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)

        | ProjNotFound (cD, cPsi, k, sA) ->
            Format.fprintf ppf
              "There is no projection named %s in type %a."
              (string_of_name k)
              (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)

        | TypMismatchElab (cD, cPsi, sA1, sA2) ->
          Error.report_mismatch ppf
            "Ill-typed expression."
	    "Expected type" (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA1)
	    "Actual type"   (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA2)

        | IllTypedElab (cD, cPsi, sA, variant) ->
          Error.report_mismatch ppf
            "Ill-typed expression."
	    "Expected type" (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) (Whnf.normTyp sA)
	    "Actual type"   (Format.pp_print_string)                  (string_of_typeVariant variant)

        | IllTypedSub (cD, cPsi, s, cPsi') ->
          Format.fprintf ppf "Ill-typed substitution.@.";
          Format.fprintf ppf "    Does not take context: %a@."
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi');
          Format.fprintf ppf "    to context: %a@."
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)

        | IllTypedSubVar (cD, cPsi, cPsi') ->
          Format.fprintf ppf "Ill-typed substitution variable.@.";
          Format.fprintf ppf "    Does not take context: %a@."
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi');
          Format.fprintf ppf "    to context: %a@."
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) (Whnf.normDCtx cPsi)

        | LeftoverConstraints x ->
          Format.fprintf ppf
            "Cannot reconstruct a type for free variable %s (leftover constraints)."
            (Id.render_name x)

        | IdCtxsub ->
            Format.fprintf ppf
              "Identity substitution .. must be associated with a context variable. \n \n If your object is closed, you should omit the identitiy substitution, since it is empty."
      	| PruningFailed ->
                Format.fprintf ppf
      	    "Pruning a type failed.@ This can happen when you have some free@ \
                   meta-variables whose type cannot be inferred."

        | CompTypAnn ->
          Format.fprintf ppf "Type synthesis of term failed."
        | InvalidLFHole ->
          Format.fprintf ppf
            "Invalid LF Hole at %s"
            (Loc.to_string loc)

        | CompTypAnnSub ->
          Format.fprintf ppf "Synthesizing the type meta-variable associated with a substitution variable failed (use typing annotation)."

        | NotPatternSpine ->
          Format.fprintf ppf "Non-pattern spine -- cannot reconstruct the type of a variable or hole." (* TODO *)

        | MissingSchemaForCtxVar psi ->
          Format.fprintf ppf
            "Missing schema for context variable %s."
            (Id.render_name psi)
        | IncompatibleSchemaForCtxVar (_cD, _psi, w, w') ->
	    (* (Pretty.fmt_ppr_lf_dctx cD 0) (Int.LF.CtxVar psi) *)
          Error.report_mismatch ppf
	    "Ill-typed context variable"
            "Expected schema for context variable"  (Format.pp_print_string) (RR.render_cid_schema w)
	    "Actual type" (Format.pp_print_string) (RR.render_cid_schema w')
	| TermWhenVar (_, _, _) ->
	  Format.fprintf ppf "A term was found when expecting a variable.@." ;

 	| SubWhenRen (_, _, _) ->
	  Format.fprintf ppf "A substitution was found when expecting a renaming.@."
	| HOMVarNotSupported ->
	  Format.fprintf ppf "Higher-order meta-variables not (currently) supported"
        | SubstVarConflict x ->
          Format.fprintf ppf
            "The variable %s was expected to be a substitution variable.\n\nPlease note that #%s and %s both denote the same variable and so the use of both concurrently to denote different things is disallowed."
            (Id.render_name x) (Id.render_name x) (Id.render_name x)

  ))

let rec conv_listToString clist = match clist with
  | [] -> " "
  | x::xs -> string_of_int x ^ ", " ^ conv_listToString xs

let rec what_head = function
  | Apx.LF.BVar _ -> "BVar"
  | Apx.LF.Const _ -> "Const"
  | Apx.LF.MVar _ -> "MVar"
  | Apx.LF.PVar (Apx.LF.Offset _ , _ ) -> "PVar Offset "
  | Apx.LF.PVar (Apx.LF.MInst _ , _ ) -> "PVar PInst "
  | Apx.LF.Proj (head, _) -> "Proj " ^ what_head head
  | Apx.LF.FVar _ -> "FVar"
  | Apx.LF.FMVar _ -> "FMVar"
  | Apx.LF.FPVar _ -> "FPVar"


(* ******************************************************************* *)
type reconType = Pibox | Pi

exception NotPatSpine

(* ******************************************************************* *)
let mkShift recT cPsi = match recT with
  | Pibox ->
      Int.LF.Shift 0

  | Pi ->
      let (None, d) = Context.dctxToHat cPsi in
        Int.LF.Shift d




(* ******************************************************************* *)
let pruningTyp locOpt cD cPsi phat sA (ms, ss)  =
  if Substitution.LF.isId ss then
    Whnf.normTyp sA
  else
    begin try
      Unify.pruneTyp cD cPsi phat sA (ms, ss) (Unify.MMVarRef (ref None))
    with _ -> raise (Error (locOpt, PruningFailed))
    end

let unify_phat cD psihat phihat =
  match phihat with
    | (Some (Int.LF.CInst ((_, ({contents = None} as cref), _, Int.LF.CTyp s_cid, _, _), _ )), d) ->
        begin match psihat with
          | (Some (Int.LF.CInst ((_, ({contents = None} as cref'), _, _, _, _), _) as c_var) , d') ->
	      if cref == cref' then
		d = d'
	      else
		(cref := Some (Int.LF.ICtx (Int.LF.CtxVar (c_var)))  ; true)
          | ((Some (c_var)) , d') ->
              if d = d' then
                ((match c_var with
                   | Int.LF.CtxName psi ->
                       FCVar.add psi (cD, Int.LF.Decl (psi, Int.LF.CTyp s_cid, Int.LF.Maybe))
                   | _ -> ());
                  cref := Some (Int.LF.ICtx (Int.LF.CtxVar (c_var)))  ; true)
              else
                (dprint (fun () -> "[unify_phat - 1] unify ctx_var with a full context");
                 raise Error.NotImplemented)
          | (None , d') ->
              if d = d' then
                (cref := Some (Int.LF.ICtx (Int.LF.Null)) ; true)
              else
                (dprint (fun () -> "[unify_phat - 2] unify ctx_var with a full context");
                 raise Error.NotImplemented)
        end

    | _ ->  (psihat = phihat)

(* ******************************************************************* *)

let getSchema cD ctxvar loc = match ctxvar with
  | Some ((Int.LF.CtxOffset offset ) as phi) ->
      Schema.get_schema (Context.lookupCtxVarSchema cD  phi)
  | Some (Int.LF.CtxName n) ->
      begin try
        let (_ , Int.LF.Decl (_, Int.LF.CTyp (Some s_cid), _dep)) = FCVar.get n in
	  Schema.get_schema s_cid
      with _ ->  raise (Error (loc,CtxVarSchema n))
      end

  | Some (Int.LF.CInst ((_,_,_,Int.LF.CTyp (Some s_cid),_,_),_)) ->
     Schema.get_schema s_cid
  | None -> raise (Error.Violation "No context variable for which we could retrieve a schema")

(* ******************************************************************* *)
(* Eta-expansion                                                       *)

  let rec addPrefix loc m tA =
    begin match tA with
      | Int.LF.Atom _ -> m
      | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ) , _ ) , tA') ->
          let _ = dprint (fun () -> "eta FMV - add Lam ") in
        Apx.LF.Lam (loc, x, addPrefix loc m tA')
    end

  let rec etaExpSub k s tA = begin match tA with
    | Int.LF.Atom _ -> (k, s)
    | Int.LF.PiTyp (_ , tA') ->
        let (k',s') = etaExpSub (k+1) s tA' in
       (k'-1, Apx.LF.Dot(Apx.LF.Head(Apx.LF.BVar(k')),s'))
  end

  let etaExpandFMV  loc m tA = m

  let etaExpandMV loc (Apx.LF.MVar (x,s)) tA =
    let ( _ , s') = etaExpSub 0 s tA  in
      addPrefix loc (Apx.LF.Root(loc, Apx.LF.MVar(x, s'), Apx.LF.Nil)) tA


(* Eta-expansion of bound variables which have function type *)
let etaExpandHead loc h tA =
  let rec etaExpSpine k tS tA = begin match  tA with
    | Int.LF.Atom _  -> (k, tS)

    | Int.LF.PiTyp (_ , tA') ->
        let tN = Int.LF.Root (loc, Int.LF.BVar k, Int.LF.Nil) in
          etaExpSpine (k+1)  (Int.LF.App(tN, tS)) tA'
  end in

  let rec etaExpPrefix loc (tM, tA) = begin match tA with
    | Int.LF.Atom _ -> tM
    | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ), _ ) , tA') ->
        Int.LF.Lam (loc, x, etaExpPrefix loc (tM, tA'))
  end in

  let (k, tS') = etaExpSpine 1 (Int.LF.Nil) tA in
  let h'       =  begin match h with
                    | Int.LF.BVar x -> Int.LF.BVar (x+k-1)
                    | Int.LF.FVar _ -> h
                  end  in
    etaExpPrefix loc (Int.LF.Root(loc, h' , tS'), tA)





(*
let etaExpandApxHead loc h tA =
  let rec etaExpApxSpine k tS tA = begin match  tA with
    | Int.LF.Atom _  -> (k, tS)

    | Int.LF.PiTyp (_ , tA') ->
        let tN = Apx.LF.Root(loc, Apx.LF.BVar k, Apx.LF.Nil) in
          etaExpApxSpine (k+1)  (Apx.LF.App(tN, tS)) tA'
  end in

  let rec etaExpApxPrefix loc (tM, tA) = begin match tA with
    | Int.LF.Atom _ -> tM
    | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ), _ ) , tA') ->
        Apx.LF.Lam (loc, x, etaExpApxPrefix loc (tM, tA'))
  end in

  let (k, tS') = etaExpApxSpine 1 (Apx.LF.Nil) tA in
  let h'       =  begin match h with
                    | Apx.LF.BVar x -> Apx.LF.BVar (x+k-1)
                    | Apx.LF.FVar _ -> h
                  end  in
    etaExpApxPrefix loc (Apx.LF.Root(loc, h' , tS'), tA)
*)

let etaExpandApxTerm  loc h tS tA =
  let rec etaExpApxSpine k tS tA = begin match  tA with
    | Int.LF.Atom _  -> (k, tS)

    | Int.LF.PiTyp (_ , tA') ->
        let tN = Apx.LF.Root(loc, Apx.LF.BVar k, Apx.LF.Nil) in
          etaExpApxSpine (k+1)  (Apx.LF.App(tN, tS)) tA'
  end in

  let rec etaExpApxPrefix loc (tM, tA) = begin match tA with
    | Int.LF.Atom _ -> tM
    | Int.LF.PiTyp ((Int.LF.TypDecl (x, _ ), _ ) , tA') ->
        let _ = dprint (fun () -> "eta - add Lam ") in
        Apx.LF.Lam (loc, x, etaExpApxPrefix loc (tM, tA'))
  end in

  let rec appendSpine tS1 tS2 = begin match tS1 with
    | Apx.LF.Nil -> tS2
    | Apx.LF.App (tM, tS) ->
        Apx.LF.App (tM, appendSpine tS tS2)
  end in

  let (k, tS') = etaExpApxSpine 1 (Apx.LF.Nil) tA in
  let _ = dprint (fun () -> "etaExpApxSpine k = " ^ string_of_int k )in
  let tS''     = appendSpine (Apxnorm.shiftApxSpine (k-1) tS) tS' in
  (* let tS''     = appendSpine tS tS' in  *)

  let h'       =  begin match h with
                    | Apx.LF.BVar x -> Apx.LF.BVar (x+k-1)
                    |  _ -> h
                  end  in
    etaExpApxPrefix loc (Apx.LF.Root(loc, h' , tS''), tA)


(* ******************************************************************* *)
(* Pattern substitutions and spines                                    *)
(* patSpine s = true iff
 *
 *     cPsi |- s : A <- P  and
 *     s is a pattern spine (simple approximate),
 *     i.e. it consists of distinct bound variables
 *)
let rec patSpine spine =
  let rec etaUnroll k m= begin match m with
    | Apx.LF.Lam (_ , _, n) ->  etaUnroll (k+1) n
    |  _ ->  (k, m)
  end in

  let rec patSpine' seen_vars spine = match spine with
    | Apx.LF.Nil ->
        (0, spine)

    | Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), spine) ->
        if not (List.mem x seen_vars) then
          let (k, p_spine) = patSpine' (x :: seen_vars) spine in
            (k+1, Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), p_spine))
        else
           raise NotPatSpine

    | Apx.LF.App (Apx.LF.Lam _ as m, spine) ->
        begin match etaUnroll 0 m with
          | (k, Apx.LF.Root( loc , Apx.LF.BVar x, spine')) ->
              (let (l', _p_spine') = patSpine spine' in
                 if l' = k && x > k then
                    let (l, p_spine) = patSpine'  ((x-k)::seen_vars) spine in
                      (l+1, Apx.LF.App(Apx.LF.Root(loc, Apx.LF.BVar (x-k), Apx.LF.Nil), p_spine))
                  else
                    raise NotPatSpine
              )
          | (k, Apx.LF.Root( loc , Apx.LF.FVar x, spine')) ->
              let (l', _p_spine') = patSpine spine' in
                (if l' = k  then
                   let (l, p_spine) = patSpine' seen_vars spine in
                     (l+1, Apx.LF.App(Apx.LF.Root(loc, Apx.LF.FVar x, Apx.LF.Nil), p_spine))
                 else
                   raise NotPatSpine)
          | _ ->  raise NotPatSpine
        end
    | _ ->  raise NotPatSpine

  in
  let s = patSpine' [] spine in
    (dprint (fun () -> "[check pat spine] done" ) ; s)



(* isPatSub s = bool *)
let rec isPatSub s = match s with
  | Apx.LF.Id | Apx.LF.RealId ->
      true

  | Apx.LF.EmptySub ->
      true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar _k), s) ->
      isPatSub s

(* We cannot handle this at the moment; to infer the type of
   FMVars which are associated with projections and impose a restriction;
   the issues arises in pruning the type of FMVars where the most general
   type is generated as a id sub from a context containing blocks to another
   one containing blocks; instead we would need to create FMVars as
   going from a flattened block context to its block equivalent, and
   unroll the id substitution to b.1 b.2 b.3 etc instead of b

    | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar _k,_j)), s) ->
      isPatSub s
*)
  | Apx.LF.Dot (Apx.LF.Head _, _s) -> false

  | Apx.LF.Dot (Apx.LF.Obj  _, _s) -> false
  | Apx.LF.SVar _ -> false


  | _ -> false

(* ******************************************************************* *)
(* isProjPatSub s = true *)
let rec isProjPatSub s = match s with
  | Apx.LF.Id | Apx.LF.RealId -> true

  | Apx.LF.EmptySub -> true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      isProjPatSub s

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.Proj(Apx.LF.BVar _k,_j)), s) ->
     isProjPatSub s

  | Apx.LF.Dot (Apx.LF.Head _, _s) -> false

  | Apx.LF.Dot (Apx.LF.Obj  _, _s) -> false
  | Apx.LF.SVar _ -> false
  | Apx.LF.FSVar _ -> false

let getProjIndex loc cD cPsi recA = function
  | Apx.LF.ByPos j -> j
  | Apx.LF.ByName j ->
    try Int.LF.getIndex recA j
    with _ -> raise (Error (loc, ProjNotFound (cD, cPsi, j, (Int.LF.Sigma recA, Substitution.LF.id))))

let getProjIndexFromType loc cD cPsi tp k =
  let Int.LF.TypDecl (_, Int.LF.Sigma recA) = tp in
  getProjIndex loc cD cPsi recA k

let flattenProjPatHead loc cD h conv_list cPsi = match h with
  | Apx.LF.BVar k -> Apx.LF.BVar (ConvSigma.new_index k conv_list)

  | Apx.LF.Proj(Apx.LF.BVar k, p) ->
      let tp = begin try Context.ctxSigmaDec cPsi k with _ -> raise Not_found end in
      let j = getProjIndexFromType loc cD cPsi tp p in
      let _ = dprint (fun () -> "flattenProjPat Proj Case: k = " ^ string_of_int k ^ "    j = "  ^ string_of_int j ^ "\n") in
      let k' = (ConvSigma.new_index k conv_list) - j + 1  in
      (Apx.LF.BVar k')

let rec flattenProjPat loc cD s conv_list cPsi = match s with
  | Apx.LF.Id  -> Apx.LF.Id
  | Apx.LF.RealId -> Apx.LF.RealId
  | Apx.LF.EmptySub -> Apx.LF.EmptySub
  | Apx.LF.Dot (Apx.LF.Head h, s) ->
      let s' = flattenProjPat loc cD s conv_list cPsi in
      let h' = flattenProjPatHead loc cD h conv_list cPsi in
        Apx.LF.Dot (Apx.LF.Head h', s')

 (* these are the only cases which can happen *)

(* isTuplePatSub s = true *)
let rec isTuplePatSub s = match s with
  | Apx.LF.Id | Apx.LF.RealId -> true

  | Apx.LF.EmptySub -> true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      isTuplePatSub s

  | Apx.LF.Dot (Apx.LF.Head _ , s) -> false

  | Apx.LF.Dot (Apx.LF.Obj  (Apx.LF.Tuple (_, tM)) , _s) ->
     isVarTuple tM && isTuplePatSub s
  | Apx.LF.Dot (Apx.LF.Obj  _ , _s) ->  false
  | Apx.LF.SVar _ -> false
  | Apx.LF.FSVar _ -> false

  and isVar tM  = match tM with
    | Apx.LF.Root(_ , Apx.LF.BVar k, Apx.LF.Nil) -> true
    | _ -> false

  and isVarTuple s = match s with
    | Apx.LF.Last tM -> isVar tM
    | Apx.LF.Cons (tM, t) ->
       isVar tM && isVarTuple t

let rec flattenSub s = match s with
  | Apx.LF.Id -> s
  | Apx.LF.RealId -> s

  | Apx.LF.EmptySub -> s

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), flattenSub s)

  | Apx.LF.Dot (Apx.LF.Head h , s) ->
     Apx.LF.Dot (Apx.LF.Head h, flattenSub s)

  | Apx.LF.Dot (Apx.LF.Obj  (Apx.LF.Tuple (_, tM)) , s) ->
     flattenVarTuple tM (flattenSub s)

(*  | Apx.LF.SVar _ -> undefined
  | Apx.LF.FSVar _ -> undefined
 *)
  and extractHead tM  = match tM with
    | Apx.LF.Root(_ , Apx.LF.BVar k, Apx.LF.Nil) -> Apx.LF.Head (Apx.LF.BVar k)
  (* other cases should not happen -bp *)

  and flattenVarTuple s sigma = match s with
    | Apx.LF.Last tM -> Apx.LF.Dot (extractHead tM, sigma)
    | Apx.LF.Cons (tM, t) ->
       Apx.LF.Dot(extractHead tM, flattenVarTuple t sigma)

(* TO BE FIXED -bp

(* sigmifyDctx cPhi s  = (cPhi', rho, k) s.t.
   cPhi' |-  rho : cPhi and
   cPsi  |- s    : cPhi' where
   s is a variable pattern substitution (or a Tuple Pattern
   Substitution)
   k is an offset corresponding to the number of declarations
   which have been contracted into a block, i.e.
   x:tA, y:tB  ~~> block (x:tA, y:tB) means k = 1
 *)
let rec sigmifyDctx cPhi s = match cPhi , s with
  |  cPhi , Apx.LF.Id _  -> (cPhi , s, k')
  |  cPhi , Apx.LF.EmptySub -> (cPhi, s, k')
  |  cPhi , Apx.LF.Dot ( Apx.LF.Obj (Apx.LF.Tuple (_ , tM)), s) ->
      let cPhi1, tA, vars_proj, k = extractBlock cPhi tM k' in (* where tA is some Sigma-type *)
      let cPhi', rho = sigmifyDctx cPhi1 s  in
      let rho'  = extend rho vars_proj in
       Int.LF.DDec (cPhi', Int.LF.TypDecl (Id.mk_name None, tA)) ,
       rho' , k' + k

  | Int.LF.DDec (cPhi, Int.LF.TypDecl (x, tA)) ,
    Apx.LF.Dot ( Apx.LF.Head (Apx.LF.BVar x) , s) ->
     let cPhi', rhom k = sigmifyDctx cPhi s in
     let h = Apx.LF.BVar (x - k) in
      Int.LF.DDec (cPhi', Int.LF.TypDecl (x, tA)) , Apx.LF.Dot ( Apx.LF.Head h , rho)

 *)

(* ******************************************************************* *)
(* PHASE 1 : Elaboration and Reconstruction (one pass)                 *)
(*  elTerm recT cD cPsi m sA = M
 *
 *  Pre-condition:
 *
 *  U = FV(m) (FV(a), FV(k) resp.)
 *  O = meta-variables in M (A, K, resp.)
 *
 * Invariant:
 *  If  O1; U1 ; (cD ; cPsi) |- m <- [s]A /_r (O2, U2) M
 *      and there exists a modal substitution r
 *      s.t. O2 |- r <= O1
 *  then
 *
 *     elTerm cD cPsi m sA succeeds and
 *
 *     O2 ; [|r|]U2 ; ([|r|]cD ; [|r|]cPsi) |- M <= [|r|][s]A
 *
 * Post-condition:
 *
 *   O2 |- U2 fvar_ctx    and   . |-{U2} O2 mvar_ctx
 *   (circular dependency between O2 and U2)
 *
 *   O2 s.t. O2 |-{U2} r <= O1 , and
 *
 * In the implementation:
 *   - meta-variables in O1 and O2 are handled destructively, and O1 and O2 resp characterize the state of memory.
 *   - r is not explicit but implicit since we  update all meta-variables in O1 destructively
 *   - U1 and U2 are the fvar_ctx; they are handled globally and hence are not carried explicitely as an argument
 *     to elTerm
 *   - may raise Error, if no modal substitution r exists.
 *
 * Similar invariants and pre- and post-conditions for:
 *
 *  elKind cD cPsi k = K'
 *  elTyp  cD cPsi a = A'
 *)

(* ******************************************************************* *)
(* Free variable constraints:
 *
 * fvar_cnstr  C := . | Root (FVar X, tS) & C
 *
 * The constraints are generated when encountering
 * a free variable X whose type is yet unknown and has a
 * non-pattern spine tS. This means we cannot easily infer
 * the type of the free variable X.
 *)


(* Constraints for free bound variables *)
let fvar_cnstr : ((Int.LF.typ_free_var * Apx.LF.normal * Int.LF.cvar)  list) ref = ref []

let add_fvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fvarCnstr () = (fvar_cnstr := [])

(* Constraints for free metavariables and parameter variables  *)
let fcvar_cnstr : ((Apx.LF.normal * Int.LF.mm_var)  list) ref = ref []

let add_fcvarCnstr  c = fcvar_cnstr := c :: !fcvar_cnstr
let reset_fcvarCnstr () = (fcvar_cnstr := [])

(* ******************************************************************* *)

(* synDom cPsi s = (cPhi , s')
 *
 * If s is a pattern substitution in approximate syntax
 *    cPsi is the range of the pattern substitution
 *
 * then
 *     s' the pattern substitution in internal syntax
 *     corresponding to s and
 *
 *     cPsi |- s' <= cPhi
 *)

let rec synHead cD loc cPsi h = match h with
   | Apx.LF.BVar k -> Context.ctxDec cPsi k, Int.LF.BVar k
   | Apx.LF.Proj(h, nj) ->
     let (tp, h') = synHead cD loc cPsi h in
     let j = getProjIndexFromType loc cD cPsi tp nj in
     let Int.LF.TypDecl (x, Int.LF.Sigma typRec) = tp in
     let sQ = Int.LF.getType h' (typRec, Substitution.LF.id) j 1 in
     Int.LF.TypDecl (x, Int.LF.TClo sQ) , Int.LF.Proj(h', j)

let rec synDom cD loc cPsi s = begin match s with
  | Apx.LF.RealId -> (cPsi, Int.LF.Shift 0)
  | Apx.LF.Id ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            let _ = dprint (fun () -> "[synDom] cPsi = " ^ P.dctxToString cD cPsi) in
            let _ = dprint (fun () -> "[synDom] d = " ^ string_of_int d) in
            (Int.LF.CtxVar psi, Int.LF.Shift d)

        | (None, _d) ->
            raise (Index.Error (loc, Index.UnboundIdSub))
      end

  | Apx.LF.EmptySub -> (Int.LF.Null, Int.LF.EmptySub)
  | Apx.LF.Dot (Apx.LF.Head h, s) ->
    let (cPhi, s') = synDom cD loc cPsi s in
    let ss = Substitution.LF.invert s' in
    begin match synHead cD loc cPsi h with
      | Int.LF.TypDecl (x, tA) , h' ->
	let tA' = pruningTyp loc cD cPsi (Context.dctxToHat cPsi)
	  (tA, Substitution.LF.id) (Int.LF.MShift 0, ss) in
	(Int.LF.DDec (cPhi, Int.LF.TypDecl (x, tA')),
        Int.LF.Dot (Int.LF.Head h', s'))
    end

  | _ -> raise (Error.Violation "Encountered non-pattern substitution")

end

(* ******************************************************************* *)
(* ELABORATION OF KINDS                                                *)
(* ******************************************************************* *)

exception SubTypingFailure

(* elKind cPsi k = K *)
let rec elKind cD cPsi k = match k with
  | Apx.LF.Typ ->
      Int.LF.Typ

  | Apx.LF.PiKind ((Apx.LF.TypDecl (x, a),dep), k) ->
      let dep'  = match dep with Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
      let tA    = elTyp
                    Pi
                    (*cD=*)Int.LF.Empty
                    cPsi
                    a
      in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elKind cD cPsi' k in
        Int.LF.PiKind ((Int.LF.TypDecl (x, tA), dep'), tK)

(* elTyp recT  cD cPsi a = A
 *
 * Pre-condition:
 *     U = set of free variables
 *     O = set of meta-variables (references subject to instantiation)
 *
 * if cD ; cPsi |- a <= type and a is in beta normal form
 *
 * then
 *        [|r|]cD ;  [|r|]cPsi   |- A <= type
 * and A is in beta-eta normal form.
 *
 * Effect:
 *     U' = FV(A)  where U' is an extension of U s.t. [|r|]U,U0 = U'
 *     O' = FMV(A) where O' |-{U'} r <= O
 *)
and elTyp recT cD cPsi a = match a with
  | Apx.LF.Atom (loc, a, s) ->
    let tK = (Typ.get a).Typ.kind in
    let i  = (Typ.get a).Typ.implicit_arguments in
    let s'  = mkShift recT cPsi in
    (* let s' = Substitution.LF.id in *)
    let tS = elKSpineI loc recT cD cPsi s i (tK, s') in
    Int.LF.Atom (loc, a, tS)

  | Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a), dep), b) ->
      let dep'  = match dep with Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
      let tA    = elTyp recT cD cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp recT cD cPsi' b in
        Int.LF.PiTyp ((Int.LF.TypDecl (x, tA),dep'), tB)

  | Apx.LF.Sigma typRec ->
      let typRec' = elTypRec recT cD cPsi typRec in
        Int.LF.Sigma typRec'


and elTypRec recT cD cPsi typ_rec = begin match typ_rec with
  | Apx.LF.SigmaLast(n, a) ->
      let tA = elTyp recT cD cPsi a in
      let _ = dprint (fun () -> "[elTypRec] Last " ^ " : " ^ P.typToString cD cPsi (tA, Substitution.LF.id)) in
        Int.LF.SigmaLast(n, tA)

  | Apx.LF.SigmaElem (name, a, typRec) ->
      let tA = elTyp recT cD cPsi a in
      let _ = dprint (fun () -> "[elTypRec] " ^ Id.render_name name ^ " : " ^
      P.typToString cD cPsi (tA, Substitution.LF.id)) in
      let cPsi' = Int.LF.DDec (cPsi, Int.LF.TypDecl (name, tA)) in
      let typRec' = elTypRec recT cD cPsi' typRec in
        Int.LF.SigmaElem (name, tA, typRec')
end

(* elTerm recT  cD cPsi m sA = M
 * elTerm recT  cD cPsi m sA = M  where sA = (A,s) is in whnf
 *                              m is in beta normal form.
 * Pre-condition:
 *     U = set of free variables   O |- U fvar_ctx
 *     O = set of meta-variables (references subject to instantiation)
 *                                 . |-{U} O mvar_ctx
 * if cD ; cPsi |- M <= [s]A'
 *
 *    cD |- cPsi ctx
 *    cD ; cPsi  |- s <= cPsi'
 *    cD ; cPsi' |- A <= type
 *
 * then
 *    [|r|]cD ; [|r|]cPsi |- M <= [|r|]A
 *
 * and M is in beta-eta normal form, i.e.
 *   all free variables are eta-expanded.
 *
 * Effect:
 *     U' = FV(A)  where U' is an extension of U s.t. [|r|]U,U0 = U'
 *     O' = FMV(A) where O' |-{U'} r <= O
 *)
and elTerm recT cD cPsi m sA = elTermW recT cD cPsi m (Whnf.whnfTyp sA)

and elTermW recT cD cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (loc, x, m),  (Int.LF.PiTyp ((Int.LF.TypDecl (_x, _tA) as decl, _ ), tB), s)) ->
       (* cPsi' = cPsi, x:tA *)
      let cPsi' = Int.LF.DDec (cPsi, Substitution.LF.decSub decl s) in
      let tM    = elTerm recT cD cPsi' m (tB, Substitution.LF.dot1 s) in
        Int.LF.Lam (loc, x, tM)

  | (Apx.LF.Lam (loc, _, _ ), (Int.LF.Atom _, _s)) ->
      raise (Error (loc, IllTypedElab (cD, cPsi, sA, VariantAtom)))

  | (Apx.LF.Lam (loc, _, _ ), (Int.LF.Sigma _, _s)) ->
      raise (Error (loc, IllTypedElab (cD, cPsi, sA, VariantSigma)))

  | (Apx.LF.Root (_loc, _h, _spine),  (Int.LF.Atom _, _s)) ->
      elTerm' recT cD cPsi m  sA

  | (Apx.LF.Root (_loc, _h, _spine),  (Int.LF.Sigma _, _s)) ->
      elTerm' recT cD cPsi m  sA

  | (Apx.LF.Tuple (loc, tuple),  (Int.LF.Sigma typRec, s)) ->
      let tuple' = elTuple recT cD cPsi tuple (typRec, s) in
        Int.LF.Tuple (loc, tuple')

  | (Apx.LF.Tuple (loc, _), (Int.LF.PiTyp _, _s)) ->
      raise (Error (loc, IllTypedElab (cD, cPsi, sA, VariantPi)))

  | (Apx.LF.Tuple (loc, _), (Int.LF.Atom _, _s)) ->
      raise (Error (loc, IllTypedElab (cD, cPsi, sA, VariantAtom)))

  (* | (Apx.LF.Root (loc, Apx.LF.FMVar (x, s),  _spine),  (Int.LF.PiTyp _ as tA, _s)) -> *)
  (*     let n = etaExpandFMV loc (Apx.LF.FMVar (x,s)) tA in *)
  (*       elTerm recT cD cPsi n sA *)

  (* | (Apx.LF.Root (loc, Apx.LF.MVar (x, s),  _spine),  (Int.LF.PiTyp _ as tA, _s)) -> *)
  (*     let n = etaExpandMV loc (Apx.LF.MVar (x,s)) tA in *)
  (*       elTerm recT cD cPsi n sA *)

  | (Apx.LF.Root (loc, h, spine ), (Int.LF.PiTyp _ as tA, _s)) ->
      let n = etaExpandApxTerm loc h spine tA in
        elTerm recT cD cPsi n sA

  | (Apx.LF.Ann (loc, m, a), tA) ->
    let tB = elTyp recT cD cPsi a in
    let tM = elTerm recT cD cPsi m (tB, Substitution.LF.id) in
    let () = Unify.unifyTyp cD cPsi (tB, Substitution.LF.id) sA in
    tM
  | (Apx.LF.LFHole loc, tA) ->
       Int.LF.LFHole loc

and elTuple recT cD cPsi tuple (typRec, s) =
  match (tuple, typRec) with
  | (Apx.LF.Last m,
     Int.LF.SigmaLast(n, tA))
    ->
      Int.LF.Last (elTerm' recT cD cPsi m (tA, s))

  | (Apx.LF.Cons(m, restOfTuple),
     Int.LF.SigmaElem(_x, tA, restOfTypRec))
    ->
      let tM = elTerm recT  cD cPsi m (tA, s) in
      let extended_s = Int.LF.Dot (Int.LF.Obj tM, s) in
      let tuple' = elTuple recT cD cPsi restOfTuple (restOfTypRec, extended_s) in
        Int.LF.Cons (tM, tuple')

  | (_, _) -> raise (Error.Violation ("elTuple arity mismatch"))


and elTerm' recT cD cPsi r sP = match r with

  | Apx.LF.Ann (_loc, m, a) ->
    elTerm' recT cD cPsi m sP

  | Apx.LF.LFHole loc ->
    Lfholes.collect (loc, cD, cPsi, sP); Int.LF.LFHole loc

  | Apx.LF.Root (loc, Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      (* let s  = mkShift recT cPsi in *)
      let s = Substitution.LF.id in
      let (tS, sQ) = elSpineI loc recT cD cPsi spine i (tA, s) in
      let tR = Int.LF.Root (loc, Int.LF.Const c, tS)  in
      begin
	try
          Unify.unifyTyp cD cPsi sQ sP ;
	  tR
        with
         | Unify.Failure msg ->
           raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
         | Unify.NotInvertible ->
           raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
      end

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
    begin
      try
        let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        let (tS, sQ) = elSpine loc recT cD cPsi spine (tA, Substitution.LF.id) in
        begin
	  try
	    (Unify.unifyTyp cD  cPsi sQ sP;
	     Int.LF.Root (loc, Int.LF.BVar x, tS))
          with
	    | Unify.Failure msg ->
	      raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
            | _ -> raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
        end
      with _ -> raise (Error (loc, CompTypAnn))
      end

  | Apx.LF.Root (loc, Apx.LF.FVar x, spine) as m ->
   (* This case can only happen durin Pi *)
      begin match recT with
        | Pi ->
            begin try
              let Int.LF.Type tA = FVar.get x in
                (* For type reconstruction to succeed, we must have
                 *
                 *  . |- tA <= type
                 *  This will be enforced during abstraction
                 *)
              let s = mkShift recT cPsi in
              let (tS, sQ) = elSpine loc recT cD cPsi spine (tA, s) in
              begin
		try
                  Unify.unifyTyp cD cPsi sQ sP;
                  Int.LF.Root (loc, Int.LF.FVar x, tS)
                with
		  | Unify.Failure msg ->
                    raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
                  | _ ->
                    raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
              end

            with Not_found ->
              begin
		try
                  let (_l, p_spine) = patSpine spine in
                  let s = mkShift recT cPsi in
                  let (tS, tA) =  elSpineSynth recT  cD cPsi p_spine s sP in
                  (* For type reconstruction to succeed, we must have
                   *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
                   *  This will be enforced during abstraction.
                   *)
                  FVar.add x (Int.LF.Type tA);
                  Int.LF.Root (loc, Int.LF.FVar x, tS)
		with NotPatSpine ->
                  (let _ = dprint (fun () -> "[elTerm'] FVar case -- Not a pattern spine...") in
                   let v = Whnf.newMVar None (cPsi, Int.LF.TClo sP) Int.LF.Maybe in
                   let tAvar = Int.LF.TypVar (Int.LF.TInst (ref None, cPsi, Int.LF.Typ, ref [])) in
                   add_fvarCnstr (tAvar, m, v);
                   Int.LF.Root (loc, Int.LF.MVar (v, Substitution.LF.id), Int.LF.Nil))
              end
            end
        | Pibox -> raise (Index.Error (loc, Index.UnboundName x))
      end


  | Apx.LF.Root (loc, Apx.LF.Hole, spine) ->
      begin try
     (let (_l, pat_spine) = patSpine spine in
      let sshift = mkShift recT cPsi in
      let (tS, tA) = elSpineSynth recT  cD cPsi pat_spine sshift sP in
        (* For LF type reconstruction to succeed, we must have
         *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
         *  This will be enforced during abstraction.
         *)
        (* Potentially need to handle eta-expansion -bp *)
        begin match recT with
          | Pi ->
              (* let u =  Whnf.newMVar (cPsi, tA) in
                Int.LF.Root (loc, Int.LF.MVar(u, Substitution.LF.id), tS) *)
              let u =  Whnf.newMVar None (Int.LF.Null, tA) Int.LF.Maybe in
                Int.LF.Root (loc, Int.LF.MVar(u, sshift), tS)
          | Pibox ->
              begin match tA with
                | Int.LF.Atom (_, a, _ ) ->
                    let (cPhi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
                    let s_proj = ConvSigma.gen_conv_sub conv_list in
		    let s_tup    = ConvSigma.gen_conv_sub' conv_list in
		    let tA' = Whnf.normTyp (tA, s_tup) in 
		      (*  cPsi |- s_proj : cPhi
			  cPhi |- s_tup : cPsi       
			  cPhi |- tQ   where  cPsi |- tA  !! tQ = [s_tup]tA !!  *)
                    (* let tA'    = ConvSigma.strans_typ cD cPsi (tA, Substitution.LF.id) conv_list  in*)
                    let h      = if !strengthen then
                                   let (ss', cPhi') = Subord.thin' cD a cPhi in
                                     (* cPhi |- ss' : cPhi' *)
                                   let ssi' = Substitution.LF.invert ss' in
                                     (* cPhi' |- ssi : cPhi *)
                                     (* cPhi' |- [ssi]tQ    *)
                                   let u =  Whnf.newMMVar None (cD, cPhi', Int.LF.TClo (tA', ssi')) Int.LF.Maybe in
                                     Int.LF.MMVar((u, Whnf.m_id), Substitution.LF.comp ss'  s_proj)
                                 else
                                   let u = Whnf.newMMVar None (cD, cPhi, tA')  Int.LF.Maybe in
                                     Int.LF.MMVar ((u, Whnf.m_id), s_proj)
                    in
                      Int.LF.Root (loc, h, tS)
                | _ -> raise (Error (loc, HolesFunction))
              end
        end)
      with NotPatSpine -> raise (Error (loc, NotPatternSpine))
      end
  (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) as m ->
      begin try
        let (cD_d, Int.LF.Decl(_, Int.LF.ClTyp (Int.LF.MTyp tQ, cPhi), _)) = FCVar.get u in
	let _ = dprint (fun () -> "Retrieving type of FMV " ^ Id.render_name u ^
      " of type " ^ P.typToString cD_d cPhi (tQ, Substitution.LF.id) ^ "[" ^
			  P.dctxToString cD_d cPhi ^ "]" ^
"\n in cD_d = " ^ P.mctxToString cD_d) in

        let _ = dprint (fun () -> "Current context cD = " ^ P.mctxToString cD) in
	let d = Context.length cD - Context.length cD_d in

        let _ = dprint (fun () -> "d = " ^ string_of_int d) in
	let (tQ', cPhi') = if d = 0 then (tQ, cPhi) else
          (if d > 0 then
	     (Whnf.cnormTyp (tQ, Int.LF.MShift d), Whnf.cnormDCtx (cPhi, Int.LF.MShift d))
           else
             let rec createMSub d = if d = 0 then Int.LF.MShift 0 else
                Int.LF.MDot (Int.LF.MUndef, createMSub (d+1)) in
             let t = createMSub d in
	     let roccur = Unify.MMVarRef (ref None) (* create dummy mmvar since pruning requires it *) in
	     let cPhi' = Unify.pruneDCtx cD cPhi t roccur in
	     let tQ'   = Unify.pruneTyp cD cPhi' (Context.dctxToHat cPhi')
	                       (tQ, Substitution.LF.id) (t, Substitution.LF.id)
			       roccur
	     in
               (tQ' , cPhi'))

           in
          (* For type reconstruction to succeed, we must have
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
           * meta-variables in cD. This will be enforced during abstraction *)
	let _ = dprint (fun () -> "[elTerm] Normalized retrieved type of FMV " ^ Id.render_name u ^
      " of type " ^ P.typToString cD cPhi' (tQ', Substitution.LF.id) ^ "[" ^
			  P.dctxToString cD cPhi' ^ "]") in
        let s'' = elSub loc recT cD cPsi s Int.LF.Subst cPhi' in
        let _ = dprint (fun () -> "[elTerm] s = " ^ P.subToString cD cPsi s'') in
        let _ = dprint (fun () -> "[elTerm] domain : " ^ P.dctxToString cD cPhi') in
        let _ = dprint (fun () -> "[elTerm] range : " ^ P.dctxToString cD cPsi) in
        let _ = dprint (fun () -> "[elTerm] Expected type : " ^ P.typToString cD cPsi sP)
          in
        (* We do not check here that tP approx. [s']tP' --
           * this check is delayed to reconstruction *)
        let tR = Int.LF.Root (loc, Int.LF.FMVar (u, s''), Int.LF.Nil) in
        begin try
		Unify.unifyTyp cD  cPsi (tQ', s'') sP ;
		tR
	  with Unify.Failure msg ->
            raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), (tQ', s''), sP)))
            |_ -> raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), (tQ', s''), sP)))
          end
      with
        | Not_found ->
          if isPatSub s then
          (* 1) given cPsi and s synthesize the domain cPhi
           * 2) [s]^-1 ([s']tP) is the type of u
           *)
          let _ = dprint (fun () -> "Synthesize domain for meta-variable " ^ (string_of_name u)
                         ^ " in context " ^ P.dctxToString cD cPsi) in
          let (cPhi, s'') = synDom cD loc cPsi s in
          let ss =  Substitution.LF.invert s'' in
          let _ = dprint (fun () ->  " with substitution "  ^ P.subToString cD cPhi s'' ^
                         " and domain  " ^ P.dctxToString cD cPhi ) in
              let tP = pruningTyp loc cD cPsi (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) in
                (* let tP = Int.LF.TClo (Int.LF.TClo sP, Substitution.LF.invert s'') in *)
                (* For type reconstruction to succeed, we must have
                 * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
                 * This will be enforced during abstraction.
                 *)
	      let _ = dprint (fun () -> "Add FMVar " ^ Id.render_name u ^
				" of type " ^ 
				P.dctxToString cD cPhi ^ " |- " ^ 
				P.typToString cD cPhi (tP, Substitution.LF.id) ) in
                FCVar.add u (cD, Int.LF.Decl(u, Int.LF.ClTyp (Int.LF.MTyp tP, cPhi), Int.LF.Maybe));
		(*The depend paramater here affects both mlam vars and case vars*)
                Int.LF.Root (loc, Int.LF.FMVar (u, s''), Int.LF.Nil)

          else
           if isProjPatSub s then
             let _ = dprint (fun () -> "Synthesize domain for meta-variable " ^ (string_of_name u) ) in
             let _ = dprint (fun () -> "isProjPatSub ... " ) in
             let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
             let _ = dprint (fun () -> "flattenDCtx done " ^ P.dctxToString cD flat_cPsi ^ "\n") in
             let _ = dprint (fun () -> "conv_list " ^ conv_listToString conv_list ) in
             let flat_s = flattenProjPat loc cD s conv_list cPsi in
             let _ = dprint (fun () -> "flattenProjPat done " ) in

             let (cPhi, s'') = synDom cD loc flat_cPsi flat_s in
               (*
                  cD ; cPsi |- sP
                  cD ; cPsi |- s : cPsi'   and   cD ; cPsi' |- P

                  flat_cPsi |-  s'' : cPhi
                  cPhi      |-  ss  : flat_cPsi

               *)
             let ss =  Substitution.LF.invert s'' in

             let _ = dprint (fun () -> "[synDom] (after flattening) cPhi = " ^ P.dctxToString cD cPhi ^ "\n") in
	     let s_tup    = ConvSigma.gen_conv_sub' conv_list in
	     let (tP, s_p) = sP in 
	     let tP' = Whnf.normTyp (tP, Substitution.LF.comp s_p s_tup) in 
             (* let tP' = ConvSigma.strans_typ cD cPsi sP conv_list in *)
             let _ = dprint (fun () -> "[synDom] Prune type sP = " ^ P.typToString cD cPsi sP ) in
      (*             let _ = dprint (fun () -> "[synDom] Prune flattened type " ^ P.typToString cD cPhi (tP', Substitution.LF.id) ) in *)
             let _ = dprint (fun () -> "[synDom] Prune flattened type (1 with resp. flat_cPsi) " ^ P.typToString cD flat_cPsi (tP', Substitution.LF.id) ) in
(*             let _ = dprint (fun () -> "[synDom] Prune flattened type (2 with resp. cPhi) (may not exist yet)" ^ P.typToString cD cPhi (tP', ss) ) in *)
             let _ = dprint (fun () -> "         with respect to ss = " ^ P.subToString cD cPhi ss ) in

             let tP = pruningTyp loc cD flat_cPsi
                         (Context.dctxToHat flat_cPsi) (tP', Substitution.LF.id) (Int.LF.MShift 0, ss)  in

             let sorig = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
             let _ = dprint (fun () -> "sorig = " ^ P.subToString cD cPsi sorig ^ "\n") in
            (* For type reconstruction to succeed, we must have
             * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
             * This will be enforced during abstraction.
             *)
             let _ = dprint (fun () -> "[synDom] Type of mvar " ^ (string_of_name u) ^ ":" ^
                               P.typToString cD cPhi (tP, Substitution.LF.id) ^ " [ " ^
                               P.dctxToString cD cPhi ^ " ] ") in

            FCVar.add u (cD, Int.LF.Decl (u, Int.LF.ClTyp (Int.LF.MTyp tP, cPhi), Int.LF.Maybe));
            Int.LF.Root (loc, Int.LF.FMVar (u, sorig), Int.LF.Nil)

           else
(*  TO BE ADDED, if we want to synthesize the type of meta-variables
    applied to variable tuples instead of individual variables -bp
	     if isTuplePatSub s then
               let _ = dprint (fun () -> "Synthesize domain for meta-variable " ^ u.string_of_name
					 ^ " in context "
					 ^ P.dctxToString cD cPsi) in
	       let s_flat = flattenSub s in
               let (cPhi, s'') = synDom cD loc cPsi s_flat in
               let ss =  Substitution.LF.invert s'' in
               let _ = dprint (fun () ->  " with substitution "  ^ P.subToString cD cPhi s'' ^
					    " and domain  " ^ P.dctxToString cD cPhi ) in
               let tP = pruningTyp loc cD cPsi (*?*) (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) in
               (* let tP = Int.LF.TClo (Int.LF.TClo sP, Substitution.LF.invert s'') in *)
               (* For type reconstruction to succeed, we must have
                 * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
                 * This will be enforced during abstraction.
                 *)
	       let (cPhi', rho') = sigmifyDctx cPhi s0 in (* cPhi' |-  rho : cPhi *)
	       let rho = elSub loc recT cD cPhi' rho' cPhi in
	       let s0 = elSub loc recT cD cPsi s cPhi' in
	       let tP' = Whnf.normTyp (tP, rho) in
	       let _ = dprint (fun () -> "Added FMVar " ^ Id.render_name u ^
					" of type " ^ P.typToString cD cPhi' (tP', Substitution.LF.id) ^
					  "[" ^ P.dctxToString cD cPhi' ^ "]") in
               FCVar.add u (cD, Int.LF.MDecl(u, Whnf.norm (tP, rho), cPhi'));
               Int.LF.Root (loc, Int.LF.FMVar (u, s0), Int.LF.Nil)

	     else
 *)
             ( (* if s = substvar whose type is known *)
              let v = Whnf.newMMVar None (cD, cPsi, Int.LF.TClo sP) Int.LF.Maybe in
                add_fcvarCnstr (m, v);
                Int.LF.Root (loc, Int.LF.MMVar ((v, Int.LF.MShift 0), Substitution.LF.id), Int.LF.Nil)

             )
        | Error.Violation msg  ->
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg) ;
            raise (Error (loc, CompTypAnn ))

      end



  | Apx.LF.Root (loc, Apx.LF.FPVar (p, s), spine) as _m ->
      begin try
        let (cD_d, Int.LF.Decl (_, Int.LF.ClTyp (Int.LF.PTyp tA, cPhi), _)) = FCVar.get p in
	let d = Context.length cD - Context.length cD_d in
	let (tA, cPhi) = if d = 0 then (tA, cPhi) else
	  (Whnf.cnormTyp (tA, Int.LF.MShift d), Whnf.cnormDCtx (cPhi, Int.LF.MShift d)) in
          (* For type reconstruction to succeed, we must have
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
           * meta-variables in cD. This will be enforced during abstraction *)

        let s'' = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, s'')  in
        let tR = Int.LF.Root (loc, Int.LF.FPVar (p, s''), tS) in
          begin try
            Unify.unifyTyp cD cPsi sQ sP;
            tR
            with
	      | Unify.Failure msg ->
		raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))
              | _ ->
		raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))
          end

      with
        | Not_found ->
          begin match (spine, isPatSub s) with
            | (Apx.LF.Nil, true) ->
                (* 1) given cPsi and s, synthesize the domain cPhi
                 * 2) [s]^-1 ([s']tP) is the type of u
                 *)
                (* Need to check that the inferred type for p is indeed in cPsi's schema -bp *)
                let (cPhi, s'') = synDom cD loc cPsi s in
                let si          = Substitution.LF.invert s'' in
                let tP = pruningTyp loc cD cPsi (Context.dctxToHat cPsi) sP
                                (Int.LF.MShift 0, si)  in
                (* let tP          = Whnf.normTyp (Int.LF.TClo sP, si) in*)
                  (* For type reconstruction to succeed, we must have
                   * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
                   * This will be enforced during abstraction.
                   *)
                let _ = begin match cPhi with
                  | Int.LF.Null -> dprint (fun () -> "Add Parameter variable in empty context !!! of type : " ^
                    P.dctxToString cD cPhi ^ " |- " ^ P.typToString cD cPhi (tP, Substitution.LF.id))
                    ;
                    dprint (fun () -> "cPsi = " ^ P.dctxToString cD cPsi);
                    dprint (fun () -> "s = " ^ P.subToString cD cPhi s'')
                  | _ -> () end in
                  FCVar.add p (cD, Int.LF.Decl(p, Int.LF.ClTyp (Int.LF.PTyp (Whnf.normTyp (tP,Substitution.LF.id)),  cPhi), Int.LF.Maybe));
                  Int.LF.Root (loc, Int.LF.FPVar (p, s''), Int.LF.Nil)

            | (Apx.LF.Nil, false) -> 
		(* cD ; cPsi |- #p[s] : sP *)
		(* cannot infer type of #p *)
		raise (Error (loc, CompTypAnn ))
            | (_, _) ->  raise (Error (loc, NotPatternSpine))
          end
        | Error.Violation msg  ->
            dprint (fun () -> "[elClosedTerm] Violation: " ^ msg) ;
            raise (Error (loc, CompTypAnn ))
      end

  (* Reconstruct: Projection *)
  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.FPVar (p, s), proj), spine) as _m ->
      (* Other case where spine is not empty is not implemented -bp *)
        begin try
          let _ = dprint (fun () -> "[Reconstruct Projection Parameter] #" ^
			    (string_of_name p) ^ "." ^ string_of_proj proj) in
          let (cD_d, Int.LF.Decl (_, Int.LF.ClTyp (Int.LF.PTyp ((Int.LF.Sigma typRec) as tA), cPhi), _)) = FCVar.get  p in
	  let d = Context.length cD - Context.length cD_d in
	  let (tA, cPhi) = if d = 0 then (tA, cPhi) else
	    (Whnf.cnormTyp (tA, Int.LF.MShift d), Whnf.cnormDCtx (cPhi, Int.LF.MShift d)) in

          let _ = dprint (fun () -> "[Reconstruct Projection Parameter] Found its type ") in
          let _ = dprint (fun () -> "      with type " ^
			    P.typToString cD cPhi (tA, Substitution.LF.id) ^ "[" ^ P.dctxToString cD cPhi ^ "]") in
	  let k = getProjIndex loc cD cPsi typRec proj in
          let s'' = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
          let sA =  begin try
                         Int.LF.getType  (Int.LF.FPVar (p, s'')) (typRec, s'') k 1
                    with _ -> raise (Error (loc, ProjNotValid (cD, cPhi, k,
                                                         (tA, Substitution.LF.id))))
                    end
              in
              let (tS, sQ ) = elSpine loc recT cD cPsi spine (Int.LF.TClo sA, s'')  in
                begin try
                  (Unify.unifyTyp cD cPsi (Int.LF.TClo sQ, s'') sP ;
                   Int.LF.Root (loc,  Int.LF.Proj (Int.LF.FPVar (p, s''), k), tS))
                with
		  | Unify.Failure msg ->
		      raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
		  | _ ->
		      raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
            end
        with Not_found ->
	  (dprint (fun () -> "[Reconstruct Projection Parameter] #" ^
			    (string_of_name p) ^ "." ^ string_of_proj proj ^ " NOT FOUND") ;
          begin match (isPatSub s, spine) with
            | (true, Apx.LF.Nil) ->
                let (cPhi, s'') = synDom cD loc cPsi s in
                let _ = dprint (fun () -> "#p is used in context cPsi = " ^  P.dctxToString cD cPsi) in
                let _ = dprint (fun () -> "           at type tP = " ^ P.typToString cD cPsi sP) in
                let _ = dprint (fun () -> "Context of #p : cPhi = " ^ P.dctxToString cD cPhi) in
                let si          = Substitution.LF.invert s'' in
                let tP = pruningTyp loc cD cPsi
		  (Context.dctxToHat  cPsi) sP (Int.LF.MShift 0, si)  in
                let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD) in
                let _ = dprint (fun () -> "cPsi = " ^ P.dctxToString cD cPsi) in
                let schema =  getSchema cD (Context.ctxVar (Whnf.cnormDCtx  (cPsi, Whnf.m_id))) loc in
		let _ = dprint (fun () -> "[ctxVar] done") in
                let h = Int.LF.FPVar (p, Substitution.LF.id) in
                let (typRec, s_inst,  kIndex) =
                  begin match synSchemaElem loc recT cD cPhi (tP, Substitution.LF.id) (h, proj) schema with
                  | None , _ -> raise (Error.Violation ("type sP = " ^ P.typToString cD cPhi (tP, Substitution.LF.id) ^ " not in schema " ^
                                             P.schemaToString schema))
                  | Some (typrec, subst) , index -> (typrec, subst, index)
                  end in
                let tB  =
                  begin match typRec with
                  | Int.LF.SigmaLast(n, tA) ->
                      (dprint (fun () -> "synType for PVar: [SigmaLast]" ^ P.typToString cD cPhi (tA, s_inst) ^ "\n"); tA)
                  | typRec' ->
                      (dprint (fun () -> "synType for PVar: [SigmaElem]" ^ P.typRecToString cD cPhi (typRec', s_inst) ^ "\n") ;
                       Int.LF.Sigma typRec' )
                  end in
                  FCVar.add p (cD, Int.LF.Decl (p, Int.LF.ClTyp (Int.LF.PTyp (Whnf.normTyp (tB, s_inst)), cPhi), Int.LF.Maybe));
                  Int.LF.Root (loc,  Int.LF.Proj (Int.LF.FPVar (p, s''), kIndex),  Int.LF.Nil)

            | (false, Apx.LF.Nil) -> failwith "Not implemented"
                (* let q = Whnf.newPVar None (cPsi, Int.LF.TClo sP)  in *)
                (*   add_fcvarCnstr (m, q); *)
                (*   Int.LF.Root (loc,  Int.LF.Proj (Int.LF.PVar (q, Substitution.LF.id), k),  Int.LF.Nil) *)

            | ( _ , _ ) -> raise (Error (loc, ParamFun))
          end
	  )
        end


  (* Reconstruction for meta-variables  *)
  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (Int.LF.MObj tN, Int.LF.ClTyp (Int.LF.MTyp tQ, cPhi)), s'), Apx.LF.Nil)  ->
          let _ = dprint (fun () -> "[elTerm] Projected type of already reconstructed object " ^
			    " which is embedded into an approximate object:\n                  " ^
			    P.dctxToString cD cPhi ^ " |- " ^
			    P.normalToString cD cPhi (tN, Substitution.LF.id) ^
			    " : " ^ P.typToString cD cPhi (tQ, Substitution.LF.id)) in
          let _ = dprint (fun () -> " in cD = " ^ P.mctxToString cD ) in

          let _ = dprint (fun () -> "\n [elTerm] Show cPsi = " ^ P.dctxToString cD  cPsi) in
          let _ = dprint (fun () -> "\n [elTerm] Show cPhi = " ^ P.dctxToString cD cPhi) in
          let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in

          let _ = dprint (fun () -> "[elTerm] " ^ P.dctxToString cD cPsi ^ " |- " ^ P.subToString cD cPsi s'' ^ " : " ^ P.dctxToString cD cPhi ) in

          let _   = dprint (fun () -> "[elTerm] Apx-mvar: Expected type: " ^ P.typToString cD cPsi sP ^ "\n") in
          let _   = dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cD cPsi (tQ, s'') ^ "\n") in
          begin
	    try
	      (* This case only applies to Beluga; MInst are introduced during cnormApxTerm. *)
	      Unify.unifyTyp cD  cPsi (tQ, s'') sP ;
	      dprint (fun () -> "[elTerm] reconstruction of mvar done ");
	      dprint (fun () -> "  sQ = " ^ P.typToString cD cPsi (tQ,s'') ^ " == " ^ P.typToString cD cPsi sP) ;
	      dprint (fun () -> "  tN = " ^ P.normalToString cD cPsi (tN, s''));
	      Int.LF.Clo(tN, s'')
	    with Error.Violation msg  ->
              (dprint (fun () -> "[elTerm] Violation: " ^ msg);
               dprint (fun () -> "[elTerm] Encountered term: " ^
			 P.normalToString cD cPsi (tN,s''));
		dprint (fun () -> "[elTerm] Expected type: " ^ P.typToString cD cPsi sP);
		dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cD cPsi (tQ, s''));
               raise (Error (loc, CompTypAnn)))
              |  Unify.Failure msg  ->
		dprint (fun () -> "[elTerm] Unification Violation: " ^ msg) ;
		dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cD cPsi (tN,s''));
		dprint (fun () -> "[elTerm] in cD  = " ^ P.mctxToString cD );
		dprint (fun () -> "[elTerm] Expected type: " ^ P.typToString cD cPsi sP);
		dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cD cPsi (tQ, s''));
		dprint (fun () -> "[elTerm] cD = " ^ P.mctxToString cD);
		raise (Error (loc, TypMismatchElab (cD, cPsi, sP, (tQ,s''))))
              | _ ->
		begin
		  dprint (fun () -> "[elTerm] Encountered term: " ^ P.normalToString cD cPsi (tN,s''));
		  dprint (fun () -> "[elTerm] Inferred type: " ^ P.typToString cD cPsi (tQ, s'') ^ " does not match expected type");
		  raise (Error (loc, CompTypAnn))
		end
	  end

  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset u, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxMDec cD u in
	let _ = dprint (fun () -> "\n[elTerm] MVAR CASE - OFFSET\n") in
        let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
	let _ = dprint (fun () -> "\n[elTerm] MVAR CASE - OFFSET - ELABORATION elSub DONE \n") in
        let (tS, sQ) = elSpine loc recT cD cPsi spine (tA, s'') in
	let _ = dprint (fun () -> "\n[elTerm] MVAR CASE - OFFSET - ELABORATION elSpine DONE \n") in
        let tR = Int.LF.Root (loc, Int.LF.MVar (Int.LF.Offset u, s''), tS) in
	let _ = dprint (fun () -> "\n cPsi = " ^ P.dctxToString cD cPsi ^ "\n") in
	let tQ = Whnf.cnormTyp ((Whnf.normTyp sQ), Whnf.m_id) in 
	let _ = dprint (fun () -> "\n[elTerm] UNIFY sQ = " ^ P.typToString cD cPsi (tQ, Substitution.LF.id) ^ "\nwith sP " ^ P.typToString cD cPsi sP ^ "\n") in
        begin
	  try
            Unify.unifyTyp cD cPsi sQ sP;
            tR
          with
	    | Unify.Failure msg ->
              raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))
            | _ ->
              raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))
          end
      with Error.Violation msg ->
        dprint (fun () -> "[elTerm] Violation: " ^ msg);
        raise (Error (loc, CompTypAnn))
      end

  (* Reconstruction for parameter variables *)
  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.MInst (Int.LF.PObj h, Int.LF.ClTyp (Int.LF.PTyp tA, cPhi)), s'), spine) ->
      begin (* try *)
        let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, s'')  in
        let _ = Unify.unifyTyp cD cPsi sQ sP  in
          begin match h with
              | Int.LF.BVar k ->
                  begin match Substitution.LF.bvarSub k s'' with
                    | Int.LF.Head (Int.LF.BVar j) -> Int.LF.Root (loc, Int.LF.BVar j, tS)
                    | Int.LF.Head (Int.LF.PVar (p,r'))   -> Int.LF.Root (loc, Int.LF.PVar (p, Substitution.LF.comp r' s''), tS)
                  end
              | Int.LF.PVar (p, r) -> Int.LF.Root (loc, Int.LF.PVar (p, Substitution.LF.comp r s''), tS)
	      (* | Int.LF.Proj (Int.LF.PVar (p,r), i) -> Int.LF.Root (loc, Int.LF *)
            end

      (* with _  -> *)
      (*   raise (Error (loc, CompTypAnn )) *)
        (* raise (Error (loc, TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))*)
      end


  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p,s'), spine) ->
    begin
      try
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
        let (tS, sQ) = elSpine loc recT cD cPsi spine (tA, s'')  in
        let tR = Int.LF.Root (loc, Int.LF.PVar (p, s''), tS) in
        begin
	  try
            Unify.unifyTyp cD cPsi sQ sP ;
            tR
          with
	    | Unify.Failure msg ->
              raise (Check.LF.Error (loc, Check.LF.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))
        end
      with Error.Violation msg  ->
        dprint (fun () -> "[elTerm] Violation: " ^ msg);
        raise (Error (loc, CompTypAnn ))
    end

  (* Reconstruction for projections *)
  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.BVar x , proj),  spine) ->
      let Int.LF.TypDecl (_, Int.LF.Sigma recA) =
        begin try Context.ctxSigmaDec cPsi x with
          _ -> raise (Error (loc, ProjBVarImpossible (cD, cPsi, x, proj)))
        end in
      let k       = getProjIndex loc cD cPsi recA proj in
      let sA       = begin try Int.LF.getType (Int.LF.BVar x) (recA, Substitution.LF.id) k 1
                     with _ -> raise (Error (loc, ProjNotValid (cD, cPsi, k,
                                                         (Int.LF.Sigma recA, Substitution.LF.id))))
                     end
       in
      let (tS, sQ) = elSpine loc recT cD  cPsi spine sA in
      begin
	try
          Unify.unifyTyp cD cPsi sQ sP;
          Int.LF.Root (loc, Int.LF.Proj (Int.LF.BVar x, k), tS)
        with
	  | Unify.Failure msg ->
           raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
      end

  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset p,t), proj),  spine) ->
    begin
      match Whnf.mctxPDec cD p with
        | (_, Int.LF.Sigma recA, cPsi') ->
          let t' = elSub loc recT cD  cPsi t Int.LF.Subst cPsi' in
	  let k       = getProjIndex loc cD cPsi recA proj in
          let sA = begin try
                      Int.LF.getType (Int.LF.PVar (p, t')) (recA,  t') k 1
                   with _ -> raise (Error (loc, ProjNotValid (cD, cPsi, k,
                                                         (Int.LF.Sigma recA, t'))))
                    end
          in
          let _ = dprint (fun () -> "[elTerm'] PVar " ^ P.headToString cD cPsi
                            (Int.LF.Proj (Int.LF.PVar (p, t'), k))) in

          let _ = dprint (fun () -> "[elTerm'] against type " ^ P.typToString cD cPsi sA) in
          let (tS, sQ) = elSpine loc recT cD  cPsi spine sA in
          begin
	    try
              Unify.unifyTyp cD cPsi sQ sP;
              Int.LF.Root (loc, Int.LF.Proj (Int.LF.PVar (p,t'), k), tS)
	    with
	      | Unify.Failure msg ->
                raise (Error (loc, TypMismatchElab (cD, cPsi, sP, sQ)))
          end
        | (_, Int.LF.PiTyp _, _) -> raise (Error (loc, IllTypedElab (cD, cPsi, sP, VariantPi)))
        | (_, Int.LF.Atom _, _) -> raise (Error (loc, IllTypedElab (cD, cPsi, sP, VariantAtom)))
    end


  | Apx.LF.Root (loc, Apx.LF.Proj(Apx.LF.PVar (Apx.LF.MInst (Int.LF.PObj h, Int.LF.ClTyp (Int.LF.PTyp tA, cPhi)), s'), proj), spine) ->
      begin try
        let recA =
              match tA with
              | Int.LF.Sigma recA -> recA
              | _ ->
                  dprint (fun () -> "Type of Parameter variable " ^ P.headToString cD cPhi h
                                  ^ "not a Sigma-Type, yet used with Projection; found "
                                  ^ P.typToString cD cPhi (tA, Substitution.LF.id) ^ "\n ill-typed") ;
                  raise (Error.Violation "Type of Parameter variable not a Sigma-Type, yet used with Projection; ill-typed")
        in
        let s''     = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
	let k       = getProjIndex loc cD cPsi recA proj in
        let sA      = begin try
                           Int.LF.getType h (recA, s'') k 1
                        with _ -> raise (Error (loc, ProjNotValid (cD, cPsi, k,
                                                         (Int.LF.Sigma recA, s''))))
                        end
        in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine sA  in
        let _ = Unify.unifyTyp cD cPsi sQ sP  in
          begin match h with
              | Int.LF.BVar y ->
                  begin match Substitution.LF.bvarSub y s'' with
                    | Int.LF.Head (Int.LF.BVar x) ->
                        Int.LF.Root (loc, Int.LF.Proj(Int.LF.BVar x, k), tS)
                    | Int.LF.Head (Int.LF.PVar (p,r'))   ->
                        Int.LF.Root (loc, Int.LF.Proj(Int.LF.PVar (p, Substitution.LF.comp r' s''), k), tS)
                  end
              | Int.LF.PVar (p, r) ->
                  Int.LF.Root (loc, Int.LF.Proj(Int.LF.PVar (p, Substitution.LF.comp r s''), k), tS)
            end

      with _   ->
        raise (Error (loc, CompTypAnn ))
        (* raise (Error.Error (loc, Error.TypMismatch (cD, cPsi, (tR, Substitution.LF.id), sQ, sP)))*)
      end

  | Apx.LF.Root (loc, Apx.LF.Proj (Apx.LF.PVar (Apx.LF.MInst _ , _), _ ), _) ->
      raise (Error.Violation "[elTerm'] Proj (PVar (MInst _, _  ) _ , _ )")

  | Apx.LF.Root (loc, Apx.LF.Proj (Apx.LF.FMVar _, _ ), _) ->
      raise (Error.Violation "[elTerm'] Proj (FMVar _ , _ )")

  | Apx.LF.Root (loc, Apx.LF.PVar _, _) ->
      raise (Error.Violation "[elTerm'] PVar ")

  | Apx.LF.Root (loc, Apx.LF.FMVar (_,_), _s) -> 
    raise (Error (loc, HOMVarNotSupported))
  | Apx.LF.Root (loc, h, _s) ->
      (dprint (fun () -> "[elTerm' **] h = " ^ what_head h ^ "\n") ;
            raise (Error (loc, CompTypAnn )))

  and instanceOfSchElem loc cD cPsi (tA, s) (some_part, sB) =
    let _ = dprint (fun () -> "[instanceOfSchElem] Begin \n") in
   (* let sArec = match Whnf.whnfTyp (tA, s) with
      | (Int.LF.Sigma tArec,s') ->  (tArec, s')
      | (nonsigma, s')          ->  (Int.LF.SigmaLast nonsigma, s') in *)
    let _ = dprint (fun () -> ("tA =" ^ P.typToString cD cPsi (tA, s) ^ " \n")) in
    let dctx        = Context.projectCtxIntoDctx some_part in
    let dctxSub     = Ctxsub.ctxToSub' cD cPsi dctx in

    (* let phat        = dctxToHat cPsi in *)

    let _ =  dprint (fun () -> "***Unify.unifyTyp ("
                        ^ "\n   cPsi = " ^ P.dctxToString cD cPsi
                        ^ "\n   dctx = " ^ P.dctxToString cD dctx
                        ^ "\n   " ^  P.typToString cD cPsi (tA, s) ) in
    let _ = dprint (fun () -> "dctxSub = " ^ P.subToString cD cPsi dctxSub ^ "\n") in

    let _ = dprint (fun () ->  P.typToString cD cPsi (tA,s)) in
    let _ = dprint (fun () ->  "== " ) in
    let _ = dprint (fun () -> P.typToString cD cPsi (Int.LF.TClo sB, dctxSub) ^ "\n" )  in
    let nB  = Whnf.normTyp (Int.LF.TClo sB, dctxSub) in
    let nA  = Whnf.normTyp (tA,s) in
      begin
        try
          Unify.unifyTyp cD cPsi (nA, Substitution.LF.id) (nB, Substitution.LF.id)
        ; dprint (fun () -> "instanceOfSchElem\n"
                            ^ "  block_part = " ^ P.typToString cD cPsi (Int.LF.TClo sB, dctxSub) ^ "\n"
                            ^ "  succeeded.")
        ; (Int.LF.TClo sB, dctxSub)
        with (Unify.Failure _)  ->
          (dprint (fun () -> "Type " ^ P.typToString cD cPsi (tA,s) ^ " doesn't unify with schema element\n");
(*          dprint (fun () ->  P.typRecToString cD cPsi (block_part, dctxSub)) *)

             raise (Error (loc, TypMismatchElab (cD, cPsi, (nA, Substitution.LF.id), (nB, Substitution.LF.id)))))
          | exn ->
              (dprint (fun () -> "[instanceOfSchElem] Non-Unify ERROR -2- "); raise exn)
      end

  and instanceOfSchElemProj loc cD cPsi (tA, s) (var, proj) (Int.LF.SchElem (cPhi, trec)) =
    let _ = dprint (fun () -> "[instanceOfSchElemProj] getType of " ^ string_of_proj proj ^ ". argument\n") in
    let cPhi'  = Context.projectCtxIntoDctx cPhi in
    let _ = dprint (fun () -> " of " ^ P.typRecToString cD cPhi' (trec, Substitution.LF.id)) in
    let _ = dprint (fun () -> " var = " ^ P.headToString cD cPsi var) in
    let k = getProjIndex loc cD cPsi trec proj in
    let sA_k (* : tclo *) = Int.LF.getType var (trec, Substitution.LF.id) k 1 in  (* bp - generates  general type with some-part still intact; this tA_k is supposed to be the type of #p.1 s - hence,eventually it the some part needs to be restricted appropriately. Tue May 25 10:13:07 2010 -bp *)
    let _ = dprint (fun () -> "[instanceOfSchElemProj] retrieved the type  " ^ P.typToString cD cPhi' sA_k) in
    let (_tA'_k, subst) =
      instanceOfSchElem loc cD cPsi (tA, s) (cPhi, sA_k)
      (* tA'_k = [subst] (sA_k) = [s]tA *)
    in
      (trec, subst, k)

(* Synthesize the type for a free parameter variable *)
and synSchemaElem loc recT  cD cPsi ((_, s) as sP) (head, k) ((Int.LF.Schema elements) as schema) =
  let self = synSchemaElem loc recT cD cPsi sP (head, k) in
  let _ = dprint (fun () -> "synSchemaElem ... head = " ^
                    P.headToString cD cPsi head ^ " Projection " ^
                    string_of_proj k  ^ "\n") in
  let _ = dprint (fun () -> "[synSchemaElem]  " ^ P.typToString cD cPsi sP
                    ^ "  schema= " ^ P.schemaToString schema) in
    match elements with
      | [] -> None, -1
      | (Int.LF.SchElem (_some_part, block_part)) as elem  ::  rest  ->
          try
            let _ = dprint (fun () -> "[instanceOfSchElemProj ] ... ") in
            let (typRec, subst, k) = instanceOfSchElemProj loc cD cPsi sP (head, k) elem in
              (* Check.LF.instanceOfSchElemProj loc cO cD cPsi sP (head, k) elem in *)
            dprint (fun () -> "synSchemaElem RESULT = "
                            ^ P.typRecToString cD cPsi (typRec, subst))
          ; (Some (typRec, subst), k) (* sP *)
          with Unify.Failure _  -> self (Int.LF.Schema rest)
            | Not_found -> self (Int.LF.Schema rest)

and elClosedTerm' recT cD cPsi r = match r with
  | Apx.LF.LFHole loc ->
      raise (Error (loc, InvalidLFHole))
  | Apx.LF.Root (loc, Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      (* let s  = mkShift recT cPsi in *)
      let s = Substitution.LF.id in
      let (tS, sQ ) = elSpineI loc recT cD cPsi spine i (tA, s)   in
        (Int.LF.Root (loc, Int.LF.Const c, tS), sQ)
  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, Substitution.LF.id) in
        (Int.LF.Root (loc, Int.LF.BVar x, tS), sQ)

  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset u, s), spine) ->
      begin try
        let (_ , tA, cPhi) = Whnf.mctxMDec cD u in
        let s'' = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, s'')  in
          (Int.LF.Root (loc, Int.LF.MVar (Int.LF.Offset u, s''), tS) , sQ)
      with Error.Violation msg  ->
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (loc, CompTypAnn))
      end

  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.Offset p, s'), spine) ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, s'')  in
          (Int.LF.Root (loc, Int.LF.PVar (p, s''), tS) , sQ)
      with Error.Violation msg  ->
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (loc, CompTypAnn ))
      end


  | Apx.LF.Root (loc, Apx.LF.PVar (Apx.LF.MInst (Int.LF.PObj (Int.LF.PVar (p0,s0)), Int.LF.ClTyp (Int.LF.PTyp tA, cPhi)), s'), spine) ->
      begin try
        let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, s'')  in
          (Int.LF.Root(loc, Int.LF.PVar (p0, Substitution.LF.comp s0 s''), tS)  , sQ)
      with Error.Violation msg  ->
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (loc, CompTypAnn))
      end


  | Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.MInst (Int.LF.MObj tM', Int.LF.ClTyp (Int.LF.MTyp tA, cPhi)), s'), spine) ->
      begin try
        let s'' = elSub loc recT cD cPsi s' Int.LF.Subst cPhi in
        let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, s'')  in
          (Whnf.reduce (tM', s'') tS  , sQ)
      with Error.Violation msg  ->
        dprint (fun () -> "[elClosedTerm] Violation: " ^ msg);
         raise (Error (loc, CompTypAnn))
      end

  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.BVar x , proj),  spine) ->
      let Int.LF.TypDecl (_, Int.LF.Sigma recA) = Context.ctxSigmaDec cPsi x in
      let k  = getProjIndex loc cD cPsi recA proj in
      let sA = begin try Int.LF.getType (Int.LF.BVar x) (recA, Substitution.LF.id) k 1
                     with _ -> raise (Error (loc, ProjNotValid (cD, cPsi, k,
                                                         (Int.LF.Sigma recA, Substitution.LF.id))))
               end
       in
      let (tS, sQ) = elSpine loc recT cD  cPsi spine sA in
        (Int.LF.Root (loc, Int.LF.Proj (Int.LF.BVar x, k), tS) , sQ)

  | Apx.LF.Root (loc,  Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset p,t), proj),  spine) ->
      begin match Whnf.mctxPDec cD p with
        | (_, Int.LF.Sigma recA, cPsi') ->
            let t' = elSub loc recT cD  cPsi t Int.LF.Subst cPsi' in
	    let k  = getProjIndex loc cD cPsi recA proj in
            let sA = begin try Int.LF.getType (Int.LF.PVar (p, t')) (recA, t') k 1
                      with _ -> raise (Error (loc, ProjNotValid (cD, cPsi, k,
                                                         (Int.LF.Sigma recA, t'))))
                      end
            in
            let (tS, sQ) = elSpine loc recT cD  cPsi spine sA in
              (Int.LF.Root (loc, Int.LF.Proj (Int.LF.PVar (p,t'), k), tS) , sQ)
        | _  ->
	    dprint (fun () -> "[elClosedTerm'] Looking for p with offset " ^ R.render_offset p);
	    dprint (fun () -> "in context cD = " ^ P.mctxToString cD);
	    raise (Error (loc, CompTypAnn))
      end

  | Apx.LF.Root (loc, Apx.LF.Proj (Apx.LF.PVar (Apx.LF.MInst (Int.LF.PObj h, Int.LF.ClTyp (Int.LF.PTyp tA, cPsi')) , s ), proj) , spine ) ->
      begin match (h, tA) with
	| (Int.LF.PVar (p, s') , Int.LF.Sigma recA) ->
	    let t' = elSub loc recT cD  cPsi s Int.LF.Subst cPsi' in
	    let s = Substitution.LF.comp s' t' in
	    let k  = getProjIndex loc cD cPsi recA proj in
              begin try
	        let sA = Int.LF.getType (Int.LF.PVar (p, s)) (recA, t') k 1 in
	        let (tS, sQ) = elSpine loc recT cD  cPsi spine sA in
            (Int.LF.Root (loc, Int.LF.Proj (Int.LF.PVar (p,s), k), tS) , sQ)
              with
                  _ ->
                    raise (Error (loc, ProjNotValid (cD, cPsi, k, (Int.LF.Sigma recA, t'))))
              end

            | _  ->
    	    dprint (fun () -> "[elClosedTerm'] Looking for p " ^ P.headToString cD cPsi' h);
    		  raise (Error (loc, CompTypAnn))
          end

  | Apx.LF.Root (loc, h , _ ) ->
      (dprint (fun () -> "[elClosedTerm'] Head not covered? - " ^ (what_head h));
      raise (Error (loc, CompTypAnn )))

  | Apx.LF.Lam (loc, _, _ ) ->
      raise (Error (loc, CompTypAnn ))

  | _ -> (dprint (fun () -> "[elClosedTerm] Violation?");
                raise (Error (Syntax.Loc.ghost, CompTypAnn)))

and elSub loc recT cD cPsi s cl cPhi =
  let rec elSub' loc recT cD cPsi s cPhi =
    let svar_le = function
      | Int.LF.Ren, Int.LF.Ren
      | Int.LF.Subst, Int.LF.Subst
      | Int.LF.Ren, Int.LF.Subst -> ()
      | Int.LF.Subst, Int.LF.Ren ->
	raise (Error (loc, SubWhenRen(cD, cPsi, s)))
    in
    match (s, cPhi) with
      | (Apx.LF.EmptySub, Int.LF.Null) -> Int.LF.EmptySub
  (* begin match Context.dctxToHat cPsi with *)
  (*   | (Some psi, d) -> Int.LF.Shift (Int.LF.CtxShift psi, d) *)
  (*   | (None, d)     -> Int.LF.Shift (Int.LF.NoCtxShift, d) *)
  (* end *)

      | (Apx.LF.EmptySub, Int.LF.CtxVar cvar) ->
	begin match cvar with
	  | Int.LF.CInst ((_, ({contents = None} as cref), _, Int.LF.CTyp s_cid, _, _), _ ) ->
            (cref := Some (Int.LF.ICtx (Int.LF.Null)); Int.LF.EmptySub
         (* begin match Context.dctxToHat cPsi with *)
         (*   | (Some psi, d) -> Int.LF.Shift (Int.LF.CtxShift psi, d) *)
         (*   | (None, d)     -> Int.LF.Shift (Int.LF.NoCtxShift, d) *)
         (* end *))
	  | _     -> raise (Error (loc, IllTypedSubVar (cD, cPsi, cPhi)))
	end
      | (Apx.LF.FSVar (s_name, sigma), cPhi) ->
      (* cPsi' |- s_name : cPhi
	 cPsi  |-  sigma : cPsi'
	 Note: users cannot write closures involving subst.vars
         hence, the offset associated with the svar will be 0.

	 Note: we could lower svars s.t. the domain of an svar, i.e. cPhi,
         is a context variable.

      *)
	begin try
		let (cD_d, Int.LF.Decl(_, Int.LF.ClTyp (Int.LF.STyp (cl0, cPhi0) , cPsi0), dep)) =
		  FCVar.get s_name
		in svar_le (cl0, cl) ;
		let d = Context.length cD - Context.length cD_d in
		let (cPhi0', cPsi0') = if d = 0 then (cPhi0, cPsi0) else
		    (if d > 0 then
			(Whnf.cnormDCtx (cPhi0, Int.LF.MShift d), Whnf.cnormDCtx (cPsi0, Int.LF.MShift d))
		     else
			let rec createMSub d = if d = 0 then Int.LF.MShift 0 else
			    Int.LF.MDot (Int.LF.MUndef, createMSub (d+1)) in
			let t = createMSub d in
			(Whnf.cnormDCtx (cPhi0, t), Whnf.cnormDCtx (cPsi0, t)))

		in
        (* For type reconstruction to succeed, we must have
         *    . |- cPsi0 ctx and .|- cPhi0 ctx, i.e. cPsi0 and cPhi0  cannot depend on
         * meta-variables in cD. This will be enforced during abstraction *)

		let sigma' = elSub loc recT cD cPsi sigma Int.LF.Subst cPsi0' in
		begin try
			Unify.unifyDCtx cD cPhi cPhi0';
			Int.LF.FSVar(0, (s_name, sigma'))
		  with Unify.Failure msg ->
		    raise (Error (loc, IllTypedSubVar (cD, cPsi, cPhi)))
		end
          with Not_found ->
            if isPatSub sigma then
              let (cPsi', sigma') = synDom cD loc cPsi sigma in
              (FCVar.add s_name
		 (cD, Int.LF.Decl
		   (s_name, Int.LF.ClTyp
		     (Int.LF.STyp (cl, cPhi), cPsi'), Int.LF.Maybe));
               Int.LF.FSVar (0, (s_name, sigma')))
            else
              raise (Error (loc, NotPatSub))
          | Match_failure (_, _, _) -> raise (Error (loc, SubstVarConflict s_name))
	end

      | (Apx.LF.SVar (Apx.LF.Offset offset, s), cPhi) ->
	let (_, cPhi1, cl1, cPhi2) = Whnf.mctxSDec cD offset in
	svar_le (cl1, cl) ;
	let _ = dprint (fun () -> "[elSub] Encountered #S : "
          ^ P.dctxToString cD cPhi1 ^
          "[ " ^ P.dctxToString cD cPhi2 ^ "]") in
	begin try Unify.unifyDCtx cD (Whnf.cnormDCtx (cPhi, Whnf.m_id))
		    (Whnf.cnormDCtx (cPhi1, Whnf.m_id));
		  let s' = elSub' loc recT cD cPsi s cPhi2 in
		  let sigma = Int.LF.SVar (offset, 0, s') in
		  let _ = dprint (fun () -> "[elSub] reconstructed subst = " ^
                    P.subToString cD cPsi sigma) in
		  let _ = dprint (fun () -> "[elSub] domain : " ^ P.dctxToString cD cPhi) in
		  let _ = dprint (fun () -> "[elSub] range : " ^ P.dctxToString cD cPsi) in
		  sigma

	  with Unify.Failure msg ->
	    raise (Error (loc, IllTypedSubVar (cD, cPsi, cPhi)))
	end

      | (Apx.LF.SVar (Apx.LF.MInst (Int.LF.SObj s0, Int.LF.ClTyp (Int.LF.STyp (cl,cPhi'), cPhi2)), s), (Int.LF.CtxVar phi as cPhi)) ->
      (*     if Whnf.convDCtx cPhi cPhi' then *)
	begin try
		Unify.unifyDCtx cD cPhi cPhi';
		let s' = elSub' loc recT cD cPsi s cPhi2 in
		Substitution.LF.comp s0 s'
	  with _ ->
	    raise (Error (loc, IllTypedSubVar (cD, cPsi, cPhi)))
	end

      | (Apx.LF.RealId , cPhi) ->
	begin try Unify.unifyDCtx cD (Whnf.cnormDCtx (cPhi, Whnf.m_id)) (Whnf.cnormDCtx (cPsi, Whnf.m_id));
		  Int.LF.Shift 0
	  with Unify.Failure msg ->
	    raise (Error (loc, IllTypedSub (cD, cPsi, s, cPhi)))
	end
      | (Apx.LF.Id , Int.LF.DDec (_cPhi', _decl)) ->
	elSub' loc recT cD cPsi (Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar 1), s)) cPhi

      | (Apx.LF.Id , Int.LF.CtxVar phi) ->
	begin match Context.dctxToHat (C.cnormDCtx (cPsi, C.m_id)) with
          | (Some psi, d)  ->
	    (*            if psi = phi then  *)
            let _ = dprint (fun () -> "[elSub'] \n cD = " ^
              P.mctxToString cD ^ "\n cPsi " ^ P.dctxToString cD cPsi
              ^ "\n phi = " ^ P.dctxToString cD cPhi ^ "\n") in
            if unify_phat cD (Some phi, 0) (Some psi, 0) then
              Int.LF.Shift d
            else
		(* check for context subsumption *)
		(* if Check.LF.subsumes cD phi psi (* psi |- wk_sub : phi *)then *)
              Int.LF.Shift d
	(*              else
			raise (Error.Violation ("elSub: not identity substitution between ctxvar: "
                        ^ "`" ^ P.dctxToString cD cPhi ^ "' does not match `" ^
                        P.dctxToString cD cPsi ^ "'"))*)

          | _ ->
            raise (Error (loc, IdCtxsub))
	end

      | (Apx.LF.Dot (Apx.LF.Head h, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl (_, tA)))  ->
      (* NOTE: if decl = x:A, and cPsi(h) = A' s.t. A =/= A'
       *       we will fail during reconstruction / type checking
       *)
	let _ = dprint (fun () -> "[elSub'] elaborate head ") in
	let _ = dprint (fun () -> "[elSub'] in cPsi = " ^ P.dctxToString cD  cPsi) in
	let (h', sA') = elHead loc recT cD cPsi h cl in
	let s' = elSub'  loc recT cD cPsi s cPhi' in
	begin try
		Unify.unifyTyp cD cPsi sA' (tA, s');
		Int.LF.Dot (Int.LF.Head h', s')
	  with
            |  _ -> raise (Error (loc, TypMismatchElab (cD, cPsi, sA', (tA, s'))))
	end

      | (Apx.LF.Dot (Apx.LF.Obj m, s), Int.LF.CtxVar cvar) ->
	begin match cvar with
	  | Int.LF.CInst ((_phi, ({contents = None} as _cref), _cD', Int.LF.CTyp s_cid, _, _), _ms') ->
            raise (Error (loc, MissingInformationCtx (cD, cPhi)))
      (*          begin try
		  let tA = synTyp loc recT cD cPsi m in
		  let (cref' : dctx option ref) = {contents = None} in
		  let cPhi = Int.LF.CtxVar (Int.LF.CInst (phi, cref', s_cid, D', ms')) in
		  let cPhi = Int.LF.DDec (cPhi, Int.LF.TypDecl ( , tA)) in
		  instantiateCtxVar (cref, Int.LF.cPhi)
      *)
      (* Instantiate cref s.t. g, x:A where A is the type of m )
         (print_string "HERE";
         raise Error.NotImplemented)
      *)

	  | _     -> raise (Error (loc, IllTypedSubVar (cD, cPsi, cPhi)))
	end


      | (Apx.LF.Dot (Apx.LF.Obj m, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl(_, tA))) ->
	let s' = elSub' loc recT cD cPsi s cPhi' in
	let _ = dprint (fun () -> "[elSub]: s := " ^ P.dctxToString cD cPsi ^
          " |- " ^ P.subToString cD cPsi s' ^ " : " ^
          P.dctxToString cD cPhi' ) in
	let _ = dprint (fun () -> "[elSub] in context type : " ^ P.typToString cD cPhi' (tA, Substitution.LF.id)) in
	let _ = dprint (fun () -> "[elSub] elaborate argument checking against type : " ^ P.typToString cD cPsi (tA, s')) in
	let m' = elTerm recT cD cPsi m (tA, s') in
        Int.LF.Dot (Int.LF.Obj m', s')
      | (Apx.LF.Dot (Apx.LF.Obj m, _), Int.LF.DDec(_,_)) when cl = Int.LF.Ren ->
	 raise (Error (loc, TermWhenVar (cD, cPsi, m)))

      | (s, cPhi) ->
	dprint (fun () ->
	  let s = match s with
            | Apx.LF.Dot _ -> "Dot _ "
            | Apx.LF.EmptySub -> " . "
            | Apx.LF.Id -> " .. "
            | Apx.LF.RealId -> ""
            | Apx.LF.SVar(u,s) -> "SVAR"
            | Apx.LF.FSVar(u,s) -> "FSVAR" in
	  "Expected substitution : " ^ P.dctxToString cD cPsi  ^ " |- " ^ s ^ " : "  ^ P.dctxToString cD cPhi);
	raise (Error (loc, IllTypedSubVar (cD, cPsi, cPhi)))
  in
  elSub' loc recT cD (Whnf.cnormDCtx (cPsi, Whnf.m_id)) s (Whnf.cnormDCtx (cPhi, Whnf.m_id))


and elHead loc recT cD cPsi head cl = match head, cl with
  | Apx.LF.BVar x, _ ->
      begin try
      let _ = dprint (fun () -> "[elHead] cPsi = " ^ P.dctxToString cD cPsi ^ "|- BVar " ^ string_of_int x ) in
      let Int.LF.TypDecl (_, tA') = Context.ctxDec (Whnf.cnormDCtx (cPsi, Whnf.m_id)) x in
      let _ = dprint (fun () -> "[elHead] done") in
        (Int.LF.BVar x,  (tA' , Substitution.LF.id))
      with _ -> raise (Error (loc, BVarTypMissing (cD, cPsi, Int.LF.BVar x)))
      end
  | Apx.LF.Const c, Int.LF.Subst ->
      let tA = (Term.get c).Term.typ in
        (Int.LF.Const c , (tA, Substitution.LF.id))

  | Apx.LF.MVar (Apx.LF.Offset u, s), Int.LF.Subst ->
      begin try
        let (_ , tA, cPhi) = Whnf.mctxMDec cD u in
        let s'  = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
          (Int.LF.MVar (Int.LF.Offset u, s') , (tA, s'))
      with Error.Violation msg  ->
        dprint (fun () -> "[elHead] Violation: " ^ msg);
         raise (Error (loc, CompTypAnn ))
      end

  | Apx.LF.PVar (Apx.LF.Offset p, s), _ ->
      begin try
        let (_, tA, cPhi) = Whnf.mctxPDec cD p in
        let s' = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
          (Int.LF.PVar (p, s') , (tA, s'))
      with Error.Violation msg  ->
        dprint (fun () -> "[elHead] Violation: " ^ msg);
        raise (Error (loc, CompTypAnn ))
      end

  | Apx.LF.PVar (Apx.LF.MInst (Int.LF.PObj (Int.LF.PVar (p,r)), Int.LF.ClTyp (Int.LF.PTyp tA, cPhi)), s), _ ->
      begin try
        let _ = dprint (fun () -> "[elHead] PInst : " ^ P.headToString cD cPhi (Int.LF.PVar (p,r))) in
        let _ = dprint (fun () -> "[elHead] PInst cPhi : " ^ P.dctxToString cD  cPhi ) in
        let _ = dprint (fun () -> "[elHead] PInst target cPsi : " ^ P.dctxToString cD cPsi ) in
        let s' = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
        let r' = Substitution.LF.comp r s' in
         (Int.LF.PVar (p, r') , (tA, r'))
      with Error.Violation msg ->
        dprint (fun () -> "[elHead] Violation: " ^ msg);
        raise (Error (loc, CompTypAnn ))
      end


  | Apx.LF.FVar x, _ ->
      raise (Index.Error (loc, Index.UnboundName x))
      (* Int.LF.FVar x *)

  | Apx.LF.FMVar (u, s), Int.LF.Subst ->
      begin try
        let (offset, Int.LF.ClTyp (Int.LF.MTyp tP, cPhi)) = Whnf.mctxMVarPos cD u  in
        let s' = elSub loc recT cD cPsi s Int.LF.Subst cPhi in
         (Int.LF.MVar (Int.LF.Offset offset,s'), (tP, s'))
      with Whnf.Fmvar_not_found ->
       raise (Index.Error (Syntax.Loc.ghost, Index.UnboundName u))
      end

  | Apx.LF.FPVar (p, s), cl ->
      let (offset, Int.LF.ClTyp (Int.LF.PTyp tA, cPhi)) = Whnf.mctxMVarPos cD p  in
      let s' = elSub loc recT cD cPsi s cl cPhi in
        (Int.LF.PVar (offset, s') , (tA, s'))

  | Apx.LF.Proj (head, proj), _ ->
      let (head', sA) = elHead loc recT cD cPsi head cl in
      let (sAi, i) = begin match Whnf.whnfTyp sA with
                 | (Int.LF.Sigma tA'rec, s') ->
		   let i  = getProjIndex loc cD cPsi tA'rec proj in
                   (Int.LF.getType head' (tA'rec, s') i 1, i)
                 | (tA',s') -> raise (Error.Violation ("[elHead] expected Sigma type  "
                                                 ^ "found type " ^ P.typToString cD cPsi (tA', s')))
                end
      in
        (Int.LF.Proj (head', i) , sAi)

  | Apx.LF.Const _, Int.LF.Ren
  | Apx.LF.MVar (Apx.LF.Offset _, _), Int.LF.Ren
  | Apx.LF.FMVar (_, _), Int.LF.Ren ->
    raise (Error (loc, TermWhenVar (cD, cPsi, (Apx.LF.Root (loc, head, Apx.LF.Nil)))))

  | h, _ -> raise (Error.Violation ("thisone" ^ what_head h))

(* elSpineI  recT cD cPsi spine i sA  = (S : sP)
 * elSpineIW recT cD cPsi spine i sA  = (S : sP)
 *
 *   where sA = (A,s) and sP = (P,s')
 *     and sA and sP in whnf
 *
 * Pre-condition:
 *   U = free variables
 *   O = meta-variables for implicit arguments
 *
 * Invariant:
 *
 * If O1 ; U1 ; (cD ; cPsi) |- spine <= [s]A  /_r (O2 ; U2) S
 * then
 *    O2 ; U2 ; [|r|](cD ; cPsi) |- S <= [|r|]([s]A) : [|r|]([s']P)
 *
 *
 * Post-condition:
 *     U2 = FV(A)  where U2 is an extension of U1 s.t. [|r|]U1,U0 = U2
 *     O2 = FMV(A) where O2 |-{U2} r <= O1

 *   U2 = extension of U1 containing all free variables of S
 *   O2 = extension of O1 containing i new meta-variables
 *            for implicit arguments
 *
 *   S is in beta-eta-normalform
 *
 * Comment: elSpineI will insert new meta-variables (as references)
 *   for omitted implicit type arguments;
 *)
and elSpineI loc recT cD cPsi spine i sA =
  elSpineIW loc recT cD cPsi spine i (Whnf.whnfTyp sA)

and elSpineIW loc recT cD cPsi spine i sA  =
  if i = 0 then
    elSpine loc recT cD cPsi spine sA
  else
    match (sA, recT) with
      | ((Int.LF.PiTyp ((Int.LF.TypDecl (n, tA), _ ), tB), s), Pi) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           *
           * tN = u[s']  and u::A'[.]
           *
           * s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
           *   and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)
           *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) n Substitution.LF.id  Int.LF.Maybe in
          let (spine', sP) = elSpineI loc recT cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            (Int.LF.App (tN, spine'), sP)

      | ((Int.LF.PiTyp ((Int.LF.TypDecl (n, tA), _), tB), s), Pibox) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           *
           * tN = u[s']  and u::P[Psi, x1:A1,....xn:An]  and A = Pi x1:A1 ... Pi xn:An.P
           *
           * s.t.  cPsi |- \x1...\xn. u[id] => [id]A  where cPsi |- id : cPsi
           *)
           (* let tN     = Whnf.etaExpandMMV loc cD cPsi (tA, s) n   Substitution.LF.id in *)
           let tN     = if !strengthen
			then ConvSigma.etaExpandMMVstr loc cD cPsi (tA, s) n
                        else Whnf.etaExpandMMV loc cD cPsi (tA, s) n Substitution.LF.id Int.LF.Maybe in

          let (spine', sP) = elSpineI loc recT cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            (Int.LF.App (tN, spine'), sP)

      (* other cases impossible by (soundness?) of abstraction *)

(* elSpine loc recT cD cPsi spine sA = S
 * elSpineW cD cPsi spine sA  = S
 *   where sA = (A,s) and sA in whnf
 *
 * Pre-condition:
 *   U = free variables
 *   O = meta-variables for implicit arguments
 *
 * Invariant:
 *
 * If O ; U ; cPsi |- spine <- [s]A  (approx)
 * then
 *    O' ; U' ; cPsi |- S <- [s]A  (pre-dependent)
 *
 *
 * Post-condition:
 *   U' = extension of U containing all free variables of S
 *   O' = extension of O containing new meta-variables of S
 *)
and elSpine loc recT cD cPsi spine sA =
  let rec spineLength = function
    | Apx.LF.Nil -> 0
    | Apx.LF.App (_, tS) -> 1 + spineLength tS in

  let rec typLength = function
    | Int.LF.Atom _ -> 0
    | Int.LF.PiTyp (_, tB2) -> 1 + typLength tB2
    | Int.LF.Sigma _ -> 0 (* raise (Error (loc, SigmaTypImpos (cD, cPsi, sA))) *) in

  (* Check first that we didn't supply too many arguments. *)
  if typLength (fst (Whnf.whnfTyp sA)) < spineLength spine then
    raise (Check.LF.Error (loc, Check.LF.SpineIllTyped (typLength (fst
  (Whnf.whnfTyp sA)), spineLength spine)));

  let rec elSpine loc rectT cD cPsi spine sA = match spine, Whnf.whnfTyp sA with
    | Apx.LF.Nil, sP ->
      (Int.LF.Nil, sP) (* errors are postponed to reconstruction phase *)

    | Apx.LF.App (m, spine), (Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s) ->
      let tM = elTerm recT cD cPsi m (tA, s) in
      let (tS, sP) = elSpine loc recT cD cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) in
      (Int.LF.App (tM, tS), sP)
  in elSpine loc recT cD cPsi spine sA

(* see invariant for elSpineI *)
and elKSpineI loc recT cD cPsi spine i sK =
  if i = 0 then
    elKSpine loc recT cD cPsi spine sK
  else
    match (sK, recT) with
      | ((Int.LF.PiKind ((Int.LF.TypDecl (n, tA), _), tK), s), Pi) ->
          (* let sshift = mkShift recT cPsi in *)
          (* let tN     = Whnf.etaExpandMV Int.LF.Null (tA,s) sshift in *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) n Substitution.LF.id Int.LF.Maybe in
          let spine' = elKSpineI loc recT cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')
      | ((Int.LF.PiKind ((Int.LF.TypDecl (n, tA), _), tK), s), Pibox) ->
          (* let sshift = mkShift recT cPsi in *)
          (* let tN     = Whnf.etaExpandMMV Syntax.Loc.ghost cD cPsi (tA, s) n Substitution.LF.id in*)
          let tN = if !strengthen then ConvSigma.etaExpandMMVstr Syntax.Loc.ghost cD cPsi (tA, s) n
                   else Whnf.etaExpandMMV Syntax.Loc.ghost cD cPsi (tA, s) n Substitution.LF.id Int.LF.Maybe   in
          let spine' = elKSpineI loc recT cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')


(* see invariant for elSpine *)
and elKSpine loc recT cD cPsi spine sK =
  let rec spineLength = function
    | Apx.LF.Nil -> 0
    | Apx.LF.App (_, tS) -> 1 + spineLength tS in

  let rec kindLength = function
    | Int.LF.Typ -> 0
    | Int.LF.PiKind (_, tK) -> 1 + kindLength tK in

  (* Check first that we didn't supply too many arguments. *)
  if kindLength (fst sK) < spineLength spine then
    raise (Check.LF.Error (loc, Check.LF.SpineIllTyped (kindLength (fst sK), spineLength spine)));

  let rec elKSpine loc recT cD cPsi spine sK = match spine, sK with
    | Apx.LF.Nil, (Int.LF.Typ, _s) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

    | Apx.LF.App (m, spine), (Int.LF.PiKind ((Int.LF.TypDecl (_, tA), _), tK), s) ->
        let tM = elTerm recT cD cPsi m (tA, s) in
        let tS = elKSpine loc recT cD cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
          Int.LF.App (tM, tS)
    | _ -> raise (Error (loc, SpineLengthMisMatch))
  in elKSpine loc recT cD cPsi spine sK



(* elSpineSynth cD cPsi p_spine s' = (S, A')
 *
 * Pre-condition:
 *   U = free variables
 *   O = meta-variables for implicit arguments
 *
 * Invariant:
 *
 * If O ; U ; (cD ; cPsi) |- spine < [s]P
 *    and spine is a pattern spine
 *
 *            cD ; cPsi |- s' <= .      |cPsi| = d  and s' = ^d
 *
 *
 *            cD ; cPsi |- s   <= cPsi'
 *            Cd ;   .  |- ss' <= cPsi
 *
 * then O ; U ; (cD ; cPsi) |- S : [s']A' < [s]P
 *
 * Post-condition:
 *   U = containing all free variables of S (unchanged)
 *   O = containing new meta-variables of S (unchanged)
 *)
and elSpineSynth recT cD cPsi spine s' sP = match (spine, sP) with
  | (Apx.LF.Nil, (_tP, _s))  ->
      let ss = Substitution.LF.invert s' in
      let tQ = pruningTyp Syntax.Loc.ghost cD cPsi (Context.dctxToHat cPsi) sP (Int.LF.MShift 0, ss) in
      (* PROBLEM: [s'][ss] [s]P is not really P; in fact [ss][s]P may not exist;
       * We use pruning to ensure that [ss][s]P does exist
       *)
        (Int.LF.Nil, tQ)

  | (Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        (* cPsi |- tA : type
         * cPsi |- s' : cPsi'
         *)
      let ss = Substitution.LF.invert s' in
      (* let tA' = Whnf.normTyp (tA, ss) in *)
      (* Is [ss]A  always guaranteed to exist? - No. Use pruning to ensure it does exist. *)
      let tA' = pruningTyp loc cD cPsi (Context.dctxToHat cPsi)  (tA, Substitution.LF.id) (Int.LF.MShift 0, ss) in

      let _ = dprint (fun () -> "elSpineSynth: PruneTyp done\n") in

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth recT  cD cPsi spine (Int.LF.Dot (Int.LF.Head(Int.LF.BVar x), s')) sP in
        (*  cPsi |- tS : [s', x]tB <= sP  *)
        (*  cPsi, y:A |- tB' <= type  *)
      let _ = dprint (fun () -> "elSpineSynth done \n") in
      let tB' =  Int.LF.PiTyp ((Int.LF.TypDecl (Id.mk_name (Id.BVarName (Typ.gen_var_name tA')), tA'),
                                Int.LF.Maybe), tB) in

      let tN' = etaExpandHead loc (Int.LF.BVar x) tA' in
        (Int.LF.App (tN', tS), tB')

   (* other cases impossible *)


let elCtxVar c_var = match c_var with
  | Apx.LF.CtxOffset offset  -> Int.LF.CtxOffset offset
  | Apx.LF.CtxName psi       -> Int.LF.CtxName psi

let rec elDCtx recT cD psi = match psi with
  | Apx.LF.CtxHole ->
    dprint (fun () -> "Encountered _ (underscore) for context...");
    Int.LF.CtxVar (Whnf.newCVar (Some (Id.mk_name (Id.SomeString "j"))) cD None Int.LF.Maybe)
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar (c_var) ->
      let cPsi = Int.LF.CtxVar(elCtxVar c_var) in
	(dprint (fun () -> "[elDCtx] " ^ P.dctxToString cD cPsi );
	cPsi)

  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtx recT cD psi' in
      let _ = dprint (fun () -> "[elDCtx] cPsi = " ^ P.dctxToString cD cPsi) in
      let tA   = elTyp  recT cD cPsi a in
      let _ = dprint (fun () -> "[elDCtx] " ^ Id.render_name x ^ ":" ^
                        P.typToString cD cPsi (tA, Substitution.LF.id)) in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))
  | Apx.LF.DDec (psi', Apx.LF.TypDeclOpt x) ->
      let cPsi = elDCtx recT cD psi' in
      Int.LF.DDec (cPsi, Int.LF.TypDeclOpt x)


let checkCtxVar loc cD c_var w = match c_var with
  | Apx.LF.CtxOffset offset  ->
      if Context.lookupSchema cD offset = w then Int.LF.CtxOffset offset
      else
	raise (Error (loc, IncompatibleSchemaForCtxVar (cD, Int.LF.CtxOffset offset, w,
							Context.lookupSchema cD offset)))
  | Apx.LF.CtxName psi       ->
      (FCVar.add psi (cD, Int.LF.Decl (psi, Int.LF.CTyp (Some w), Int.LF.Maybe));
       Int.LF.CtxName psi)

let rec checkDCtx loc recT cD psi w = match psi with
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar (c_var) ->  Int.LF.CtxVar(checkCtxVar loc cD c_var w)

  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = checkDCtx loc recT cD psi' w in
      let tA   = elTyp  recT cD cPsi a in
      let _ = dprint (fun () -> "[elDCtx] " ^ Id.render_name x ^ ":" ^
                        P.typToString cD cPsi (tA, Substitution.LF.id)) in
      let Syntax.Int.LF.Schema s_elems = Schema.get_schema w in
      let _ = begin try
                Check.LF.checkTypeAgainstSchema (Syntax.Loc.ghost) cD cPsi tA s_elems
             with _ -> raise (Check.Comp.Error (Syntax.Loc.ghost, Check.Comp.IllegalParamTyp  (cD, cPsi, tA)))
             end
      in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))


(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr recT cD cnstr = match cnstr with
  | [] -> ()
  | ((_ , Apx.LF.Root (loc, Apx.LF.FVar x, spine),
      Int.LF.Inst (_, ({contents = None} as r), _, Int.LF.ClTyp (Int.LF.MTyp tP,cPsi), _, _)) :: cnstrs) ->
      begin try
	begin match FVar.get x with
          | Int.LF.Type tA ->
              (* For type reconstruction to succeed, we must have
               *  . |- tA <= type
               *  This will be enforced during abstraction.
               *)
              let sshift = mkShift recT cPsi in

              (* let tS = elSpine cPsi spine (tA, Substitution.LF.id) (tP,s) in *)
              let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, sshift) in
	      begin
		try
                  Unify.unifyTyp cD cPsi sQ (tP, Substitution.LF.id);
                  r := Some (Int.LF.INorm (Int.LF.Root (loc, Int.LF.FVar x, tS)));
                  solve_fvarCnstr recT cD cnstrs
		with
		  | Unify.Failure msg ->
		    raise (Error (loc, TypMismatchElab (cD, cPsi, (tP, Substitution.LF.id), sQ)))
	      end
          | Int.LF.TypVar _ ->
              raise (Error (loc, LeftoverConstraints x))
	end
      with _ -> raise (Index.Error (loc, Index.UnboundName x))
      end


  | ((_ , Apx.LF.Root (loc, Apx.LF.FVar x, spine),
      Int.LF.Inst (_, {contents = Some (Int.LF.INorm tR)}, _, Int.LF.ClTyp (Int.LF.MTyp tP,cPsi), _ , _)) :: cnstrs) ->
      begin try
        begin match FVar.get x with
        | Int.LF.Type tA ->
          (* For type reconstruction to succeed, we must have
           *  . |- tA <= type
           *  This will be enforced during abstraction.
           *)
            let sshift = mkShift recT cPsi in

            (* let tS = elSpine cPsi spine (tA, Substitution.LF.id) (tP,s) in *)
            let (tS, sQ ) = elSpine loc recT cD cPsi spine (tA, sshift) in
            (* let psihat = Context.dctxToHat cPsi in *)
            begin
	      try
                Unify.unifyTyp cD cPsi sQ (tP, Substitution.LF.id) ;
                Unify.unify cD cPsi
		  (Int.LF.Root (loc, Int.LF.FVar x, tS), Substitution.LF.id)
		  (tR, Substitution.LF.id);
		(* r := Some (Int.LF.Root (loc, Int.LF.FVar x, tS)); *)
		solve_fvarCnstr recT cD cnstrs
	      with
		| Unify.Failure msg ->
		  raise (Error (loc, TypMismatchElab (cD, cPsi, (tP, Substitution.LF.id), sQ)))
            end
        | Int.LF.TypVar _ ->
          raise (Error (loc, LeftoverConstraints x))
      end

    with _ -> raise (Index.Error (loc, Index.UnboundName x))
    end

let rec solve_fcvarCnstr cnstr = match cnstr with
  | [] -> ()
  | ((Apx.LF.Root (loc, Apx.LF.FMVar (u,s), _nil_spine), (_, r, cD, Int.LF.ClTyp (Int.LF.MTyp _,cPsi), _, _)) :: cnstrs) ->
      begin try
        let (cD_d, Int.LF.Decl (_, Int.LF.ClTyp (Int.LF.MTyp _tP, cPhi), _)) = FCVar.get u in
	let d = Context.length cD - Context.length cD_d in
	let cPhi = (if d = 0 then cPhi else
                      Whnf.cnormDCtx (cPhi, Int.LF.MShift d)) in
        let s'' = elSub loc Pibox cD cPsi s Int.LF.Subst cPhi in
          r := Some (Int.LF.INorm (Int.LF.Root (loc, Int.LF.FMVar (u, s''), Int.LF.Nil)));
          solve_fcvarCnstr cnstrs
      with Not_found ->
        raise (Error (loc, LeftoverConstraints u))
      end

  | ((Apx.LF.Root (loc, Apx.LF.FPVar (x,s), spine), (_, r, cD, Int.LF.ClTyp (Int.LF.MTyp _,cPsi), _, _)) :: cnstrs) ->
      begin try
        let (cD_d, Int.LF.Decl (_, Int.LF.ClTyp (Int.LF.PTyp tA, cPhi), _)) = FCVar.get x in
	let d = Context.length cD - Context.length cD_d in
	let (tA, cPhi) = if d = 0 then (tA, cPhi) else
	  (Whnf.cnormTyp (tA, Int.LF.MShift d), Whnf.cnormDCtx (cPhi, Int.LF.MShift d)) in

        let s'' = elSub loc Pibox cD cPsi s Int.LF.Subst cPhi in

        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let (tS, _ ) = elSpine loc Pibox cD cPsi spine (tA, s'') in
          r := Some (Int.LF.INorm (Int.LF.Root (loc, Int.LF.FPVar (x,s''), tS)));
          solve_fcvarCnstr cnstrs
      with Not_found ->
        raise (Error (loc, LeftoverConstraints x))
      end

let solve_constraints cD' =
  (solve_fcvarCnstr !fcvar_cnstr ;
  reset_fcvarCnstr ();
  Unify.forceGlobalCnstr (!Unify.globalCnstrs);
  Unify.resetGlobalCnstrs () )

let solve_fvarCnstr rectyp =
  solve_fvarCnstr rectyp Int.LF.Empty !fvar_cnstr
