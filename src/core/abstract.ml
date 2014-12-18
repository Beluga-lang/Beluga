(**
   @author Renaud Germain
   @author Brigitte Pientka
*)
open Store
open Store.Cid
open Substitution
open Syntax
open Id

module S    = Substitution.LF
module I    = Int.LF
module Comp = Int.Comp

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [3])

type varvariant =
    VariantFV | VariantFCV | VariantMMV
  | VariantMV | VariantFMV | VariantFPV 
  | VariantFSV

type error =
  | LeftoverVars of varvariant
  | LeftoverConstraints
  | CyclicDependency of varvariant
  | UnknownIdentifier
  | UnknownSchemaCtx of name


exception Error of Syntax.Loc.t * error

let getLocation' (loc, i) = match i with
  | Comp.MApp (loc, _, _ ) -> loc
  | Comp.Apply (loc, _, _ ) -> loc
  | Comp.Equal (loc, _, _ ) -> loc
  | Comp.PairVal (loc, _ , _) -> loc
  | _ -> loc

let getLocation e = match e with
  | Comp.Syn (loc , i ) ->
    getLocation' (loc, i)
  | Comp.Rec (loc, _ , _ ) -> loc
  | Comp.Fun (loc, _, _ ) -> loc
  | Comp.Cofun (loc, _ ) -> loc
  | Comp.MLam (loc, _, _) -> loc
  | Comp.Pair (loc, _, _ ) -> loc
  | Comp.LetPair (loc, _, _ ) -> loc
  | Comp.Box (loc, _)    -> loc
  | Comp.Case (loc, _, _, _ ) -> loc
  | Comp.If (loc, _, _, _ ) -> loc
  | Comp.Hole (loc, _) -> loc




let string_of_varvariant = function
  | VariantFV  -> "free variables"
  | VariantFCV -> "free context variables"
  | VariantMMV -> "meta^2-variables and free variables"
  | VariantMV  -> "meta-variables and free variables"
  | VariantFMV -> "free meta-variables"
  | VariantFPV -> "free parameter-variables"
  | VariantFSV -> "free substitution-variables"

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | UnknownSchemaCtx psi ->
            Format.fprintf ppf "Unable to infer schema for context variable %s"
              (R.render_name psi)
        | LeftoverVars VariantFCV ->
          Format.fprintf ppf "Abstraction not valid LF-type because of leftover context variable"
        | LeftoverVars VariantMV ->
          Format.fprintf ppf "Leftover meta-variables in computation-level expression; provide a type annotation"
        | LeftoverVars (VariantMMV as varvariant) ->
          Format.fprintf ppf
            ("Encountered %s,@ which we cannot abstract over@ \
            because they depend on meta-variables;@ \
            the user needs to supply more information,@ \
            since the type of a given expression@ \
            is not uniquely determined.@ \
            Meta^2-variables are introduced during type reconstruction;@ \
            if you explicitely quantify over some meta-variables,@ \
            these meta-variables will impose constraints on meta^2-variables@ \
            and we may not be able to abstract over the meta^2-variables.@ \
            The solution is either to not specify any meta-variables explicitly,@ \
            or specify all of them.")
            (string_of_varvariant varvariant)
        | LeftoverConstraints ->
          Format.fprintf ppf "Leftover constraints during abstraction."
        | CyclicDependency variant ->
          Format.fprintf ppf "Cyclic dependencies among %s" (string_of_varvariant variant)
        | UnknownIdentifier ->
          Format.fprintf ppf "Unknown identifier in program."))

(* ******************************************************************* *)
(* Abstraction:

   - Abstract over the meta-variables in O
   - Abstract over the free variables in F

   Abstraction only succeeds, if O and F are not cyclic.

  We write {{Q}} for the context of Q, where MVars and FVars have
  been translated to declarations and their occurrences to BVars.
  We write {{A}}_Q, {{M}}_Q, {{S}}_Q for the corresponding translation
  of a type, an expression or spine.

  Just like contexts Psi, any Q is implicitly assumed to be
  well-formed and in dependency order. ** note that Q may contain
  cyclic dependencies, which need to be detected **

  We write  Q ; Psi ||- M  if all MVars and FVars in M and Psi are
  collected in Q. In particular, . ; Psi ||- M means M and Psi contain
  no MVars or FVars.  Similarly, for spines . ; Psi ||- S and other
  syntactic categories.

  Abstraction proceeds in three phases:

   - Collection of all MVars and FVars in M into Q;

   - Abstraction over all MVars and FVars (which are listed in Q)
     and occur in M, will yield a new term M'

   -

 Collection and abstraction raise Error if there are unresolved
  constraints after simplification.



   Collection will work in a generic way so we can collect
   - FVar  (named free LF-bound variables),
   - FMVar (named free meta-variables),
   - FPVar (named free parameter variables),

   - MVars (references to meta-variables representing unknowns)

   Abstraction over LF-bound variables and abstraction of named
   meta-variables and parameter variables are however kept separate.

   Abstraction over LF-bound variables is performed by the functions
   abstractTerm, abstractType, etc.

   Abstraction over meta-variables and parameter variables is
   performed by the functions abstractMVarTerm, abstractMVarType, etc.





*)

(* marker will indicate whether the type of the variable is already clean,
   i.e. the meta-variables and free variables occurring the type had been
   collected *)
type marker = Pure | Impure

type free_var =
  (* Free variables (references): unnamed *)

  (* For MMV, MV and PV it suffices to store the reference for the
     respective MMVar, MVar and PVar; the substitution associated with an
     MMVar, MVar and PVar is irrelevant here *)

  | MMV of marker * I.mm_var       (* Y ::= u[ms,s]   where h = MMVar(u, cD, Psi, P, _)
                                      and    cD' ; Psi' |- u[ms, s] <= [ms ; s]P      *)
  | CV of I.dctx

  (* Free named variables *)
  | FV of marker * Id.name * I.typ option
                                (*     | (F, A)                  . |- F <= A *)

  | FMV of marker * Id.name * I.ctyp option
  | FCV of Id.name * Id.cid_schema option (* TODO: Can this be merged with FMV? *)

  | CtxV of (Id.name * cid_schema * I.depend)


let rec prefixCompTyp tau = match tau with
  | Comp.TypPiBox (_, tau) -> 1 + prefixCompTyp tau
  | _ -> 0

let rec prefixCompKind cK = match cK with
  | Comp.PiKind (_, _, cK) -> 1 + prefixCompKind cK
  | _ -> 0


let rec raiseType cPsi tA = match cPsi with
  | I.Null -> (None, tA)
  | I.CtxVar psi -> (Some psi, tA)
  | I.DDec (cPsi', decl) ->
      raiseType cPsi' (I.PiTyp ((decl, I.Maybe), tA))

let rec raiseKind cPsi tK = match cPsi with
  | I.Null -> tK
  | I.DDec (cPsi', decl) ->
      raiseKind cPsi' (I.PiKind ((decl, I.Maybe), tK))

let rec collectionToString cQ = match cQ with
  | I.Empty -> ""
  | I.Dec(cQ, CV(I.CtxVar(I.CInst(_n, _r, s_cid, _, _theta)) as cPsi)) ->
      collectionToString cQ ^ " " ^ P.dctxToString I.Empty cPsi ^ " : " ^ R.render_cid_schema s_cid ^ "\n"

  | I.Dec(cQ, FCV(psi, Some s_cid)) ->
      collectionToString cQ ^ " " ^
        R.render_name psi ^ ":" ^
        R.render_cid_schema s_cid ^ "\n"

  | I.Dec(cQ, MMV (_ , ((_n, _r, cD, ityp, _c, _) as mm))) ->
       collectionToString cQ ^ " "
     ^ P.mmvarToString mm
     ^ " : "
     ^ P.mtypToString cD ityp
     ^ "\n"

  | I.Dec (cQ, FMV (Pure, u, Some mtyp)) ->
      let cD = I.Empty in
       collectionToString cQ
     ^ " " ^ R.render_name u ^ " : "
     ^ P.mtypToString cD mtyp ^"\n"

  | I.Dec(cQ, FV (_marker, _n, None)) ->  collectionToString cQ ^ ",  FV _ .\n"

  | I.Dec(cQ, FV (_marker, n, Some tA)) ->
      let cD = I.Empty in
        collectionToString cQ ^ ",  FV " ^ n.string_of_name ^ " : "
      ^ "(" ^ P.typToString cD I.Null (tA, LF.id) ^ ")"
      ^ "\n"
  | I.Dec(cQ, FMV (Impure , u, None)) -> "FMV "  ^ R.render_name u ^ " (impure) "
  | I.Dec(_cQ, _ ) -> " ?? "

let printCollection s =
  (print_string "Print Collection of contextual variables:\n";
   print_string (collectionToString s) )

(* checkOccurrence p cQ = result

   If the first occurrence of Y in cQ s.t. p(Y) = Some Pure, then Yes
   If the first occurrence of Y:Impure in cQ s.t. p(Y) = Some Impure then Cycle
   otherwise No

*)
type occurrs = Yes | No | Cycle

let rec checkOccurrence p = function
  | I.Empty        -> No
  | I.Dec(cQ', y)  ->
    match p y with
      | No -> checkOccurrence p cQ'
      | result -> result

(* length cPsi = |cPsi| *)
let length cPsi =
  let (_, n) = Context.dctxToHat cPsi in
    n

let rec lengthCollection cQ = match cQ with
  | I.Empty        -> 0
  | I.Dec (cQ', MMV(Impure, _ )) -> lengthCollection cQ'
  | I.Dec (cQ', FV(Impure, _ , _ )) -> lengthCollection cQ'
  | I.Dec (cQ', FMV(Impure, _ , _ )) -> lengthCollection cQ'
  | I.Dec (cQ', _ )  -> lengthCollection cQ' + 1



(* Eta-expansion of bound variables which have function type *)
let etaExpandHead loc h tA =
  let rec etaExpSpine k tS tA = begin match  tA with
    | I.Atom _  -> (k, tS)

    | I.PiTyp (_ , tA') ->
        let tN = I.Root(loc, I.BVar k, I.Nil) in
          etaExpSpine (k+1)  (I.App(tN, tS)) tA'
  end in

  let rec etaExpPrefix loc (tM, tA) = begin match tA with
    | I.Atom _ -> tM
    | I.PiTyp ((I.TypDecl (x, _ ), _ ) , tA') ->
        I.Lam (loc, x, etaExpPrefix loc (tM, tA'))
  end in

  let (k, tS') = etaExpSpine 1 (I.Nil) tA in
  let h'       =  begin match h with
                    | I.BVar x -> I.BVar (x+k-1)
                    | I.FVar _ -> h
                  end  in
    etaExpPrefix loc (I.Root(loc, h' , tS'), tA)




(* eqMMVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let eqMMVar mmV1 mmV2 = match (mmV1, mmV2) with
  | (_, r1, _, _, _, _) , MMV (marker , (_, r2, _, _, _, _)) ->
      if r1 == r2 then
        match marker with Pure -> Yes  | Impure -> Cycle
      else
        No
  | _ -> No

(* eqFVar n fV' = B
   where B iff n and fV' represent same variable
*)
let eqFVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FV (marker, n2, _)) ->
      if n1 = n2 then
        match marker with Pure -> Yes | Impure -> Cycle
      else No
  | _ -> No


(* eqFMVar n fV' = B
   where B iff n and fV' represent same variable
*)
let eqFMVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FMV (marker, n2, _)) ->
      if n1 = n2 then
        match marker with Pure -> Yes | Impure -> Cycle
      else
        No
  | _ -> No


(* eqFSVar n fV' = B
   where B iff n and fV' represent same variable
*)
let eqFSVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FMV (marker, n2, _)) ->
      if n1 = n2 then
        match marker with Pure -> Yes | Impure -> Cycle
      else
        No
  | _ -> No

(* eqFCVar n fV' = B
   where B iff n and fV' represent same variable
*)
let eqFCVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FCV (n2, _)) ->
      if n1 = n2 then
         Yes
      else
        No
  | _ -> No


(* eqCVar n fV' = B
   where B iff n and fV' represent same variable
*)
let eqCVar n1 fV2 = match (n1, fV2) with
  | (I.CInst (_, r, _, _, _theta ) ,  CV (I.CtxVar (I.CInst (_, r_psi, _, _, _theta' )))) ->
      if r == r_psi then
         Yes
      else
        No
  | _ -> No

(* eqFPVar n fV' = B
   where B iff n and fV' represent same variable
*)
let eqFPVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FMV (marker, n2, _ )) ->
      if n1 = n2 then
        match marker with Pure -> Yes | Impure -> Cycle
      else
        No
  | _ -> No


let rec constraints_solved cnstr = match cnstr with
  | [] -> true
  | ({contents = I.Queued} :: cnstrs) ->
      constraints_solved cnstrs
  | ({contents = I.Eqn (_cD, cPsi, tM, tN)} :: cnstrs) ->
      if Whnf.conv (tM, LF.id) (tN, LF.id) then
        constraints_solved cnstrs
      else
        (dprint (fun () -> "Encountered unsolved constraint:\n" ^
           P.normalToString I.Empty cPsi (tM, LF.id) ^ " == " ^
           P.normalToString I.Empty cPsi (tN, LF.id) ^ "\n\n") ;
         false )
  | ({contents = I.Eqs (_cD, cPsi, s, s')} :: cnstrs) ->
      if Whnf.convSub s s' then
        constraints_solved cnstrs
      else
        (dprint (fun () -> "Encountered unsolved constraint:\n" ^
           P.subToString I.Empty cPsi s ^ " == " ^
           P.subToString I.Empty cPsi s' ^ "\n\n") ;
         false )
 | ({contents = I.Eqh (_cD, _cPsi, h1, h2)} :: cnstrs) ->
      if Whnf.convHead (h1, LF.id) (h2, LF.id) then
        constraints_solved cnstrs
      else false



(* Check that a synthesized computation-level type is free of constraints *)
let rec cnstr_ctyp tau =  match tau  with
  | Comp.TypBox (_, I.MTyp (tA, cPsi)) -> cnstr_typ (tA, LF.id) && cnstr_dctx cPsi
  | Comp.TypSub (_, cPhi, cPsi) -> cnstr_dctx cPhi && cnstr_dctx cPsi

and cnstr_typ sA = match sA with
  | (I.Atom  (_, _a, spine),  s)  -> cnstr_spine (spine , s)

  | (I.PiTyp ((t_decl, _ ), tB),  s) ->
      cnstr_typ_decl (t_decl, s) && cnstr_typ (tB, LF.dot1 s)

  | (I.Sigma t_rec,  s) -> cnstr_typ_rec (t_rec, s)

and cnstr_term sM = match sM with
  | (I.Lam(_ , _x , tM), s) -> cnstr_term (tM, LF.dot1 s)
  | (I.Root (_, h, spine), s) ->
      cnstr_head h && cnstr_spine (spine, s)

and cnstr_spine sS = match sS with
  | (I.Nil, _s) -> false
  | (I.App(tM, tS), s) ->
      cnstr_term (tM, s) && cnstr_spine (tS, s)
  | (I.SClo (tS, s'), s) -> cnstr_spine (tS, LF.comp s' s)


and cnstr_head h = match h with
  | I.MMVar((_, _r, _, _ , cnstr, _), (_ms, s)) ->
       (if constraints_solved (!cnstr) then
          cnstr_sub s
        else false)

  | I.MVar(I.Inst (_, _r, _ , _ , cnstr, _), s) ->
       (if constraints_solved (!cnstr) then
          cnstr_sub s
        else false)
 |  _  -> false


and cnstr_sub s = match s with
  | I.Shift _   -> false
  | I.Dot (I.Head h , s) -> cnstr_head h && cnstr_sub s
  | I.Dot (I.Obj tM , s) -> cnstr_term (tM, LF.id) && cnstr_sub s
  | I.Dot (I.Undef, s')  -> cnstr_sub s'


and cnstr_dctx cPsi = match cPsi with
  | I.Null -> false
  | I.CtxVar _ -> false
  | I.DDec (cPsi, t_decl) -> cnstr_dctx cPsi && cnstr_typ_decl (t_decl, LF.id)


and cnstr_typ_decl st_decl = match st_decl with
  | (I.TypDecl (_ , tA), s) -> cnstr_typ (tA, s)
  | _ -> false


and cnstr_typ_rec (t_rec, s) = match t_rec with
  | I.SigmaLast (_, tA) -> cnstr_typ (tA, s)
  | I.SigmaElem (_, tA, t_rec) -> cnstr_typ (tA, s) && cnstr_typ_rec (t_rec, s)

(* index_of cQ n = i
   where cQ = cQ1, Y, cQ2 s.t. n = Y and length cQ2 = i
*)
let rec index_of cQ n =
  match (cQ, n) with
  | (I.Empty, _) ->
      raise (Error.Violation "index_of for a free variable (FV, FMV, FPV, MV) does not exist.")

  | (I.Dec (cQ', MMV(Impure, _ )), _ ) ->
      index_of cQ' n

  | (I.Dec (cQ', FMV(Impure, _ , _ )), _ ) ->
      index_of cQ' n

  | (I.Dec (cQ', FV(Impure, _ , _ )), _ ) ->
      index_of cQ' n

  | (I.Dec (cQ', MMV (Pure, u1)), MMV (Pure, u2)) ->
      begin match eqMMVar u1 (MMV (Pure, u2)) with
        | Yes -> 1
        | No  -> (index_of cQ' n) + 1
        | Cycle -> raise (Error (Syntax.Loc.ghost, CyclicDependency VariantMMV))
      end

  | (I.Dec (cQ', FV (Pure, f1, _)), FV (Pure, f2, tA)) ->
      begin match eqFVar f1 (FV (Pure, f2, tA)) with
        | Yes -> 1
        | No  -> (index_of cQ' n) + 1
        | Cycle -> raise (Error (Syntax.Loc.ghost, CyclicDependency VariantFV))
      end

  | (I.Dec (cQ', CV(I.CtxVar psi1)), CV (psi2)) ->
      begin match eqCVar psi1 (CV (psi2)) with
        | Yes ->  1
        | No ->
            (index_of cQ' n) + 1
        | Cycle -> raise (Error (Syntax.Loc.ghost, CyclicDependency VariantFCV))
      end

  | (I.Dec (cQ', FCV(psi1 , _ )), FCV (psi2, s_cid)) ->
      begin match eqFCVar psi1 (FCV (psi2, s_cid)) with
        | Yes -> 1
        | No -> (index_of cQ' n) + 1
        | Cycle -> raise (Error (Syntax.Loc.ghost, CyclicDependency VariantFCV))
      end

  | (I.Dec (cQ', FMV (Pure, u1, _)), FMV (Pure, u2, mtyp)) ->
      begin match eqFMVar u1 (FMV (Pure, u2, mtyp)) with
        | Yes -> 1
        | No -> (index_of cQ' n) + 1
        | Cycle -> raise (Error (Syntax.Loc.ghost, CyclicDependency VariantFMV))
      end

  | (I.Dec (cQ', _), _) ->
      (index_of cQ' n) + 1

(* If   cQ = cQ1 (MV u) cQ2
   and  u :: A[Psi]
   then (ctxToDctx cQ) = (ctxToDctx cQ1) Pi Psi . A (ctxToDctx cQ2)

   If   cQ = cQ1 (FV (F, A)) cQ2
   then (ctxToDctx cQ) = (ctxToDctx cQ1) A (ctxToDctx cQ2)
*)
let rec ctxToDctx cQ = match cQ with
  | I.Empty ->
      I.Null

  | I.Dec (cQ', MMV (Impure, _ )) ->
      ctxToDctx cQ'

  | I.Dec (cQ', FV (Impure, _ , _ )) ->
      ctxToDctx cQ'

  | I.Dec (cQ', MMV (Pure, (_, _, _, I.MTyp(tA,cPsi), _, _))) ->
      begin match raiseType cPsi tA with
        | (None, tA') ->
            let x = Id.mk_name (Id.MVarName (Typ.gen_var_name tA')) in
            I.DDec (ctxToDctx cQ', I.TypDecl (x, tA'))
        | (Some _, _ ) -> raise (Error.Violation "ctxToDctx generates LF-dctx with context variable.")
      end
  | I.Dec (cQ', FV (Pure, x, Some tA)) ->
      (* let x = Id.mk_name (Id.BVarName (Typ.gen_var_name tA)) in  *)
      I.DDec (ctxToDctx cQ', I.TypDecl (x, tA))


let rec ctxToCtx cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', MMV (Pure, (_, _, _, I.MTyp(tA,cPsi), _, _))) ->
      begin match raiseType cPsi tA with
        | (None, tA') ->
            let x = Id.mk_name (Id.MVarName (Typ.gen_var_name tA')) in
            I.Dec (ctxToCtx cQ', I.TypDecl (x, tA'))
        | (Some _, _ ) -> raise (Error.Violation "ctxToDctx generates LF-dctx with context variable.")
      end
  | I.Dec (cQ', FV (Pure, x, Some tA)) ->
      (* let x = Id.mk_name (Id.BVarName (Typ.gen_var_name tA)) in  *)
      I.Dec (ctxToCtx cQ', I.TypDecl (x, tA))

  | I.Dec (cQ', FV (Impure, _x, _ )) ->
    ctxToCtx cQ'

  | I.Dec (cQ', MMV (Impure, _u )) ->
    ctxToCtx cQ'

let rec ctxToMCtx ?(dep'=I.Maybe) cQ = match cQ with
  | I.Empty ->
      I.Empty

  (* The case where cD is not empty and a meta^2-variable is uninstantiated
     should never happen. -bp *)
  | I.Dec (cQ', MMV (Pure, (n, _, I.Empty, ityp, _, dep))) ->
      I.Dec (ctxToMCtx cQ', I.Decl (n, ityp, dep))

  | I.Dec (_cQ', MMV (Pure, (_, _, _cD, _, _, _))) ->
      raise (Error (Syntax.Loc.ghost, LeftoverVars VariantMMV))

  | I.Dec (cQ', CV (I.CtxVar (I.CInst (n, {contents = None}, s_cid, _, _theta)))) ->
      (* let psi = Id.mk_name (NoName) in *)
      (* this case should not happen? -bp *)
      I.Dec (ctxToMCtx cQ', I.Decl (n, I.CTyp s_cid, I.No))

  | I.Dec (cQ', FCV (psi, Some (s_cid))) ->
      I.Dec (ctxToMCtx cQ', I.Decl (psi, I.CTyp s_cid, I.Maybe))

  | I.Dec (cQ', FMV (Pure, u, Some mtyp)) ->
(*       let mtyp' = begin match mtyp with
        | I.MTyp(tA, cPsi, d) -> I.MTyp(tA, cPsi, d)
        | I.PTyp(tA, cPsi, d) -> I.PTyp(tA, cPsi, d)
        | I.STyp(cPhi, cPsi, d) -> I.STyp(cPhi, cPsi, d)
      end in *)
      I.Dec (ctxToMCtx cQ', I.Decl (u, mtyp, I.Maybe))

  | I.Dec (cQ', CtxV (x,w, dep)) ->
      I.Dec (ctxToMCtx cQ', I.Decl (x, I.CTyp w, dep))

  (* this case should not happen -bp *)
   | I.Dec (cQ', FV (_, _, Some tA)) ->
      raise (Error.Violation "Free variables in computation-level reconstruction.")

   | I.Dec (cQ', FMV(Impure, _, _ )) ->
       ctxToMCtx cQ'


(* collectTerm p cQ phat (tM,s) = cQ'

   Invariant:

   If  cPsi' |- tM <= tA'   and
       cPsi  |- s  <= cPsi' and  (tM, s) is ins whnf
                            and   phat = |cPsi|
       No circularities in [s]tM
       (enforced by extended occurs-check for FVars
        in Unify (to be done -bp))

   then cQ' = cQ, cQ''
        where cQ'' contains all MVars and FVars in tM
            all MVars and FVars in s are already in cQ.


   Improvement: if tM is in normal form, we don't
                need to call whnf.
*)
let rec collectTerm p cQ phat sM = collectTermW p cQ phat (Whnf.whnf sM)

and collectTermW p cQ ((cvar, offset) as phat) sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      let (cQ', tM') =  collectTerm p cQ (cvar, offset + 1) (tM, LF.dot1 s) in
        (cQ', I.Lam (loc, x, tM'))

  | (I.Tuple (loc, tuple), s) ->
      let (cQ', tuple') = collectTuple p cQ phat (tuple, s) in
        (cQ', I.Tuple (loc, tuple'))

  | (I.Root (loc, h, tS), s) ->
      let (cQ', h') = collectHead p cQ phat loc (h, s) in
      let (cQ'', tS') =  collectSpine p cQ' phat (tS, s) in
        (cQ'', I.Root(loc, h', tS'))
  | (I.LFHole _loc, s) ->
      (cQ, I.LFHole _loc)


and collectTuple p cQ phat = function
  | (I.Last tM, s) ->
      let (cQ', tM') = collectTerm p cQ phat (tM, s) in
        (cQ', I.Last tM')
  | (I.Cons (tM, tuple), s) ->
      let (cQ', tM') = collectTerm p cQ phat (tM, s) in
      let (cQ2, tuple') = collectTuple p cQ' phat (tuple, s) in
        (cQ2, I.Cons(tM', tuple'))


(* collectSpine p cQ phat (S, s) = cQ'

   Invariant:
   If    cPsi |- s : cPsi1     cPsi1 |- S : A > P
   then  cQ' = cQ, cQ''
       where cQ'' contains all MVars and FVars in (S, s)

*)
and collectSpine (p:int) cQ phat sS = match sS with
  | (I.Nil, _) -> (cQ, I.Nil)

  | (I.SClo (tS, s'), s) ->
      collectSpine p cQ phat (tS, LF.comp s' s)

  | (I.App (tM, tS), s) ->
    let (cQ', tM') = collectTerm p cQ phat (tM, s)  in
    let (cQ'', tS') = collectSpine p cQ' phat (tS, s) in
      (cQ'', I.App (tM', tS'))


(* collectSub p cQ phat s = cQ'

   Invariant:
   If    cPsi |- s : cPsi1    and phat = |cPsi|
   then  cQ' = cQ, cQ''
   where cQ'' contains all MVars and FVars in s

*)
and collectSub (p:int) cQ phat s = match s with
  | I.EmptySub -> (cQ, s)
  | I.Undefs -> (cQ, s)
  | I.Shift _ -> (cQ, s) (* we do not collect the context variable in the
                            argument to shift; if the substitution is
                            well-typed, then it has been already collected *)
  | I.Dot (I.Head h, s) ->
      let (cQ1, h') = collectHead p cQ phat (Syntax.Loc.ghost) (h, LF.id) in
      let (cQ2, s') =  collectSub p cQ1 phat s in
        (cQ2, I.Dot(I.Head h', s'))

  | I.Dot (I.Obj tM, s) ->
      let (cQ1, tM') = collectTerm p cQ phat (tM, LF.id) in
      let (cQ2,s') =  collectSub p cQ1 phat s in
        (cQ2, I.Dot (I.Obj tM', s'))

  | I.Dot (I.Undef, s') ->
    (let _ = Printf.printf "Collect Sub encountered undef\n" in
       (* -bp Aug 24, 2009 BUG: If the substitution includes an undef
          one would need to prune the type of the MVAR with which this
          substitution is associated. *)
     let (cQ1, s) = collectSub p cQ phat  s' in
       (cQ1, I.Dot (I.Undef, s)))

  | I.FSVar (s_name, n, s') ->
        begin match checkOccurrence (eqFSVar s_name) cQ with
          | Yes ->
              let (cQ', sigma) = collectSub p cQ phat s' in
                (cQ', I.FSVar (s_name, n, sigma))
          | No ->
              let (cQ0, sigma) = collectSub p cQ phat s' in
              let (cD_d, I.Decl (_, mtyp,_))  = FCVar.get s_name in
	      let d = p - Context.length cD_d in
	      let mtyp' = Whnf.cnormMTyp (mtyp, Int.LF.MShift d) in
              let cQ' = I.Dec(cQ0, FMV(Impure, s_name, None)) in
              let (cQ1, mtyp'')  = collectMTyp p cQ' mtyp' in
                (* tA must be closed with respect to cPhi *)
                (* Since we only use abstraction on pure LF objects,
                   there are no context variables; different abstraction
                   is necessary for handling computation-level expressions,
                   and LF objects which occur in comp utations. *)
                (I.Dec (cQ1, FMV (Pure, s_name, Some mtyp'')),
                 I.FSVar (s_name, n, sigma))

          | Cycle -> raise (Error ((Syntax.Loc.ghost), CyclicDependency VariantFSV))
        end

  | I.SVar (offset, n, s) ->
    let (cQ1,s') = collectSub p cQ phat s in
       (cQ1, I.SVar(offset, n, s'))

  | I.MSVar ((n, s, cD, I.STyp(cPhi, cPsi), ({contents = cnstr} as c), dep) as sv, k, (ms',s')) ->
    if constraints_solved cnstr then
      begin match checkOccurrence (eqMMVar sv) cQ with
        | Yes ->
            let (cQ0, ms') = collectMSub k cQ ms' in
            let (cQ', s') = collectSub p cQ0 phat s' in
              (cQ', I.MSVar(sv, k, (ms',s')))
        | No  ->
            let (cQ, ms') = collectMSub k cQ ms' in
            let (cQ0, s') = collectSub p cQ phat s' in
            let cQ' = I.Dec(cQ0, MMV(Impure, sv)) in
            let psihat = Context.dctxToHat cPsi in
            let (cQ1, cPsi')  = collectDctx (Syntax.Loc.ghost) k cQ' psihat cPsi in
            let phihat = Context.dctxToHat cPhi in
            let (cQ2, cPhi')  = collectDctx  (Syntax.Loc.ghost) k cQ1 phihat cPhi in
	    let sv' = (n,s, cD, I.STyp(cPhi', cPsi'), c, dep) in
            let sigma' = I.MSVar (sv', k , (ms',s')) in
              (I.Dec (cQ2, MMV (Pure, sv')), sigma')

        | Cycle -> raise (Error (Syntax.Loc.ghost, CyclicDependency VariantMMV))
      end
    else
        raise (Error (Syntax.Loc.ghost, LeftoverConstraints))

and collectMObj p cQ1 = function 
  | I.MObj(phat, tM) ->
      let (cQ1, phat') = collectHat p cQ1 phat in
      let (cQ2, tM') = collectTerm p cQ1 phat' (tM, LF.id) in
        (cQ2 , I.MObj (phat', tM'))
  | I.PObj(phat, h) ->
      let (cQ1, phat') = collectHat p cQ1 phat in
      let (cQ2, h') = collectHead p cQ1 phat' (Syntax.Loc.ghost) (h, LF.id) in
        (cQ2, I.PObj (phat', h'))
  | I.CObj (cPsi) ->
      let phat = Context.dctxToHat cPsi in
      let (cQ2, cPsi') = collectDctx (Syntax.Loc.ghost) p cQ1 phat cPsi in
        (cQ2, I.CObj (cPsi'))
  | I.SObj (phat, s) ->
    let (cQ1, phat') = collectHat p cQ1 phat in
    let (cQ2, s')    = collectSub p cQ1 phat' s in
      (cQ2, I.SObj(phat', s'))

(* collectMSub p cQ theta = cQ' *)
and collectMSub p cQ theta =  match theta with
  | I.MShift _n ->  (cQ , theta)
  | I.MDot(mobj, t) ->
    let (cQ1, t') = collectMSub p cQ t in
    let (cQ2, mobj') = collectMObj p cQ1 mobj in
     (cQ2, I.MDot (mobj', t'))

and collectHead (k:int) cQ phat loc ((head, _subst) as sH) =
    match sH with

  | (I.BVar _x, _s)  -> (cQ, head)

  | (I.Const _c, _s) -> (cQ, head)

  | (I.FVar name, _s) ->
      begin match checkOccurrence (eqFVar name) cQ with
        | Yes -> (cQ, I.FVar name)
        | No ->
            let Int.LF.Type tA  = FVar.get name in
            let (cQ', tA') = collectTyp k (I.Dec(cQ, FV(Impure, name, None))) (None, 0) (tA, LF.id) in
              (* tA must be closed *)
              (* Since we only use abstraction on pure LF objects,
                 there are no context variables; different abstraction
                 is necessary for handling computation-level expressions,
                 and LF objects which occur in computations. *)
              (I.Dec (cQ', FV (Pure, name, Some tA')) , I.FVar name)
        | Cycle -> raise (Error (loc, CyclicDependency VariantFV))
      end


  | (I.FMVar (u, s'), s) ->
        begin match checkOccurrence (eqFMVar u) cQ with
          | Yes ->
              let (cQ', sigma) = collectSub k cQ phat (LF.comp s' s) in (cQ', I.FMVar (u, sigma))
          | No ->
              let (cQ0, sigma) = collectSub k cQ phat (LF.comp s' s) in
              let (cD_d, I.Decl (_, mtyp,dep))  = FCVar.get u in
	      let mtyp = (Whnf.cnormMTyp (mtyp, Int.LF.MShift (k - Context.length cD_d))) in
              let cQ' = I.Dec(cQ0, FMV(Impure, u, None)) in
              let (cQ1, I.MTyp (tA', cPhi'))  = collectMTyp k cQ' mtyp in
                (* tA must be closed with respect to cPhi *)
                (* Since we only use abstraction on pure LF objects,
                   there are no context variables; different abstraction
                   is necessary for handling computation-level expressions,
                   and LF objects which occur in comp utations. *)
                (I.Dec (cQ1, FMV (Pure, u, Some (I.MTyp (tA', cPhi')))), I.FMVar (u, sigma))
          | Cycle -> raise (Error (loc, CyclicDependency VariantFMV))
      end

  | (I.MVar (I.Inst ((n, q, cD, I.MTyp(tA,cPsi),  ({contents = cnstr} as c), dep) as u) as r, s'), _s) ->
      if constraints_solved cnstr then
          begin match checkOccurrence (eqMMVar u) cQ with
            | Yes ->
                let (cQ', sigma) = collectSub k cQ phat s' in
                  (cQ', I.MVar(r, sigma))
            | No ->
                (*  checkEmpty !cnstrs? -bp *)
                let (cQ0, sigma) = collectSub k cQ phat s' in
                let cQ' = I.Dec(cQ0, MMV(Impure, u)) in
                let phihat = Context.dctxToHat cPsi in
                let (cQ1, cPsi')  = collectDctx loc k cQ' phihat cPsi in
                let (cQ'', tA') = collectTyp k cQ1  phihat (tA, LF.id) in
		let v' = (n, q, cD, I.MTyp(tA',cPsi'),  c, dep) in
                let v = I.MVar (I.Inst v', sigma) in
                  (I.Dec (cQ'', MMV (Pure, v')) , v)
            | Cycle -> raise (Error (loc, CyclicDependency VariantMV))
          end
      else
        raise (Error (loc, LeftoverConstraints))

  | (I.MMVar ((n, ({contents = None} as q), I.Empty, I.MTyp(tA,cPsi),  ({contents = cnstr} as c), dep) as r, (ms', s')), _s) ->
      if constraints_solved cnstr then
          begin match checkOccurrence (eqMMVar r) cQ with
            | Yes ->
                let (cQ0, ms1) = collectMSub k cQ ms' in
                let (cQ', sigma) = collectSub k cQ0 phat s' in
                  (cQ', I.MMVar(r, (ms1, sigma)))
            | No  ->  (*  checkEmpty !cnstrs ? -bp *)
                let (cQ0, ms1) = collectMSub k cQ ms' in
                let (cQ2, sigma) = collectSub k cQ0 phat s' in

                let cQ' = I.Dec(cQ2, MMV(Impure, r)) in
                let phihat = Context.dctxToHat cPsi in
                (* let cPsi = Whnf.normDCtx cPsi in *)
                let (cQ1, cPsi')  = collectDctx loc k cQ' phihat cPsi in
                (* let (_ , offset) = phihat in
                   let _ = dprint (fun () -> "[collect] (collect in cPsi and tA) for MMV : " ^ P.headToString I.Empty (Context.hatToDCtx phihat) head) in
                   let _ = dprint (fun () -> "[collect] offset = " ^ string_of_int offset) in
                   let _ = dprint (fun () -> "[collect] MMV before : cPsi = " ^ P.dctxToString I.Empty cPsi) in
                   let _ = dprint (fun () -> "[collect] MMV after: cPsi' = " ^
                   P.dctxToString I.Empty cPsi') in
                *)
                let (cQ'', tA') = collectTyp k cQ1  phihat (tA, LF.id) in
		let v' = (n, q, I.Empty, I.MTyp(tA',cPsi'),  c, dep) in
                let v = I.MMVar (v', (ms1, sigma)) in
                  (I.Dec (cQ'', MMV (Pure, v')) , v)
            | Cycle -> raise (Error (loc, CyclicDependency VariantMMV))
          end
      else
        raise (Error (loc, LeftoverConstraints))

  | (I.MMVar ((_n, _r, _cD, I.MTyp(_tA,_cPsi),  _, _), _),  _s) ->
      raise (Error (loc, LeftoverVars VariantMMV))

  | (I.MPVar ((n, ({contents = None} as q), I.Empty, I.PTyp(tA,cPsi),  ({contents = cnstr} as c), dep) as r, (ms', s')), _s) ->
      if constraints_solved cnstr then
          begin match checkOccurrence (eqMMVar r) cQ with
            | Yes ->
                let (cQ0, ms1) = collectMSub k cQ ms' in
                let (cQ', sigma) = collectSub k cQ0 phat s' in
                  (cQ', I.MPVar(r, (ms1, sigma)))
            | No  ->  (*  checkEmpty !cnstrs ? -bp *)
                let (cQ0, ms1) = collectMSub k cQ ms' in
                let (cQ2, sigma) = collectSub k cQ0 phat s' in

                let cQ' = I.Dec(cQ2, MMV(Impure, r)) in
                let phihat = Context.dctxToHat cPsi in
                let (cQ1, cPsi')  = collectDctx loc k cQ' phihat cPsi in
                let (cQ'', tA') = collectTyp k cQ1  phihat (tA, LF.id) in
		let v' = (n, q, I.Empty, I.PTyp(tA',cPsi'),  c, dep) in
                let v = I.MPVar (v', (ms1, sigma)) in
                  (I.Dec (cQ'', MMV (Pure, v')) , v)
            | Cycle -> raise (Error (loc, CyclicDependency VariantMMV))
          end
      else
        raise (Error (loc, LeftoverConstraints))

  | (I.MPVar ((_n, ({contents = Some (I.IHead h)} as _q), cD, I.PTyp(_tA,cPsi),
    ({contents = _cnstr} as _c), _) as _r, (ms', s')), s) ->
      let h' = Whnf.cnormHead (h,ms') in
      collectHead k cQ phat loc (h', LF.comp s' s)

  | (I.MPVar ((_n, _r, _cD, I.PTyp(_tA,_cPsi),  _, _), _),  _s) ->
      raise (Error (loc, LeftoverVars VariantMMV))

  | (I.MVar (I.Offset j, s'), s) ->
      let (cQ', sigma) = collectSub k cQ phat (LF.comp s' s)  in
        (cQ', I.MVar (I.Offset j, sigma))

  | (I.FPVar (u, s'), _s) ->
      begin match checkOccurrence (eqFPVar u) cQ with
          | Yes ->
              let (cQ', sigma) = collectSub k cQ phat s' (* (LF.comp s' s) *) in
                (cQ', I.FPVar (u, sigma))
          | No  ->
              let (cQ2, sigma) = collectSub k cQ phat s' (* (LF.comp s' s) *) in
              let (cD_d, I.Decl (_, mtyp,_))  = FCVar.get u in
	      let mtyp = Whnf.cnormMTyp (mtyp, Int.LF.MShift (k - Context.length cD_d)) in
                (* tA must be closed with respect to cPhi *)
                (* Since we only use abstraction on pure LF objects,
                   there are no context variables; different abstraction
                   is necessary for handling computation-level expressions,
                   and LF objects which occur in computations. *)

              let cQ' = I.Dec(cQ2, FMV(Impure, u, None)) in
              let (cQ'', mtyp)   = collectMTyp k cQ' mtyp in
                (I.Dec (cQ'', FMV (Pure, u, Some mtyp)), I.FPVar (u, sigma))
          | Cycle -> raise (Error (loc, CyclicDependency VariantFPV))
        end

  | (I.PVar (k', s'), _s) ->
      let (cQ', sigma) =  collectSub k cQ phat s' (* (LF.comp s' s) *) in
        (cQ', I.PVar (k', sigma))


  | (I.Proj (head, j),  s) ->
      let (cQ', h') = collectHead k cQ phat loc (head, s)  in
        (cQ' , I.Proj (h', j))


and collectTyp p cQ ((cvar, offset) as phat) sA = match sA with
  | (I.Atom (loc, a, tS), s) ->
      let (cQ', tS') = collectSpine p cQ phat (tS, s) in
        (cQ', I.Atom (loc, a, tS'))

  | (I.PiTyp ((I.TypDecl (x, tA), dep ), tB),  s) ->
      let (cQ', tA')  = collectTyp p cQ phat (tA, s) in
      let (cQ'', tB') = collectTyp p cQ' (cvar, offset + 1) (tB, LF.dot1 s) in
        (cQ'', I.PiTyp ((I.TypDecl (x, tA'), dep ), tB'))

  | (I.TClo (tA, s'),  s) ->
      collectTyp p cQ phat (tA, LF.comp s' s)

  | (I.Sigma typRec,  s) ->
      let (cQ', typRec') = collectTypRec p cQ phat (typRec, s) in
        (cQ', I.Sigma typRec')


and collectTypRec p cQ ((cvar, offset) as phat) = function
  | (I.SigmaLast(n, tA), s) ->
      let (cQ', tA') = collectTyp p cQ phat (tA, s) in
        (cQ', I.SigmaLast(n,tA'))

  | (I.SigmaElem(loc, tA, typRec), s) ->
       let (cQ',tA') = collectTyp p cQ phat (tA, s) in
       let (cQ'', typRec') = collectTypRec p cQ' (cvar, offset + 1) (typRec, LF.dot1 s) in
         (cQ'', I.SigmaElem (loc, tA', typRec'))

and collectKind p cQ ((cvar, offset) as phat) sK = match sK with
  | (I.Typ, _s) ->
      (cQ, I.Typ)

  | (I.PiKind ((I.TypDecl (x, tA), dep), tK), s) ->
      let (cQ', tA') = collectTyp p cQ phat (tA, s) in
      let (cQ'', tK')= collectKind p cQ' (cvar, offset + 1) (tK, LF.dot1 s) in
        (cQ'', I.PiKind ((I.TypDecl (x, tA'), dep), tK'))


and collectHat p cQ phat = match phat with
  | (None, _offset ) -> (cQ, phat)
  | (Some (I.CtxOffset _) , _ ) -> (cQ, phat)
  | (Some (I.CInst (_, {contents=Some cPsi}, _, _, theta )), k ) ->
       let phat' = begin match Context.dctxToHat (Whnf.cnormDCtx (cPsi, theta)) with
                  | (None, i) -> (None, k+i)
                  | (Some cvar', i) -> (Some cvar', i+k)
                  end
       in
         collectHat p cQ phat'
  | (Some (I.CInst (_, {contents=None}, _, _, _theta ) as psi), _ ) ->
       (* this case should not happen -bp *)
        begin match checkOccurrence (eqCVar psi) cQ with
          | Yes -> (cQ, phat)
          | No ->  (I.Dec (cQ, CV (I.CtxVar psi)) , phat)
        end
  | (Some (I.CtxName psi) , _ ) ->
      begin match checkOccurrence (eqFCVar psi) cQ with
          | Yes -> (cQ, phat)
          | No ->
              let (_,I.Decl (_, I.CTyp s_cid,_))  = FCVar.get psi in
                (I.Dec (cQ, FCV (psi, Some (s_cid))),
                 phat)
        end

and collectDctx loc (p:int) cQ (cvar, offset) cPsi =
  collectDctx' loc p cQ (cvar, offset) (Whnf.normDCtx cPsi)

and collectDctx' loc p cQ ((cvar, offset) as _phat) cPsi = match cPsi with
  | I.Null ->  (cQ, I.Null)

  | I.CtxVar (I.CtxName psi) ->
        begin match checkOccurrence (eqFCVar psi) cQ with
          | Yes ->   (cQ , cPsi)
          | No ->
	      begin try
		let (_,I.Decl (_, I.CTyp s_cid, _))  = FCVar.get psi in
                  (I.Dec (cQ, FCV (psi, Some (s_cid))),
                   I.CtxVar (I.CtxName psi))
	      with
		  Not_found -> raise (Error (loc, UnknownSchemaCtx psi))
	      end
        end
  | I.CtxVar (I.CtxOffset _ ) -> (cQ , cPsi)

  | I.CtxVar (I.CInst (_, {contents = Some cPsi} , _, _cD, theta)) ->
      collectDctx' loc p cQ (cvar, offset) (Whnf.cnormDCtx (cPsi, theta))

  | I.CtxVar (I.CInst (_, {contents = None} , _, _cD, _theta) as psi) ->
        (* this case should not happen *)
        begin match checkOccurrence (eqCVar psi) cQ with
          | Yes -> (cQ, cPsi)
          | No ->  (I.Dec (cQ, CV (cPsi)) , cPsi)
        end
  | I.DDec(cPsi, I.TypDecl(x, tA)) ->
      let (cQ', cPsi') =  collectDctx' loc p cQ (cvar, offset - 1) cPsi in

      let (cQ'', tA')  =  collectTyp p cQ' (cvar, offset - 1) (tA, LF.id) in
        (cQ'', I.DDec (cPsi', I.TypDecl(x, tA')))


and collectMTyp p cQ = function 
  | I.CTyp (sW, dep) -> (cQ, I.CTyp (sW, dep))
  | I.MTyp (tA, cPsi) -> 
    let phat = Context.dctxToHat cPsi in
    let (cQ', cPsi') = collectDctx (Syntax.Loc.ghost) p cQ phat cPsi in
    let (cQ'', tA')    =  collectTyp p cQ' phat  (tA, LF.id) in
    (cQ'', I.MTyp (tA', cPsi'))
  | I.PTyp (tA, cPsi) -> 
    let phat = Context.dctxToHat cPsi in
    let (cQ', cPsi') = collectDctx (Syntax.Loc.ghost) p cQ phat cPsi in
    let (cQ'', tA')    =  collectTyp p cQ' phat  (tA, LF.id) in
    (cQ'', I.PTyp (tA', cPsi'))
  | I.STyp (cPhi, cPsi) ->
     let psi_hat = Context.dctxToHat cPsi in
     let phi_hat = Context.dctxToHat cPhi in
     let (cQ0, cPsi') = collectDctx (Syntax.Loc.ghost) p cQ psi_hat cPsi in
     let (cQ1, cPhi') = collectDctx (Syntax.Loc.ghost) p cQ0 phi_hat cPhi in
       (cQ1, I.STyp (cPhi', cPsi'))

let collectCDecl p cQ cdecl = match cdecl with
  | I.Decl (u, mtyp,dep) -> 
    let (cQ', mtyp') = collectMTyp p cQ mtyp in
    (cQ', I.Decl(u, mtyp',dep))

let rec collectMctx  cQ cD = match cD with
  | I.Empty -> (cQ, I.Empty)
  | I.Dec(cD, cdecl) ->
      let (cQ', cD')  = collectMctx cQ cD in
      let (cQ'', cdecl') = collectCDecl 0 cQ' cdecl in
        (cQ'', I.Dec(cD', cdecl'))

(* ****************************************************************** *)
(* Abstraction over LF-bound variables                                *)
(* ****************************************************************** *)

(* abstractKind cQ offset tK = tK'

   where tK' is tK with all occurences of FVar and MVar have been replaced by
   BVar and indexed according to their order in cQ and the base offset

   assumes there are no cycles
*)

let rec abstractKind cQ offset sK = match sK with
  | (I.Typ, _s) -> I.Typ

  | (I.PiKind ((I.TypDecl (x, tA), dep), tK), s) ->
      I.PiKind ((I.TypDecl (x, abstractTyp cQ offset (tA,s)), dep),
                abstractKind cQ (offset + 1) (tK, LF.dot1 s))

and abstractTyp cQ offset sA = abstractTypW cQ offset (Whnf.whnfTyp sA)

and abstractTypW cQ offset sA = match sA with
  | (I.Atom (loc, a, tS), s (* id *)) ->
      I.Atom (loc, a, abstractSpine cQ offset (tS, s))

  | (I.PiTyp ((I.TypDecl (x, tA), dep),  tB), s) ->
      I.PiTyp ((I.TypDecl (x, abstractTyp cQ offset (tA, s)), dep),
               abstractTyp cQ (offset + 1) (tB, LF.dot1 s))


and abstractTypRec cQ offset = function
  | (I.SigmaLast(n, tA), s) -> I.SigmaLast(n, (abstractTyp cQ offset (tA, s)))
  | (I.SigmaElem(x, tA, typRec), s) ->
      let tA = abstractTyp cQ offset (tA, s) in
      let typRec = abstractTypRec cQ offset (typRec, LF.dot1 s) in
        I.SigmaElem(x, tA, typRec)



and abstractTerm cQ offset sM = abstractTermW cQ offset (Whnf.whnf sM)

and abstractTermW cQ offset sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      I.Lam (loc, x, abstractTerm cQ (offset + 1) (tM, LF.dot1 s))

  | (I.Root (loc, (I.MVar (I.Inst ((_n, _r, _, I.MTyp(_tP,cPsi), _cnstr, _) as tH), s)), _tS (* Nil *)), _s)
  | (I.Root (loc, I.MMVar ((_n,_r,_,I.MTyp(_tP,cPsi),_cnstr,_) as tH, (_,s)), _tS), _s) ->
    (* Since sM is in whnf, _u is MVar (Inst (ref None, tP, _, _)) *)
      let x = index_of cQ (MMV (Pure, tH)) + offset in
        I.Root (loc, I.BVar x, subToSpine cQ offset (s,cPsi) I.Nil)

  | (I.Root (loc, tH, tS), s (* LF.id *)) ->
      I.Root (loc, abstractHead cQ offset tH, abstractSpine cQ offset (tS, s))


and abstractHead cQ (offset:int) tH = match tH with
  | I.BVar x ->
      I.BVar x

  | I.Const c ->
      I.Const c

  | I.FVar n ->
      I.BVar ((index_of cQ (FV (Pure, n, None))) + offset)

  | I.AnnH (_tH, _tA) ->
      raise Error.NotImplemented

  (* other cases impossible for object level *)


and subToSpine cQ offset (s,cPsi) tS = match (s, cPsi) with
  | (I.Shift _k, I.Null) ->  tS

  | (I.Shift k , I.DDec(_cPsi', _dec)) ->
       subToSpine cQ offset (I.Dot (I.Head (I.BVar (k + 1)), I.Shift (k + 1)), cPsi) tS

  | (I.Dot (I.Head (I.BVar k), s), I.DDec(cPsi', I.TypDecl (_, tA))) ->
      let tN = etaExpandHead Syntax.Loc.ghost (I.BVar k) (Whnf.normTyp (tA, LF.id)) in
      subToSpine cQ offset  (s,cPsi') (I.App (tN, tS))

  | (I.Dot (I.Head (I.MVar (_u, _r)), _s) , I.DDec(_cPsi', _dec)) ->
      (Printf.printf "SubToSpine encountered MVar as head\n";
      raise Error.NotImplemented)
      (* subToSpine cQ offset s (I.App (I.Root (I.BVar k, I.Nil), tS)) *)

  | (I.Dot (I.Obj tM, s), I.DDec(cPsi', _dec)) ->
      subToSpine cQ offset (s, cPsi') (I.App (abstractTerm cQ offset (tM, LF.id), tS))

and abstractSpine cQ offset sS = match sS with
  | (I.Nil, _s) ->
      I.Nil

  | (I.App (tM, tS), s) ->
      I.App (abstractTerm cQ offset (tM,s),  abstractSpine cQ offset (tS, s))

  | (I.SClo (tS, s'), s)  ->
      abstractSpine cQ offset (tS, LF.comp s' s)

and abstractCtx cQ =  match cQ with
  | I.Empty ->
      I.Empty
  | I.Dec (cQ, MMV (Impure, _ )) ->
      abstractCtx cQ

  | I.Dec (cQ, FV (Impure, _ , _ )) ->
      abstractCtx cQ

  | I.Dec (cQ, MMV (Pure, (n, r, cD, I.MTyp(tA,cPsi), cnstr, dep))) ->
      let cQ'   = abstractCtx cQ  in
      let l     = length cPsi in
      let cPsi' = abstractDctx cQ cPsi l in
      let tA'   = abstractTyp cQ l (tA, LF.id) in
      let u'    = (n, r, cD, I.MTyp(tA',cPsi'), cnstr, dep) in
        I.Dec (cQ', MMV (Pure, u'))

  | I.Dec (cQ, FV (Pure, f, Some tA)) ->
      let cQ' = abstractCtx cQ in
      let tA' = abstractTyp cQ 0 (tA, LF.id) in
        I.Dec (cQ', FV (Pure, f, Some tA'))


(* abstractDctx cQ cPsi l = cPsi'
   where cQ only contains FV variables not free contextual variables *)
and abstractDctx cQ cPsi l = match cPsi with
  | I.Null ->
      I.Null

  | I.CtxVar psi -> cPsi

 | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractDctx cQ cPsi (l-1) in
      let tA'   = abstractTyp cQ (l-1) (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

  (* other cases impossible in LF layer *)

  (* what about I.Dot (I.Undef, s) ? *)

  (* SVar impossible in LF layer *)

(* ****************************************************************** *)
(* Abstraction over meta-variables and parameter variables            *)
(* ****************************************************************** *)

(* Abstracting over free meta-variables (MVars with references),
   named free meta-variables, and named free parameter variables to
   create a context cD.


   This is needed in type checking and type reconstruction for computations.

*)

let rec abstractMVarTyp cQ offset sA = abstractMVarTypW cQ offset (Whnf.whnfTyp sA)

and abstractMVarTypW cQ offset sA = match sA with
  | (I.Atom (loc, a, tS), s (* id *)) ->
      I.Atom (loc, a, abstractMVarSpine cQ offset (tS, s))

  | (I.PiTyp ((I.TypDecl (x, tA), dep), tB), s) ->
      I.PiTyp ((I.TypDecl (x, abstractMVarTyp cQ offset (tA, s)), dep),
               abstractMVarTyp cQ offset (tB, LF.dot1 s))

  | (I.Sigma typRec,  s) ->
      let typRec'   = abstractMVarTypRec cQ offset (typRec, s) in
        I.Sigma typRec'


and abstractMVarTypRec cQ offset = function
  | (I.SigmaLast(n, tA), s) -> I.SigmaLast(n, (abstractMVarTyp cQ offset (tA, s)))
  | (I.SigmaElem(x, tA, typRec), s) ->
      let tA = abstractMVarTyp cQ offset (tA, s) in
      let typRec = abstractMVarTypRec cQ offset (typRec, LF.dot1 s) in
        I.SigmaElem(x, tA, typRec)

and abstractMVarTerm cQ offset sM = abstractMVarTermW cQ offset (Whnf.whnf sM)

and abstractMVarTermW cQ offset sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      I.Lam (loc, x, abstractMVarTerm cQ offset (tM, LF.dot1 s))

  | (I.Tuple (loc, tuple), s) ->
      I.Tuple (loc, abstractMVarTuple cQ offset (tuple, s))

  | (I.Root (loc, tH, tS), s (* LF.id *)) ->
      I.Root (loc, abstractMVarHead cQ offset tH, abstractMVarSpine cQ offset (tS,s))

  | (I.LFHole _loc, s) -> 
      I.LFHole _loc

and abstractMVarTuple cQ offset = function
  | (I.Last tM, s) ->
      let tM' = abstractMVarTerm cQ offset (tM, s) in
        I.Last tM'
  | (I.Cons (tM, tuple), s) ->
      let tM' = abstractMVarTerm cQ offset (tM, s) in
      let tuple' = abstractMVarTuple cQ offset (tuple, s) in
      I.Cons (tM', tuple')

and abstractMVarHead cQ ((l,d) as offset) tH = match tH with
  | I.BVar x ->
      I.BVar x

  | I.FPVar (p, s) ->
      let x = index_of cQ (FMV (Pure, p, None)) + d in
        I.PVar (x, abstractMVarSub cQ offset s)

  | I.MMVar ((_n, _r, I.Empty, _ , _cnstr, _) as r, (_ms, s)) ->
      let x = index_of cQ (MMV (Pure, r)) + d in
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MMVar ((_n, _r, _cD, _, _cnstr, _), (_ms, _s)) ->
      raise (Error (Syntax.Loc.ghost, LeftoverVars VariantMMV))

  | I.MPVar ((_n, _r, I.Empty, _, _cnstr, _) as r, (_ms, s)) ->
      let x = index_of cQ (MMV (Pure, r)) + d in
        I.PVar (x, abstractMVarSub cQ offset s)

  | I.MPVar ((_n, _r, _cD, _, _cnstr, _), (_ms, _s)) ->
      raise (Error (Syntax.Loc.ghost, LeftoverVars VariantMMV))

  | I.MVar (I.Inst ((_n, _r, cPsi, _tP , _cnstr, _) as tH), s) ->
      let x = index_of cQ (MMV (Pure, tH)) + d in
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MVar (I.Offset x , s) ->
      (* let k = Context.length cQ in  *)
      let k = lengthCollection cQ in
      if x > d then I.MVar(I.Offset ( x + k), abstractMVarSub cQ offset s)
      else
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  |  I.FMVar (u, s) ->
      let x = index_of cQ (FMV (Pure, u, None)) + d in
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.Const c ->
      I.Const c

(* Should never happen
  | I.FVar n ->
      I.BVar ((index_of cQ (FV (Pure, n, None))) + d)
*)
  | I.AnnH (_tH, _tA) ->
      raise Error.NotImplemented

  | I.Proj (head, k) ->
      let head = abstractMVarHead cQ offset head in   (* ??? -jd *)
        I.Proj (head, k)

  | I.PVar (p , s) ->
      let k = lengthCollection cQ in
      (* let k = Context.length cQ in *)
      if p > d then  I.PVar ((p+k), abstractMVarSub cQ offset s)
      else
        I.PVar (p, abstractMVarSub cQ offset s)


  (* other cases impossible for object level *)
and abstractMVarSpine cQ offset sS = match sS with
  | (I.Nil, _s) ->
      I.Nil

  | (I.App (tM, tS), s) ->
      I.App (abstractMVarTerm cQ offset (tM,s),  abstractMVarSpine cQ offset (tS, s))

  | (I.SClo (tS, s'), s)  ->
      abstractMVarSpine cQ offset (tS, LF.comp s' s)

and abstractMVarSub cQ offset s = abstractMVarSub'
  cQ offset (Whnf.cnormSub (s, Whnf.m_id))

and abstractMVarSub' cQ ((l,d) as offset) s = match s with
  | I.EmptySub -> I.EmptySub
  | I.Undefs -> I.Undefs
  | I.Shift _ -> s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractMVarHead cQ offset tH), abstractMVarSub' cQ offset s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractMVarTerm cQ offset (tM, LF.id)), abstractMVarSub' cQ offset s)

  | I.SVar (s, n, sigma) ->
      let _ = dprint (fun () -> "[abstractMVarSub] d = " ^ string_of_int d) in
(*      let k = lengthCollection cQ in
      if s > d then I.SVar (I.Offset (s + k), (ctx_offset, n), abstractMVarSub' cQ offset sigma)
      else*)
        I.SVar (s, n, abstractMVarSub' cQ offset sigma)

  | I.Dot (I.Undef, s) ->
      I.Dot (I.Undef, abstractMVarSub' cQ offset s)

  | I.FSVar (s, n, sigma) ->
      let x = index_of cQ (FMV (Pure, s, None)) + d in
      I.SVar (x, n, abstractMVarSub cQ offset sigma)

  | I.MSVar ((_n, _r, _cD, I.STyp(_cPhi, _cPsi), _cnstr, _) as r, k, (_mt, s')) ->
    let s = index_of cQ (MMV (Pure, r)) + d  in
    I.SVar (s, k, abstractMVarSub' cQ offset s')


and abstractMVarHat cQ (l,offset) phat = match phat with
  | (None, _ ) -> phat
  | (Some (I.CtxOffset x), k ) ->
      if x <= offset then phat
      else (Some (I.CtxOffset (x+l)), k)
  | (Some (I.CtxName psi), k) ->
      let x = index_of cQ (FCV (psi, None)) + offset in
        (Some (I.CtxOffset x), k)
  (* case where contents = Some cPsi cannot happen,
     since collect normalized phat *)
  | (Some (I.CInst (_, {contents = None}, _, _, _theta ) as psi), k) ->
      let x = index_of cQ (CV (I.CtxVar psi)) + offset in
        (Some (I.CtxOffset x  ), k)
  |  _ -> abstractMVarHat cQ (l,offset) (Whnf.cnorm_psihat phat Whnf.m_id)

and abstractMVarDctx cQ (l,offset) cPsi = match cPsi with
  | I.Null ->
      I.Null
  | I.CtxVar (I.CtxOffset psi) ->
      if psi <= offset then
        cPsi
      else
           I.CtxVar (I.CtxOffset (psi + l))
  | I.CtxVar (I.CtxName psi) ->
      let x = index_of cQ (FCV (psi, None)) + offset in
        I.CtxVar (I.CtxOffset x)
  | I.CtxVar (I.CInst (_, {contents = Some cPsi}, _, _, theta )) ->
      abstractMVarDctx cQ (l,offset) (Whnf.cnormDCtx (cPsi, theta))
  | I.CtxVar (I.CInst (_, {contents = None}, _, _, _theta)) ->
      (* this case should not happen -bp *)
      let x = index_of cQ (CV cPsi) + offset in
        I.CtxVar (I.CtxOffset x)

  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractMVarDctx cQ (l,offset) cPsi in
      let tA'   = abstractMVarTyp cQ (l,offset) (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

and abstractMVarMTyp cQ mtyp loff = match mtyp with
  | I.MTyp (tA, cPsi) ->
    I.MTyp (abstractMVarTyp cQ loff (tA, LF.id), abstractMVarDctx cQ loff cPsi)
  | I.PTyp (tA, cPsi) ->
    I.PTyp (abstractMVarTyp cQ loff (tA, LF.id), abstractMVarDctx cQ loff cPsi)
  | I.STyp (cPhi, cPsi) ->
    I.STyp (abstractMVarDctx cQ loff cPhi, abstractMVarDctx cQ loff cPsi)
  | I.CTyp sW -> I.CTyp sW


and abstractMVarMetaTyp cQ mtyp loff = abstractMVarMTyp cQ mtyp loff


and abstractMVarCdecl cQ loff cdecl = match cdecl with
  | I.Decl (u, mtyp, dep) -> I.Decl (u, abstractMVarMTyp cQ mtyp loff, dep)

and abstractMVarMctx cQ cD (l,offset) = match cD with
  | I.Empty -> I.Empty
  | I.Dec(cD, cdecl) ->
    I.Dec(abstractMVarMctx cQ cD (l, offset - 1), abstractMVarCdecl cQ (l, offset) cdecl)

and abstractMVarCtx cQ l =  match cQ with
  | I.Empty -> I.Empty

  | I.Dec (cQ, MMV (Pure, (n, r, I.Empty, ityp, cnstr, dep))) ->
      let cQ'   = abstractMVarCtx  cQ (l-1) in
      let u'    = (n, r, I.Empty, abstractMVarMTyp cQ ityp (l,0), cnstr, dep) in
        I.Dec (cQ', MMV (Pure, u'))

  | I.Dec (_cQ, MMV (Pure, _)) ->
      raise (Error (Syntax.Loc.ghost, LeftoverVars VariantMMV))

  | I.Dec (cQ, CV (cPsi)) -> (* cPsi = CtxVar (CInst _ ) *)
      let cQ'   = abstractMVarCtx  cQ (l-1) in
      I.Dec(cQ', CV (cPsi))

  | I.Dec (cQ, CtxV cdecl) ->
      let cQ'   = abstractMVarCtx  cQ (l-1) in
      I.Dec(cQ', CtxV cdecl)

  | I.Dec (cQ, FCV (psi, Some s_cid)) ->
      let cQ'   = abstractMVarCtx  cQ (l-1) in
      I.Dec(cQ', FCV (psi, Some s_cid))

  | I.Dec (cQ, FMV (Pure, u, Some mtyp)) ->
      let cQ'   = abstractMVarCtx cQ (l-1) in
      let mtyp' = abstractMVarMTyp cQ mtyp (l, 0) in
      I.Dec (cQ', FMV (Pure, u, Some mtyp'))

  | I.Dec (cQ, MMV (Impure, _u)) ->
      abstractMVarCtx  cQ l

  | I.Dec (cQ, FMV (Impure, _u, _)) ->
      abstractMVarCtx  cQ l


  | I.Dec (_cQ, FV _) ->
        (* This case is hit in e.g.  ... f[g, x:block y:tp. exp unk], where unk is an unknown identifier;
         * is it ever hit on correct code?  -jd 2009-02-12
         * No. This case should not occur in correct code - bp
         *)
      raise (Error (Syntax.Loc.ghost, UnknownIdentifier))


(* Cases for: FMV, FPV *)
let abstrMObj cQ = function
  | I.MObj(phat, tM) ->
     let phat' = abstractMVarHat cQ (0,0) phat in
     let tM' = abstractMVarTerm cQ (0,0) (tM, LF.id) in
     I.MObj(phat', tM')

  | I.PObj(phat, h) ->
     let phat' = abstractMVarHat cQ (0,0) phat in
     let h' = abstractMVarHead cQ (0,0) h in
     I.PObj(phat', h')

  | I.CObj(cPsi) ->
     I.CObj(abstractMVarDctx cQ (0,0) cPsi)

  | I.SObj (phat, s) ->
     let phat' = abstractMVarHat cQ (0,0) phat in
     let s'    = abstractMVarSub cQ (0,0) s in
     I.SObj (phat', s')
  | I.MV k -> I.MV k

let rec abstrMSub cQ t =
  let l = lengthCollection cQ in
  let rec abstrMSub' t =
    match t with
      | I.MShift n -> I.MShift (n+l)
      | I.MDot(mobj, t) -> I.MDot(abstrMObj cQ mobj, abstrMSub' t)
  in
    abstrMSub' t

and abstractMSub t =
  let (cQ, t') = collectMSub 0 I.Empty t in
  let cQ' = abstractMVarCtx cQ 0 in
  let t'' = abstrMSub cQ' t' in
  let cD' = ctxToMCtx cQ' in
  (t'', cD')

(* wrapper function *)
let abstrKind tK =
  (* what is the purpose of phat? *)
  let empty_phat = (None, 0) in
  let (cQ, tK')      = collectKind 0 I.Empty empty_phat (tK, LF.id) in
    begin match cQ with
        Int.LF.Empty -> (tK', 0)
      | _       ->
          let cQ'        = abstractCtx cQ in
          let tK''        = abstractKind cQ' 0 (tK', LF.id) in
          let cPsi       = ctxToDctx cQ' in
            (raiseKind cPsi tK'', length cPsi)
    end

and abstrTyp tA =
  let empty_phat = (None, 0) in

  let (cQ, tA')       = collectTyp 0 I.Empty empty_phat (tA, LF.id) in
   begin match cQ with
        Int.LF.Empty -> (tA', 0)
      | _       ->
          let cQ'        = abstractCtx cQ in
          let tA2        = abstractTyp cQ' 0 (tA', LF.id) in
          let cPsi       = ctxToDctx cQ' in
            begin match raiseType cPsi tA2 with
              | (None, tA3) -> (tA3, length cPsi)
              | _            -> raise (Error (Syntax.Loc.ghost, LeftoverVars VariantFCV))
            end
    end

(* *********************************************************************** *)
(* Abstract over computations *)
(* *********************************************************************** *)


let rec collectCompKind p cQ cK = match cK with
  | Comp.Ctype _ -> (cQ, cK)
  | Comp.PiKind (loc, cdecl, cK1) ->
      let (cQ' , cdecl') = collectCDecl p cQ cdecl in
      let (cQ'', cK2)    = collectCompKind p cQ' cK1 in
        (cQ'', Comp.PiKind (loc, cdecl', cK2) )

let rec collect_meta_obj p cQ cM = match cM with
  | Comp.MetaCtx (loc, cPsi) ->
      let phat = Context.dctxToHat cPsi in
      let (cQ', cPsi') = collectDctx loc p cQ phat cPsi in
        (cQ', Comp.MetaCtx (loc, cPsi'))
  | Comp.MetaObj (loc, phat, Int.LF.INorm tM) ->
      let (cQ', phat') = collectHat p cQ phat in
      let (cQ', tM') = collectTerm p cQ' phat' (tM, LF.id) in
        (cQ', Comp.MetaObj (loc, phat', Int.LF.INorm tM'))
  | Comp.MetaObjAnn (loc, cPsi, Int.LF.INorm tM) ->
      let phat = Context.dctxToHat cPsi in
      let (cQ', cPsi') = collectDctx loc p cQ phat cPsi in
      let (cQ'', tM') = collectTerm p cQ' phat (tM, LF.id) in
        (cQ'', Comp.MetaObjAnn (loc, cPsi', Int.LF.INorm tM'))
  | Comp.MetaObj (loc, phat, Int.LF.IHead h) ->
      let (cQ', phat') = collectHat p cQ phat in
      let (cQ'', h') = collectHead p cQ' phat loc (h, LF.id) in
        (cQ'', Comp.MetaObj (loc, phat', Int.LF.IHead h'))
  | Comp.MetaObj (loc, phat, Int.LF.ISub tM) ->
      let (cQ', phat') = collectHat p cQ phat in
      let (cQ', tM') = collectSub p cQ' phat' tM in
        (cQ', Comp.MetaObj (loc, phat', Int.LF.ISub tM'))
  | Comp.MetaObjAnn (loc, cPsi, Int.LF.ISub tM) ->
      let phat = Context.dctxToHat cPsi in
      let (cQ', cPsi') = collectDctx loc p cQ phat cPsi in
      let (cQ'', tM') = collectSub p cQ' phat tM in
        (cQ'', Comp.MetaObjAnn (loc, cPsi', Int.LF.ISub tM'))

and collect_meta_spine p cQ cS = match cS with
  | Comp.MetaNil -> (cQ, Comp.MetaNil)
  | Comp.MetaApp (cM, cS) ->
      let (cQ', cM') = collect_meta_obj p cQ cM in
      let (cQ'', cS') = collect_meta_spine p cQ' cS in
        (cQ'', Comp.MetaApp (cM', cS'))

let collectMetaTyp loc p cQ mT = match mT with 
  | Int.LF.MTyp (tA, cPsi) -> 
      let phat = Context.dctxToHat cPsi in
      let (cQ', cPsi') = collectDctx loc p cQ phat cPsi in
      let (cQ'', tA')  = collectTyp p cQ' phat (tA, LF.id) in
	(cQ'', Int.LF.MTyp (tA', cPsi'))
  | Int.LF.CTyp _w -> (cQ, mT)


let rec collectCompTyp p cQ tau = match tau with
  | Comp.TypBase (loc, a, ms) ->
      let (cQ', ms') = collect_meta_spine p cQ ms in
        (cQ', Comp.TypBase (loc, a, ms'))
  | Comp.TypCobase (loc, a, ms) ->
      let (cQ', ms') = collect_meta_spine p cQ ms in
        (cQ', Comp.TypCobase (loc, a, ms'))

  | Comp.TypBox (loc, mT) ->
      let (cQ', mT') = collectMetaTyp loc p cQ mT in
        (cQ', Comp.TypBox (loc, mT'))

  | Comp.TypSub (loc, cPhi, cPsi) ->
      let phat = Context.dctxToHat cPsi in
      let (cQ', cPsi') = collectDctx loc p cQ phat cPsi in
      let (cQ'', cPhi') = collectDctx loc p cQ phat cPhi in
        (cQ'', Comp.TypSub (loc, cPhi', cPsi'))

  | Comp.TypArr (tau1, tau2) ->
      let (cQ1, tau1') = collectCompTyp p cQ tau1 in
      let (cQ2, tau2') = collectCompTyp p cQ1 tau2 in
        (cQ2, Comp.TypArr (tau1', tau2'))

  | Comp.TypCross (tau1, tau2) ->
      let (cQ1, tau1') = collectCompTyp p cQ tau1 in
      let (cQ2, tau2') = collectCompTyp p cQ1 tau2 in
        (cQ2, Comp.TypCross (tau1', tau2'))

  | Comp.TypPiBox ((cdecl), tau) ->
      let (cQ', cdecl') = collectCDecl p cQ cdecl in
      let (cQ'', tau') = collectCompTyp p cQ' tau in
      (cQ'', Comp.TypPiBox (cdecl', tau'))

  | Comp.TypBool  -> (cQ, tau)
  | Comp.TypClo _ -> (dprint (fun () -> "collectCTyp -- TypClo missing");
                      raise Error.NotImplemented)


let rec collectGctx cQ cG = match cG with
  | I.Empty -> (cQ, I.Empty)
  | I.Dec (cG, Comp.CTypDecl (x, tau)) ->
      let (cQ1, cG') = collectGctx cQ cG in
      let (cQ2, tau') = collectCompTyp 0 cQ1 tau in
        (cQ2, I.Dec (cG', Comp.CTypDecl (x, tau')))

let rec collectExp cQ e = match e with
  | Comp.Syn (loc, i) ->
      let (cQ', i') = collectExp' cQ i in
        (cQ', Comp.Syn(loc, i'))

  | Comp.Rec (loc, f, e) ->
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.Rec (loc, f, e') )

  | Comp.Fun (loc, x, e) ->
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.Fun (loc, x, e'))

  | Comp.Cofun (loc, bs) ->
      let (cQ', bs') = collectCofuns cQ bs in
        (cQ', Comp.Cofun (loc, bs'))

  | Comp.MLam (loc, u, e) ->
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.MLam (loc, u, e'))

  | Comp.Pair (loc, e1, e2) ->
      let (cQ1, e1') = collectExp cQ e1 in
      let (cQ2, e2') = collectExp cQ1 e2 in
        (cQ2, Comp.Pair (loc, e1', e2') )

  | Comp.LetPair (loc, i, (x, y, e)) ->
      let (cQi, i') = collectExp' cQ i in
      let (cQ2, e') = collectExp cQi e in
        (cQ2, Comp.LetPair (loc, i', (x, y, e')))

  | Comp.Let (loc, i, (x, e)) ->
      let (cQi, i') = collectExp' cQ i in
      let (cQ2, e') = collectExp cQi e in
        (cQ2, Comp.Let (loc, i', (x, e')))

  | Comp.Box (loc, cM) ->
      let (cQ'', cM') = collect_meta_obj 0 cQ cM in
        (cQ'', Comp.Box (loc, cM'))


  | Comp.Case (loc, prag, i, branches) ->
      let (cQ', i') = collectExp' cQ i in
      let (cQ2, branches') = collectBranches cQ' branches in
        (cQ2, Comp.Case (loc, prag, i', branches'))

  | Comp.If (loc, i, e1, e2) ->
      let (cQ', i') = collectExp' cQ i in
      let (cQ1, e1') = collectExp cQ' e1 in
      let (cQ2, e2') = collectExp cQ1 e2 in
        (cQ2, Comp.If (loc, i', e1', e2'))

  | Comp.Hole (loc, f) -> (cQ, Comp.Hole (loc, f))

and collectExp' cQ i = match i with
  | Comp.Var (_, _x) -> (cQ , i)
  | Comp.DataConst (_, _c) ->  (cQ , i)
  | Comp.DataDest (_, _c) -> (cQ , i)
  | Comp.Const (_, _c) ->  (cQ , i)
  | Comp.Apply (loc, i, e) ->
      let (cQ', i') = collectExp' cQ i  in
      let (cQ'', e') = collectExp cQ' e in
        (cQ'', Comp.Apply (loc, i', e'))

  | Comp.MApp (loc, i, cM) ->
      let (cQ', i') = collectExp' cQ i  in
      let (cQ'', cM') = collect_meta_obj 0 cQ cM in
        (cQ'', Comp.MApp (loc, i', cM'))

  | Comp.Ann  (e, tau) ->
      let (cQ', e') = collectExp cQ e in
      let (cQ'', tau') = collectCompTyp 0 cQ' tau in
        (cQ'', Comp.Ann  (e', tau'))

  | Comp.Equal (loc, i1, i2) ->
     let (cQ', i1') = collectExp' cQ i1  in
     let (cQ'', i2') = collectExp' cQ' i2  in
       (cQ'', Comp.Equal(loc, i1', i2'))

  | Comp.PairVal (loc, i1, i2) ->
     let (cQ', i1') = collectExp' cQ i1  in
     let (cQ'', i2') = collectExp' cQ' i2  in
       (cQ'', Comp.PairVal(loc, i1', i2'))

  | Comp.Boolean b -> (cQ, Comp.Boolean b)

and collectCofun cQ csp = match csp with
  | Comp.CopatNil loc -> (cQ, Comp.CopatNil loc)
  | Comp.CopatApp (loc, dest, csp') ->
      let (cQ, csp') = collectCofun cQ csp' in
        (cQ, Comp.CopatApp (loc, dest, csp'))
  | Comp.CopatMeta (loc, cM, csp') ->
      let (cQ, cM') = collect_meta_obj 0 cQ cM in
      let (cQ, csp') = collectCofun cQ csp' in
        (cQ, Comp.CopatMeta (loc, cM', csp'))

and collectCofuns cQ csps = match csps with
  | [] -> (cQ, [])
  | (c, e)::csps' ->
      let (cQ', c') = collectCofun cQ c in
      let (cQ2, e') = collectExp cQ' e in
      let (cQ2', csps'') =  collectCofuns cQ' csps' in
        (cQ2', (c', e')::csps'')

and collectPatObj cQ pat = match pat with
  | Comp.PatEmpty (loc, cPsi) ->
      let (cQ1, cPsi') = collectDctx loc 0 cQ (Context.dctxToHat cPsi) cPsi in
        (cQ1, Comp.PatEmpty (loc, cPsi'))
  | Comp.PatFVar (loc, x) -> (cQ, pat)
  | Comp.PatVar  (loc, x) -> (cQ, pat)
  | Comp.PatTrue loc -> (cQ, pat)
  | Comp.PatFalse loc -> (cQ, pat)
  | Comp.PatPair (loc, pat1, pat2) ->
      let (cQ1, pat1') = collectPatObj cQ pat1 in
      let (cQ2, pat2') = collectPatObj cQ1 pat2 in
        (cQ2, Comp.PatPair (loc, pat1', pat2'))
  | Comp.PatAnn (loc, pat, tau) ->
      let (cQ1, pat') = collectPatObj cQ pat in
      let (cQ2, tau') = collectCompTyp 0 cQ1 tau in
        (cQ2, Comp.PatAnn (loc, pat', tau'))
  | Comp.PatConst (loc, c, pat_spine) ->
      let (cQ1, pat_spine') = collectPatSpine cQ pat_spine in
        (cQ1, Comp.PatConst (loc, c, pat_spine'))
  | Comp.PatMetaObj (loc, cM) ->
      let (cQ, cM') = collect_meta_obj 0 cQ cM in
        (cQ, Comp.PatMetaObj (loc, cM'))

and collectPatSpine cQ pat_spine = match pat_spine with
  | Comp.PatNil -> (cQ, Comp.PatNil)
  | Comp.PatApp (loc, pat, pat_spine) ->
      let (cQ1, pat') = collectPatObj cQ pat in
      let (cQ2, pat_spine') = collectPatSpine cQ1 pat_spine in
        (cQ2, Comp.PatApp (loc, pat', pat_spine'))


and collectPattern cQ cD cPsi (phat, tM) tA =
  let (cQ1, cD') = collectMctx cQ cD in
  let (cQ2, cPsi') = collectDctx (Syntax.Loc.ghost) 0 cQ1 phat cPsi in
  let (cQ2', phat') = collectHat 0 cQ2 phat in
  let (cQ3, tM') = collectTerm 0 cQ2' phat' (tM, LF.id) in
  let (cQ4, tA') = collectTyp 0 cQ3 phat' (tA, LF.id) in
    (cQ4, cD', cPsi', (phat', tM'), tA')



and collectSubPattern cQ cD cPsi sigma cPhi =
  let (cQ1, cD')    = collectMctx cQ cD in
  let phat = Context.dctxToHat cPsi in
  let (cQ2, cPsi')  = collectDctx (Syntax.Loc.ghost) 0 cQ1 phat cPsi in
  let (cQ3, cPhi')  = collectDctx (Syntax.Loc.ghost) 0 cQ2 phat cPhi in
  let (cQ4, sigma') = collectSub  0 cQ3 phat sigma in

    (cQ4, cD', cPsi', sigma', cPhi')




and collectBranch cQ branch = match branch with
  | Comp.Branch (loc, cD, cG, pat, msub, e) ->
      (* cG, cD, and pat cannot contain any free meta-variables *)
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.Branch (loc, cD, cG, pat, msub, e'))
  | Comp.EmptyBranch _  ->
        (cQ, branch)
  | Comp.BranchBox (cO, cD, (dctx, Comp.NormalPattern(pat, e), msub, csub)) ->
      (* pat and cD cannot contain any free meta-variables *)
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.BranchBox (cO, cD, (dctx, Comp.NormalPattern(pat, e'), msub, csub)))

  | Comp.BranchBox (cO, cD, (dctx, Comp.EmptyPattern, msub, csub)) ->
      (* pat and cD cannot contain any free meta-variables *)
        (cQ, Comp.BranchBox (cO, cD, (dctx, Comp.EmptyPattern, msub, csub)))

and collectBranches cQ branches = match branches with
  | [] -> (cQ, [])
  | b::branches ->
      let (cQ', b') = collectBranch cQ b in
      let (cQ2, branches') =  collectBranches cQ' branches in
        (cQ2, b'::branches')

let rec abstractMVarCompKind cQ (l,offset) cK = match cK with
  | Comp.Ctype _loc -> cK
  | Comp.PiKind (loc, cdecl, cK) ->
      let cK'  = abstractMVarCompKind cQ (l,offset+1) cK in
      let cdecl' = abstractMVarCdecl cQ (l,offset) cdecl in
        Comp.PiKind (loc, cdecl', cK')

let rec abstractMVarMetaObj cQ offset cM = match cM with
  | Comp.MetaCtx (loc, cPsi) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
        Comp.MetaCtx (loc, cPsi')
  | Comp.MetaObj (loc, phat, Int.LF.INorm tM) ->
      let phat' = abstractMVarHat cQ offset phat in
      let tM' = abstractMVarTerm  cQ  offset (tM, LF.id) in
        Comp.MetaObj (loc, phat', Int.LF.INorm tM')
  | Comp.MetaObjAnn (loc, cPsi, Int.LF.INorm tM) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tM' = abstractMVarTerm  cQ  offset (tM, LF.id) in
        Comp.MetaObjAnn (loc, cPsi', Int.LF.INorm tM')
  | Comp.MetaObj (loc, phat, Int.LF.IHead h) ->
      let phat' = abstractMVarHat cQ offset phat in
      let h' = abstractMVarHead cQ offset h in
        Comp.MetaObj (loc, phat', Int.LF.IHead h')
  | Comp.MetaObj (loc, phat, Int.LF.ISub tM) ->
      let phat' = abstractMVarHat cQ offset phat in
      let tM' = abstractMVarSub  cQ  offset tM in
        Comp.MetaObj (loc, phat', Int.LF.ISub tM')
  | Comp.MetaObjAnn (loc, cPsi, Int.LF.ISub tM) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tM' = abstractMVarSub  cQ  offset tM in
        Comp.MetaObjAnn (loc, cPsi', Int.LF.ISub tM')

and abstractMVarMetaSpine cQ offset cS = match cS with
  | Comp.MetaNil -> Comp.MetaNil
  | Comp.MetaApp (cM, cS) ->
      let cM' = abstractMVarMetaObj cQ offset cM in
      let cS' = abstractMVarMetaSpine cQ offset cS in
        Comp.MetaApp (cM', cS')

let rec abstractMVarCompTyp cQ ((l,d) as offset) tau = match tau with
  | Comp.TypBase (loc, a, cS) ->
      let cS' = abstractMVarMetaSpine cQ offset cS in
        Comp.TypBase (loc, a , cS')
  | Comp.TypCobase (loc, a, cS) ->
      let cS' = abstractMVarMetaSpine cQ offset cS in
        Comp.TypCobase (loc, a , cS')
  | Comp.TypBox (loc, Int.LF.MTyp (tA, cPsi)) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in
        Comp.TypBox (loc, Int.LF.MTyp (tA', cPsi'))

  | Comp.TypSub (loc, cPhi, cPsi) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let cPhi' = abstractMVarDctx cQ offset cPhi in
        Comp.TypSub (loc, cPhi', cPsi')

  | Comp.TypArr (tau1, tau2) ->
      Comp.TypArr (abstractMVarCompTyp cQ offset tau1,
                   abstractMVarCompTyp cQ offset tau2)

  | Comp.TypCross (tau1, tau2) ->
      Comp.TypCross (abstractMVarCompTyp cQ offset tau1,
                     abstractMVarCompTyp cQ offset tau2)
  | Comp.TypPiBox (cdecl, tau) ->
    Comp.TypPiBox ((abstractMVarCdecl cQ offset cdecl), abstractMVarCompTyp cQ (l,d+1) tau)

  | Comp.TypBool -> Comp.TypBool


let rec abstractMVarGctx cQ offset cG = match cG with
  | I.Empty -> I.Empty
  | I.Dec (cG, Comp.CTypDecl (x, tau)) ->
      let cG' = abstractMVarGctx cQ offset cG in
      let tau' = abstractMVarCompTyp cQ offset tau in
        I.Dec (cG', Comp.CTypDecl (x, tau'))

let rec abstractMVarPatObj cQ cG offset pat = match pat with
  | Comp.PatEmpty (loc, cPsi) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
        Comp.PatEmpty (loc, cPsi')
  | Comp.PatTrue loc -> pat
  | Comp.PatFalse loc -> pat
  | Comp.PatVar (_loc,_x) -> pat
  | Comp.PatFVar (loc,x) -> pat

  | Comp.PatPair (loc, pat1, pat2) ->
      let pat1' = abstractMVarPatObj cQ cG offset pat1 in
      let pat2' = abstractMVarPatObj cQ cG offset pat2 in
        Comp.PatPair (loc, pat1', pat2')
  | Comp.PatAnn (loc, pat, tau) ->
      let  pat' = abstractMVarPatObj cQ cG offset pat in
      let tau' = abstractMVarCompTyp cQ offset tau in
        Comp.PatAnn (loc, pat', tau')
  | Comp.PatConst (loc, c, pat_spine) ->
      let pat_spine' = abstractMVarPatSpine cQ cG offset pat_spine in
        Comp.PatConst (loc, c, pat_spine')

  | Comp.PatMetaObj (loc, mO) ->
      let mO' = abstractMVarMetaObj cQ offset mO in
        Comp.PatMetaObj (loc, mO')

and abstractMVarPatSpine cQ cG offset pat_spine = match pat_spine with
  | Comp.PatNil -> Comp.PatNil
  | Comp.PatApp (loc, pat, pat_spine) ->
      let pat' = abstractMVarPatObj cQ cG offset pat in
      let pat_spine' = abstractMVarPatSpine cQ cG offset pat_spine in
        Comp.PatApp (loc, pat', pat_spine')


let rec raiseCompTyp cD tau =  match cD with
  | I.Empty -> tau
  | I.Dec(cD, I.Decl (psi, I.CTyp w, dep)) ->
      raiseCompTyp cD (Comp.TypPiBox ((I.Decl(psi, I.CTyp w, dep)), tau))
  | I.Dec(cD ,mdecl) ->
      raiseCompTyp cD (Comp.TypPiBox ((mdecl), tau))

let raiseCompKind cD cK =
  let
(*    rec roll cK = match cK with
    | Comp.PiKind (loc, (cdecl, dep), cK') ->
        Comp.PiKind (loc, (cdecl, dep), roll cK')
    | _ ->  raisePiBox cD cK
*)
  rec raisePiBox cD cK = match cD with
    | I.Empty -> cK
    | I.Dec(cD', mdecl) ->
        raisePiBox cD' (Comp.PiKind (Syntax.Loc.ghost, mdecl, cK))
  in
    raisePiBox cD cK

let abstrCompKind cK =
  let rec roll cK cQ = match cK with
    | Comp.PiKind (_, I.Decl(psi, I.CTyp w, dep), cK) ->
        roll cK (I.Dec(cQ, CtxV (psi,w, dep)))
    | cK -> (cQ, cK)
  in
  let (cQ, cK')  = roll cK I.Empty in
  let l'           = lengthCollection cQ in
  let p = prefixCompKind cK' in (* p = number of explicitely declared mvars *)
  let (cQ, cK1)  = collectCompKind (l'+p) cQ cK' in
  let k           = lengthCollection cQ in
  let l           = (k - l') in
  let cQ'  = abstractMVarCtx cQ (l-1-p)  in
  let cK' = abstractMVarCompKind cQ' (l,0) cK1 in
  let cD' = ctxToMCtx cQ' in
  let cK2 = raiseCompKind cD' cK' in
    (cK2, Context.length cD')

let abstrCompTyp tau =
  let rec roll tau cQ = match tau with
    | Comp.TypPiBox (I.Decl(psi, I.CTyp w, dep), tau) ->
        roll tau (I.Dec(cQ, CtxV (psi,w,dep)))
    | tau -> (cQ, tau)
  in
  let (cQ, tau')  = roll tau I.Empty in
  let l'           = lengthCollection cQ in
  let p = prefixCompTyp tau' in (* p = number of explicitely declared mvars *)
  let (cQ, tau1)  = collectCompTyp (l'+p) cQ tau' in
  let k           = lengthCollection cQ in
  let l           = (k - l') in
  let cQ'  = abstractMVarCtx cQ (l-1-p) in
  (* let cQ'  = abstractMVarCtx cQ (l-1) in  *)
  let tau' = abstractMVarCompTyp cQ' (l,0) tau1 in
  let cD' = ctxToMCtx cQ' in
  let tau'' = raiseCompTyp cD' tau' in
    (tau'', Context.length cD' )


let abstrPatObj loc cD cG pat tau =
  let pat = Whnf.cnormPattern (pat, Whnf.m_id) in
  let cG = Whnf.cnormCtx (cG, Whnf.m_id) in
  let (cQ1, cD1') = collectMctx I.Empty cD in
  let (cQ2, cG)   = collectGctx cQ1 cG   in
  let (cQ3, pat') = collectPatObj cQ2 pat in
  let (cQ, tau') = collectCompTyp 0 cQ3 tau in
  let cQ'     = abstractMVarCtx cQ 0 in
  let offset  = Context.length cD1' in
  let cG'     = abstractMVarGctx cQ' (0,offset) cG in
  let pat'    = abstractMVarPatObj cQ' cG' (0,offset) pat' in
  let tau'    = abstractMVarCompTyp cQ' (0,offset) tau' in
  let cD'     = ctxToMCtx cQ' in 
  let cD2     = abstractMVarMctx cQ' cD1' (0,offset-1) in
  let cD      = Context.append cD' cD2 in
      (cD, cG', pat', tau')

(*
   1) Collect FMVar and FPVars  in cD1, Psi1, tM and tA
   2) Abstract FMVar and FPVars in cD1, Psi1, tM and tA

*)
let abstrPattern cD1 cPsi1  (phat, tM) tA =
  let (cQ, cD1', cPsi1', (phat, tM'), tA')  = collectPattern I.Empty cD1 cPsi1 (phat,tM) tA in
  let cQ'     = abstractMVarCtx cQ 0 in
  let offset  = Context.length cD1' in
  let cPsi2   = abstractMVarDctx cQ' (0,offset) cPsi1' in
  let tM2     = abstractMVarTerm cQ' (0,offset) (tM', LF.id) in
  let tA2     = abstractMVarTyp  cQ' (0,offset) (tA', LF.id) in
  let cD2     = abstractMVarMctx cQ' cD1' (0, offset-1) in
(*  let cs1'    = abstractMVarCSub cQ' offset cs1 in
  let cs'     = abstractMVarCSub cQ' offset cs in *)
  let cD'     = ctxToMCtx ~dep':I.No cQ' in
  let cD      = Context.append cD' cD2 in
    (cD, cPsi2, (phat, tM2), tA2)


let abstrMObjPatt cD1 cM mT =
  let (cQ1, cD1') = collectMctx I.Empty cD1 in
  let (cQ2, cM') = collect_meta_obj 0 cQ1 cM in
  let (cQ3, mT') = collectMetaTyp (Syntax.Loc.ghost) 0 cQ2 mT in
  let cQ'     = abstractMVarCtx cQ3 0 in
  let offset  = Context.length cD1' in
  let cM'     = abstractMVarMetaObj cQ' (0, offset) cM' in
  let mT'      = abstractMVarMetaTyp cQ' mT' (0, offset) in
  let cD2     = abstractMVarMctx cQ' cD1' (0, offset-1) in
  let cD'     = ctxToMCtx ~dep':I.No cQ' in
  let cD      = Context.append cD' cD2 in
    (cD, cM', mT')

(*
   1) Collect FMVar and FPVars  in cD1, Psi1, tM and tA
   2) Abstract FMVar and FPVars in cD1, Psi1, tM and tA

*)
let abstrSubPattern cD1 cPsi1  sigma cPhi1 =
  let (cQ, cD1', cPsi1', sigma', cPhi1')  = collectSubPattern I.Empty cD1 cPsi1 sigma cPhi1 in
  let cQ'      = abstractMVarCtx cQ 0 in
  let offset   = Context.length cD1' in
  let cPsi2    = abstractMVarDctx cQ' (0,offset) cPsi1' in
  let sigma2   = abstractMVarSub cQ' (0,offset) sigma' in
  let cPhi2    = abstractMVarDctx cQ' (0,offset) cPhi1' in
  let cD2      = abstractMVarMctx cQ' cD1' (0, offset-1) in
  let cD'      = ctxToMCtx cQ' in
  let cD       = Context.append cD' cD2 in
    (cD, cPsi2, sigma2, cPhi2)



let abstrExp e =
  let (cQ, e')    = collectExp I.Empty e in
  let loc = getLocation e' in
    begin match cQ with
        I.Empty -> e'
      | _       ->
            let _ = dprint (fun () -> "Collection of MVars\n" ^ collectionToString cQ )in
              raise (Error (loc, LeftoverVars VariantMV))
    end

(* appDCtx cPsi1 cPsi2 = cPsi1, cPsi2 *)
let rec appDCtx cPsi1 cPsi2 = match cPsi2 with
  | I.Null -> cPsi1
  | I.DDec (cPsi2', dec) ->
      let cPsi1' = appDCtx cPsi1 cPsi2' in
        I.Dec (cPsi1', dec)

let abstrSchema (I.Schema elements) =
  let rec abstrElems elements = match elements with
    | [] -> []
    | Int.LF.SchElem (cPsi, trec) ::els ->
        let cPsi0 = Context.projectCtxIntoDctx cPsi in
        let (cQ, cPsi0') = collectDctx (Syntax.Loc.ghost) 0 I.Empty (Context.dctxToHat I.Null) cPsi0 in
        let (_, l) as phat = Context.dctxToHat cPsi0 in
        let (cQ, trec') = collectTypRec 0 cQ phat (trec, LF.id) in
        let cQ' = abstractCtx cQ in

        let cPsi' = abstractDctx cQ' cPsi0'  l in
        let trec' = abstractTypRec cQ' l (trec', LF.id) in
        let cPsi1 = ctxToCtx cQ' in
        let cPsi1' = appDCtx cPsi1 cPsi' in

        let els'  = abstrElems els in
          Int.LF.SchElem (cPsi1', trec') :: els'
  in
    I.Schema (abstrElems elements)

let printFreeMVars phat tM =
  let (cQ, _ ) = collectTerm 0 I.Empty  phat (tM, LF.id) in
    printCollection cQ

let rec fvarInCollection cQ = begin match cQ with
  | I.Empty -> false
  | I.Dec(_cQ, FV (_, _, None)) ->  true
  | I.Dec(cQ, FV (_, _, Some (tA))) ->
       let (cQ',_ ) = collectTyp 0 I.Empty (None, 0) (tA, LF.id) in
         begin match cQ' with
             Int.LF.Empty -> (print_string "empty" ; fvarInCollection cQ)
           | _ -> true
         end


  | I.Dec(cQ, _ ) -> fvarInCollection cQ
end

let closedTyp (cPsi, tA) =
  let (cQ1, _ ) = collectDctx (Syntax.Loc.ghost) 0 I.Empty (None, 0) cPsi in
  let (cQ2, _ ) = collectTyp 0 cQ1 (Context.dctxToHat cPsi) (tA, LF.id) in
    not (fvarInCollection cQ2)


(* We abstract over the MVars in cPsi, tM, and tA *)
let abstrCovGoal cPsi tM tA ms =
  let phat = Context.dctxToHat cPsi in
  let (cQ0 , ms') = collectMSub 0 I.Empty ms in
  let (cQ1, cPsi') = collectDctx (Syntax.Loc.ghost) 0 cQ0 phat cPsi in
  let (cQ2, tA') = collectTyp 0 cQ1 phat (tA, LF.id) in
  let (cQ3, tM')   = collectTerm 0 cQ2 phat (tM, LF.id) in


  let cQ'     = abstractMVarCtx cQ3 0 in

  let ms0     = abstrMSub cQ' ms' in
  let cPsi0   = abstractMVarDctx cQ' (0,0) cPsi' in
  let tM0     = abstractMVarTerm cQ' (0,0) (tM', LF.id) in
  let tA0     = abstractMVarTyp  cQ' (0,0) (tA', LF.id) in

  let cD0     = ctxToMCtx cQ' in

    (cD0, cPsi0, tM0, tA0, ms0)

let abstrCovPatt cG pat tau ms =
  let (cQ1 , ms') = collectMSub 0 I.Empty ms in
  let (cQ2, cG') = collectGctx cQ1 cG in
  let (cQ3, pat') = collectPatObj cQ2 pat in
  let (cQ, tau') = collectCompTyp 0 cQ3 tau in
  let cQ'     = abstractMVarCtx cQ 0 in
  let ms0     = abstrMSub cQ' ms' in
  let cG'     = abstractMVarGctx cQ' (0,0) cG in
  let pat'    = abstractMVarPatObj cQ' cG' (0,0) pat' in
  let tau'    = abstractMVarCompTyp cQ' (0,0) tau' in
  let cD'     = ctxToMCtx cQ' in
    (cD', cG', pat', tau', ms0)

(* Shorter names for export outside of this module. *)
let kind = abstrKind
let typ = abstrTyp
let covgoal = abstrCovGoal
let covpatt = abstrCovPatt
let schema = abstrSchema
let msub = abstractMSub
let compkind = abstrCompKind
let comptyp = abstrCompTyp
let exp = abstrExp
let pattern = abstrPattern
let patobj = abstrPatObj
let subpattern = abstrSubPattern
let mobj = abstrMObjPatt
