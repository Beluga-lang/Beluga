(**
   @author Renaud Germain
   @author Brigitte Pientka
*)
open Store
open Store.Cid
open Substitution
open Syntax
open Id

module I    = Int.LF
module Comp = Int.Comp

module P = Pretty.Int.DefaultPrinter


let (dprint, _) = Debug.makeFunctions (Debug.toFlags [3])


type kind =
  | MMV of (Id.name * I.iterm option ref)
  | FV of Id.name

type error =
  | LeftoverVars
  | LeftoverConstraints
  | CyclicDependency of kind
  | UnknownIdentifier
  | UnknownMTyp of name

let pat_flag = ref false

exception Error of Syntax.Loc.t * error

let string_of_varvariant = function
  | FV _  -> "free variables"
  | MMV _ -> "meta^2-variables and free variables"

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | UnknownMTyp psi ->
            Format.fprintf ppf "Unable to infer type for variable %s"
              (Id.render_name psi)
        | LeftoverVars ->
          Format.fprintf ppf "Leftover meta-variables in computation-level expression; provide a type annotation"
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
type flag = LF | Comp
type sort = LFTyp of I.typ | MetaTyp of I.ctyp * I.depend
type marker = Pure of sort | Impure

type free_var =
  | FDecl of kind * marker
  (* Bound variables. I think we could allow these to be more general than just contexts  *)
  (* Would these in general be a kind of FDecl and have a marker? *)
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

let rec raiseType' cPsi tA = match cPsi with
  | I.Empty -> (None, tA)
  | I.Dec (cPsi', decl) ->
      raiseType' cPsi' (I.PiTyp ((decl, I.Maybe), tA))

let rec raiseKind cPsi tK = match cPsi with
  | I.Empty -> tK
  | I.Dec (cPsi', decl) ->
      raiseKind cPsi' (I.PiKind ((decl, I.Maybe), tK))

let depToString dep = match dep with
  | I.No -> "^e"
  | I.Maybe -> "^i"
  | _ -> "*"

let rec collectionToString cQ = match cQ with
  | I.Empty -> ""

  | I.Dec(cQ, FDecl (MMV (_n,_r), Pure (MetaTyp (mtyp, dep)))) ->
       collectionToString cQ ^ " MMV"
     ^ P.mtypToString I.Empty mtyp ^ depToString dep
     ^ "\n"
  | I.Dec(cQ, FDecl (MMV (_n,_r), Impure)) ->
       collectionToString cQ ^ " MMV Impure"
     ^ "\n"

  | I.Dec (cQ, FDecl (FV u, Pure (MetaTyp (mtyp, _ )))) ->
      let cD = I.Empty in
       collectionToString cQ
     ^ " " ^ Id.render_name u ^ " : "
     ^ P.mtypToString cD mtyp ^"\n"

  | I.Dec(cQ, FDecl (FV _n, Impure)) ->  collectionToString cQ ^ ",  FV _ .\n"

  | I.Dec(cQ, FDecl (FV n, Pure (LFTyp tA))) ->
      let cD = I.Empty in
        collectionToString cQ ^ ",  FV " ^ (string_of_name n) ^ " : "
      ^ "(" ^ P.typToString cD I.Null (tA, LF.id) ^ ")"
      ^ "\n"
  | I.Dec(_cQ, _ ) -> " ?? "

let printCollection s =
  (print_string "Print Collection of contextual variables:\n";
   print_string (collectionToString s) )

(* checkOccurrence p cQ = result

   If the first occurrence of Y in cQ s.t. p(Y) = Some Pure, then Yes
   If the first occurrence of Y:Impure in cQ s.t. p(Y) = Some Impure then Cycle
   otherwise No

*)
type occurrs = Yes | No


(* eqMMVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let eqVar mmV1 mmV2 = match (mmV1, mmV2) with
  | MMV (_, r1) , MMV (_,r2) -> (r1 == r2)
  | (FV n1 ,  FV n2) -> (n1 = n2)
  | _ -> false

let rec checkOccurrence loc p = function
  | I.Empty        -> No
  | I.Dec (cQ', FDecl (y,m))  ->
    if eqVar p y then
      (match m with
	| Pure _ -> Yes
	| Impure -> raise (Error (loc, CyclicDependency p)))
    else checkOccurrence loc p cQ'
  | I.Dec (cQ', CtxV _) -> No

(* length cPsi = |cPsi| *)
let length cPsi =
  let (_, n) = Context.dctxToHat cPsi in
    n

let rec length' = function
  | I.Empty -> 0
  | I.Dec (c, _) -> length' c + 1

let rec lengthCollection cQ = match cQ with
  | I.Empty        -> 0
  | I.Dec (cQ', FDecl(_,Impure)) -> lengthCollection cQ'
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




let rec constraints_solved cnstr = match cnstr with
  | [] -> true
  | ({contents = I.Queued} :: cnstrs) ->
      constraints_solved cnstrs
  | ({contents = I.Eqn (_cD, cPsi, tM, tN)} :: cnstrs) ->
      if Whnf.convITerm tM tN then
        constraints_solved cnstrs
      else
        (dprint (fun () -> "Encountered unsolved constraint:\n" ^
           P.itermToString I.Empty cPsi tM ^ " == " ^
           P.itermToString I.Empty cPsi tN ^ "\n\n") ;
         false )



(* Check that a synthesized computation-level type is free of constraints *)
let rec cnstr_ctyp tau =  match tau  with
  | Comp.TypBox (_, I.ClTyp (I.MTyp tA, cPsi)) -> cnstr_typ (tA, LF.id) && cnstr_dctx cPsi
  | Comp.TypBox (_, I.ClTyp (I.STyp (_,cPhi), cPsi)) -> cnstr_dctx cPhi && cnstr_dctx cPsi

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
  | I.MMVar(((_, _r, _, _ , cnstr, _), _), s)
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

  | (I.Dec (cQ', FDecl (_, Impure)), _ ) ->
      index_of cQ' n

  | (I.Dec (cQ', FDecl (k1, Pure t1)), k2) ->
      if eqVar k1 k2 then 1 else ((index_of cQ' n) + 1)

  | (I.Dec (cQ', _), _) ->
      (index_of cQ' n) + 1

(* If   cQ = cQ1 (MV u) cQ2
   and  u :: A[Psi]
   then (ctxToDctx cQ) = (ctxToDctx cQ1) Pi Psi . A (ctxToDctx cQ2)

   If   cQ = cQ1 (FV (F, A)) cQ2
   then (ctxToDctx cQ) = (ctxToDctx cQ1) A (ctxToDctx cQ2)
*)

let rec ctxToCtx cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', FDecl (MMV (_,_), Pure (MetaTyp(I.ClTyp (I.MTyp tA,cPsi), _dep)))) ->
      begin match raiseType cPsi tA with
        | (None, tA') ->
            let x = Id.mk_name (Id.MVarName (Typ.gen_mvar_name tA')) in
            I.Dec (ctxToCtx cQ', I.TypDecl (x, tA'))
        | (Some _, _ ) -> raise (Error.Violation "ctxToDctx generates LF-dctx with context variable.")
      end
  | I.Dec (cQ', FDecl (FV x, Pure (LFTyp tA))) ->
      (* let x = Id.mk_name (Id.BVarName (Typ.gen_var_name tA)) in  *)
      I.Dec (ctxToCtx cQ', I.TypDecl (x, tA))

  | I.Dec (cQ', FDecl (_, Impure)) ->
    ctxToCtx cQ'

let getName = function
  | MMV (n,_) | FV n -> n

(* dep' indicates whether FVars are treated implicit or explicit *)
let rec ctxToMCtx dep' cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', FDecl (FV n, Pure (MetaTyp (ityp, _dep)))) ->
      I.Dec (ctxToMCtx dep' cQ', I.Decl (n, ityp, dep'))

  | I.Dec (cQ', FDecl (s, Pure (MetaTyp (ityp, _dep)))) ->
      I.Dec (ctxToMCtx dep' cQ', I.Decl (getName s, ityp, dep'))

  | I.Dec (cQ', CtxV (x,w, dep)) ->
      I.Dec (ctxToMCtx dep' cQ', I.Decl (x, I.CTyp (Some w), dep))

  (* this case should not happen -bp *)
   | I.Dec (cQ', FDecl (FV _, Pure (LFTyp tA)))->
      raise (Error.Violation "Free variables in computation-level reconstruction.")

   | I.Dec (cQ', FDecl (_, Impure)) ->
       ctxToMCtx dep' cQ'


let rec ctxToMCtx_pattern cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', FDecl (FV n, Pure (MetaTyp (ityp, _dep)))) ->
      I.Dec (ctxToMCtx_pattern cQ', I.Decl (n, ityp, I.No))

  | I.Dec (cQ', FDecl (s, Pure (MetaTyp (ityp, dep)))) ->
      I.Dec (ctxToMCtx_pattern cQ', I.Decl (getName s, ityp, dep))

  | I.Dec (cQ', CtxV (x,w, dep)) ->
      I.Dec (ctxToMCtx_pattern cQ', I.Decl (x, I.CTyp (Some w), dep))

| I.Dec (cQ', FDecl (_, Impure)) ->
       ctxToMCtx_pattern cQ'


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

and collectBothTyp loc p cQ = function
  | MetaTyp (tp, dep) ->
    let (cQ', tp') = collectMetaTyp loc p cQ tp in
    (cQ', MetaTyp (tp', dep))
  | LFTyp tA -> (* tA must be closed *)
       (* Since we only use abstraction on pure LF objects,
          there are no context variables; different abstraction
          is necessary for handling computation-level expressions,
          and LF objects which occur in computations. *)
    let (cQ', tA') = collectTyp p cQ (None, 0) (tA, LF.id) in
    (cQ', LFTyp tA')

and addVar loc p cQ v tp = match checkOccurrence loc v cQ with
   | Yes ->  (cQ, tp)
   | No  ->
     let cQ' = I.Dec(cQ, FDecl(v, Impure)) in
     let (cQ2, tp') = collectBothTyp loc p cQ' tp in
     (I.Dec (cQ2, FDecl (v, Pure tp')), tp')

and getType loc p name f =
  begin try match f with
  | LF -> let Int.LF.Type tA = FVar.get name in (LFTyp tA)
  | Comp ->
    let (cD_d, I.Decl (_, mtyp,dep))  = FCVar.get name in
    let mtyp' = Whnf.cnormMTyp (mtyp, Int.LF.MShift (p - Context.length cD_d)) in
      if !pat_flag then MetaTyp (mtyp', I.No) else
	MetaTyp (mtyp', dep)
   with Not_found -> raise (Error (loc, UnknownMTyp name))
  end

and collectFVar fl loc p cQ name =
  let (cQ2, _tp) = addVar loc p cQ (FV name) (getType loc p name fl) in
  cQ2

and collectLFVar l = collectFVar LF l

and collectCompFVar l = collectFVar Comp l

and collectFVarSub p cQ phat (name, s') =
  let cQ = collectCompFVar Syntax.Loc.ghost p cQ name in
  let (cQ,s') = collectSub p cQ phat s' in
  (cQ, (name,s'))

and collectMMVar loc p cQ (n,q,cD,tp,c,dep) =
  match cD with
    | I.Empty -> begin
      if constraints_solved !c then
	match !q with
	  | None -> 
	       let (cQ', MetaTyp (tp',dep')) = addVar loc p cQ (MMV (n,q)) (MetaTyp (tp, dep)) in
	       (cQ', (n, q, cD, tp', c, dep'))
	  | Some _ -> raise (Error.Violation "Expected whnf")
      else
	raise (Error (loc, LeftoverConstraints))
    end
    | I.Dec(_,_) -> let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD) in
                    raise (Error (loc, LeftoverVars))

and collectMVarMSub loc p cQ (i,ms') =
  let (cQ0, ms') = collectMSub p cQ ms' in
  let (cQ1, i') = collectMMVar loc p cQ0 i in
  (cQ1, (i', ms'))

and collectMVarInst loc p cQ phat (ims, s') =
  let (cQ0, ims') = collectMVarMSub loc p cQ ims in
  let (cQ1, s') = collectSub p cQ0 phat s' in
  (cQ1, (ims',s'))

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

  | I.Dot (I.Undef, s) ->
      let (cQ2, s') =  collectSub p cQ phat s in
        (cQ2, I.Dot(I.Undef, s'))

  | I.Dot (I.Obj tM, s) ->
      let (cQ1, tM') = collectTerm p cQ phat (tM, LF.id) in
      let (cQ2,s') =  collectSub p cQ1 phat s in
        (cQ2, I.Dot (I.Obj tM', s'))

  | I.FSVar (n, ns) ->
    let (cQ', ns) = collectFVarSub p cQ phat ns in
    (cQ', I.FSVar (n, ns))

  | I.SVar (offset, n, s) ->
    let (cQ1,s') = collectSub p cQ phat s in
       (cQ1, I.SVar(offset, n, s'))

  | I.MSVar (k, i) ->
    let (cQ', i') = collectMVarInst Syntax.Loc.ghost p cQ phat i
    in  (cQ', I.MSVar (k, i'))

and collectClObj p cQ1 phat' = function
  | I.MObj tM ->
      let (cQ2, tM') = collectTerm p cQ1 phat' (tM, LF.id) in
        (cQ2 , I.MObj tM')
  | I.PObj h ->
      let (cQ2, h') = collectHead p cQ1 phat' (Syntax.Loc.ghost) (h, LF.id) in
        (cQ2, I.PObj h')
  | I.SObj s ->
    let (cQ2, s')    = collectSub p cQ1 phat' s in
      (cQ2, I.SObj s')

and collectMObj p cQ1 = function
  | I.ClObj(phat, tM) ->
      let (cQ1, phat') = collectHat p cQ1 phat in
      let (cQ2, tM') = collectClObj p cQ1 phat' tM in
        (cQ2 , I.ClObj (phat', tM'))
  | I.CObj (cPsi) ->
      let phat = Context.dctxToHat cPsi in
      let (cQ2, cPsi') = collectDctx (Syntax.Loc.ghost) p cQ1 phat cPsi in
        (cQ2, I.CObj (cPsi'))
  | I.MUndef -> raise (Error.Violation "Unexpected undef")
  | I.MV k -> (cQ1, I.MV k)

(* collectMSub p cQ theta = cQ' *)
and collectMSub p cQ theta =  match theta with
  | I.MShift _n ->  (cQ , theta)
  | I.MDot(mobj, t) ->
    let (cQ1, t') = collectMSub p cQ t in
    let (cQ2, mobj') = collectMObj p cQ1 mobj in
     (cQ2, I.MDot (mobj', t'))

and collectHead (k:int) cQ phat loc (head, _s) =
    match head with

  | (I.BVar _x)  -> (cQ, head)

  | (I.Const _c) -> (cQ, head)

  | (I.FVar name) ->
    (collectLFVar loc k cQ name, I.FVar name)

  | (I.FMVar ns) ->
    let (cQ0, ns) = collectFVarSub k cQ phat ns in
    (cQ0, I.FMVar ns)

  | (I.MVar (I.Inst i, s')) ->
     let (cQ', ((i', ms'),s')) = collectMVarInst loc k cQ phat ((i, Whnf.m_id), s') in
	 (cQ', I.MVar (I.Inst i', s'))

  | (I.MMVar i) ->
    let (cQ', i') = collectMVarInst loc k cQ phat i
    in  (cQ', I.MMVar i')

  | (I.MPVar i) ->
    let (cQ', i') = collectMVarInst loc k cQ phat i
    in  (cQ', I.MPVar i')

  | (I.MVar (I.Offset j, s')) ->
      let (cQ', sigma) = collectSub k cQ phat s' in
        (cQ', I.MVar (I.Offset j, sigma))

  | (I.FPVar ns) ->
    let (cQ', ns) = collectFVarSub k cQ phat ns in
    (cQ', I.FPVar ns)

  | (I.PVar (k', s')) ->
      let (cQ', sigma) =  collectSub k cQ phat s' in
        (cQ', I.PVar (k', sigma))

  | (I.Proj (head, j)) ->
      let (cQ', h') = collectHead k cQ phat loc (head, _s)  in
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


and collectCVar loc p cQ = function
  | I.CtxOffset k -> (cQ, I.CtxOffset k)
  | I.CInst ims ->
    let (cQ', ims') = collectMVarMSub loc p cQ ims in
    (cQ', I.CInst ims')
  | (I.CtxName psi) ->
    (collectCompFVar loc p cQ psi, I.CtxName psi)

and collectHat p cQ (cv,offset) = match cv with
  | None -> (cQ, (None,offset))
  | Some cv ->
    let (cQ', cv') = collectCVar Syntax.Loc.ghost p cQ cv
    in (cQ', (Some cv', offset))

and collectDctx loc (p:int) cQ (cvar, offset) cPsi =
  collectDctx' loc p cQ (cvar, offset) (Whnf.normDCtx cPsi)

and collectDctx' loc p cQ ((cvar, offset)) cPsi = match cPsi with
  | I.Null ->  (cQ, I.Null)
  | I.CtxVar cv ->
    let (cQ', cv') = collectCVar loc p cQ cv
    in (cQ', I.CtxVar cv')

  | I.DDec(cPsi, I.TypDecl(x, tA)) ->
      let (cQ', cPsi') =  collectDctx' loc p cQ (cvar, offset - 1) cPsi in
      let (cQ'', tA')  =  collectTyp p cQ' (cvar, offset - 1) (tA, LF.id) in
        (cQ'', I.DDec (cPsi', I.TypDecl(x, tA')))


and collectMTyp p cQ = collectMetaTyp Syntax.Loc.ghost p cQ

and collectClTyp loc p cQ' phat = function
  | I.MTyp tA ->
    let (cQ'', tA')    =  collectTyp p cQ' phat  (tA, LF.id) in
    (cQ'', I.MTyp tA')
  | I.PTyp tA ->
    let (cQ'', tA')    =  collectTyp p cQ' phat  (tA, LF.id) in
    (cQ'', I.PTyp tA')
  | I.STyp (cl, cPhi) ->
     let phi_hat = Context.dctxToHat cPhi in
     let (cQ1, cPhi') = collectDctx loc p cQ' phi_hat cPhi in
     (cQ1, I.STyp (cl, cPhi'))

and collectMetaTyp loc p cQ = function
  | I.CTyp sW -> (cQ, I.CTyp sW)
  | I.ClTyp (tp, cPsi) ->
    let phat = Context.dctxToHat cPsi in
    let (cQ', cPsi') = collectDctx loc p cQ phat cPsi in
    let (cQ'', tp') = collectClTyp loc p cQ' phat tp in
    (cQ'', I.ClTyp (tp', cPsi'))


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
      let typRec = abstractTypRec cQ (offset+1) (typRec, LF.dot1 s) in
        I.SigmaElem(x, tA, typRec)



and abstractTerm cQ offset sM = abstractTermW cQ offset (Whnf.whnf sM)

and abstractTermW cQ offset sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      I.Lam (loc, x, abstractTerm cQ (offset + 1) (tM, LF.dot1 s))

  | (I.Root (loc, (I.MVar (I.Inst ((n, r, _, (I.ClTyp (_,cPsi)), _cnstr, _)), s)), _tS (* Nil *)), _s)
  | (I.Root (loc, I.MMVar (((n,r,_,(I.ClTyp (_,cPsi)),_cnstr,_), _),s), _tS), _s) ->
    (* Since sM is in whnf, _u is MVar (Inst (ref None, tP, _, _)) *)
      let x = index_of cQ (MMV (n,r)) + offset in
        I.Root (loc, I.BVar x, subToSpine cQ offset (s,cPsi) I.Nil)

  | (I.Root (loc, tH, tS), s (* LF.id *)) ->
      I.Root (loc, abstractHead cQ offset tH, abstractSpine cQ offset (tS, s))


and abstractHead cQ (offset:int) tH = match tH with
  | I.BVar x ->
      I.BVar x

  | I.Const c ->
      I.Const c

  | I.FVar n ->
      I.BVar ((index_of cQ (FV n)) + offset)

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
  | I.Dec (cQ, FDecl (_, Impure)) ->
      abstractCtx cQ

  | I.Dec (cQ, FDecl (MMV (n,r), Pure (MetaTyp (I.ClTyp (I.MTyp tA,cPsi),dep)))) ->
      let cQ'   = abstractCtx cQ  in
      let l     = length cPsi in
      let cPsi' = abstractDctx cQ cPsi l in
      let tA'   = abstractTyp cQ l (tA, LF.id) in
      let tp' = I.ClTyp (I.MTyp tA',cPsi') in
        I.Dec (cQ', FDecl (MMV (n,r), Pure (MetaTyp (tp',dep))))

  | I.Dec (cQ, FDecl (FV f, Pure (LFTyp tA))) ->
      let cQ' = abstractCtx cQ in
      let tA' = abstractTyp cQ 0 (tA, LF.id) in
        I.Dec (cQ', FDecl (FV f, Pure (LFTyp tA')))


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

and abstractMMVar cQ d = function
  | (n,r,I.Empty,_tp,_cnstr,_dep) -> index_of cQ (MMV (n,r)) + d
  | (n,r,_cD,_tp,_cnstr,_dep) -> raise (Error (Syntax.Loc.ghost, LeftoverVars))

and abstractMMVarMSub cQ (l,d) (i,_ms) =
  abstractMMVar cQ d i (* Shouldn't this apply ms? *)

and abstractMMVarInst cQ loff (ims,s) =
  (abstractMMVarMSub cQ loff ims, abstractMVarSub cQ loff s)

and abstractFVarSub cQ ((l,d) as offset) (name,s) =
  (index_of cQ (FV name) + d, abstractMVarSub cQ offset s)

and abstractOffset cQ (l,d) x =
  let k = lengthCollection cQ in
  if x > d then x + k else x

and abstractOffsetSub cQ loff (x,s) =
  (abstractOffset cQ loff x, abstractMVarSub cQ loff s)

and abstractMVarHead cQ loff tH = match tH with
  | I.BVar x -> I.BVar x

  | I.FPVar ns -> I.PVar (abstractFVarSub cQ loff ns)

  | I.FMVar (u, s) ->
    let (x,s') = abstractFVarSub cQ loff (u, s) in
    I.MVar (I.Offset x, s')

  | I.MMVar mi ->
    let (off,s') = abstractMMVarInst cQ loff mi in
    I.MVar (I.Offset off, s')

  | I.MVar (I.Inst i, s) ->
    let (off,s') = abstractMMVarInst cQ loff ((i,Whnf.m_id),s) in
    I.MVar (I.Offset off, s')

  | I.MPVar mi ->  I.PVar (abstractMMVarInst cQ loff mi)

  | I.MVar (I.Offset x , s) ->
    let (x',s') = abstractOffsetSub cQ loff (x, s) in
    I.MVar (I.Offset x', s')

  | I.PVar os -> I.PVar (abstractOffsetSub cQ loff os)

  | I.Const c ->
      I.Const c

  | I.AnnH (_tH, _tA) ->
      raise Error.NotImplemented

  | I.Proj (head, k) ->
      let head = abstractMVarHead cQ loff head in   (* ??? -jd *)
        I.Proj (head, k)


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

and abstractMVarSub' cQ loff s = match s with
  | I.EmptySub -> I.EmptySub
  | I.Undefs -> I.Undefs
  | I.Shift _ -> s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractMVarHead cQ loff tH), abstractMVarSub' cQ loff s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractMVarTerm cQ loff (tM, LF.id)), abstractMVarSub' cQ loff s)

  | I.SVar (s, n, sigma) ->
    let (s',sigma') = abstractOffsetSub cQ loff (s,sigma) in
    I.SVar (s', n, sigma')

  | I.Dot (I.Undef, s) ->
      I.Dot (I.Undef, abstractMVarSub' cQ loff s)

  | I.FSVar (n, fs ) ->
      let (x,s') = abstractFVarSub cQ loff fs in
      I.SVar (x, n, s')

  | I.MSVar (k, i) ->
    let (sv,s) = abstractMMVarInst cQ loff i in
    I.SVar (sv, k, s)

and abstractCtxVar cQ ((l,d) as loff) = function
  | I.CtxOffset psi ->
      if psi <= d then
        I.CtxOffset psi
      else
        I.CtxOffset (psi + l)
  | I.CtxName psi -> I.CtxOffset (index_of cQ (FV psi) + d)
  | I.CInst ims -> I.CtxOffset (abstractMMVarMSub cQ loff ims)

and abstractMVarHat cQ loff (cv,k) = match cv with
  | None -> (None, k)
  | Some cv -> (Some (abstractCtxVar cQ loff cv), k)

and abstractMVarDctx cQ loff cPsi = match cPsi with
  | I.Null -> I.Null
  | I.CtxVar cv -> I.CtxVar (abstractCtxVar cQ loff cv)
  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractMVarDctx cQ loff cPsi in
      let tA'   = abstractMVarTyp cQ loff (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

and abstractMVarClTyp cQ loff = function
  | I.MTyp tA -> I.MTyp (abstractMVarTyp cQ loff (tA, LF.id))
  | I.PTyp tA -> I.PTyp (abstractMVarTyp cQ loff (tA, LF.id))
  | I.STyp (cl, cPhi) -> I.STyp (cl, abstractMVarDctx cQ loff cPhi)

and abstractMVarMTyp cQ mtyp loff = match mtyp with
  | I.ClTyp (tp, cPsi) -> I.ClTyp (abstractMVarClTyp cQ loff tp, abstractMVarDctx cQ loff cPsi)
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
  | I.Dec (cQ, FDecl (v, Pure (MetaTyp (ityp,dep)))) ->
      let cQ'   = abstractMVarCtx  cQ (l-1) in
        I.Dec (cQ', FDecl (v, Pure (MetaTyp (abstractMVarMTyp cQ ityp (l,0),dep))))
  | I.Dec (cQ, CtxV cdecl) ->
      let cQ'   = abstractMVarCtx  cQ (l-1) in
      I.Dec(cQ', CtxV cdecl)

  | I.Dec (cQ, FDecl (_, Impure)) ->
      abstractMVarCtx  cQ l

  | I.Dec (_cQ, FDecl (FV _, _)) ->
        (* This case is hit in e.g.  ... f[g, x:block y:tp. exp unk], where unk is an unknown identifier;
         * is it ever hit on correct code?  -jd 2009-02-12
         * No. This case should not occur in correct code - bp
         *)
      raise (Error (Syntax.Loc.ghost, UnknownIdentifier))


(* Cases for: FMV *)

let abstrClObj cQ off = function
  | I.MObj tM -> I.MObj (abstractMVarTerm cQ off (tM, LF.id))
  | I.PObj h -> I.PObj (abstractMVarHead cQ off h)
  | I.SObj s -> I.SObj (abstractMVarSub cQ off s)

let abstrMObj cQ off = function
  | I.ClObj(phat, tM) ->
    I.ClObj(abstractMVarHat cQ off phat, (abstrClObj cQ off tM))
  | I.CObj(cPsi) -> I.CObj(abstractMVarDctx cQ off cPsi)
  | I.MV k -> I.MV k

let rec abstrMSub cQ t =
  let l = lengthCollection cQ in
  let rec abstrMSub' t =
    match t with
      | I.MShift n -> I.MShift (n+l)
      | I.MDot(mobj, t) -> I.MDot(abstrMObj cQ (0,0) mobj, abstrMSub' t)
  in
    abstrMSub' t

and abstractMSub t =
  let rec ctxToMCtx' cQ = match cQ with
  | I.Empty -> I.Empty
  | I.Dec (cQ', FDecl (FV n, Pure (MetaTyp (ityp, dep)))) ->
      I.Dec (ctxToMCtx' cQ', I.Decl (n, ityp, dep))
  | I.Dec (cQ', FDecl (s, Pure (MetaTyp (ityp, dep)))) ->
      I.Dec (ctxToMCtx' cQ', I.Decl (getName s, ityp, dep))
  | I.Dec (cQ', CtxV (x,w, dep)) ->
      I.Dec (ctxToMCtx' cQ', I.Decl (x, I.CTyp (Some w), dep))
   | I.Dec (cQ', FDecl (_, Impure)) ->
       ctxToMCtx' cQ'
  in
  let (cQ, t') = collectMSub 0 I.Empty t in
  let cQ' = abstractMVarCtx cQ 0 in
  let t'' = abstrMSub cQ' t' in
  let _ = dprint (fun () -> "[abstractMSub] Collection cQ'  = " ^
		    collectionToString cQ') in
  let cD' = ctxToMCtx'  cQ' in
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
          let cPsi       = ctxToCtx cQ' in
            (raiseKind cPsi tK'', length' cPsi)
    end

and abstrTyp tA =
  let empty_phat = (None, 0) in

  let (cQ, tA')       = collectTyp 0 I.Empty empty_phat (tA, LF.id) in
   begin match cQ with
        Int.LF.Empty -> (tA', 0)
      | Int.LF.Dec(_,FDecl (s,_))        ->
          let cQ'        = abstractCtx cQ in
          let tA2        = abstractTyp cQ' 0 (tA', LF.id) in
          let cPsi       = ctxToCtx cQ' in
            begin match raiseType' cPsi tA2 with
              | (None, tA3) -> (tA3, length' cPsi)
              | _            -> raise (Error (Syntax.Loc.ghost, LeftoverVars))
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

let rec collect_meta_obj p cQ (loc,cM) =
  let (cQ', cM') = collectMObj p cQ cM in (cQ', (loc, cM'))

and collect_meta_spine p cQ cS = match cS with
  | Comp.MetaNil -> (cQ, Comp.MetaNil)
  | Comp.MetaApp (cM, cS) ->
      let (cQ', cM') = collect_meta_obj p cQ cM in
      let (cQ'', cS') = collect_meta_spine p cQ' cS in
        (cQ'', Comp.MetaApp (cM', cS'))

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
  | Comp.TypInd tau ->
      let (cQ', tau') = collectCompTyp p cQ tau in
	(cQ', Comp.TypInd tau')


let rec collectGctx cQ cG = match cG with
  | I.Empty -> (cQ, I.Empty)
  | I.Dec (cG, Comp.CTypDecl (x, tau, flag)) ->
      let (cQ1, cG') = collectGctx cQ cG in
      let (cQ2, tau') = collectCompTyp 0 cQ1 tau in
        (cQ2, I.Dec (cG', Comp.CTypDecl (x, tau', flag)))

let rec collectExp cQ e = match e with
  | Comp.Syn (loc, i) ->
      let (cQ', i') = collectExp' cQ i in
        (cQ', Comp.Syn(loc, i'))

  | Comp.Rec (loc, f, e) ->
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.Rec (loc, f, e') )

  | Comp.Fn (loc, x, e) ->
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.Fn (loc, x, e'))
          
  | Comp.Fun (loc, fbr) -> 
    let (cQ', fbr') = collectFBranches cQ fbr in
        (cQ', Comp.Fun (loc, fbr'))

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

  | Comp.Hole (loc, name, f) -> (cQ, Comp.Hole (loc, name, f))

and collectExp' cQ i = match i with
  | Comp.Var (_, _x) -> (cQ , i)
  | Comp.DataConst (_, _c) ->  (cQ , i)
  | Comp.Obs (loc, e, t, obs) ->
    let (cQ', t') = collectMSub 0 cQ t in
    let (cQ1, e') = collectExp cQ' e in
    (cQ1 , Comp.Obs (loc, e', t', obs))
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
  | Comp.PatObs (loc, obs, ms, pat_spine) ->
    let (cQ1, ms') = collectMSub 0 cQ ms in
    let (cQ2, pat_spine') = collectPatSpine cQ1 pat_spine in
        (cQ2, Comp.PatObs (loc, obs, ms', pat_spine'))

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

and collectBranches cQ branches = match branches with
  | [] -> (cQ, [])
  | b::branches ->
      let (cQ', b') = collectBranch cQ b in
      let (cQ2, branches') =  collectBranches cQ' branches in
      (cQ2, b'::branches')

and collectFBranches cQ fbr = match fbr with
  | Comp.NilFBranch _ -> (cQ, fbr)
  | Comp.ConsFBranch (loc, (cD, cG, ps, e), fbr') ->
    (* cG, cD, and pat cannot contain any free meta-variables *)
    let (cQ', e') = collectExp cQ e in
    let (cQ1, fbr'') = collectFBranches cQ' fbr' in
      (cQ1, Comp.ConsFBranch (loc, (cD, cG, ps, e'), fbr''))
        

let rec abstractMVarCompKind cQ (l,offset) cK = match cK with
  | Comp.Ctype _loc -> cK
  | Comp.PiKind (loc, cdecl, cK) ->
      let cK'  = abstractMVarCompKind cQ (l,offset+1) cK in
      let cdecl' = abstractMVarCdecl cQ (l,offset) cdecl in
        Comp.PiKind (loc, cdecl', cK')

let rec abstractMVarMetaObj cQ offset (loc,cM) =
  (loc, abstrMObj cQ offset cM)

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
  | Comp.TypBox (loc, mtyp) ->
        Comp.TypBox (loc, abstractMVarMTyp cQ mtyp offset)
  | Comp.TypArr (tau1, tau2) ->
      Comp.TypArr (abstractMVarCompTyp cQ offset tau1,
                   abstractMVarCompTyp cQ offset tau2)

  | Comp.TypCross (tau1, tau2) ->
      Comp.TypCross (abstractMVarCompTyp cQ offset tau1,
                     abstractMVarCompTyp cQ offset tau2)
  | Comp.TypPiBox (cdecl, tau) ->
    Comp.TypPiBox ((abstractMVarCdecl cQ offset cdecl), abstractMVarCompTyp cQ (l,d+1) tau)

  | Comp.TypBool -> Comp.TypBool
  | Comp.TypInd tau ->
      Comp.TypInd (abstractMVarCompTyp cQ offset tau)

let rec abstractMVarGctx cQ offset cG = match cG with
  | I.Empty -> I.Empty
  | I.Dec (cG, Comp.CTypDecl (x, tau, flag)) ->
      let cG' = abstractMVarGctx cQ offset cG in
      let tau' = abstractMVarCompTyp cQ offset tau in
        I.Dec (cG', Comp.CTypDecl (x, tau', flag))

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
  | Comp.PatObs (loc, obs, ms, pat_spine) ->
    let ms' = abstrMSub cQ ms in
    let pat_spine' = abstractMVarPatSpine cQ cG offset pat_spine in
    Comp.PatObs (loc, obs, ms', pat_spine')

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
    | Comp.PiKind (_, I.Decl(psi, I.CTyp (Some w), dep), cK) ->
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
  let cD' = ctxToMCtx (I.Maybe) cQ' in
  let cK2 = raiseCompKind cD' cK' in
    (cK2, Context.length cD')

let abstrCompTyp tau =
  let rec roll tau cQ = match tau with
    | Comp.TypPiBox (I.Decl(psi, I.CTyp (Some w), dep), tau) ->
        roll tau (I.Dec(cQ, CtxV (psi,w,dep)))
    | tau -> (cQ, tau)
  in
  let tau0        = Whnf.cnormCTyp (tau, Whnf.m_id) in
  let (cQ, tau')  = roll tau0 I.Empty in
  let l'           = lengthCollection cQ in
  let p = prefixCompTyp tau' in (* p = number of explicitely declared mvars *)
  let (cQ, tau1)  = collectCompTyp (l'+p) cQ tau' in
  let k           = lengthCollection cQ in
  let l           = (k - l') in
  let cQ'  = abstractMVarCtx cQ (l-1-p) in
  (* let cQ'  = abstractMVarCtx cQ (l-1) in  *)
  let tau' = abstractMVarCompTyp cQ' (l,0) tau1 in
  let cD' = ctxToMCtx (I.Maybe) cQ' in
  let tau'' = raiseCompTyp cD' tau' in
    (tau'', Context.length cD' )

let abstrCodataTyp cD tau tau' =
  let rec split cD = match cD with
    | I.Dec (cD', (I.Decl(psi, I.CTyp (Some w), dep) as decl)) ->
      let (cD_ctx, cD_rest) = split cD' in
      (I.Dec (cD_ctx, decl), cD_rest)
    | I.Dec (cD', decl) ->
      let (cD_ctx, cD_rest) = split cD' in
      (cD_ctx, I.Dec (cD_rest, decl))
    | I.Empty -> (I.Empty, I.Empty)
  in
  let (cD_ctx, cD_rest) = split cD in
  let _ = dprint (fun () -> "cD_ctx = " ^ P.mctxToString cD_ctx
    ^ "\ncD_rest = " ^ P.mctxToString cD_rest) in
  let tau0        = Whnf.cnormCTyp (tau, Whnf.m_id) in
  let tau1        = Whnf.cnormCTyp (tau', Whnf.m_id) in

  let (cQ1, cD'_ctx) = collectMctx I.Empty cD_ctx in
  let (cQ2, cD'_rest) = collectMctx cQ1 cD_rest in
  let l' = Context.length cD_ctx in
  let p = Context.length cD_rest in
  
  let (cQ3, tau0')  = collectCompTyp (l'+p) cQ2 tau0 in
  let k           = lengthCollection cQ3 in
  let l = k - l' in
  let cQ'  = abstractMVarCtx cQ3 (l-1-p) in
  let tau_obs = abstractMVarCompTyp cQ' (l,0) tau0' in
  let cD' = ctxToMCtx (I.Maybe) cQ' in
  let _ = dprint (fun () -> "tau0' = " ^ P.compTypToString cD tau0'
    ^ "\ntau_obs = " ^ P.compTypToString cD' tau_obs) in
  let _ = dprint (fun () -> "cD' = " ^ P.mctxToString cD') in
    
  (* Assumes: cQ3, cQ3' = cQ4 *)
  let (cQ4, tau1')  = collectCompTyp (l'+p) cQ3 tau1 in
  let k           = lengthCollection cQ4 in
  let l = k - l' in
  let cQ''  = abstractMVarCtx cQ4 0 in
  let tau_res = abstractMVarCompTyp cQ'' (l,0) tau1' in
  let cD'' = ctxToMCtx (I.Maybe) cQ'' in
  let _ = dprint (fun () -> "cD'' = " ^ P.mctxToString cD'') in

  let rec drop p cD = match p, cD with
    | 0, _ -> cD
    | _, I.Dec (cD', decl) -> drop (p-1) cD'
  in
  let cD1' = drop p cD' in
  let _ = dprint (fun () -> "cD1' = " ^ P.mctxToString cD1') in
  let cD1'' = drop p cD'' in
  let _ = dprint (fun () -> "cD1'' = " ^ P.mctxToString cD1'') in
  let rec subtract cD1 cD2 =
    let l_cD1 = Context.length cD1 in
    let l_cD2 = Context.length cD2 in
    if l_cD1 = l_cD2 then
      I.Empty
    else (* thus, l_cD1 > l_cD2 *)
      let I.Dec (cD1', decl) = cD1 in
      let cD = subtract cD1' cD2 in
      I.Dec (cD, decl)
  in
  let cD_res = subtract cD'' cD' in
  let _ = dprint (fun () -> "cD_res = " ^ P.mctxToString cD_res) in
  (* cD'' = cD', cD_res *)
  let tau_res' = raiseCompTyp cD_res tau_res in
  (cD', tau_obs, tau_res', Context.length cD_res)

let abstrPatObj loc cD cG pat tau =
  let _ = pat_flag := true in
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
  let cD'     = ctxToMCtx_pattern cQ' in
  let cD2     = abstractMVarMctx cQ' cD1' (0,offset-1) in
  let cD      = Context.append cD' cD2 in
    (pat_flag := false;
      (cD, cG', pat', tau'))


let abstrPatSpine loc cD cG patSpine tau =
  let _ = pat_flag := true in
  let patSpine = Whnf.cnormPatSpine (patSpine, Whnf.m_id) in
  let cG = Whnf.cnormCtx (cG, Whnf.m_id) in
  let (cQ1, cD1') = collectMctx I.Empty cD in
  let (cQ2, cG)   = collectGctx cQ1 cG   in
  let (cQ3, patSpine') = collectPatSpine cQ2 patSpine in
  let (cQ, tau') = collectCompTyp 0 cQ3 tau in
  let cQ'     = abstractMVarCtx cQ 0 in
  let offset  = Context.length cD1' in
  let cG'     = abstractMVarGctx cQ' (0,offset) cG in
  let patSpine' = abstractMVarPatSpine cQ' cG' (0,offset) patSpine' in
  let tau'    = abstractMVarCompTyp cQ' (0,offset) tau' in
  let cD'     = ctxToMCtx_pattern cQ' in
  let cD2     = abstractMVarMctx cQ' cD1' (0,offset-1) in
  let cD      = Context.append cD' cD2 in
    (pat_flag := false;
      (cD, cG', patSpine', tau'))


(*
   1) Collect FMVar and FPVars  in cD1, Psi1, tM and tA
   2) Abstract FMVar and FPVars in cD1, Psi1, tM and tA

*)
let abstrPattern cD1 cPsi1  (phat, tM) tA =
  let _ = pat_flag := true in
  let (cQ, cD1', cPsi1', (phat, tM'), tA')  = collectPattern I.Empty cD1 cPsi1 (phat,tM) tA in
  let cQ'     = abstractMVarCtx cQ 0 in
  let offset  = Context.length cD1' in
  let cPsi2   = abstractMVarDctx cQ' (0,offset) cPsi1' in
  let tM2     = abstractMVarTerm cQ' (0,offset) (tM', LF.id) in
  let tA2     = abstractMVarTyp  cQ' (0,offset) (tA', LF.id) in
  let cD2     = abstractMVarMctx cQ' cD1' (0, offset-1) in
(*  let cs1'    = abstractMVarCSub cQ' offset cs1 in
  let cs'     = abstractMVarCSub cQ' offset cs in *)
  let cD'     = ctxToMCtx_pattern cQ' in
  let cD      = Context.append cD' cD2 in
    (pat_flag := false ; (cD, cPsi2, (phat, tM2), tA2))


let abstrMObjPatt cD1 cM mT =
  let _ = pat_flag := true in
  let (cQ1, cD1') = collectMctx I.Empty cD1 in
  let (cQ2, cM')  = collect_meta_obj 0 cQ1 cM in
  let (cQ3, mT')  = collectMetaTyp (Syntax.Loc.ghost) 0 cQ2 mT in
  let cQ'         = abstractMVarCtx cQ3 0 in
  let offset      = Context.length cD1' in
  let cM'         = abstractMVarMetaObj cQ' (0, offset) cM' in
  let mT'         = abstractMVarMetaTyp cQ' mT' (0, offset) in
  let cD2         = abstractMVarMctx cQ' cD1' (0, offset-1) in
  let cD'         = ctxToMCtx_pattern cQ' in
  let cD          = Context.append cD' cD2 in
    (pat_flag := false ; (cD, cM', mT'))

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
  let cD'      = ctxToMCtx (I.Maybe) cQ' in
  let cD       = Context.append cD' cD2 in
    (cD, cPsi2, sigma2, cPhi2)

let abstrExp e =
  collectExp I.Empty e

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
  | I.Dec(_cQ, FDecl (FV _, Impure)) ->  true
  | I.Dec(cQ, FDecl (FV _, Pure (LFTyp tA))) ->
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

  let cD0     = ctxToMCtx (I.Maybe) cQ' in

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
  let cD'     = ctxToMCtx (I.Maybe) cQ' in
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
let codatatyp = abstrCodataTyp
let exp = abstrExp
let pattern = abstrPattern
let pattern_spine = abstrPatSpine
let patobj = abstrPatObj
let subpattern = abstrSubPattern
let mobj = abstrMObjPatt

