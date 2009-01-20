(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

(* TODO
 *
 * - Extension to deal with schemas
 * - Checking Schemas
 *
 * - Extension to handle sigma-types
 *    -> need to change data-type definition for typ_rec
 *
 * - Sgn module (see syntax.ml/syntax.mli)
 *   what is this for? – All individual pieces are already
 *   stored somehow using store.ml
 *
 * - Cycle detection?
 * - Code walk for reconstruction
 *)

open Store
open Store.Cid
open Syntax
open Substitution
open Error
open Id

module Unify = Unify.EmptyTrail
module C     = Cwhnf

exception NotImplemented
exception Error of error

exception Violation of string

let rec lookup cG k = match (cG, k) with
  | (Int.LF.Dec(_cG', (_,  tau)), 1) ->  tau
  | (Int.LF.Dec( cG', (_, _tau)), k) ->
      lookup cG' (k-1)

(* PHASE 0 : Indexing
 *
 * index_term names ext_m = m
 *
 * Translates an object ext_m in external syntax
 * into an object m in approximate internal syntax.
 *
 *
 * ASSUMPTION:
 *
 *    ext_m is in beta-eta normal form
 *        m is in beta-eta normal form, i.e.
 *    all occurrences of free variables in m
 *    are eta-expanded.
 *
 * Generalization:
 *    Allow user to write terms which are not eta-expanded.
 *    this possibly requires a change in the definition of FVar constructor.
 *
 *    FVar of name
 *
 *    would need to change to  FVar of name * sub * typ * dctx
 *    and may also need information about its type and context in
 *    which it was created;
 *)
let rec index_kind cvars bvars = function
  | Ext.LF.Typ _ ->
      Apx.LF.Typ

  | Ext.LF.ArrKind (_, a, k) ->
      let x      = Id.mk_name None
      and a'     = index_typ cvars bvars a in
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let k'     = index_kind cvars bvars' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let a'     = index_typ cvars bvars a
      and bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let k'     = index_kind cvars bvars' k in
        Apx.LF.PiKind (Apx.LF.TypDecl (x, a'), k')

and index_typ cvars bvars = function
  | Ext.LF.Atom (_, a, s) ->
      let a' = Typ.index_of_name a
      and s' = index_spine cvars bvars s in
        Apx.LF.Atom (a', s')

  | Ext.LF.ArrTyp (_, a, b) ->
      let x      = Id.mk_name None
      and a'     = index_typ cvars bvars a in
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let b'     = index_typ cvars bvars' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

  | Ext.LF.PiTyp (_, Ext.LF.TypDecl (x, a), b) ->
      let a'     = index_typ cvars bvars  a
      and bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let b'     = index_typ cvars bvars' b in
        Apx.LF.PiTyp (Apx.LF.TypDecl (x, a'), b')

and index_term cvars bvars = function
  | Ext.LF.Lam (_, x, m)   ->
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let m'     = index_term cvars bvars' m in
        Apx.LF.Lam (x, m')

  | Ext.LF.Root (_, h, s) ->
      let h' = index_head  cvars bvars h
      and s' = index_spine cvars bvars s in
        Apx.LF.Root (h', s')

and index_head cvars bvars = function
  | Ext.LF.Name (_, n) ->
      begin try
        Apx.LF.BVar (BVar.index_of_name bvars n)
      with Not_found -> try
        Apx.LF.Const (Term.index_of_name n)
      with Not_found ->
        Apx.LF.FVar n
      end

  | Ext.LF.PVar (_, p, s) ->
      begin try
        let offset = CVar.index_of_name cvars p in
        let s'     = index_sub cvars bvars s in
          Apx.LF.PVar (offset, s')
      with Not_found ->
        let s'     = index_sub cvars bvars s in
          Apx.LF.FPVar (p, s')
      end

  | Ext.LF.MVar (_, u, s) ->
      begin try
        let offset = CVar.index_of_name cvars u in
        let s'     = index_sub cvars bvars s in
          Apx.LF.MVar (offset, s')
      with Not_found ->
        let s'     = index_sub cvars bvars s in
          Apx.LF.FMVar (u, s')
      end

and index_spine cvars bvars = function
  | Ext.LF.Nil ->
      Apx.LF.Nil

  | Ext.LF.App (_, m, s) ->
      let m' = index_term  cvars bvars m
      and s' = index_spine cvars bvars s in
        Apx.LF.App (m', s')

and index_sub cvars bvars = function
  | Ext.LF.Id _ -> Apx.LF.Id

  | Ext.LF.Dot (_, s, Ext.LF.Head h) ->
      let s' = index_sub cvars bvars s  in
      let h' = index_head cvars bvars h in
        Apx.LF.Dot (Apx.LF.Head h', s')

  | Ext.LF.Dot (_, s, Ext.LF.Normal m) ->
      let s' = index_sub cvars bvars s  in
      let m' = index_term cvars bvars m in
        Apx.LF.Dot (Apx.LF.Obj  m', s')

  | Ext.LF.EmptySub _ ->
      Apx.LF.EmptySub

let index_decl cvars bvars (Ext.LF.TypDecl(x, a)) =
  let a'     = index_typ cvars bvars a in
  let bvars' = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDecl (x,a'), bvars')

let rec index_dctx ctx_vars cvars bvars = function
  | Ext.LF.Null        -> (Apx.LF.Null , bvars)
  | Ext.LF.CtxVar psi_name  ->
      let offset = CVar.index_of_name ctx_vars psi_name in
        (Apx.LF.CtxVar offset , bvars)
  | Ext.LF.DDec (psi, decl) ->
      let (psi', bvars') = index_dctx ctx_vars cvars bvars psi in
      let (decl', bvars'')  = index_decl cvars bvars' decl in
        (Apx.LF.DDec (psi', decl'), bvars'')

(* Order of psihat ? -bp
   It's not clear how to know that the last name is a bound variable
   or if it is a name of a context variable...
*)
let index_psihat ctx_vars explicit_psihat =
  let bv = BVar.create () in

  let rec index_hat bvars = function
    | [] -> (0, bvars)
    | x :: psihat ->
        let bvars' = BVar.extend bvars (BVar.mk_entry x) in
        let (l, bvars'') = index_hat bvars' psihat in
          (l + 1, bvars'')
  in
    begin match explicit_psihat with
      | [] -> ((None, 0), bv)
      | x :: psihat ->
          begin try
            let ctx_var = CVar.index_of_name ctx_vars x in
            let (d, bvars) = index_hat bv psihat in
              ((Some (Int.LF.Offset ctx_var), d) , bvars)
          with Not_found ->
            let (d, bvars ) = index_hat bv explicit_psihat in
              ((None, d) , bvars)
          end
    end


let rec index_ctx cvars bvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty , bvars)

  | Ext.LF.Dec (psi, dec) ->
      let (psi', bvars')  = index_ctx  cvars bvars psi in
      let (dec', bvars'') = index_decl cvars bvars' dec in
        (Apx.LF.Dec (psi', dec'), bvars'')

let index_cdecl ctx_vars cvars = function
  | Ext.LF.MDecl (_, u, a, psi) ->
      let (psi', bvars') = index_dctx ctx_vars cvars (BVar.create ()) psi in
      let  a'            = index_typ  cvars bvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry u) in
        (Apx.LF.MDecl (u, a', psi'), cvars')

  | Ext.LF.PDecl (_, p, a, psi) ->
      let (psi', bvars') = index_dctx ctx_vars cvars (BVar.create ()) psi in
      let  a'            = index_typ  cvars bvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry p) in
        (Apx.LF.PDecl (p, a', psi') , cvars')


let rec index_mctx ctx_vars cvars = function
  | Ext.LF.Empty -> 
      (Apx.LF.Empty , cvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (delta', cvars') = index_mctx ctx_vars cvars delta in
      let (cdec', cvars'') = index_cdecl ctx_vars cvars' cdec in
        (Apx.LF.Dec (delta', cdec'), cvars'')


(* Records are not handled in a general manner
 * We need to change the datatype for typ_rec to be typ_decl ctx
 *)
let rec index_typrec cvars bvars = function
  | Ext.LF.SigmaLast last_a -> 
      Apx.LF.SigmaLast (index_typ cvars bvars last_a)

  | Ext.LF.SigmaElem (x, a, arec) -> 
      Apx.LF.SigmaElem (x, index_typ cvars bvars a, index_typrec cvars bvars arec)


(* Translation of external schemas into approximate schemas *)
let rec index_elements el_list = match el_list with
  | [] -> []
  | el :: el_list' -> index_el el :: index_elements el_list'


and index_el (Ext.LF.SchElem (_, typ_ctx, Ext.LF.SigmaDecl (x, typ_rec))) =
  let cvars = (CVar.create ()) in
  let bvars = (BVar.create ()) in
  let (typ_ctx', bvars') = index_ctx cvars bvars typ_ctx in
  let typ_rec'           = index_typrec cvars bvars' typ_rec in
    Apx.LF.SchElem (typ_ctx', Apx.LF.SigmaDecl (x, typ_rec'))


let index_schema (Ext.LF.Schema el_list) =
  Apx.LF.Schema (index_elements el_list)


(* Translation of external computations into approximate computations *)
let rec index_comptyp ctx_vars cvars  = function
  | Ext.Comp.TypBox (_, a, psi)    ->
      let (psi', bvars') = index_dctx ctx_vars cvars (BVar.create ()) psi in
      let  a'            = index_typ cvars bvars' a   in
        Apx.Comp.TypBox (a', psi')

  | Ext.Comp.TypArr (_, tau, tau') ->
      Apx.Comp.TypArr (index_comptyp ctx_vars cvars tau, index_comptyp ctx_vars cvars tau')

  | Ext.Comp.TypPiBox (_, cdecl, tau)    ->
      let (cdecl', cvars') = index_cdecl ctx_vars cvars cdecl in
        Apx.Comp.TypPiBox (cdecl', index_comptyp ctx_vars cvars' tau)

  | Ext.Comp.TypCtxPi (_, (ctx_name, schema_name), tau)    ->
      let ctx_vars'        = CVar.extend ctx_vars (CVar.mk_entry ctx_name) in
      let schema_cid       = Schema.index_of_name schema_name in
        (* if exception Not_Found is raised, it means schema_name does not exist *)
        Apx.Comp.TypCtxPi ((ctx_name, schema_cid), index_comptyp ctx_vars' cvars tau)


let rec index_exp ctx_vars cvars vars = function
  | Ext.Comp.Syn (_ , i)   ->
      Apx.Comp.Syn (index_exp' ctx_vars cvars vars i)

  | Ext.Comp.Fun (_, x, e) ->
      let vars' = Var.extend vars (Var.mk_entry x) in
        Apx.Comp.Fun (x, index_exp ctx_vars cvars vars' e)

  | Ext.Comp.CtxFun (_, psi_name, e) ->
      let ctx_vars' = CVar.extend ctx_vars (CVar.mk_entry psi_name) in
        Apx.Comp.CtxFun (psi_name, index_exp ctx_vars' cvars vars e)

  | Ext.Comp.MLam (_, u, e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry u) in
        Apx.Comp.MLam (u, index_exp ctx_vars cvars' vars e)

  | Ext.Comp.Box (_, psihat, m) ->
      let (psihat', bvars) = index_psihat ctx_vars psihat in
        Apx.Comp.Box (psihat', index_term cvars bvars m)

  | Ext.Comp.Case (_, i, branches) ->
      let i' = index_exp' ctx_vars cvars vars i in
      let branches' = List.map (function b -> index_branch ctx_vars cvars vars b) branches in
        Apx.Comp.Case (i', branches')

and index_exp' ctx_vars cvars vars = function
  | Ext.Comp.Var (_, x) ->
      begin try
        Apx.Comp.Var (Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (Comp.index_of_name x)
      with Not_found ->
        raise (Error (UnboundName x))
      end

  | Ext.Comp.Apply (_, i, e) ->
      let i' = index_exp' ctx_vars cvars vars i in
      let e' = index_exp  ctx_vars cvars vars e in
        Apx.Comp.Apply (i', e')

  | Ext.Comp.CtxApp (_, i, psi) ->
      let i'   = index_exp' ctx_vars cvars vars i in
      let (psi', _) = index_dctx ctx_vars cvars (BVar.create ()) psi in
        Apx.Comp.CtxApp (i', psi')

  | Ext.Comp.MApp (_, i, (psihat, m)) ->
      let i'      = index_exp' ctx_vars cvars vars i in
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let m' = index_term cvars bvars m in
        Apx.Comp.MApp (i', (psihat', m'))


  | Ext.Comp.Ann (_, e, tau) ->
      Apx.Comp.Ann (index_exp  ctx_vars cvars vars e,
                    index_comptyp ctx_vars cvars tau)


and index_branch ctx_vars cvars vars branch = match branch with
  | (Ext.Comp.BranchBox(_, delta, (psihat, m, Some (a, psi)), e)) ->
      let (delta', cvars')  = index_mctx ctx_vars cvars delta in
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let m'               = index_term cvars' bvars m in
      let (psi', _bvars)   = index_dctx ctx_vars cvars' (BVar.create ()) psi in
        (* _bvars = bvars *)
      let a'               = index_typ cvars' bvars a in
      let e'               = index_exp ctx_vars cvars' vars e in
        Apx.Comp.BranchBox (delta', (psihat', m', Some (a', psi')), e')


  | (Ext.Comp.BranchBox(_, delta, (psihat, m, None), e)) ->
      let (delta', cvars')  = index_mctx ctx_vars cvars delta in
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let m'               = index_term cvars' bvars m in
      let e'               = index_exp ctx_vars cvars' vars e in
        Apx.Comp.BranchBox (delta', (psihat', m', None), e')


(* ******************************************************************* *)
(* PHASE 1 : Elaboration and free variables typing                     *)

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
let fvar_cnstr : ((Apx.LF.normal * Int.LF.cvar)  list) ref = ref []

let add_fvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fvarCnstr () = (fvar_cnstr := [])

(* Constraints for free metavariables and parameter variables  *)
let fcvar_cnstr : ((Apx.LF.normal * Int.LF.cvar)  list) ref = ref []

let add_fcvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fcvarCnstr () = (fvar_cnstr := [])

let rec raiseType cPsi tA = match cPsi with
  | Int.LF.Null -> tA
  | Int.LF.DDec (cPsi', decl) ->
      raiseType cPsi' (Int.LF.PiTyp (decl, tA))

(* patSpine s = bool
 *
 * if cPsi |- s : A <- P  and
 *    s is a pattern spine (simple approximate),
 * i.e. it consists of distinct bound variables
 *
 * then
 *    return true;
 *    otherwise false.
 *)
let patSpine spine =
  let rec patSpine' seen_vars spine = match spine with
    | Apx.LF.Nil ->
        (true, 0)

    | Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine) ->
        if not (List.mem x seen_vars) then
          let (b,l) = patSpine' (x :: seen_vars) spine in
            (b, l + 1)
        else
          (false, 0)

    | _ -> (false, 0)
  in
    patSpine' [] spine


(* etaExpandMV cPsi sA s' = tN
 *
 *  cPsi'  |- s'   <= cPsi
 *  cPsi   |- [s]A <= typ
 *
 *  cPsi'  |- tN   <= [s'][s]A
 *)
let rec etaExpandMV cPsi sA s' = etaExpandMV' cPsi (Whnf.whnfTyp sA)  s'

and etaExpandMV' cPsi sA  s' = match sA with
  | (Int.LF.Atom (_a, _tS) as tP, s) ->
      let u = Whnf.newMVar (cPsi, Int.LF.TClo(tP,s)) in
        Int.LF.Root (Int.LF.MVar (u, s'), Int.LF.Nil)

  | (Int.LF.PiTyp (Int.LF.TypDecl (x, _tA) as decl, tB), s) ->
      Int.LF.Lam (x, etaExpandMV (Int.LF.DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) (LF.dot1 s'))


(* isPatSub s = bool *)
let rec isPatSub s = match s with
  | Apx.LF.Id -> 
      true

  | Apx.LF.EmptySub -> 
      true

  | Apx.LF.Dot (Apx.LF. Head (Apx.LF.BVar _k), s) ->
      isPatSub s

  | _ -> 
      false

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
let rec synDom cPsi s = match s with
  | Apx.LF.Id -> (cPsi, Int.LF.Shift 0)
  | Apx.LF.EmptySub ->
      let (_, d) = Context.dctxToHat cPsi in
        (Int.LF.Null , Int.LF.Shift d)

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      begin match Context.ctxDec cPsi k with
        | Int.LF.TypDecl(x, tA) ->
            let (cPhi, s') = synDom cPsi s in
              (*  cPsi |- s <= cPhi
               *  cPsi |- tA <= type
               *  tA' = [s]^-1(tA)
               *
               * Note: We may need to check that indeed
               *        [s]^-1(tA) exists.
               *
               *  Wed Jan 14 13:51:11 2009 -bp
               *)
              (Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, Int.LF.TClo(tA, Substitution.LF.invert s'))),
               Int.LF.Dot(Int.LF.Head(Int.LF.BVar k), s'))

      end
  | _ -> raise (Violation "Encountered non-pattern substitution")

(* elKind  cPsi (k,s) = K *)
let rec elKind cPsi k = match k with
  | Apx.LF.Typ ->
      Int.LF.Typ

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let tA    = elTyp Int.LF.Empty cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elKind cPsi' k in
        Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK)

(* elTyp cD cPsi a = A
 *
 * Pre-condition:
 *     Upsilon = set of free variables
 *
 * if cD ; cPsi |- a <= type and
 *    a is in beta-eta normal form
 * then
 *    cD ; cPsi   |- A <- type (pre-dependent)
 * and A is in beta-eta normal form.
 *
 * Effect:
 *     Upsilon' = FV(A)  where Upsilon' is an extension of Upsilon
 *)
and elTyp cD cPsi a = match a with
  | Apx.LF.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let (_, d) = Context.dctxToHat cPsi in
      let tS = elKSpineI cD cPsi s i (tK, Int.LF.Shift d) in
        Int.LF.Atom (a, tS)

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let tA    = elTyp cD cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp cD cPsi' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB)

(* elTerm  cD cPsi m sA = M
 * elTermW cD cPsi m sA = M  where sA = (A,s) is in whnf
 *                              m is in beta-eta normal form.
 * if |cPsi| |- m <= |[s]A'|
 *
 *    cD |- cPsi ctx
 *    cD ; cPsi  |- s <= cPsi'
 *    cD ; cPsi' |- A <- type (pre-dependent)
 *
 * then
 *    cD ; cPsi |- M <- A     (pre-dependent)
 *
 * and M is in beta-eta normal form, i.e.
 *   all free variables are eta-expanded.
 *)
and elTerm cD cPsi m sA = elTermW cD cPsi m (Whnf.whnfTyp sA)

and elTermW cD cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (Int.LF.TypDecl (_x, _tA) as decl, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm cD cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam (x, tM)

  | (Apx.LF.Root (Apx.LF.Const c, spine), ((Int.LF.Atom _ ), _s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let (_, d) = Context.dctxToHat cPsi in
      let tS = elSpineI cD cPsi spine i (tA, Int.LF.Shift d)  in
        Int.LF.Root (Int.LF.Const c, tS)

  | (Apx.LF.Root (Apx.LF.BVar x, spine), (Int.LF.Atom _ , _s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine cD cPsi spine (tA, LF.id)  in
        Int.LF.Root (Int.LF.BVar x, tS)

  | (Apx.LF.Root (Apx.LF.MVar (u, s'), spine), (Int.LF.Atom _, _s)) ->
      let (tA, cPhi) = Cwhnf.mctxMDec cD u in
      let s'' = elSub cD cPsi s' cPhi in
      let tS = elSpine cD cPsi spine (tA, s'')  in
        Int.LF.Root (Int.LF.MVar (Int.LF.Offset u, s''), tS)

  | (Apx.LF.Root (Apx.LF.PVar (p,s'), spine), (Int.LF.Atom _, _s)) ->
      let (tA, cPhi) = Cwhnf.mctxPDec cD p in
      let s'' = elSub cD cPsi s' cPhi in
      let tS = elSpine cD cPsi spine (tA, s'')  in
        Int.LF.Root (Int.LF.PVar (Int.LF.Offset p, s''), tS)

  | (Apx.LF.Root (Apx.LF.FVar x, spine) as m, (Int.LF.Atom _ as tP , s)) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
           * . |- tA <= type
           * This will be enforced during abstraction *)
        let (_, d) = Context.dctxToHat cPsi in
        let tS = elSpine cD cPsi spine (tA, Int.LF.Shift d) in
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        let (patternSpine, _l) = patSpine spine in
          if patternSpine then
            let (_, d) = Context.dctxToHat cPsi in
            let (tS, tA) = elSpineSynth cD cPsi spine (Int.LF.Shift d) (tP, s) in
              (* For type reconstruction to succeed, we must have
               * . |- tA <= type  and cPsi |- tS : tA <= [s]tP
               * This will be enforced during abstraction.
               *)
            let _        = FVar.add x tA in
              Int.LF.Root (Int.LF.FVar x, tS)
          else
            let v = Whnf.newMVar (cPsi, Int.LF.TClo(tP, s)) in
              add_fvarCnstr (m, v);
              Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)

      end

  (* We only allow free meta-variables of atomic type *)
  | (Apx.LF.Root (Apx.LF.FMVar (u, s), Apx.LF.Nil) as m, (Int.LF.Atom _ as tP', s')) ->
      begin try
        (* For named free meta-variables which may occur in branches of case-expressions;
         * these named free meta-variables may be bound by the pattern.
         *)
        let (offset, (_tP, cPhi)) = Cwhnf.mctxPos cD u  in
        let s'' = elSub cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' --
           * this check is delayed to reconstruction 
           *)
          Int.LF.Root (Int.LF.MVar (Int.LF.Offset offset, s''), Int.LF.Nil)

      with Cwhnf.Fmvar_not_found ->
        begin try
          let (_tP, cPhi) = FMVar.get u in
            (* For type reconstruction to succeed, we must have
             * . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
             * meta-variables in cD. This will be enforced during abstraction 
             *)

          let s'' = elSub cD cPsi s cPhi in
            (* We do not check here that tP approx. [s']tP' --
               this check is delayed to reconstruction *)
            Int.LF.Root (Int.LF.FMVar (u, s''), Int.LF.Nil)

        with Not_found ->
          if isPatSub s then
            (* 1) given cPsi and s synthesize the domain cPhi
             * 2) [s]^-1 ([s']tP) is the type of u
             *)

            let (cPhi, s'') = synDom cPsi s in
            let tP   = Int.LF.TClo( Int.LF.TClo(tP',s'), Substitution.LF.invert s'') in
              (* For type reconstruction to succeed, we must have
               * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
               * This will be enforced during abstraction.
               *)
            let _   = FMVar.add u (tP, cPhi) in
              Int.LF.Root (Int.LF.FMVar (u, s''), Int.LF.Nil)
          else
            let v = Whnf.newMVar (cPsi, Int.LF.TClo(tP', s')) in
              add_fcvarCnstr (m, v);
              Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)
        end
      end

  (* Add case for parameter variables -bp *)

  (* TODO find a way to postpone type mismatch to reconstruction step *)

(* elSub cD cPsi s cPhi = s'
 *
 * We elaborate the substitution s, but we do not check if it is
 * approximately well-typed.
 *)
and elSub cD cPsi s cPhi = match (s, cPhi) with
  | (Apx.LF.EmptySub, Int.LF.Null )  ->
      let (_, d) = Context.dctxToHat cPsi in
        Int.LF.Shift d

  | (Apx.LF.Id , _)  ->
      let (ctx_v , d )  = Context.dctxToHat cPsi in
      let (ctx_v', d')  = Context.dctxToHat cPhi in
      let k  = d - d' in
        if k < 0 && ctx_v = ctx_v' then
          raise (Error IllTypedIdSub)
        else
          Int.LF.Shift k

  | (Apx.LF.Dot (Apx.LF.Head h, s), Int.LF.DDec (cPhi', _decl)) ->
      (* NOTE: if decl = x:A, and cPsi(h) = A' s.t. A =/= A'
       *       we will fail during reconstruction / type checking 
       *)
      Int.LF.Dot (Int.LF.Head (elHead cD cPsi h), elSub cD cPsi s cPhi')

  | (Apx.LF.Dot (Apx.LF.Obj m, s), Int.LF.DDec (cPhi', Int.LF.TypDecl(_, tA))) ->
      let s' = elSub cD cPsi s cPhi' in
      let m' = elTerm cD cPsi m (tA, s') in
        Int.LF.Dot (Int.LF.Obj m', s')

and elHead cD cPsi h   = match h with
  | Apx.LF.BVar x -> 
      Int.LF.BVar x

  | Apx.LF.Const c -> 
      Int.LF.Const c

  | Apx.LF.MVar (u,s) ->
      let (_tA, cPhi) = Cwhnf.mctxMDec cD u in
        Int.LF.MVar (Int.LF.Offset u, elSub cD cPsi s cPhi)

  | Apx.LF.PVar (p,s) ->
      let (_tA, cPhi) = Cwhnf.mctxPDec cD p in
        Int.LF.PVar (Int.LF.Offset p, elSub cD cPsi s cPhi)

  | Apx.LF.FVar x -> 
      Int.LF.FVar x


(* elSpineI  cD cPsi spine i sA sP  = S
 * elSpineIW cD cPsi spine i sA sP  = S
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
 * If O ; U ; (cD ; cPsi) |- spine <- [s]A  (approx)
 * then
 *    O' ; U' ; (cD ; cPsi) |- S <- [s]A : [s']P (pre-dependent)
 *
 *
 * Post-condition:
 *   U' = extension of U containing all free variables of S
 *   O' = extension of O containing i new meta-variables
 *            for implicit arguments
 *
 * Comment: elSpineI will insert new meta-variables (as references)
 *   for omitted implicit type arguments; their type is pre-dependent.
 *)
and elSpineI cD cPsi spine i sA =
  elSpineIW cD cPsi spine i (Whnf.whnfTyp sA)

and elSpineIW cD cPsi spine i sA =
  if i = 0 then
    elSpine cD cPsi spine sA
  else
    match sA with
      | (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           * 
           * tN = u[s']  and u::A'[.]
           * 
           * s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
           *   and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)
           *)
          let (_, d) = Context.dctxToHat cPsi in
          let tN     = etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift d) in
          let spine' = elSpineI cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')
      (* other cases impossible by (soundness?) of abstraction *)

(* elSpine cD cPsi spine sA = S
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
and elSpine cD cPsi spine sA =
  elSpineW cD cPsi spine (Whnf.whnfTyp sA)

and elSpineW cD cPsi spine sA = match (spine, sA) with
  | (Apx.LF.Nil, (_tP , _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm  cD cPsi m (tA, s) in
      let tS = elSpine cD cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      raise (Error ExpAppNotFun) (* TODO postpone to reconstruction *)

(* see invariant for elSpineI *)
and elKSpineI cD cPsi spine i sK =
  if  i = 0 then
    elKSpine cD cPsi spine sK
  else
    match sK with
      | (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s) ->
          let (_, d) = Context.dctxToHat cPsi in
          let tN     = etaExpandMV Int.LF.Null (tA,s) (Int.LF.Shift d) in
          let spine' = elKSpineI cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

(* other cases impossible by (soundness?) of abstraction *)

(* see invariant for elSpine *)
and elKSpine cD cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (_tK, _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm   cD cPsi m (tA, s) in
      let tS = elKSpine cD cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      raise (Error ExpAppNotFun) (* TODO postpone to reconstruction *)

(* elSpineSynth cD cPsi spine s' = (S, A')
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
and elSpineSynth cD cPsi spine s' sP = match (spine, sP) with
  | (Apx.LF.Nil, (tP, s))  ->
      let ss = LF.invert s' in
        (* ensure that [ss] ([s]tP) exists ! *)
        (Int.LF.Nil, Int.LF.TClo(tP, LF.comp s ss))

  | (Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        (* cPsi |- tA : type
         * cPsi |- s' : cPsi'
         *)
      let ss = LF.invert s' in
      let tA' = Whnf.normTyp (tA, ss) in

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth cD cPsi spine (Int.LF.Dot(Int.LF.Head(Int.LF.BVar x), s')) sP in

        (*  cPsi |- tS : [s', x]tB <- sP  (pre-dependent) *)

        (* cPsi, y:A |- tB' <- type (pre-dependent) *)

        (Int.LF.App (Int.LF.Root (Int.LF.BVar x, Int.LF.Nil), tS),
         Int.LF.PiTyp (Int.LF.TypDecl (Id.mk_name None, tA'), tB))

   (* other cases impossible *)

(* REVISE DEFINITION OF SCHEMA ELEMENTS:
 *
 * It would be more convenient, if ctx would be
 * a dctx, since then we can do simple type-checking
 * of the rest of the typrec. -bp
 *
 * TODO double check -bp
 *)

(* let rec elSchElem (Apx.Int.SchElem (ctx, Apx.Int.SigmaDecl [a])) =
 * let ctx' = elCtx ctx in
 *)


let rec elSchema (Apx.LF.Schema _list) = Int.LF.Schema []
(*  Int.LF.Schema (
 *   List.map (function schElem -> elSchElem schElem) el_list)
 *)

let rec elDCtx cD psi = match psi with
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar offset -> Int.LF.CtxVar (Int.LF.Offset offset)

  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtx cD psi' in
      let tA   = elTyp cD cPsi a in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))


let rec elCDecl cD cdecl = match cdecl with
  | Apx.LF.MDecl (u, a, psi) ->
      let cPsi = elDCtx cD psi in
      let tA   = elTyp cD cPsi a in
        Int.LF.MDecl (u, tA, cPsi)
  | Apx.LF.PDecl (u, a, psi) ->
      let cPsi = elDCtx cD psi in
      let tA   = elTyp cD cPsi a in
        Int.LF.PDecl (u, tA, cPsi)


let rec elMCtx delta = match delta with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (delta, cdec) ->
      let cD    = elMCtx delta in
      let cdec' = elCDecl cD cdec in
        Int.LF.Dec (cD, cdec')


(* ******************************************************************* *)
(* elNeut  cD phat r = (R,
 * elNeutW cD phat r = R  where sA = (A,s) is in whnf
 *                              m is in beta-eta normal form.
 * if |cPsi| |- m <= |[s]A'|
 *
 *    cD |- cPsi ctx
 *    cD ; cPsi  |- s <= cPsi'
 *    cD ; cPsi' |- A <- type (pre-dependent)
 *
 * then
 *    cD ; cPsi |- M <- A     (pre-dependent)
 *
 * and M is in beta-eta normal form, i.e.
 *   all free variables are eta-expanded.
 *)
(*
and elTerm cD cPsi m sA = elTermW cD cPsi m (Whnf.whnfTyp sA)

and elTermW cD cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (Int.LF.TypDecl (_x, _tA) as decl, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm cD cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam(x, tM)

  | (Apx.LF.Root (Apx.LF.Const c, spine), ((Int.LF.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let (_, d) = Context.dctxToHat cPsi in
      let tS = elSpineI cD cPsi spine i (tA, Int.LF.Shift d) (tP, s) in
        Int.LF.Root (Int.LF.Const c, tS)

  | (Apx.LF.Root (Apx.LF.BVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine cD cPsi spine (tA, LF.id) (tP, s) in
        Int.LF.Root (Int.LF.BVar x, tS)

  | (Apx.LF.Root (Apx.LF.MVar (u,s'), spine), (Int.LF.Atom (_a, _) as tP, s)) ->
      let (tA, cPhi) = Cwhnf.mctxMDec cD u in
      let s'' = elSub cD cPsi s' cPhi in
      let tS = elSpine cD cPsi spine (tA, s'') (tP, s) in
          Int.LF.Root (Int.LF.MVar(Int.LF.Offset u, s''), tS)

  | (Apx.LF.Root (Apx.LF.PVar (p,s'), spine), (Int.LF.Atom (_a, _) as tP, s)) ->
      let (tA, cPhi) = Cwhnf.mctxPDec cD p in
      let s'' = elSub cD cPsi s' cPhi in
      let tS = elSpine cD cPsi spine (tA, s'') (tP, s) in
          Int.LF.Root (Int.LF.PVar(Int.LF.Offset p, s''), tS)

  | (Apx.LF.Root (Apx.LF.FVar x, spine) as m, (Int.LF.Atom _ as tP, s)) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
        let (_, d) = Context.dctxToHat cPsi in
      let tS = elSpine cD cPsi spine (tA, Int.LF.Shift d) (tP, s) in
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        let (patternSpine, _l) = patSpine spine in
        if patternSpine then
        let (_, d) = Context.dctxToHat cPsi in
        let (tS, tA) = elSpineSynth cD cPsi spine (Int.LF.Shift d) (tP, s) in
            (* For type reconstruction to succeed, we must have
               . |- tA <= type  and cPsi |- tS : tA <= [s]tP
               This will be enforced during abstraction.
            *)
          let _        = FVar.add x tA in
            Int.LF.Root (Int.LF.FVar x, tS)
        else
          let v = Whnf.newMVar (cPsi, Int.LF.TClo(tP, s)) in
            (add_fvarCnstr (m, v) ;
             Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)
            )

      end

  (* We only allow free meta-variables of atomic type *)
  | (Apx.LF.Root (Apx.LF.FMVar (u, s), Apx.LF.Nil) as m, (Int.LF.Atom _ as tP', s')) ->
      begin try
        (* For named free meta-variables which may occur in branches of case-expressions;
           these named free meta-variables may be bound by the pattern.
         *)
        let (offset, (_tP, cPhi)) = Cwhnf.mctxPos cD u  in
        let s'' = elSub cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' --
             this check is delayed to reconstruction *)
          Int.LF.Root (Int.LF.MVar (Int.LF.Offset offset, s''), Int.LF.Nil)

      with Cwhnf.Fmvar_not_found ->
      begin try
        let (_tP, cPhi) = FMVar.get u in
          (* For type reconstruction to succeed, we must have
               . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
             meta-variables in cD. This will be enforced during abstraction *)

      let s'' = elSub cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' --
             this check is delayed to reconstruction *)
          Int.LF.Root (Int.LF.FMVar (u, s''), Int.LF.Nil)

      with Not_found ->
        if isPatSub s then
          (* 1) given cPsi and s synthesize the domain cPhi
             2) [s]^-1 ([s']tP) is the type of u
          *)

          let (cPhi, s'') = synDom cPsi s in
          let tP   = Int.LF.TClo( Int.LF.TClo(tP',s'), Substitution.LF.invert s'') in
            (* For type reconstruction to succeed, we must have
               . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
               This will be enforced during abstraction.
            *)
          let _   = FMVar.add u (tP, cPhi) in
            Int.LF.Root (Int.LF.FMVar (u, s''), Int.LF.Nil)
        else
         let v = Whnf.newMVar (cPsi, Int.LF.TClo(tP', s')) in
            (add_fcvarCnstr (m, v) ;
             Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)
            )
      end
      end

  (* Add case for parameter variables -bp *)

  | _ ->
      raise (Error (IllTyped (cPsi, m, sA)))
*)

(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr cD cnstr = match cnstr with
  | []  -> ()
  | ((Apx.LF.Root (Apx.LF.FVar x, spine) , Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
        let (_, d) = Context.dctxToHat cPsi in

        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let tS = elSpine cD cPsi spine (tA, Int.LF.Shift d) in
          r := Some (Int.LF.Root (Int.LF.FVar x, tS));
          solve_fvarCnstr cD cnstrs
      with Not_found ->
        raise (Error LeftOverConstraints)
      end


(* ******************************************************************* *)
(* PHASE 2 : Reconstruction *)

(*  recTerm cPsi sM sA = ()
 *
 *  Pre-condition:
 *
 *  U = FV(M) (FV(A), FV(K) resp.)
 *  O = meta-variables in M (A, K, resp.)
 *
 * Invariant:
 *  If  O ; U ; (cD ; cPsi) |- [s']M <- [s]A (predependent)
 *      and there exists a modal substitution r
 *      s.t. O' |- r <= O
 *  then
 *
 *     recTerm cPsi sM sA succeeds and
 *
 *     O' ; [|r|]U ; ([|r|]cD ; [|r|]cPsi) |- [|r|][s']M <= [|r|][s]A
 *
 * Post-condition:
 *
 *   U' = [|r|]U
 *   O' s.t. O' |- r <= O , and
 *
 * Effect:
 *   - all meta-variables in O have been destructively updated.
 *   - may raise exception Error, if no modal substitution r exists.
 *
 * Similar invariants and pre- and post-conditions for:
 *
 *  recKind cD cPsi (K,s) = K'
 *  recTyp  cD cPsi (A,s) = A'
 *)
let rec recKind cD cPsi sK = match sK with
  | (Int.LF.Typ, _s) ->
      ()

  | (Int.LF.PiKind (Int.LF.TypDecl(_x, tA) as adec, tK), s) -> (
      recTyp cD cPsi (tA, s);
      recKind cD (Int.LF.DDec (cPsi, LF.decSub adec s)) (tK, LF.dot1 s)
    )

and recTyp cD cPsi sA = recTypW cD cPsi (Whnf.whnfTyp sA)

and recTypW cD cPsi sA = match sA with
  | (Int.LF.Atom (a, tS) , s) ->
      let tK = (Typ.get a).Typ.kind in
      let (_, d) = Context.dctxToHat cPsi in
      let tA' =  recKSpine cD cPsi (tS, s) (tK, Int.LF.Shift d) in
        tA'

  | (Int.LF.PiTyp ((Int.LF.TypDecl (_x, tA) as adec), tB), s) -> (
      recTyp cD cPsi (tA, s);
      recTyp cD (Int.LF.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s)
    )

and recTerm cD cPsi sM sA = recTermW cD cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW cD cPsi sM sA = match (sM, sA) with
  | ((Int.LF.Lam (_, tM), s'), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
        recTerm cD cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)

  | ((Int.LF.Root (_ , _) , _) as sR , (Int.LF.Atom (_ , _), _)) ->
      let sP' = synTerm cD cPsi sR in
        begin try
          Unify.unifyTyp (Context.dctxToHat cPsi, sP', sA)
        with Unify.Error _ -> 
          raise (Error (TypMisMatch (cPsi, sA, sP')))
        end

  | _ ->
      raise (Error (IllTyped (cPsi, sM, sA)))

(* synTerm cD cPsi sR = sP *)
and synTerm cD cPsi sR = synTermW cD cPsi (Whnf.whnf sR)

and synTermW cD cPsi sR = match sR with
  | (Int.LF.Root (Int.LF.Const c, tS), s') ->
      let tA = (Term.get c).Term.typ in
      let (_, d) = Context.dctxToHat cPsi in
        synSpine cD cPsi (tS, s') (tA, Int.LF.Shift d)

  | (Int.LF.Root (Int.LF.BVar x, tS), s') ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        synSpine cD cPsi (tS, s') (tA, LF.id)

  | (Int.LF.Root (Int.LF.MVar (Int.LF.Inst (_r, cPhi, tP', _cnstr), t), _tS), s') ->
      (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
      (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in
        recSub cD cPsi s1 cPhi;
        (tP', s1)

  | (Int.LF.Root (Int.LF.MVar (Int.LF.Offset u, t), _tS), s') ->
      (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
      (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in
      let (tP', cPsi') = Cwhnf.mctxMDec cD u in
        recSub cD cPsi s1 cPsi';
        (tP', s1)

  | (Int.LF.Root (Int.LF.FMVar (u, t), _tS), s') ->
      (* By invariant of whnf: tS = Nil *)
      let s1 = (LF.comp t s') in
      let (tP', cPhi) = FMVar.get u in
        recSub cD cPsi s1 cPhi;
        (tP', s1)

  | (Int.LF.Root (Int.LF.FPVar (p, t), tS), s') ->
      let s1 = (LF.comp t s') in
      let (tA', cPhi) = FPVar.get p in
      let (_, d) = Context.dctxToHat cPsi in
        recSub cD cPsi s1 cPhi;
        synSpine cD cPsi (tS, s') (tA', Int.LF.Shift d)

  | (Int.LF.Root (Int.LF.PVar (Int.LF.Offset p, t), tS), s') ->
      let s1 = (LF.comp t s') in
      let _ = Printf.printf  "Checking bound parameter variable  \n\n" in
      let (tA, cPsi') = Cwhnf.mctxPDec cD p in
        recSub cD cPsi s1 cPsi';
        synSpine cD cPsi (tS, s') (tA, t)


  | (Int.LF.Root (Int.LF.FVar x, tS), s') ->
      (* x is in eta-expanded form and tA is closed
       * type of FVar x : A[cPsi'] and FVar x should be
       * associated with a substitution, since tA is not always
       * closed.
       *
       * by invariant of whnf: s'  id
       *)
      let tA = FVar.get x in
      let (_, d) = Context.dctxToHat cPsi in
        synSpine cD cPsi (tS, s') (tA, Int.LF.Shift d)

and synSpine cD cPsi sS sA =
  synSpineW cD cPsi sS (Whnf.whnfTyp sA)

and synSpineW cD cPsi sS sA = match (sS, sA) with
  | ((Int.LF.Nil, _s), sP') ->
      sP'

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) -> (
      let _ = recTerm  cD cPsi (tM, s') (tA, s) in
        (*   cPsi |-  s <= cPsi1     cPsi1 |- Pi x:tA .tB <= typ
         *                           cPsi1 |- tA <= typ
         *                           cPsi1, x:tA |- tB <= typ
         *
         *   cPsi |-  s'<= cPsi2     cPsi |- [s']tM <= tA'   tA' = [s]tA
         *
         *   cPsi2 |- tM <= tA2       [s']tA2 = tA' = [s]tA
         *
         *   cPsi |-  [s']tM . s <= cPsi1, x: tA
         *)
        synSpine cD cPsi (tS, s') (tB, Int.LF.Dot (Int.LF.Obj (Int.LF.Clo (tM,s')), s))
    )

  | ((Int.LF.SClo (tS, s), s'), sA) ->
      synSpine cD cPsi (tS, LF.comp s s') sA


and recKSpine cD cPsi sS sK = match (sS, sK) with
  | ((Int.LF.Nil, _s), (Int.LF.Typ, _s')) ->
      ()

  | ((Int.LF.Nil, _s), _) ->
      raise (Error KindMisMatch)

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) -> (
      recTerm   cD cPsi (tM, s') (tA, s);
      recKSpine cD cPsi (tS, s') (tK, Int.LF.Dot (Int.LF.Obj tM, s))
    )

  (* TODO confirm this is necessary, instead of having recKSpineW *)
  | ((Int.LF.SClo (tS, s),  s'), sK) ->
      recKSpine cD cPsi (tS, LF.comp s s') sK

  | ((Int.LF.App _, _s), (Int.LF.Typ, _s')) ->
      raise (Error ExpAppNotFun)

and recSub cD cPsi s cPhi = match (s, cPhi) with
  | (Int.LF.Shift _n, _cPhi) ->
      (* We may need to expand cPhi further if n =/= 0 *)
      ()

  | (Int.LF.Dot (Int.LF.Head Int.LF.BVar x, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) ->
      let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
        recSub cD cPsi s cPhi;
        Unify.unifyTyp (Context.dctxToHat cPsi, (tA', LF.id), (tA, s))


  | (Int.LF.Dot (Int.LF.Obj tM, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) -> (
      recSub  cD cPsi s cPhi;
      recTerm cD cPsi (tM, LF.id) (tA, s)
    )

  | (Int.LF.Dot (Int.LF.Undef, _s), _) ->
      raise (Error LeftOverUndef)

  (* needs other cases for Head(h) where h = MVar, Const, etc. -bp *)


(* ******************************************************************* *)
(* Elaboration of computations *)

let rec elCompTyp cO cD tau = match tau with
  | Apx.Comp.TypBox (a, psi) ->
      let cPsi = elDCtx cD psi in
      let tA   = elTyp cD cPsi a in
        Int.Comp.TypBox (tA, cPsi)

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCtxPi ((x, schema_cid) , tau) ->
      let tau' = elCompTyp cO (Int.LF.Dec (cD, Int.LF.CDecl (x, schema_cid))) tau in
        Int.Comp.TypCtxPi ((x, schema_cid), tau')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl cD cdecl  in
      let tau'   = elCompTyp cO (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox (cdecl', tau')

let rec elExp cO cD cG e theta_tau = elExpW cO cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cO cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Syn i, _) ->
      let (i', _t) = elExp' cO cD cG i in
        Int.Comp.Syn i'

  | (Apx.Comp.Fun (x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
      let e' = elExp cO cD (Int.LF.Dec (cG, (x, Int.Comp.TypClo (tau1, theta)))) e (tau2, theta) in
        Int.Comp.Fun (x, e')

  | (Apx.Comp.CtxFun (psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid), tau), theta)) ->
      let e' = elExp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD cG e (tau, theta) in
        Int.Comp.CtxFun (psi_name, e')

  | (Apx.Comp.MLam (u, e), , (Int.Comp.TypPiBox(Int.LF.MDecl(_u, tA, cPsi), tau), theta))  ->
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
        cG e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (u, e')

  | (Apx.Comp.Box (psihat, tM), (Int.Comp.TypBox (tA, cPsi), theta)) ->
      let tM' = elTerm cD (C.cnormDCtx (cPsi, theta)) tM (C.cnormTyp (tA, theta), LF.id) in
        Int.Comp.Box (psihat, tM')

  | (Apx.Comp.Case (i, branches), tau_theta) ->
      let (i', tau_theta') = elExp' cO cD cG i in
        begin match C.cwhnfCTyp tau_theta'  with
          | (Int.Comp.TypBox (_tA, _cPsi), _theta') ->
              (* We don't check that each branch has approximate type tA[cPsi] - DOUBLE CHECK -bp  *)
              let branches' = List.map (function b -> elBranch cO cD cG b tau_theta) branches in
                Int.Comp.Case (i', branches')

          | _ -> raise (Violation "Case-expression ill-typed; Trying to branch on an expression which is not a boxed-LF type")
        end

  | (_, _) ->
      raise (Violation "Elaboration: Found ill-typed computation-level expression.")


and elExp' cO cD cG i = match i with
  | Apx.Comp.Var offset -> (Int.Comp.Var offset, (lookup cG offset, C.id))

  | Apx.Comp.Const prog -> (Int.Comp.Const prog, ((Comp.get prog).Comp.typ, C.id))

  | Apx.Comp.Apply (i, e) ->
      begin match elExp' cO cD cG i with
        | (i', (Int.Comp.TypArr (tau2, tau), theta)) ->
            let e' = elExp cO cD cG e (tau2, theta) in
              (Int.Comp.Apply (i', e'), (tau, theta))
        | _ -> raise (Violation "Elaboration Error: Function mismatch")
      end

  | Apx.Comp.CtxApp (i, cPsi) ->
      begin match elExp' cO cD cG i with
        | (i', (Int.Comp.TypCtxPi ((_psi, _sW) , tau), theta)) ->
            let cPsi'  = elDCtx cD cPsi in
            let theta' = Cwhnf.csub_msub cPsi' 1 theta in
            let tau'   = Cwhnf.csub_ctyp cPsi' 1 tau in
              (Int.Comp.CtxApp (i', cPsi') , (tau', theta'))

        | _ -> raise (Violation "Context abstraction mismatch")
      end


  | Apx.Comp.MApp (i, (psihat, tM)) ->
      begin match elExp' cO cD cG i with
        | (i', (Int.Comp.TypPiBox (Int.LF.MDecl(_, tA, cPsi), tau), theta)) ->
            let tM'  = elTerm cD (C.cnormDCtx (cPsi, theta)) tM  (C.cnormTyp (tA, theta), LF.id) in
              (Int.Comp.MApp (i', (psihat, tM')),
               (tau, Int.Comp.MDot(Int.Comp.MObj (psihat, tM'), theta)))
        | _ -> raise (Violation "MLam mismatch")
      end

  | Apx.Comp.Ann (e, tau) ->
      let tau' = elCompTyp cO cD tau in
      let e' = elExp cO cD cG e (tau', C.id) in
        (Int.Comp.Ann (e', tau') , (tau', C.id))


(* We don't check that each box-expression has approximately
 *  the same type as the expression we analyze.
 *
 * TODO double check -bp 
 *)
(* NOTE: Any context variable occurring in delta, psihat, a, psi is bound
 *  in cD !  So delta (and cD') do not contain it!!!! 
 *)
and elBranch cO cD cG branch (tau, theta) = match branch with
  | (Apx.Comp.BranchBox (delta, (psihat, m, Some (a, psi)), e)) ->
      let cD'     = elMCtx delta in
      let cPsi'   = elDCtx (* cO *) cD' psi in

      let tA'     = elTyp  (* cO *) cD' cPsi' a in

      let tM'     = elTerm (* cO *) cD' cPsi' m (tA', LF.id) in

      let _       = Printf.printf "Elaborated pattern: \n %s ; \n %s \n |- \n %s     :     %s \n\n"
        (Pretty.Int.DefaultPrinter.mctxToString cD')
        (Pretty.Int.DefaultPrinter.dctxToString cPsi')
        (Pretty.Int.DefaultPrinter.normalToString tM')
        (Pretty.Int.DefaultPrinter.typToString tA') in

      let _ = recTerm (* cO *) cD' cPsi' (tM', LF.id) (tA', LF.id) in
      let (cD1', cPsi1', (phat', tM1'), tA1') =
        Abstract.abstrPattern cD' cPsi' (psihat, tM') tA' in


      (*      let cD1' = cD' and cPsi1' = cPsi' and tM1' = tM' and tA1' = tA' and phat' = psihat in *)

      let _ = Printf.printf "Reconstructed Pattern : \n  %s ;  \n %s \n |- \n %s      :     %s \n\n"
        (Pretty.Int.DefaultPrinter.mctxToString cD1')
        (Pretty.Int.DefaultPrinter.dctxToString cPsi1')
        (Pretty.Int.DefaultPrinter.normalToString tM1')
        (Pretty.Int.DefaultPrinter.typToString tA1') in

      let n       = Context.length cD1' in
      let cD_i    = Context.append cD cD1' in
      let theta_i = C.mshift theta n in
      let _ = Printf.printf "theta_i = %s \n\n"
        (Pretty.Int.DefaultPrinter.msubToString theta_i) in
      let e'     = elExp cO cD_i cG e (tau, theta_i) in
      let b =         Int.Comp.BranchBox (cD1', (phat', tM1', (tA1', cPsi1')), e') in


      let _ = Printf.printf "Elaborated Branch: \n %s \n\n" (Pretty.Int.DefaultPrinter.branchToString b) in
        b

(*
  | (Apx.Comp.BranchBox (delta, (psihat, r, None), e))  ->
      let cD'     = elMCtx delta in
      let cPsi'   = elDCtx (* cO *) cD' psi in

      let tA'     = elTyp  (* cO *) cD' cPsi' a in

      let tM'     = elTerm (* cO *) cD' cPsi' m (tA', LF.id) in

(*      let sP      = synTerm (* cO *) cD'    *)
      let n       =  Context.length cD' in
      let cD_i    = Context.append cD cD' in
      let theta_i = C.mshift theta n in
      let e'     = elExp cO cD_i cG e (tau, theta_i) in
        Int.Comp.BranchBox (cD', (psihat, tM', (tA', cPsi')), e')


*)

(* ******************************************************************* *)


(* Reconstruction for computations *)
(* First version be identical to type checking computations *)

let rec length cD = match cD with
  | Int.LF.Empty -> 0
  | Int.LF.Dec (cD, _) -> 1 + length cD

let rec lookup cG k = match (cG, k) with
  | (Int.LF.Dec (_cG', (_,  tau)), 1) ->  tau
  | (Int.LF.Dec ( cG', (_, _tau)), k) ->
      lookup cG' (k-1)

let rec split tc d = match (tc, d) with
  | (tc, 0) -> tc
  | (Int.Comp.MDot (_ft, t), d) -> split t (d-1)

let rec mctxToMSub cD = match cD with
  | Int.LF.Empty -> C.id
  | Int.LF.Dec (cD', Int.LF.MDecl(_, tA, cPsi)) ->
      let t     = mctxToMSub cD' in
      let cPsi' = Cwhnf.cnormDCtx (cPsi,t) in
      let tA'   = Cwhnf.cnormTyp (tA, t) in
      let u     = Whnf.newMVar (cPsi' , tA') in
      let phat  = Context.dctxToHat cPsi in
        Int.Comp.MDot(Int.Comp.MObj (phat, Int.LF.Root (Int.LF.MVar (u, LF.id), Int.LF.Nil)) , t)
  | Int.LF.Dec(cD', Int.LF.PDecl(_, tA, cPsi)) ->
      let t    = mctxToMSub cD' in
      let p    = Whnf.newPVar (Cwhnf.cnormDCtx (cPsi,t),  Cwhnf.cnormTyp (tA, t)) in
      let phat = Context.dctxToHat cPsi in
        Int.Comp.MDot (Int.Comp.PObj(phat, Int.LF.PVar(p, LF.id)) , t)

(* extend t1 t2 = t
 *
 * Invariant:
 * If    . |- t1 <= cD1
 *   and . |- t2 <= cD2
 *   and FMV(cD1) intersect FMV(cD2) = {}
 *   (i.e. no modal variable occurring in type declarations in cD1
 *    also occurs in a type declaration of cD2)
 * then
 *       . |- t1,t2 <= cD1, cD2   and t = t1,t2
 *)
let extend t1 t2 =
  let rec ext t2 = match t2 with
    | Int.Comp.MShift 0 -> t1
        (* other cases should be impossible *)
    | Int.Comp.MDot (ft, t) -> Int.Comp.MDot (ft, ext t)
  in ext t2


let rec checkTyp cO cD tau = match tau with
  | Int.Comp.TypBox (tA, cPsi) -> (
      Check.LF.checkDCtx cO cD cPsi;
      Check.LF.checkTyp  cO cD cPsi (tA, LF.id)
    )

  | Int.Comp.TypArr (tau1, tau2) -> (
      checkTyp cO cD tau1;
      checkTyp cO cD tau2
    )

  | Int.Comp.TypCtxPi ((psi_name, schema_cid), tau) ->
      checkTyp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD tau

  | Int.Comp.TypPiBox (cdecl, tau) ->
      checkTyp cO (Int.LF.Dec (cD, cdecl)) tau


(* check cO cD cG e (tau, theta) = ()
 *
 * Invariant:
 *
 * If  cO ; cD ; cG |- e wf-exp
 * and cO ; cD |- theta <= cD'
 * and cO ; cD'|- tau <= c_typ
 * returns ()
 * if  cO ; cD ; cG |- e <= [|t|]tau
 *
 * otherwise exception Error is raised
 *)
let rec checkW cO cD cG e ttau = match (e , ttau) with
  | (Int.Comp.Rec (f, e), (tau, t)) ->
      check cO cD (Int.LF.Dec (cG, (f, Int.Comp.TypClo (tau,t)))) e ttau

  | (Int.Comp.Fun (x, e), (Int.Comp.TypArr (tau1, tau2), t)) ->
      check cO cD (Int.LF.Dec (cG, (x, Int.Comp.TypClo (tau1, t)))) e (tau2, t)

  | (Int.Comp.CtxFun(psi, e) , (Int.Comp.TypCtxPi ((_psi, schema), tau), t)) ->
      check (Int.LF.Dec (cO, Int.LF.CDecl (psi, schema))) cD cG e (tau, t)

  | (Int.Comp.MLam (u, e), (Int.Comp.TypPiBox (Int.LF.MDecl (_u, tA, cPsi), tau), t)) ->
      check cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
        cG e (tau, C.mvar_dot1 t)

  | (Int.Comp.Box (_phat, tM), (Int.Comp.TypBox (tA, cPsi), t)) ->
      Check.LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, LF.id) (C.cnormTyp (tA, t), LF.id)

  | (Int.Comp.Case (e, branches), (tau, t)) ->
      begin match C.cwhnfCTyp (syn cO cD cG e) with
        | (Int.Comp.TypBox (tA, cPsi),  t') ->
            checkBranches cO cD cG branches (C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) (tau, t)
        | _ -> raise (Violation "Case scrutinee not of boxed type")
      end

  | (Int.Comp.Syn e, (tau, t)) ->
      if C.convCTyp (tau,t) (syn cO cD cG e) then
        ()
      else
        raise (Violation "Type mismatch")

and check cO cD cG e (tau, t) =
  checkW cO cD cG e (C.cwhnfCTyp (tau, t))

and syn cO cD cG e = match e with
  | Int.Comp.Var x  -> (lookup cG x, C.id)
      (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD !!! *)

  | Int.Comp.Const prog  -> ((Comp.get prog).Comp.typ, C.id)

  | Int.Comp.Apply (e1, e2) ->
      begin match C.cwhnfCTyp (syn cO cD cG e1) with
        | (Int.Comp.TypArr (tau2, tau), t) -> (
            check cO cD cG e2 (tau2, t);
            (tau, t)
          )
        | _ -> raise (Violation "Function mismatch")
      end
  | Int.Comp.CtxApp (e, cPsi) ->
      begin match C.cwhnfCTyp (syn cO cD cG e) with
        | (Int.Comp.TypCtxPi ((_psi, sW) , tau), t) ->
            let _ = Printf.printf "\n Schema checking omitted \n" in
              (* REVISIT: Sun Jan 11 17:48:52 2009 -bp *)
              (* let tau' =  Cwhnf.csub_ctyp cPsi 1 tau in
                 let t'   = Cwhnf.csub_msub cPsi 1 t in   *)

            let tau1 = Cwhnf.csub_ctyp cPsi 1 (Cwhnf.cnormCTyp (tau,t)) in
              Check.LF.checkSchema cO cD cPsi ((Schema.get sW).Schema.schema);
              (* (tau', t') *)
              (tau1, Cwhnf.id)
        | _ -> raise (Violation "Context abstraction mismatch")
      end
  | Int.Comp.MApp (e, (phat, tM)) ->
      begin match C.cwhnfCTyp (syn cO cD cG e) with
        | (Int.Comp.TypPiBox (Int.LF.MDecl(_, tA, cPsi), tau), t) -> (
            Check.LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, LF.id) (C.cnormTyp (tA, t), LF.id);
            (tau, Int.Comp.MDot(Int.Comp.MObj (phat, tM), t))
          )
        | _ -> raise (Violation "MLam mismatch")
      end

  | (Int.Comp.Ann (e, tau)) -> (
      check cO cD cG e (tau, C.id);
      (tau, C.id)
    )

and checkBranches cO cD cG branches tAbox ttau = match branches with
  | [] -> ()
  | (branch :: branches) ->
      let _ = checkBranch cO cD cG branch tAbox ttau in
        checkBranches cO cD cG branches tAbox ttau

(*  and checkBranch _cO _cD _cG _branch (_tA, _cPsi) (_tau, _t) =
    Printf.printf "WARNING: BRANCH CHECKING NOT IMPLEMENTED!"
*)


and checkBranch cO cD cG branch (tA, cPsi) (tau, t) =
(*    let _ = Printf.printf "BEGIN: Checking branch: \n %s ; \n %s \n |- \n %s \n\n"
         (Pretty.Int.DefaultPrinter.mctxToString (Cwhnf.normMCtx cD))
         (Pretty.Int.DefaultPrinter.gctxToString (Cwhnf.normCtx  cG))
         (Pretty.Int.DefaultPrinter.branchToString branch) in
*)
  match branch with
    | Int.Comp.BranchBox (cD1, (phat, tM1, (tA1, cPsi1)), e1) ->
        let _ = Printf.printf "Checking Pattern Term is well-typed: \n %s ; %s   |-    %s <= %s \n\n"
          (Pretty.Int.DefaultPrinter.mctxToString cD1)
          (Pretty.Int.DefaultPrinter.dctxToString cPsi1)
          (Pretty.Int.DefaultPrinter.normalToString tM1)
          (Pretty.Int.DefaultPrinter.typToString tA1) in


        let _ = Check.LF.check cO cD1 cPsi1 (tM1, LF.id) (tA1, LF.id) in
          (* This is like a double-check here, since reconstruction was done during elaboration of branch *)


        let _ = Printf.printf "DONE: Pattern Term  \n %s ; %s   |-    %s <= %s  is well-typed.\n\n"
          (Pretty.Int.DefaultPrinter.mctxToString cD1)
          (Pretty.Int.DefaultPrinter.dctxToString cPsi1)
          (Pretty.Int.DefaultPrinter.normalToString tM1)
          (Pretty.Int.DefaultPrinter.typToString tA1) in

        let d1 = length cD1 in
        let _d  = length cD in
        let t1 = mctxToMSub cD1 in   (* {cD1} |- t1 <= cD1 *)
        let t' = mctxToMSub cD in    (* {cD}  |- t' <= cD *)
        let tc = extend t' t1 in     (* {cD1, cD} |- t', t1 <= cD, cD1 *)

        let  _   = Printf.printf "Type of scrutinee: %s   |-    %s \n\n Type of Pattern in branch: %s   |-  %s \n\n"
          (Pretty.Int.DefaultPrinter.dctxToString cPsi)
          (Pretty.Int.DefaultPrinter.typToString tA)
          (Pretty.Int.DefaultPrinter.dctxToString cPsi1)
          (Pretty.Int.DefaultPrinter.typToString tA1) in

        let _    = Unify.unifyDCtx (C.cnormDCtx (cPsi, t')) (C.cnormDCtx (cPsi1, tc)) in
        let _    = Unify.unifyTyp (phat, (C.cnormTyp (tA, t'), LF.id), (C.cnormTyp (tA1, tc), LF.id))  in

(*      let  _   = Printf.printf "Resulting msub from unifying type annotations in branches: \n %s\n\n"
        (Pretty.Int.DefaultPrinter.msubToString tc) in
*)
        let (tc', cD1'') = Abstract.abstractMSub tc in  (* cD1' |- tc' <= cD, cD1 *)


(*      let cD1_n  = (Cwhnf.normMCtx cD1') in  *)

(*      let  _   = Printf.printf "Resulting msub after abstraction: \n %s   |-   %s    <=  %s \n\n"
         (Pretty.Int.DefaultPrinter.mctxToString cD1_n)
        (Pretty.Int.DefaultPrinter.msubToString tc')
         (Pretty.Int.DefaultPrinter.mctxToString (Context.append cD cD1))  in
*)
        let t'' = split tc' d1 in (* cD1' |- t'' <= cD  suffix *)
        let cG1 = C.cwhnfCtx (cG, t'') in
(*      let cGn = (Cwhnf.normCtx cG1) in *)
        let e1' = C.cnormExp (e1, tc') in

        let tau' = (tau, C.mcomp t'' t)  in
(*      let taun = (C.cnormCTyp tau') in  *)

(*      let _ = Printf.printf "\n Check branch  \n %s ; \n %s  \n   |-   \n %s \n has type: %s  .\n\n"
         (Pretty.Int.DefaultPrinter.mctxToString (Cwhnf.normMCtx cD1_n))
         (Pretty.Int.DefaultPrinter.gctxToString cGn)
         (Pretty.Int.DefaultPrinter.expChkToString e1')
         (Pretty.Int.DefaultPrinter.compTypToString  taun) in
*)
      (* NOTE: cnormCtx and cnormExp not implemented
         -- should handle computation-level expressions in whnf so we don't need to normalize here -bp
      *)
          check cO cD1'' cG1 e1' tau'

(* ------------------------------------------------------------------- *)

let recSgnDecl d = match d with
  | Ext.Sgn.Typ (_, a, extK)   ->
      let apxK     = index_kind (CVar.create ()) (BVar.create ()) extK in
      let _        = FVar.clear () in
      let tK       = elKind Int.LF.Null apxK in
      let _        = solve_fvarCnstr Int.LF.Empty !fvar_cnstr in
      let _        = reset_fvarCnstr () in
      let _        = recKind Int.LF.Empty Int.LF.Null (tK, LF.id) in
      let (tK', i) = Abstract.abstrKind tK in
      (* let _        = Printf.printf "\n Reconstruction (wih abstraction) of constant %s \n %s \n\n" a.string_of_name
        (Pretty.Int.DefaultPrinter.kindToString tK') in *)
      let _        = Check.LF.checkKind Int.LF.Empty Int.LF.Empty Int.LF.Null tK' in
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" a.string_of_name  in
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        (* why does Term.add return a' ? -bp *)
        (* because (a : name) and (a' : cid_typ) *)
        Int.Sgn.Typ (a', tK')

  | Ext.Sgn.Const (_, c, extT) ->
      let apxT     = index_typ (CVar.create ()) (BVar.create ()) extT in
      let _        = Printf.printf "\n Reconstruct constant : %s  \n" c.string_of_name  in
      let _        = FVar.clear () in
      let tA       = elTyp Int.LF.Empty Int.LF.Null apxT in
      let _        = solve_fvarCnstr Int.LF.Empty !fvar_cnstr in
      let _        = reset_fvarCnstr () in
      (* let _        = Printf.printf "\n Elaboration of constant %s \n : %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))) in   *)
      let cD       = Int.LF.Empty in
      let _        = recTyp cD Int.LF.Null (tA, LF.id) in
      (* let _        = Printf.printf "\n Reconstruction (without abstraction) of constant %s \n %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))) in  *)

      let (tA', i) = Abstract.abstrTyp tA in
      (* let _        = Printf.printf "\n Reconstruction (with abstraction) of constant %s \n %s \n\n" c.string_of_name
         (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA', LF.id))) in *)
      let _        = Check.LF.checkTyp Int.LF.Empty Int.LF.Empty Int.LF.Null (tA', LF.id) in
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" c.string_of_name  in
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
        Int.Sgn.Const (c', tA')


  | Ext.Sgn.Schema (_, g, schema) ->
      let apx_schema = index_schema schema in
      let _          = Printf.printf "\n Reconstruct schema : %s  \n" g.string_of_name  in
      let sW         = elSchema apx_schema in
(*      let _        = Printf.printf "\n Elaboration of schema %s \n : %s \n\n" g.string_of_name
                        (Pretty.Int.DefaultPrinter.schemaToString sW) in   *)
      let cPsi       = Int.LF.Null in
      let cD         = Int.LF.Empty in
      let cO         = Int.LF.Empty in
      let _          = Check.LF.checkSchema cO cD cPsi sW in
      let _          = Printf.printf "\n TYPE CHECK for schema : %s  successful! \n" g.string_of_name  in
      let g'         = Schema.add (Schema.mk_entry g sW) in
        Int.Sgn.Schema (g', sW)


  | Ext.Sgn.Rec (_, f, tau, e) ->
      let apx_tau = index_comptyp (CVar.create ()) (CVar.create ()) tau in
      let _       = Printf.printf "\n Reconstruct function : %s  \n" f.string_of_name  in
      let cD      = Int.LF.Empty in
      let cO      = Int.LF.Empty in
      let tau'    = elCompTyp cO cD apx_tau in
(*      let _        = Printf.printf "\n Elaboration of program type %s \n : %s \n\n" f.string_of_name
                        (Pretty.Int.DefaultPrinter.compTypToString tau') in  *)
      let _       = Check.Comp.checkTyp cO cD tau' in
      let _       = Printf.printf "\n Checking computation type %s successful ! \n\n "
        (Pretty.Int.DefaultPrinter.compTypToString tau') in

      let vars'   = Var.extend  (Var.create ()) (Var.mk_entry f) in
      let apx_e   = index_exp (CVar.create ()) (CVar.create ()) vars' e in
      let _       = Printf.printf "\n Indexing  computation done ! \n\n " in
      let cG      = Int.LF.Dec(Int.LF.Empty, (f, tau'))  in
      let _       = Printf.printf "\n Starting elaboration of computation ! \n\n " in
      let e'      = elExp cO cD cG apx_e (tau', C.id) in
      let _       = Printf.printf "\n Starting elaboration of computation ! \n\n " in
      let _       = Printf.printf "\n Elaboration of program %s \n : %s \n %s \n" f.string_of_name
        (Pretty.Int.DefaultPrinter.compTypToString tau')
        (Pretty.Int.DefaultPrinter.expChkToString e') in

      (* let _       = check  cO cD cG e' (tau', C.id) in  *)
      let _       = Check.Comp.check cO cD  cG e' (tau', C.id) in
      let _       = Printf.printf "\n TYPE CHECK for program : %s  successful! \n\n" f.string_of_name  in
      let f'      = Comp.add (Comp.mk_entry f tau' 0 e') in
        Int.Sgn.Rec (f', tau', e')
