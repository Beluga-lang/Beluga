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

module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

exception NotImplemented
exception Error of error

exception Violation of string

type reconType = PiboxRecon | PiRecon


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

  | Ext.LF.Hole _ -> Apx.LF.Hole

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
      begin try 
        let offset = CVar.index_of_name ctx_vars psi_name in
          (Apx.LF.CtxVar (Apx.LF.CtxOffset offset) , bvars)
      with Not_found ->  
        (Apx.LF.CtxVar (Apx.LF.CtxName psi_name) , bvars)
      end 
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
              ((Some (Int.LF.CtxOffset ctx_var), d) , bvars)
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
let rec index_elements el_list = List.map index_el el_list

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
  | (Ext.Comp.BranchBox(_, delta, (psi1, m, Some (a, psi)), e)) ->
    let (delta', cvars')  = index_mctx ctx_vars (CVar.create()) delta in 
(*    let (psihat', bvars) = index_psihat ctx_vars psihat in  *)
    let (psi1', bvars)    = index_dctx ctx_vars cvars' (BVar.create ()) psi1 in 
    let m'               = index_term cvars' bvars m in 
    let (psi', _bvars)   = index_dctx ctx_vars cvars' (BVar.create ()) psi in 
    (* _bvars = bvars *)
    let a'               = index_typ cvars' bvars a in 
    let cvars_all        = CVar.append cvars' cvars in 
    let e'               = index_exp ctx_vars cvars_all vars e in 
      Apx.Comp.BranchBox (delta', (psi1', m', Some (a', psi')), e')


  | (Ext.Comp.BranchBox(_, delta, (psi, m, None), e)) ->
      let (delta', cvars')  = index_mctx ctx_vars (CVar.create()) delta in
      (* let (psihat', bvars) = index_psihat ctx_vars psihat in *)
      let (psi1', bvars)    = index_dctx ctx_vars cvars' (BVar.create ()) psi in 
      let m'               = index_term cvars' bvars m in
      let cvars_all        = CVar.append cvars' cvars in 
      let e'               = index_exp ctx_vars cvars_all vars e in
        Apx.Comp.BranchBox (delta', (psi1', m', None), e')


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
            (b, l+1)
        else
          (false, 0)

    | _ -> (false, 0)
  in
    patSpine' [] spine

let rec mkShift recT cPsi = match recT with
  | PiboxRecon -> Int.LF.Shift(Int.LF.NoCtxShift, 0)
  | PiRecon -> 
      let (None, d) = Context.dctxToHat cPsi in 
        Int.LF.Shift(Int.LF.NoCtxShift, d)

(* etaExpandMV moved to whnf.ml -jd 2009-02-01 *)

(* isPatSub s = bool *)
let rec isPatSub s = match s with
  | Apx.LF.Id -> 
      true

  | Apx.LF.EmptySub -> 
      true

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar _k), s) ->
      isPatSub s

  | Apx.LF.Dot (Apx.LF.Head _, _s) -> 
      (Printf.printf "Check apxSub is patSub: FAILED \n Encountered Head other than BVar!\n";
       false)

  | Apx.LF.Dot (Apx.LF.Obj  _, _s) -> 
      (Printf.printf "Check apxSub is patSub: FAILED\n Encountered Obj !\n";
       false)

(*  | _ -> 
      false
*)
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
let rec synDom cPsi s = begin match s with
  | Apx.LF.Id ->
      begin match  Context.dctxToHat cPsi  with
        |  (Some psi, d) -> 
            (* (Int.LF.CtxVar psi, Int.LF.Shift (Some psi, d)) *)
             (Int.LF.CtxVar psi, Int.LF.Shift (Int.LF.NoCtxShift, d))

        |  (None, _d)     -> 
             raise (Violation "Identity substitution should only be used with context variables")
      end 

  | Apx.LF.EmptySub -> 
      begin match Context.dctxToHat cPsi  with
        | (Some psi, d) -> 
            (Int.LF.Null , Int.LF.Shift (Int.LF.CtxShift psi, d))
        |  (None, d) ->  (Int.LF.Null , Int.LF.Shift (Int.LF.NoCtxShift, d))
      end
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
(*         | _ -> raise (Violation "Undefined bound variable \n") *)
      end
  | _ -> raise (Violation "Encountered non-pattern substitution")

end 




(* elKind  cPsi (k,s) = K *)
let rec elKind cPsi k = match k with
  | Apx.LF.Typ ->
      Int.LF.Typ

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let tA    = elTyp PiRecon Int.LF.Empty cPsi a in
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
and elTyp recT cD cPsi a = match a with
  | Apx.LF.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let s'  = mkShift recT cPsi in 
      let tS = elKSpineI recT cD cPsi s i (tK, s') in
        Int.LF.Atom (a, tS)

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let tA    = elTyp recT cD cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp recT cD cPsi' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB)

(* elTerm recT  cD cPsi m sA = M
 * elTerm recTW cD cPsi m sA = M  where sA = (A,s) is in whnf
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
and elTerm recT cD cPsi m sA = elTermW recT cD cPsi m (Whnf.whnfTyp sA)

and elTermW recT cD cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (Int.LF.TypDecl (_x, _tA) as decl, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm recT cD cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam (x, tM)

  | (Apx.LF.Root (_h, _spine), (Int.LF.Atom _ , _s)) -> 
      elTerm' recT cD cPsi m  sA

and elTerm' recT cD cPsi r sP = match r with 
  | Apx.LF.Root (Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let s  = mkShift recT cPsi in 
      let tS = elSpineI recT cD cPsi spine i (tA, s)  in 
      let tR =  Int.LF.Root (Int.LF.Const c, tS) in 
        tR

  | Apx.LF.Root (Apx.LF.BVar x, spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine recT cD cPsi spine (tA, LF.id)  in
        Int.LF.Root (Int.LF.BVar x, tS)

  | Apx.LF.Root(Apx.LF.Hole, spine) -> 
      let (patternSpine, _l) = patSpine spine in
        if patternSpine then
          let sshift = mkShift recT cPsi in 
          let (tS, tA) = elSpineSynth cD cPsi spine sshift sP in
            (* For Beluga type reconstruction to succeed, we must have
             *  cPsi |- tA <= type  and cPsi |- tS : tA <= [s]tP
             *  This will be enforced during abstraction.
             *)
            (* For LF type reconstruction to succeed, we must have
             *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
             *  This will be enforced during abstraction.
             *)
            (* We could try to create u already lowered *)
          let u =  Whnf.newMVar (cPsi, tA) in 
            Int.LF.Root(Int.LF.MVar(u, LF.id), tS)              
        else 
          raise NotImplemented

  | Apx.LF.Root (Apx.LF.MVar (u, s'), spine) ->
      let (tA, cPhi) = Cwhnf.mctxMDec cD u in
      let s'' = elSub recT cD cPsi s' cPhi in
      let tS = elSpine recT cD cPsi spine (tA, s'')  in 
          Int.LF.Root (Int.LF.MVar(Int.LF.Offset u, s''), tS)

  | Apx.LF.Root (Apx.LF.PVar (p,s'), spine) ->
      let (tA, cPhi) = Cwhnf.mctxPDec cD p in
      let s'' = elSub recT cD cPsi s' cPhi in
      let tS = elSpine recT cD cPsi spine (tA, s'')  in
        Int.LF.Root (Int.LF.PVar (Int.LF.Offset p, s''), tS)

  | (Apx.LF.Root (Apx.LF.FVar x, spine) as m) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
           *  
           *  . |- tA <= type
           *  This will be enforced during abstraction *)
        let s = mkShift recT cPsi in 
        let tS = elSpine recT cD cPsi spine (tA, s)  in
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        let (patternSpine, _l) = patSpine spine in
          if patternSpine then
        let s = mkShift recT cPsi in 
        let (tS, tA) = elSpineSynth cD cPsi spine s sP in
            (* For type reconstruction to succeed, we must have
             *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
             *  This will be enforced during abstraction.
             *)
          let _        = FVar.add x tA in
            Int.LF.Root (Int.LF.FVar x, tS)
        else
          let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
            (add_fvarCnstr (m, v) ;
             Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)
            )

      end

  (* We only allow free meta-variables of atomic type *)
  | (Apx.LF.Root (Apx.LF.FMVar (u, s), Apx.LF.Nil) as m) -> 
      begin try 
        (* For named free meta-variables which may occur in branches of case-expressions;
         * these named free meta-variables may be bound by the pattern.
         *)
        let (offset, (_tP, cPhi)) = Cwhnf.mctxMVarPos cD u  in 

        let s'' = elSub recT cD cPsi s cPhi in  
          (* We do not check here that tP approx. [s']tP' -- 
             this check is delayed to reconstruction *)        
          Int.LF.Root (Int.LF.MVar (Int.LF.Offset offset, s''), Int.LF.Nil) 

      with Cwhnf.Fmvar_not_found -> 
      begin try
        let (_tP, cPhi) = FMVar.get u in
          (* For type reconstruction to succeed, we must have 
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on 
           * meta-variables in cD. This will be enforced during abstraction *)
      let s'' = elSub recT cD cPsi s cPhi in  
          (* We do not check here that tP approx. [s']tP' -- 
           * this check is delayed to reconstruction *)        
          Int.LF.Root (Int.LF.FMVar (u, s''), Int.LF.Nil) 

      with Not_found ->
          if isPatSub s then
            (* 1) given cPsi and s synthesize the domain cPhi
             * 2) [s]^-1 ([s']tP) is the type of u
             *)

            let (cPhi, s'') = synDom cPsi s in
            let tP   = Int.LF.TClo( Int.LF.TClo sP, Substitution.LF.invert s'') in
              (* For type reconstruction to succeed, we must have
               * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
               * This will be enforced during abstraction.
               *)
            let _   = FMVar.add u (tP, cPhi) in
              Int.LF.Root (Int.LF.FMVar (u, s''), Int.LF.Nil)
          else
            let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
              add_fcvarCnstr (m, v);
              Int.LF.Root (Int.LF.MVar (v, LF.id), Int.LF.Nil)
        end
      end


  | (Apx.LF.Root (Apx.LF.FPVar (p, s), spine) as m) -> 
      begin try 
        (* For named free parameter-variables which may occur in branches of case-expressions;
         * these named free parameter-variables may be bound by the pattern.
         *)
        let (offset, (tA, cPhi)) = Cwhnf.mctxPVarPos cD p  in 

        let s'' = elSub recT cD cPsi s cPhi in  
          (* We do not check here that tP approx. [s']tP' -- 
             this check is delayed to reconstruction *)        
          Int.LF.Root (Int.LF.PVar (Int.LF.Offset offset, s''), elSpine recT cD cPsi spine (tA, s'')) 

      with Cwhnf.Fmvar_not_found -> 
      begin try
        let (tA, cPhi) = FPVar.get p in
          (* For type reconstruction to succeed, we must have 
           *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on 
           * meta-variables in cD. This will be enforced during abstraction *)

      let s'' = elSub recT cD cPsi s cPhi in  
          (* We do not check here that tP approx. [s']tP' -- 
           * this check is delayed to reconstruction *)        
          Int.LF.Root (Int.LF.FPVar (p, s''), elSpine recT cD cPsi spine (tA, s'')) 

      with Not_found ->
        begin match (spine, isPatSub s) with 
          | (Apx.LF.Nil, true) -> 
            (* 1) given cPsi and s synthesize the domain cPhi
             * 2) [s]^-1 ([s']tP) is the type of u
             *)
            let (cPhi, s'') = synDom cPsi s in
            let si         = Substitution.LF.invert s'' in 
            let tP   = Int.LF.TClo( Int.LF.TClo sP, si) in
              (* For type reconstruction to succeed, we must have
               * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
               * This will be enforced during abstraction.
               *)
            let _   = FPVar.add p (tP, cPhi) in
              Int.LF.Root (Int.LF.FPVar (p, s''), Int.LF.Nil)                

        | (Apx.LF.Nil, false) -> 
            let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
              add_fcvarCnstr (m, q);
              Int.LF.Root (Int.LF.PVar (q, LF.id), Int.LF.Nil)

        | ( _ , _ ) -> raise NotImplemented
        end
      end
      end



  (* TODO find a way to postpone type mismatch to reconstruction step *)

(* elSub recT cD cPsi s cPhi = s'
 *
 * We elaborate the substitution s, but we do not check if it is
 * approximately well-typed.
 *)
and elSub recT cD cPsi s cPhi = match (s, cPhi) with
  | (Apx.LF.EmptySub, Int.LF.Null )  ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) -> Int.LF.Shift(Int.LF.CtxShift psi, d)
        | (None, d)     -> Int.LF.Shift(Int.LF.NoCtxShift, d)
      end

  | (Apx.LF.Id , Int.LF.CtxVar phi)  ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) -> 
            if psi = phi then 
              Int.LF.Shift(Int.LF.NoCtxShift, d) 
            else
              raise (Violation "Id must be associated with same ctxvar")
        | _ -> raise (Violation "Id must be associated with ctxvar")      
      end

  | (Apx.LF.Dot (Apx.LF.Head h, s), Int.LF.DDec (cPhi', _decl)) ->
      (* NOTE: if decl = x:A, and cPsi(h) = A' s.t. A =/= A'
       *       we will fail during reconstruction / type checking 
       *)
        Int.LF.Dot (Int.LF.Head (elHead recT cD cPsi h), elSub recT cD cPsi s cPhi')

  | (Apx.LF.Dot (Apx.LF.Obj m, s), Int.LF.DDec (cPhi', Int.LF.TypDecl(_, tA))) ->
      let _ = (print_string  "elSub: Obj m ... \n" ; flush_all ()) in 
      let s' = elSub recT cD cPsi s cPhi' in
      let m' = elTerm recT cD cPsi m (tA, s') in
        Int.LF.Dot (Int.LF.Obj m', s')

and elHead recT cD cPsi h   = match h with
  | Apx.LF.BVar x -> 
      Int.LF.BVar x

  | Apx.LF.Const c -> 
      Int.LF.Const c

  | Apx.LF.MVar (u,s) ->
      let (_tA, cPhi) = Cwhnf.mctxMDec cD u in
        Int.LF.MVar (Int.LF.Offset u, elSub recT cD cPsi s cPhi)

  | Apx.LF.PVar (p,s) ->
      let (_tA, cPhi) = Cwhnf.mctxPDec cD p in
        Int.LF.PVar (Int.LF.Offset p, elSub recT cD cPsi s cPhi)

  | Apx.LF.FVar x -> 
      Int.LF.FVar x

  | Apx.LF.FMVar (u,s) ->
        let (offset, (_tP, cPhi)) = Cwhnf.mctxMVarPos cD u  in 
        Int.LF.MVar (Int.LF.Offset offset, elSub recT cD cPsi s cPhi)

  | Apx.LF.FPVar (p,s) ->
      let (offset, (_tA, cPhi)) = Cwhnf.mctxPVarPos cD p  in        
        Int.LF.PVar (Int.LF.Offset offset, elSub recT cD cPsi s cPhi)


(* elSpineI  recT cD cPsi spine i sA sP  = S
 * elSpineIW recT cD cPsi spine i sA sP  = S
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
and elSpineI recT cD cPsi spine i sA =
  elSpineIW recT cD cPsi spine i (Whnf.whnfTyp sA)

and elSpineIW recT cD cPsi spine i sA =
  if i = 0 then
    let tS' = elSpine recT cD cPsi spine sA in 
      tS'
  else
    match (sA, recT) with
      | ((Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s), PiRecon) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           * 
           * tN = u[s']  and u::A'[.]
           * 
           * s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
           *   and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)           
           *)
          let (_, d) = Context.dctxToHat cPsi in 

          let tN     = Whnf.etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift(Int.LF.NoCtxShift, d)) in

          let spine' = elSpineI recT cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

      | ((Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s), PiboxRecon) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           * 
           * tN = u[s']  and u::P[Psi, x1:A1,....xn:An]  and A = Pi x1:A1 ... Pi xn:An.P
           * 
           * s.t.  cPsi |- \x1...\xn. u[id] => [id]A  where cPsi |- id : cPsi
           *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in

          let spine' = elSpineI recT cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')
      (* other cases impossible by (soundness?) of abstraction *)

(* elSpine recT cD cPsi spine sA = S
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
and elSpine recT cD cPsi spine sA =
  elSpineW recT cD cPsi spine (Whnf.whnfTyp sA)

and elSpineW recT cD cPsi spine sA = match (spine, sA) with
  | (Apx.LF.Nil, (_tP , _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm recT cD cPsi m (tA, s) in
      let tS = elSpine recT cD cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      raise (Error ExpAppNotFun) (* TODO postpone to reconstruction *)

(* see invariant for elSpineI *)
and elKSpineI recT cD cPsi spine i sK =
  if  i = 0 then
    elKSpine recT cD cPsi spine sK
  else
    match sK with
      | (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s) ->
          let sshift = mkShift recT cPsi in 
          let tN     = Whnf.etaExpandMV Int.LF.Null (tA,s) sshift in
          let spine' = elKSpineI recT cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

(* other cases impossible by (soundness?) of abstraction *)

(* see invariant for elSpine *)
and elKSpine recT cD cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (_tK, _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm recT  cD cPsi m (tA, s) in
      let tS = elKSpine recT cD cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
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

   It would be more convenient if ctx were
   a dctx, since then we can do simple type-checking
   of the rest of the typrec. -bp

   TODO double check -bp
   *)

let rec projectCtxIntoDctx = function
  |  Int.LF.Empty -> Int.LF.Null
  |  Int.LF.Dec (rest, last) -> Int.LF.DDec (projectCtxIntoDctx rest, last)

let rec elTypDeclCtx cD cPsi = function
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (ctx, Apx.LF.TypDecl(name, typ)) ->
      let ctx'    = elTypDeclCtx cD cPsi ctx in
      let typDecl' = Int.LF.TypDecl(name, elTyp PiRecon cD cPsi typ) in
        Int.LF.Dec (ctx', typDecl')

 let rec elSchElem (Apx.LF.SchElem (ctx, Apx.LF.SigmaDecl (name, typRec))) =
   let cD = Int.LF.Empty in
   let el_ctx = elTypDeclCtx cD Int.LF.Null in
   let el_typ ctx = elTyp PiRecon cD (projectCtxIntoDctx ctx) in
   let rec elTypRec ctx = function
     | Apx.LF.SigmaLast a ->
         let ctx' = el_ctx ctx in
           Int.LF.SigmaLast (el_typ ctx' a)
     | Apx.LF.SigmaElem (name, tA, typRec) ->
         let ctx' = el_ctx ctx in
           Int.LF.SigmaElem(name, el_typ ctx' tA, elTypRec ctx typRec)
   in
     Int.LF.SchElem(el_ctx ctx, Int.LF.SigmaDecl (name, elTypRec ctx typRec))

let rec elSchema (Apx.LF.Schema el_list) =
   Int.LF.Schema (List.map elSchElem el_list)

let rec elDCtx recT cD psi = match psi with
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) -> Int.LF.CtxVar (Int.LF.CtxOffset offset)
  | Apx.LF.CtxVar (Apx.LF.CtxName psi)      -> Int.LF.CtxVar (Int.LF.CtxName psi)

  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtx recT cD psi' in
      let tA   = elTyp recT cD cPsi a in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))


let rec elCDecl recT cD cdecl = match cdecl with
  | Apx.LF.MDecl (u, a, psi) ->
      let cPsi = elDCtx recT cD psi in
      let tA   = elTyp recT cD cPsi a in
        Int.LF.MDecl (u, tA, cPsi)
  | Apx.LF.PDecl (u, a, psi) ->
      let cPsi = elDCtx recT cD psi in
      let tA   = elTyp recT cD cPsi a in
        Int.LF.PDecl (u, tA, cPsi)


let rec elMCtx recT delta = match delta with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (delta, cdec) ->
      let cD    = elMCtx recT delta in
      let cdec' = elCDecl recT cD cdec in
        Int.LF.Dec (cD, cdec')


(* ******************************************************************* *)
(* Solve free variable constraints *) 

let rec solve_fvarCnstr recT cD cnstr = match cnstr with  
  | []  -> ()  
  | ((Apx.LF.Root (Apx.LF.FVar x, spine) , Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
           *  . |- tA <= type
           *  This will be enforced during abstraction.
           *)
        let sshift = mkShift recT cPsi in 

        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let tS = elSpine recT cD cPsi spine (tA, sshift) in
          (r := Some (Int.LF.Root (Int.LF.FVar x, tS));
           solve_fvarCnstr recT cD cnstrs
          )
     with Not_found ->
       raise (Error LeftoverConstraints) 
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
 *  recT  cD cPsi (A,s) = A'
 *)

let rec recTerm recT cD cPsi sM sA = recTermW recT cD cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW recT cD cPsi sM sA = match (sM, sA) with
  | ((Int.LF.Lam (_, tM), s'), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
        recTerm recT cD cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)


  | ((Int.LF.Root (_ , _ ) , _) as sR , (Int.LF.Atom (_ , _ ), _ )) -> 
      (let sP' = synTerm recT cD cPsi sR  in 
        begin
          try 
            Unify.unifyTyp cD (Context.dctxToHat cPsi, sP', sA) 
          with _ -> (Printf.printf "Non unifiable:  \n %s    =/= \n %s \n \n" 
                                   (P.typToString (Whnf.normTyp sP')) 
                                   (P.typToString (Whnf.normTyp sA));
                                 raise (Error (TypMismatch (cPsi, sA, sP'))))
        end)
  | _ ->
      (Printf.printf "Ill Typed\n";
       Printf.printf "Expected: \n %s  \n |- \n %s     :     %s \n\n"
         (P.dctxToString cPsi) (P.normalToString (Whnf.norm sM)) (P.typToString (Whnf.normTyp sA))  ;
      raise (Error (IllTyped (cPsi, sM, sA))))

(* synTerm cD cPsi sR = sP *)
and synTerm recT cD cPsi sR = synTermW recT cD cPsi (Whnf.whnf sR)

and synTermW recT cD cPsi sR = match sR with
  | (Int.LF.Root (Int.LF.Const c, tS), s') ->
      let tA = (Term.get c).Term.typ in

      let sshift = begin match recT with 
                    | PiboxRecon -> Int.LF.Shift(Int.LF.NoCtxShift, 0)           
                    | PiRecon -> 
                        let (_, d) = Context.dctxToHat cPsi in 
                      Int.LF.Shift(Int.LF.NoCtxShift, d)                     
                   end 
      in 
        synSpine recT cD cPsi (tS, s') (tA, sshift)

  | (Int.LF.Root (Int.LF.BVar x, tS), s') ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in 
        synSpine recT cD cPsi (tS, s') (tA, LF.id)

  | (Int.LF.Root (Int.LF.MVar (Int.LF.Inst (_r, cPhi, tP', _cnstr), t), _tS), s') ->
      (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
      (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in       
        recSub recT cD cPsi s1 cPhi;
        (tP', s1)

  | (Int.LF.Root (Int.LF.MVar (Int.LF.Offset u, t), _tS), s') ->
      (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
      (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in
      let (tP', cPsi') = Cwhnf.mctxMDec cD u in        
        recSub recT cD cPsi s1 cPsi';
        (tP', s1)

  | (Int.LF.Root (Int.LF.FMVar (u, t), _tS), s') ->
      (* By invariant of whnf: tS = Nil *)
      let s1 = (LF.comp t s') in
      let (tP', cPhi) = FMVar.get u in
        (recSub recT cD cPsi s1 cPhi 
        ; (tP', s1)
        )

  | (Int.LF.Root (Int.LF.FPVar (p, t), tS), s') ->
      let s1 = (LF.comp t s') in
      let (tA', cPhi) = FPVar.get p in
      (* cPsi |- t : cPhi *)
        recSub recT cD cPsi s1 cPhi;
        synSpine recT cD cPsi (tS, s') (tA',t)    

  | (Int.LF.Root (Int.LF.PVar (Int.LF.Offset p, t), tS), s') ->
      let s1 = (LF.comp t s') in
      let (tA, cPsi') = Cwhnf.mctxPDec cD p in
        recSub recT cD cPsi s1 cPsi';
        synSpine recT cD cPsi (tS, s') (tA, t)


  | (Int.LF.Root (Int.LF.FVar x, tS), s') ->
      (* x is in eta-expanded form and tA is closed
       * type of FVar x : A[cPsi'] and FVar x should be
       * associated with a substitution, since tA is not always
       * closed.
       *
       * by invariant of whnf: s'  id
       * 
       * This only applies to LF reconstruction
       *)
      let tA = FVar.get x in
      let (None, d) = Context.dctxToHat cPsi in 
        synSpine recT cD cPsi (tS, s') (tA, Int.LF.Shift(Int.LF.NoCtxShift, d))

and synSpine recT cD cPsi sS sA =
  synSpineW recT cD cPsi sS (Whnf.whnfTyp sA)

and synSpineW recT cD cPsi sS sA = match (sS, sA) with
  | ((Int.LF.Nil, _s), sP') ->
      sP'

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) -> (
      let _ = recTerm recT cD cPsi (tM, s') (tA, s) in
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
        synSpine recT cD cPsi (tS, s') (tB, Int.LF.Dot (Int.LF.Obj (Int.LF.Clo (tM,s')), s))
    )

  | ((Int.LF.SClo (tS, s), s'), sA) ->
      synSpine recT cD cPsi (tS, LF.comp s s') sA


and recSub recT cD cPsi s cPhi = match (cPsi, s, cPhi) with
(*  | (Int.LF.Shift (_, _n), _cPhi) ->
      (* We may need to expand cPhi further if n =/= 0 *)
      ()
*)
    | (Int.LF.Null, Int.LF.Shift (Int.LF.NoCtxShift, 0), Int.LF.Null)  -> () 

    | (Int.LF.CtxVar psi, Int.LF.Shift (Int.LF.NoCtxShift, 0), Int.LF.CtxVar psi')  ->
        if psi = psi' then  
          ()
        else raise (Violation "Context variable mismatch") 


    | (Int.LF.CtxVar psi, Int.LF.Shift (Int.LF.CtxShift psi', 0), Int.LF.Null)  ->
        if psi = psi' then  
          ()
        else raise (Violation "Context variable mismatch") 

    | (Int.LF.Null, Int.LF.Shift (Int.LF.NegCtxShift psi, 0), Int.LF.CtxVar psi')  -> 
        if psi = psi' then () else 
          raise (Violation "Substitution illtyped – negative shift on CtxVar")

    | (Int.LF.DDec (cPsi, _tX), Int.LF.Shift (psi, k), Int.LF.Null)   -> 
        if k > 0
        then recSub recT cD cPsi (Int.LF.Shift (psi, k - 1)) Int.LF.Null
        else raise (Violation "Substitution illtyped")

    | (Int.LF.DDec (cPsi, _tX), Int.LF.Shift (phi, k), Int.LF.CtxVar psi)   ->
        if k > 0
        then recSub recT cD cPsi (Int.LF.Shift (phi, k - 1)) (Int.LF.CtxVar psi) 
        else raise (Violation ("Substitution illtyped: k = %s" ^ (string_of_int k)))
                      (* (SubIllTyped) *)

    | (cPsi', Int.LF.Shift (psi, k), cPsi)              ->
        recSub recT cD cPsi' (Int.LF.Dot (Int.LF.Head (Int.LF.BVar (k + 1)), Int.LF.Shift (psi, k + 1))) cPsi 


    | (cPsi, Int.LF.Dot (Int.LF.Head Int.LF.BVar x, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) ->
        let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
          recSub recT cD cPsi s cPhi;
          Unify.unifyTyp cD(Context.dctxToHat cPsi, (tA', LF.id), (tA, s))
            
            
    | (cPsi, Int.LF.Dot (Int.LF.Obj tM, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) -> (
        recSub  recT cD cPsi s cPhi;
        recTerm recT cD cPsi (tM, LF.id) (tA, s)
      )

    | (_cPsi, Int.LF.Dot (Int.LF.Undef, _s), _) ->
        raise (Error LeftoverUndef)

    | _ -> raise (Violation "Reconstruction of substitution undefined")

  (* needs other cases for Head(h) where h = MVar, Const, etc. -bp *)

let rec recKSpine recT cD cPsi sS sK = match (sS, sK) with
  | ((Int.LF.Nil, _s), (Int.LF.Typ, _s')) ->
      ()

  | ((Int.LF.Nil, _s), _) ->
      raise (Error KindMismatch)

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) -> (
      recTerm   recT cD cPsi (tM, s') (tA, s);
      recKSpine recT cD cPsi (tS, s') (tK, Int.LF.Dot (Int.LF.Obj tM, s))
    )

  (* TODO confirm this is necessary, instead of having recKSpineW *)
  | ((Int.LF.SClo (tS, s),  s'), sK) ->
      recKSpine recT cD cPsi (tS, LF.comp s s') sK

  | ((Int.LF.App _, _s), (Int.LF.Typ, _s')) ->
      raise (Error ExpAppNotFun)


let rec recTyp recT cD cPsi sA = recTypW recT cD cPsi (Whnf.whnfTyp sA)

and recTypW recT cD cPsi sA = match sA with
  | (Int.LF.Atom (a, tS) , s) ->
      let tK = (Typ.get a).Typ.kind in

      let sshift = begin match recT with 
                    | PiboxRecon -> Int.LF.Shift(Int.LF.NoCtxShift, 0)           
                    | PiRecon -> 
                        let (_, d) = Context.dctxToHat cPsi in 
                      Int.LF.Shift(Int.LF.NoCtxShift, d)                     
                   end in 

      (* let sshift = 
        begin match Context.dctxToHat cPsi with
          | (Some psi, d) -> Int.LF.Shift(Int.LF.CtxShift psi, d)
          | (None, d)     -> Int.LF.Shift(Int.LF.NoCtxShift, d)
        end
      in *)
      let tA' =  recKSpine recT cD cPsi (tS, s) (tK, sshift) in 
        tA'

  | (Int.LF.PiTyp ((Int.LF.TypDecl (_x, tA) as adec), tB), s) -> (
      recTyp recT cD cPsi (tA, s);
      recTyp recT cD (Int.LF.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s)
    )

let rec recTypRec recT cD cPsi (typRec, s) = match typRec with
  | Int.LF.SigmaLast lastA         -> recTyp recT cD cPsi (lastA, s)
  | Int.LF.SigmaElem(_x, tA, recA) ->
        recTyp  recT cD cPsi (tA, s)
        ; recTypRec recT cD
          (Int.LF.DDec (cPsi, LF.decSub (Int.LF.TypDecl (Id.mk_name None, tA)) s))
          (recA, LF.dot1 s)


let recDec recT cD cPsi (decl, s) = match decl with
    | Int.LF.TypDecl (_, tA) -> 
        recTyp recT cD cPsi (tA, s)


let recSigmaDec recT cD cPsi (sigma_decl, s) = match sigma_decl with
    | Int.LF.SigmaDecl (_, arec) -> 
        recTypRec recT cD cPsi (arec, s)


let rec recDCtx recT cO cD cPsi = match cPsi with 
  | Int.LF.Null -> ()
  | Int.LF.DDec (cPsi, tX)     ->
      recDCtx recT cO cD cPsi
      ; recDec recT cD cPsi (tX, LF.id)

  | Int.LF.SigmaDec (cPsi, tX) ->
      recDCtx recT cO cD cPsi
      ; recSigmaDec recT cD cPsi (tX, LF.id)

  | Int.LF.CtxVar (Int.LF.CtxOffset psi_offset)  -> 
      if psi_offset <= (Context.length cO) then ()
      else 
        raise (Violation "Context variable out of scope")




let rec recKind cD cPsi sK = match sK with
  | (Int.LF.Typ, _s) ->
      ()

  | (Int.LF.PiKind (Int.LF.TypDecl(_x, tA) as adec, tK), s) -> (
      recTyp PiRecon cD cPsi (tA, s)
      ; recKind cD (Int.LF.DDec (cPsi, LF.decSub adec s)) (tK, LF.dot1 s)
    )


(* ******************************************************************* *)
(* Elaboration of computations *)
(* Given a type-level constant a of type K , it will generate the most general
   type a U1 ... Un *)
let mgTyp cPsi a kK = 
  let rec genSpine sK = match sK with

  | (Int.LF.Typ, _s) -> Int.LF.Nil 

  | (Int.LF.PiKind (Int.LF.TypDecl (_, tA1), kK), s) -> 
     let u = Whnf.newMVar (cPsi , Int.LF.TClo(tA1,s)) in 
     let tR = Int.LF.Root(Int.LF.MVar(u, LF.id), Int.LF.Nil) in 
     let tS = genSpine (kK, Int.LF.Dot(Int.LF.Head(Int.LF.MVar(u, LF.id)), s)) in 
       Int.LF.App (tR, tS)
  in 
    Int.LF.Atom(a, genSpine (kK, LF.id))


let rec genMApp (i,  tau_t) = genMAppW (i,  Cwhnf.cwhnfCTyp tau_t) 

and genMAppW   (i, tau_t)  = match tau_t with 
  | (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi),  Int.Comp.Implicit ), tau), theta) -> 
      let psihat  = Context.dctxToHat cPsi in 

      let tM'     = Whnf.etaExpandMV (C.cnormDCtx (cPsi, theta))  (C.cnormTyp (tA,theta), LF.id) LF.id in
        genMApp ((Int.Comp.MApp (i, (psihat, tM'))) ,  (tau, Int.Comp.MDot(Int.Comp.MObj (psihat, tM'), theta)))

  | _ -> (i, tau_t)


let rec elCompTyp cO cD tau = match tau with
  | Apx.Comp.TypBox (a, psi) ->
      let cPsi = elDCtx PiboxRecon cD psi in
      let tA   = elTyp PiboxRecon cD cPsi a in
        Int.Comp.TypBox (tA, cPsi)

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCtxPi ((x, schema_cid) , tau) ->
      let tau' = elCompTyp (Int.LF.Dec (cO, Int.LF.CDecl (x, schema_cid))) cD tau in
        Int.Comp.TypCtxPi ((x, schema_cid), tau')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl PiboxRecon cD cdecl  in
      let tau'   = elCompTyp cO (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox ((cdecl', Int.Comp.Explicit), tau')

let rec elExp cO cD cG e theta_tau = elExpW cO cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cO cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Syn i, _) ->
      let (i', _t) = genMApp (elExp' cO cD cG i) in
        Int.Comp.Syn i'

  | (Apx.Comp.Fun (x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
      let e' = elExp cO cD (Int.LF.Dec (cG, (x, Int.Comp.TypClo (tau1, theta)))) e (tau2, theta) in
        Int.Comp.Fun (x, e')

  | (Apx.Comp.CtxFun (psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid), tau), theta)) ->
      let e' = elExp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD cG e (tau, theta) in
        Int.Comp.CtxFun (psi_name, e')

  | (Apx.Comp.MLam (u, e) , (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
        cG e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (u, e')

  | (e , (Int.Comp.TypPiBox((Int.LF.MDecl(u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
                cG e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (u, e')

  | (Apx.Comp.Box (psihat, tM), (Int.Comp.TypBox (tA, cPsi), theta)) -> 
      let tM' = elTerm PiboxRecon cD (C.cnormDCtx (cPsi, theta)) tM (C.cnormTyp (tA, theta), LF.id) in 
        Int.Comp.Box (psihat, tM')

  | (Apx.Comp.Case (i, branches), tau_theta) ->
      let (i', tau_theta') = genMApp (elExp' cO cD cG i) in
        begin match C.cwhnfCTyp tau_theta'  with
          | (Int.Comp.TypBox (tP, cPsi), _theta') ->
              (* We don't check that each branch has approximate type tA[cPsi] - DOUBLE CHECK -bp  *)
              let branches' = List.map (function b -> elBranch cO cD cG b tau_theta (tP, cPsi)) branches in
                Int.Comp.Case (i', branches')

          | _ -> raise (Violation "Case-expression ill-typed; Trying to branch on an expression which is not a boxed-LF type")
        end

  | (_, _) ->
      raise (Violation "Elaboration: Found ill-typed computation-level expression.")


and elExp' cO cD cG i = match i with
  | Apx.Comp.Var offset -> (Int.Comp.Var offset, (lookup cG offset, C.id))

  | Apx.Comp.Const prog -> (Int.Comp.Const prog, ((Comp.get prog).Comp.typ, C.id))

  | Apx.Comp.Apply (i, e) ->
      begin match genMApp (elExp' cO cD cG i) with
        | (i', (Int.Comp.TypArr (tau2, tau), theta)) ->
            let e' = elExp cO cD cG e (tau2, theta) in
              (Int.Comp.Apply (i', e'), (tau, theta))

        | _ -> raise (Violation "Elaboration Error: Function mismatch")
      end

  | Apx.Comp.CtxApp (i, cPsi) ->
      begin match genMApp (elExp' cO cD cG i) with
        | (i', (Int.Comp.TypCtxPi ((_psi, _sW) , tau), theta)) ->
            let cPsi'  = elDCtx PiboxRecon cD cPsi in
            let theta' = Cwhnf.csub_msub cPsi' 1 theta in
            let tau'   = Cwhnf.csub_ctyp cPsi' 1 tau in
              (Int.Comp.CtxApp (i', cPsi') , (tau', theta'))

        | _ -> raise (Violation "Context abstraction mismatch")
      end


  | Apx.Comp.MApp (i, (psihat, tM)) ->
      begin match genMApp (elExp' cO cD cG i) with
        | (i', (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi), Int.Comp.Explicit ), tau), theta)) ->
            let tM'  = elTerm PiboxRecon cD (C.cnormDCtx (cPsi, theta)) tM  (C.cnormTyp (tA, theta), LF.id) in
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

and elBranch cO cD cG branch (tau, theta) (Int.LF.Atom(a, _spine) , _cPsi) = match branch with 
  | (Apx.Comp.BranchBox (delta, (psi1, m, Some (a, psi)), e)) -> 

      let cD'     = elMCtx PiboxRecon delta in 
      let cPsi'   = elDCtx PiboxRecon (* cO *) cD' psi in 
      let cPsi1   = elDCtx PiboxRecon (* cO *) cD' psi1 in 

      (* Check that Psi = Psi' using Whnf.conv and or unify; 
         if they are not equal, then we need to fail... -bp *)

      let psihat  =  Context.dctxToHat cPsi1 in 

      let tA'     = elTyp PiboxRecon  (* cO *) cD' cPsi' a in 
      let tM'     = elTerm PiboxRecon (* cO *) cD' cPsi' m (tA', LF.id) in                  

      let _ = recTerm PiboxRecon (* cO *) cD' cPsi' (tM', LF.id) (tA', LF.id) in 

      let (cD1', cPsi1', (phat', tM1'), tA1') =
        Abstract.abstrPattern cD' cPsi' (psihat, tM') tA' in    

      let n       = Context.length cD1' in   
      let cD_i    = Context.append cD cD1' in 
      let theta_i = C.mshift theta n in 

      let _        = FMVar.clear () in
      let _        = FPVar.clear () in

      let e'     = elExp cO cD_i cG e (tau, theta_i) in
        
        Int.Comp.BranchBox (cD1', (phat', tM1', (tA1', cPsi1')), e') 


  | (Apx.Comp.BranchBox (delta, (psi, r, None), e))  ->
      let cD'     = elMCtx PiboxRecon delta in
      let cPsi'   = elDCtx PiboxRecon (* cO *) cD' psi in
      let tP0     = mgTyp cPsi' a (Typ.get a).Typ.kind  in

      let tR      = elTerm' PiboxRecon (* cO *) cD' cPsi' r  (tP0, LF.id) in 

      (* let _       = Printf.printf "Elaborated pattern...\n" in   

      let _ = Printf.printf "%s ; \n %s  \n   |-   \n %s \n has type: %s  .\n\n"
                  (P.mctxToString (Cwhnf.normMCtx cD'))
                  (P.dctxToString cPsi')
                  (P.normalToString tR)
                  (P.typToString  tP0) in
      *)
      let psihat  = Context.dctxToHat cPsi' in 

      let sP      = synTerm PiboxRecon (* cO *) cD' cPsi' (tR, LF.id) in   
       
      (*
      let _       = Printf.printf "Reconstructed pattern...\n" in   
      let _ = Printf.printf "%s ; \n %s  \n   |-   \n %s \n has type: %s  .\n\n"
                  (P.mctxToString (Cwhnf.normMCtx cD'))
                  (P.dctxToString cPsi')
                  (P.normalToString tR)
                  (P.typToString  tP0) in
      *)

      let _       = Unify.unifyTyp cD' (psihat, sP, (tP0, LF.id)) in 

      let (cD1', cPsi1', (phat', tR1'), tP1') =
          Abstract.abstrPattern cD' cPsi' (psihat, tR) (Int.LF.TClo(sP)) in    

      let n       = Context.length cD1' in  
      let cD_i    = Context.append cD cD1' in 

      let theta_i = C.mshift theta n in 

      let _        = FMVar.clear () in
      let _        = FPVar.clear () in

      let e'     = elExp cO cD_i cG e (tau, theta_i) in
        Int.Comp.BranchBox (cD1', (phat', tR1', (tP1', cPsi1')), e') 




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

let rec mctxToMSub cD =  match cD with
  | Int.LF.Empty -> C.id
  | Int.LF.Dec (cD', Int.LF.MDecl(_, tA, cPsi)) ->
      let t     = mctxToMSub cD' in
      let cPsi' = Cwhnf.cnormDCtx (cPsi,t) in
      let tA'   = Cwhnf.cnormTyp (tA, t) in
      let u     = Whnf.newMVar (cPsi' , tA') in
      let phat  = Context.dctxToHat cPsi in 
        Int.Comp.MDot (Int.Comp.MObj (phat, Int.LF.Root (Int.LF.MVar (u, LF.id), Int.LF.Nil)) , t)

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


let rec recCompTyp cO cD tau = match tau with
  | Int.Comp.TypBox (tA, cPsi) -> (
      recDCtx PiboxRecon cO cD cPsi;
      recTyp PiboxRecon cD cPsi (tA, LF.id)
    )

  | Int.Comp.TypArr (tau1, tau2) -> (
      recCompTyp cO cD tau1;
      recCompTyp cO cD tau2
    )

  | Int.Comp.TypCtxPi ((psi_name, schema_cid), tau) ->
      recCompTyp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD tau

  | Int.Comp.TypPiBox ((cdecl, _), tau) ->
      recCompTyp cO (Int.LF.Dec (cD, cdecl)) tau


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
      let e' = check cO cD (Int.LF.Dec (cG, (f, Int.Comp.TypClo (tau,t)))) e ttau in 
        Int.Comp.Rec (f, e')

  | (Int.Comp.Fun (x, e), (Int.Comp.TypArr (tau1, tau2), t)) ->
      let e' = check cO cD (Int.LF.Dec (cG, (x, Int.Comp.TypClo (tau1, t)))) e (tau2, t) in 
      Int.Comp.Fun (x, e')

  | (Int.Comp.CtxFun(psi, e) , (Int.Comp.TypCtxPi ((_psi, schema), tau), t)) ->
      let e' = check (Int.LF.Dec (cO, Int.LF.CDecl (psi, schema))) cD cG e (tau, t) in 
        Int.Comp.CtxFun (psi, e')

  | (Int.Comp.MLam (u, e), (Int.Comp.TypPiBox ((Int.LF.MDecl (_u, tA, cPsi), _ ), tau), t)) ->
      let e' = check cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
                     cG e (tau, C.mvar_dot1 t) in 
        Int.Comp.MLam(u, e')

  | (Int.Comp.Box (_phat, tM), (Int.Comp.TypBox (tA, cPsi), t)) ->
      (* Check.LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, LF.id) (C.cnormTyp (tA, t), LF.id) *)
      begin try 
        let cPsi' = C.cnormDCtx (cPsi, t) in 
        let tA'   = C.cnormTyp (tA, t) in 
          (recTerm PiboxRecon cD  cPsi' (tM, LF.id) (tA', LF.id) ;
           e )
      with Cwhnf.FreeMVar (Int.LF.FMVar(u, _ )) -> 
        raise (Violation ("Free meta-variable " ^ (R.render_name u)))
      end 

  | (Int.Comp.Case (e, branches), (tau, t)) ->
      let (i, tau') = syn cO cD cG e in
      begin match C.cwhnfCTyp tau' with
        | (Int.Comp.TypBox (tA, cPsi),  t') ->
            let branches' = checkBranches cO cD cG branches (C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) (tau, t) in 
              Int.Comp.Case (i, branches')
        | _ -> raise (Violation "Case scrutinee not of boxed type")
      end

  | (Int.Comp.Syn e, (tau, t)) ->
      let (i, tau_t') = syn cO cD cG e in 
      (* if C.convCTyp (tau,t) tau_t' then *)
      try       
        Unify.unifyCompTyp cD (tau,t) (tau_t') ;
        (Int.Comp.Syn i)
      with  _ -> 
        (let  _ = Printf.printf "Synthesized type: %s \n Expected type %s\n" 
                  (P.compTypToString (Cwhnf.cnormCTyp tau_t'))           
                  (P.compTypToString (Cwhnf.cnormCTyp (tau,t))) 
         in  
           raise (Violation "Type mismatch"))

and check cO cD cG e (tau, t) =
  checkW cO cD cG e (C.cwhnfCTyp (tau, t))

and syn cO cD cG e = match e with
  | Int.Comp.Var x  -> (e, (lookup cG x, C.id))
      (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD ???!!! *)

  | Int.Comp.Const prog  -> (e, ((Comp.get prog).Comp.typ, C.id))

  | Int.Comp.Apply (e1, e2) ->
      let (i, tau) = syn cO cD cG e1 in 
        begin match C.cwhnfCTyp tau with
          | (Int.Comp.TypArr (tau2, tau1), t) -> 
              (* Note: We need to normalize here before checking that e2 has type (tau2,t)
               *   because during the check we will destructively update references denoting
               *   unknown meta-variables in tau2, t and e2. Hence [|t|]tau2 BEFROE the update
               *   may not be the same as [|t|]tau2 AFTER the updates.
               *)
              let tau2' = C.cnormCTyp (tau2, t) in 

              let tau' = C.cnormCTyp (tau1, t) in  

              let e = check cO cD cG e2 (tau2', C.id) in  

              (* This is being on the safe side: Using (tau2, t) should work here *)

              (Int.Comp.Apply (i, e) , (tau', C.id))
          | _ -> raise (Violation "Function mismatch")
        end

  | Int.Comp.CtxApp (e, cPsi) ->
      let (i, tau) = syn cO cD cG e in 
        begin match C.cwhnfCTyp tau with
          | (Int.Comp.TypCtxPi ((_psi, _sW) , tau), t) ->
              let _ = Printf.printf "\n Schema checking omitted \n" in
                (* REVISIT: Sun Jan 11 17:48:52 2009 -bp *)
                (* let tau' =  Cwhnf.csub_ctyp cPsi 1 tau in
                   let t'   = Cwhnf.csub_msub cPsi 1 t in   *)
                
              let tau1 = Cwhnf.csub_ctyp cPsi 1 (Cwhnf.cnormCTyp (tau,t)) in
                (Int.Comp.CtxApp (i, cPsi) , (tau1, Cwhnf.id))

          | _ -> raise (Violation "Context abstraction mismatch")
        end

  | Int.Comp.MApp (e, (phat, tM)) ->
      let (i, tau') = syn cO cD cG e in 
        begin match C.cwhnfCTyp tau' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi), _ (* Int.Comp.Explicit*) ), tau), t) ->               
              (let _ = recTerm PiboxRecon cD (C.cnormDCtx (cPsi, t)) (tM, LF.id) (C.cnormTyp (tA, t), LF.id) in 
               let t' = Int.Comp.MDot(Int.Comp.MObj (phat, tM), t) in 
                 
                 (Int.Comp.MApp (i, (phat, tM)) , (tau, t'))
              )
          | _ -> raise (Violation "MLam mismatch")
        end

  | (Int.Comp.Ann (e, tau)) -> 
      let e' = check cO cD cG e (tau, C.id) in        
       (Int.Comp.Ann (e', tau) , (tau, C.id))
    

and checkBranches cO cD cG branches tAbox ttau = match branches with
  | [] -> []
  | (branch :: branches) ->
      let b = checkBranch cO cD cG branch tAbox ttau in
        b :: (checkBranches cO cD cG branches tAbox ttau)

 
and checkBranch cO cD cG branch (tA, cPsi) (tau, t) =    
  match branch with
    | Int.Comp.BranchBox (cD1, (phat, tM1, (tA1, cPsi1)), e1) ->  
        let _ = Check.LF.check cO cD1 cPsi1 (tM1, LF.id) (tA1, LF.id) in   
       (* This is a double-check here, since reconstruction was 
        * done during elaboration of branch 
        *)

        let d1 = length cD1 in  
        let _d  = length cD in 
        let t1 = mctxToMSub cD1 in   (* {cD1} |- t1 <= cD1 *)
        let t' = mctxToMSub cD in    (* {cD}  |- t' <= cD *)
        let tc = extend t' t1 in     (* {cD1, cD} |- t', t1 <= cD, cD1 *) 

        let _  = begin try 
                    (Unify.unifyDCtx (Int.LF.Empty) 
                                    (C.cnormDCtx (cPsi, t')) (C.cnormDCtx (cPsi1, tc)) 
                   ; Unify.unifyTyp (Int.LF.Empty) 
                                  (phat, (C.cnormTyp (tA, t'), LF.id), (C.cnormTyp (tA1, tc), LF.id)))
                 with 
                     _ -> (let _ = Printf.printf "Unify ERROR:"   in
                                         let _ = Printf.printf "Inferred pattern type : %s  |- %s \n Expected pattern type: %s |- %s" 
                                           (P.dctxToString (C.cnormDCtx (cPsi1, tc))) 
                                           (P.typToString (C.cnormTyp (tA1, tc)))
                                           (P.dctxToString  (C.cnormDCtx (cPsi, t'))) 
                                           (P.typToString (C.cnormTyp (tA, t')))
                                         in   
                                            raise (Violation "Pattern Type Clash")
                                        )
                 end
        in 

        let (tc', cD1'') = Abstract.abstractMSub tc in  (* cD1' |- tc' <= cD, cD1 *) 

        let t'' = split tc' d1 in (* cD1' |- t'' <= cD  suffix *) 
        let cG1 = C.cwhnfCtx (cG, t'') in 

        let e1' = begin try C.cnormExp (e1, tc')  
                    with Cwhnf.FreeMVar (Int.LF.FMVar(u, _ )) -> 
                      raise (Violation ("Encountered free meta-variable " ^ (R.render_name u)))
                  end  in

        let tau' = (tau, C.mcomp t'' t)  in

        (* let _ = Printf.printf "\nRecon: Check branch  \n %s ; \n %s  \n   |-   \n %s \n has type: %s  .\n\n"
                  (P.mctxToString (Cwhnf.normMCtx cD1''))
                  (P.gctxToString cG1)
                  (P.expChkToString e1')
                  (P.compTypToString  (Cwhnf.cnormCTyp tau')) in
        *)

        let e1_r =  check cO cD1'' cG1 e1' tau' in 
        (*
        let _ = Printf.printf "\nRecon (DONE): Check branch  \n %s ; \n %s  \n   |-   \n %s \n has type: %s  .\n\n"
                  (P.mctxToString (Cwhnf.normMCtx cD1''))
                  (P.gctxToString cG1)
                  (P.expChkToString e1_r)
                  (P.compTypToString  (Cwhnf.cnormCTyp tau')) in
        *)

        let e1''   = try Cwhnf.invExp (e1_r, tc') 0 with 
                      Cwhnf.NonInvertible -> 
                        raise (Violation "Reconstruction suceeded,i.e. the expression is well-typed – but we cannot uniquely generate the actual expression\n")
        in 

          Int.Comp.BranchBox (cD1, (phat, tM1, (tA1, cPsi1)), e1'')  

          

(* ------------------------------------------------------------------- *)

let recSgnDecl d = match d with
  | Ext.Sgn.Typ (_, a, extK)   ->
      let apxK     = index_kind (CVar.create ()) (BVar.create ()) extK in
      let _        = FVar.clear () in
      let tK       = elKind Int.LF.Null apxK in
      let _        = solve_fvarCnstr PiRecon Int.LF.Empty !fvar_cnstr in
      let _        = reset_fvarCnstr () in
      let _        = recKind Int.LF.Empty Int.LF.Null (tK, LF.id) in
      let (tK', i) = Abstract.abstrKind tK in
      (* let _        = Printf.printf "\n Reconstruction (wih abstraction) of constant %s \n %s \n\n" a.string_of_name
        (P.kindToString tK') in *)
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
      let tA       = elTyp PiRecon Int.LF.Empty Int.LF.Null apxT in
      let _        = solve_fvarCnstr PiRecon Int.LF.Empty !fvar_cnstr in
      let _        = reset_fvarCnstr () in
      (* let _        = Printf.printf "\n Elaboration of constant %s \n : %s \n\n" c.string_of_name
        (P.typToString (Whnf.normTyp (tA, LF.id))) in   *)
      let cD       = Int.LF.Empty in
      let _        = recTyp PiRecon cD Int.LF.Null (tA, LF.id) in
      (* let _        = Printf.printf "\n Reconstruction (without abstraction) of constant %s \n %s \n\n" c.string_of_name
        (P.typToString (Whnf.normTyp (tA, LF.id))) in  *)

      let (tA', i) = Abstract.abstrTyp tA in
      (* let _        = Printf.printf "\n Reconstruction (with abstraction) of constant %s \n %s \n\n" c.string_of_name
         (P.typToString (Whnf.normTyp (tA', LF.id))) in *)
      let _        = Check.LF.checkTyp Int.LF.Empty Int.LF.Empty Int.LF.Null (tA', LF.id) in
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" c.string_of_name  in
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
      let       _  = (print_string "Add constant \n"; flush_all ()) in 
      let _        = Printf.printf "\n Added constant : %s  successful! \n" c.string_of_name  in
        Int.Sgn.Const (c', tA')


  | Ext.Sgn.Schema (_, g, schema) ->
      let apx_schema = index_schema schema in
      let _        = Printf.printf "\n Reconstruct schema: %s\n" g.string_of_name  in
      let sW         = elSchema apx_schema in
(*      let _        = Printf.printf "\n Elaboration of schema %s \n : %s \n\n" g.string_of_name
                        (P.schemaToString sW) in   *)
      let cPsi       = Int.LF.Null in
      let cD         = Int.LF.Empty in
      let cO         = Int.LF.Empty in
      let _          = Check.Comp.checkSchema cO cD cPsi sW in
      let _        = Printf.printf "\n TYPE CHECK for schema %s successful!\n" g.string_of_name  in
      let g'         = Schema.add (Schema.mk_entry g sW) in
        Int.Sgn.Schema (g', sW)


  | Ext.Sgn.Rec (_, f, tau, e) ->
      (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in  *)
      let apx_tau = index_comptyp (CVar.create ()) (CVar.create ()) tau in
      let _       = Printf.printf "\n Reconstruct function: %s  \n" f.string_of_name  in 
      let cD      = Int.LF.Empty in
      let cO      = Int.LF.Empty in

      let tau'    = elCompTyp cO cD apx_tau  in  

      (* let _        = Printf.printf "\n Elaboration of program type %s \n : %s \n\n" f.string_of_name
                        (P.compTypToString tau') in  *)

      let _       = recCompTyp cO cD tau' in

      let (tau', _i) = Abstract.abstrCompTyp tau' in 

      let  _      = Check.Comp.checkTyp cO cD tau' in 

      (* let _       = Printf.printf "\n Checking computation type %s successful ! \n\n "
                                  (P.compTypToString tau') in *)

      
      let vars' = Var.extend  (Var.create ()) (Var.mk_entry f) in

      let apx_e   = index_exp (CVar.create ()) (CVar.create ()) vars' e in

      let cG      = Int.LF.Dec(Int.LF.Empty, (f, tau'))  in

      let e'      = elExp cO cD cG apx_e (tau', C.id) in

      (* let _       = Printf.printf "\n Elaboration of program %s \n : %s \n %s \n" f.string_of_name
                         (P.compTypToString tau')
                         (P.expChkToString e') in 
      *)
      let e_r     = check  cO cD cG e' (tau', C.id) in  
      let e_r'    = Abstract.abstrExp e_r in  

      let _       = Printf.printf "\n Reconstructed program %s \n : %s \n %s \n" f.string_of_name
                         (P.compTypToString tau')
                         (P.expChkToString e_r') in  

      let _       = Check.Comp.check cO cD  cG e_r' (tau', C.id) in   
      let _        = Printf.printf "\n DOUBLE CHECK for program : %s  successful! \n\n" f.string_of_name  in 
      let f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' ) in 
        Int.Sgn.Rec (f', tau',  e_r' )
