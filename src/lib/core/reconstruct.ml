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

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [4])

exception NotImplemented
exception Error of Syntax.Loc.t option * error
exception SpineMismatch

exception Violation of string

type reconType = PiboxRecon | PiRecon

type caseType  = IndexObj of Int.LF.psi_hat * Int.LF.normal | DataObj


let rec lookup cG k = match (cG, k) with
  | (Int.LF.Dec(_cG', Int.Comp.CTypDecl (_, tau)), 1) ->   tau
  | (Int.LF.Dec( cG', Int.Comp.CTypDecl (_, _tau)), k) ->
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
      let x      = Id.mk_name Id.NoName
      and a'     = index_typ cvars bvars a in
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let k'     = index_kind cvars bvars' k in
        Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.No), k')

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let a'     = index_typ cvars bvars a
      and bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let k'     = index_kind cvars bvars' k in
        Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), k')

and index_typ cvars bvars = function
  | Ext.LF.Atom (loc, a, s) ->
      begin try 
        let _        = dprint (fun () -> "Indexing type constant " ^ a.string_of_name) in 
        let a' = Typ.index_of_name a in
        and s' = index_spine cvars bvars s in
          Apx.LF.Atom (loc, a', s')
      with Not_found ->
       raise (Error (Some loc, UnboundName a))
      end
    

  | Ext.LF.ArrTyp (_, a, b) ->
      let x      = Id.mk_name Id.NoName
      and a'     = index_typ cvars bvars a in
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let b'     = index_typ cvars bvars' b in
        Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.No), b')

  | Ext.LF.PiTyp (_, Ext.LF.TypDecl (x, a), b) ->
      let a'     = index_typ cvars bvars  a
      and bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let b'     = index_typ cvars bvars' b in
        Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), b')
  
  | Ext.LF.Sigma (_, typRec) ->
      let typRec' = index_typ_rec cvars bvars typRec in
      Apx.LF.Sigma typRec'

and index_typ_rec cvars bvars = function
  | Ext.LF.SigmaLast a -> Apx.LF.SigmaLast (index_typ cvars bvars a)
  | Ext.LF.SigmaElem (x, a, rest) ->
      let a' = index_typ cvars bvars a
      and bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let rest' = index_typ_rec cvars bvars' rest in
        Apx.LF.SigmaElem (x, a', rest')

and index_tuple cvars bvars = function
  | Ext.LF.Last m -> Apx.LF.Last (index_term cvars bvars m)
  | Ext.LF.Cons (m, rest) ->
      let m' = index_term cvars bvars m in
      let rest' = index_tuple cvars bvars rest in
        Apx.LF.Cons (m', rest')

and index_term cvars bvars = function
  | Ext.LF.Lam (loc, x, m) ->
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let m'     = index_term cvars bvars' m in
        Apx.LF.Lam (loc, x, m')

  | Ext.LF.Tuple (loc, tuple) ->
      let tuple' = index_tuple cvars bvars tuple in
        Apx.LF.Tuple (loc, tuple')

  | Ext.LF.Root (loc, h, s) ->
      let h' = index_head  cvars bvars h
      and s' = index_spine cvars bvars s in
        Apx.LF.Root (loc, h', s')

and index_head cvars bvars = function
  | Ext.LF.Name (_, n) ->
      let _        = dprint (fun () -> "Indexing name " ^ n.string_of_name) in 
      begin try
        Apx.LF.BVar (BVar.index_of_name bvars n)
      with Not_found -> try
        Apx.LF.Const (Term.index_of_name n)
      with Not_found ->
        Apx.LF.FVar n
      end

  | Ext.LF.ProjName (loc, k, n) ->
      let bvar = index_head cvars bvars (Ext.LF.Name (loc, n)) in
        Apx.LF.Proj(bvar, k)

  | Ext.LF.PVar (_, p, s) ->
      begin try
        let offset = CVar.index_of_name cvars p in
        let s'     = index_sub cvars bvars s in
          Apx.LF.PVar (offset, s')
      with Not_found ->
        let _ = dprint (fun () -> "PVar Not_found " ^ R.render_name p)  in
      let s'     = index_sub cvars bvars s in
          Apx.LF.FPVar (p, s')
      end

  | Ext.LF.ProjPVar (loc, k, (p, s)) ->
      let pvar = index_head cvars bvars (Ext.LF.PVar(loc, p, s)) in
        Apx.LF.Proj(pvar, k)

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
      let a' = index_typ cvars bvars a
      and bvars' = BVar.extend bvars (BVar.mk_entry x) in
        Apx.LF.SigmaElem (x, a', index_typrec cvars bvars' arec)


(* Translation of external schemas into approximate schemas *)
let rec index_elements el_list = List.map index_el el_list

and index_el (Ext.LF.SchElem (_, typ_ctx, typ_rec)) =
  let cvars = (CVar.create ()) in
  let bvars = (BVar.create ()) in
  let (typ_ctx', bvars') = index_ctx cvars bvars typ_ctx in
  let typ_rec'           = index_typrec cvars bvars' typ_rec in
    Apx.LF.SchElem (typ_ctx', typ_rec')


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

  | Ext.Comp.TypCross (_, tau, tau') ->
      Apx.Comp.TypCross (index_comptyp ctx_vars cvars tau, index_comptyp ctx_vars cvars tau')

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

  | Ext.Comp.Pair (_, e1, e2) ->
      let e1 = index_exp ctx_vars cvars vars e1 in
      let e2 = index_exp ctx_vars cvars vars e2 in
        Apx.Comp.Pair (e1, e2)

  | Ext.Comp.LetPair (_, i, (x, y, e)) ->
      let i' = index_exp' ctx_vars cvars vars i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let vars2 = Var.extend vars1 (Var.mk_entry y) in
      let e' = index_exp ctx_vars cvars vars2 e in
        Apx.Comp.LetPair( i', (x,y,e'))

  | Ext.Comp.Box (_, psihat, m) ->
      let (psihat', bvars) = index_psihat ctx_vars psihat in
        Apx.Comp.Box (psihat', index_term cvars bvars m)

  | Ext.Comp.Case (_, i, branches) ->
      let i' = index_exp' ctx_vars cvars vars i in
      let branches' = List.map (function b -> index_branch ctx_vars cvars vars b) branches in
        Apx.Comp.Case (i', branches')

and index_exp' ctx_vars cvars vars = function
  | Ext.Comp.Var (loc, x) ->
      begin try
        Apx.Comp.Var (Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (Comp.index_of_name x)
      with Not_found ->
        raise (Error (Some loc, UnboundName x))
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

  | Ext.Comp.BoxVal (_, psi, m) ->
      let (psi', bvars) = index_dctx ctx_vars cvars  (BVar.create ()) psi in
        Apx.Comp.BoxVal (psi', index_term cvars bvars m)

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
      raiseType cPsi' (Int.LF.PiTyp ((decl, Int.LF.Maybe), tA))

(* patSpine s = true iff
 *
 *     cPsi |- s : A <- P  and
 *     s is a pattern spine (simple approximate),
 *     i.e. it consists of distinct bound variables
 *)
let patSpine spine =
  let rec patSpine' seen_vars spine = match spine with
    | Apx.LF.Nil ->
        (true, 0)

    | Apx.LF.App (Apx.LF.Root (_, Apx.LF.BVar x, Apx.LF.Nil), spine) ->
        if not (List.mem x seen_vars) then
          let (b,l) = patSpine' (x :: seen_vars) spine in
            (b, l+1)
        else
          (false, 0)

    | _ -> (false, 0)
  in
    patSpine' [] spine

let rec mkShift recT cPsi = match recT with
  | PiboxRecon -> 
      Int.LF.Shift (Int.LF.NoCtxShift, 0)

  | PiRecon ->
      let (None, d) = Context.dctxToHat cPsi in
        Int.LF.Shift (Int.LF.NoCtxShift, d) 

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
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            (Int.LF.CtxVar psi, Int.LF.Shift (Int.LF.NoCtxShift, d))

        | (None, _d) ->
            raise (Error (None, UnboundIdSub))
      end

  | Apx.LF.EmptySub ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            (Int.LF.Null, Int.LF.Shift (Int.LF.CtxShift psi, d))

        | (None, d) ->
            (Int.LF.Null, Int.LF.Shift (Int.LF.NoCtxShift, d))
      end

  | Apx.LF.Dot (Apx.LF.Head (Apx.LF.BVar k), s) ->
      begin match Context.ctxDec cPsi k with
        | Int.LF.TypDecl (x, tA) ->
            let (cPhi, s') = synDom cPsi s in
              (*  cPsi |- s <= cPhi
               *  cPsi |- tA <= type
               *  tA' = [s]^-1(tA)
               *
               * Note: We may need to check that [s]^-1(tA) actually exists.
               *
               *  Wed Jan 14 13:51:11 2009 -bp
               *)
              (Int.LF.DDec (cPhi,
                            Int.LF.TypDecl (x, Int.LF.TClo(tA, Substitution.LF.invert s'))),
               Int.LF.Dot (Int.LF.Head(Int.LF.BVar k), s'))
(*         | _ -> raise (Violation "Undefined bound variable \n") *)
      end
  | _ -> raise (Violation "Encountered non-pattern substitution")

end


(* elKind  cPsi (k,s) = K *)
let rec elKind cPsi k = match k with
  | Apx.LF.Typ ->
      Int.LF.Typ

  | Apx.LF.PiKind ((Apx.LF.TypDecl (x, a),dep), k) ->
      let dep'  = match dep with Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
      let tA    = elTyp
                    PiRecon
                    (*cO=*)Int.LF.Empty
                    (*cD=*)Int.LF.Empty
                    cPsi
                    a
      in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elKind cPsi' k in
        Int.LF.PiKind ((Int.LF.TypDecl (x, tA), dep'), tK)

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
and elTyp recT cO cD cPsi a = match a with
  | Apx.LF.Atom (loc, a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      (* let s'  = mkShift recT cPsi in *)
      let s' = LF.id in
      let tS = elKSpineI recT cO cD cPsi s i (tK, s') in
        Int.LF.Atom (Some loc, a, tS)

  | Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a), dep), b) ->
      let dep'  = match dep with Apx.LF.No -> Int.LF.No | Apx.LF.Maybe -> Int.LF.Maybe in
      let tA    = elTyp recT cO cD cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp recT cO cD cPsi' b in
        Int.LF.PiTyp ((Int.LF.TypDecl (x, tA),dep'), tB)

  | Apx.LF.Sigma typRec ->
      let typRec' = elTypRec recT cO cD cPsi typRec in
        Int.LF.Sigma typRec'
   
       
and elTypRec recT cO cD cPsi =
(*  let el_typ ctx = elTyp recT cD (projectCtxIntoDctx ctx) in *)
    function
      | Apx.LF.SigmaLast a ->
          Int.LF.SigmaLast (elTyp recT cO cD cPsi a)

      | Apx.LF.SigmaElem (name, a, typRec) ->
          let tA = elTyp recT cO cD cPsi a in
          let cPsi' = Int.LF.DDec (cPsi, Int.LF.TypDecl (name, tA)) in
          let typRec' = elTypRec recT cO cD cPsi' typRec in
            Int.LF.SigmaElem (name, tA, typRec')


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
and elTerm recT cO cD cPsi m sA = elTermW recT cO cD cPsi m (Whnf.whnfTyp sA)

and elTermW recT cO cD cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (loc, x, m), (Int.LF.PiTyp ((Int.LF.TypDecl (_x, _tA) as decl, _ ), tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm recT cO cD cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam (Some loc, x, tM)

  | (Apx.LF.Root (_, _h, _spine), (Int.LF.Atom _, _s)) ->
      elTerm' recT cO cD cPsi m  sA
  | _ -> raise (Violation "Elaboration encountered ill-typed term: Check for eta-expansion")

and elFindInContext recT cO cD cPsi sP (head, k) ((Int.LF.Schema elements) as schema) =
  let self = elFindInContext recT cO cD cPsi sP (head, k) in
  let _ = dprint (fun () -> "elFindInContext ... "
                    ^ P.typToString cO cD cPsi sP
                    ^ "  schema= "
                    ^ P.schemaToString schema) in
    match elements with
      | [] -> None
      | (Int.LF.SchElem (_some_part, block_part)) as elem  ::  rest  ->
          try
            Check.LF.checkTypeAgainstElementProjection cO cD cPsi sP (head, k) elem
          ; Some block_part
          with _exn -> self (Int.LF.Schema rest)

and lookupCtxVar = function
  | Int.LF.Empty -> raise (Violation ("Context variable not found"))
  | Int.LF.Dec (cO, Int.LF.CDecl (psi, schemaName)) -> function
      | Int.LF.CtxName phi when psi = phi -> (psi, schemaName)
      | (Int.LF.CtxName _phi) as ctx_var  -> lookupCtxVar cO ctx_var
      | Int.LF.CtxOffset 1                -> (psi, schemaName)
      | Int.LF.CtxOffset n                -> lookupCtxVar cO (Int.LF.CtxOffset (n - 1))

and elTerm' recT cO cD cPsi r sP = match r with
  | Apx.LF.Root (loc,  Apx.LF.Proj ((Apx.LF.FPVar (p, s) as _head), k),  Apx.LF.Nil) as m ->
      begin try
        let _ = dprint (fun () -> "1") in
        let (offset, (_tA, cPhi)) = Cwhnf.mctxPVarPos cD p  in
          
        let s'' = elSub recT cO cD cPsi s cPhi in
          Int.LF.Root (Some loc,
                       Int.LF.Proj (Int.LF.PVar (Int.LF.Offset offset, s''), k),
                       Int.LF.Nil)
            
      with Cwhnf.Fmvar_not_found ->
        begin try
        let _ = dprint (fun () -> "2") in
          let (_tA, cPhi) = FPVar.get p in
          let s'' = elSub recT cO cD cPsi s cPhi in
            Int.LF.Root (Some loc,  Int.LF.FPVar (p, s''),  Int.LF.Nil)
        with Not_found ->
        let _ = dprint (fun () -> "3") in
          begin match isPatSub s with
            | true ->
                let (_givenType, givenSub) = sP in
                let (cPhi, s'') = synDom cPsi s in
                let si          = Substitution.LF.invert s'' in
                let psi = match Context.ctxVar cPsi with Some psi -> psi in
                let schemaOfP = Schema.get_schema (snd (lookupCtxVar cO psi)) in
                let head' = Int.LF.FPVar (p, s'') in
                let typrecFromSchema = match elFindInContext recT cO cD cPsi sP (head', k) schemaOfP with
                  | None -> raise (Violation ("type sP not in psi's schema"))
                  | Some typrec -> typrec in
                let typeFromSchema = match typrecFromSchema with
                  | Int.LF.SigmaLast oneType -> oneType
                  | actualSigma -> Int.LF.Sigma actualSigma in
                let tP          = Int.LF.TClo(Int.LF.TClo (typeFromSchema, givenSub), si) in
                let _ = dprint (fun () -> "elTerm'    | (Apx.LF.Root (loc, Apx.LF.FPVar (p, s), []) as m) ->\n"
                                        ^ "tP = " ^ P.typToString cO cD cPsi (tP, LF.id) ^ "\n"
                                        ^ "cPhi = " ^ P.dctxToString cO cD cPhi) in
                  (* For type reconstruction to succeed, we must have
                   * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
                   * This will be enforced during abstraction.
                   *)
                  FPVar.add p (tP, cPhi);
                  Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.FPVar (p, s''), k),  Int.LF.Nil)
                    
            | false ->
                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc,  Int.LF.Proj (Int.LF.PVar (q, LF.id), k),  Int.LF.Nil)
          end
        end
      end
  
  | Apx.LF.Root (loc,  Apx.LF.Proj (tuple_r, k),  Apx.LF.Nil) ->
       let Int.LF.Root(_, internal_tuple_r, _) =
         elTerm' recT cO cD cPsi (Apx.LF.Root(loc, tuple_r, Apx.LF.Nil)) sP
      in
       let _ = dprint(fun () -> "elTerm' Proj\n"
                       ^ "    tP (under s) = " ^ P.typToString cO cD cPsi sP ^ "\n"
                       ^ "            cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                       ^ "internal_tuple_r = " ^ P.headToString cO cD cPsi internal_tuple_r
                     )
       in
         Int.LF.Root (Some loc,  Int.LF.Proj (internal_tuple_r, k),  Int.LF.Nil)
  
  | Apx.LF.Root (loc, Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      (* let s  = mkShift recT cPsi in *)
      let s = LF.id in
      let tS = elSpineI recT cO cD cPsi spine i (tA, s)  in
        Int.LF.Root (Some loc, Int.LF.Const c, tS)

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine recT cO cD cPsi spine (tA, LF.id) in
        Int.LF.Root (Some loc, Int.LF.BVar x, tS)

  | Apx.LF.Root (loc, Apx.LF.Hole, spine) ->
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
            Int.LF.Root (Some loc, Int.LF.MVar(u, LF.id), tS)
        else
          (Printf.printf "elTerm' encountered hole with non-pattern spine\n";
           raise NotImplemented)

  | Apx.LF.Root (loc, Apx.LF.MVar (u, s'), spine) ->
      let _ = dprint (fun () -> "elTerm: Looking for " ^ R.render_cvar cD u) in  
      let _ = dprint (fun () -> " \n in context " ^ P.mctxToString cO cD) in 
      let (tA, cPhi) = Cwhnf.mctxMDec cD u in
      let _  = dprint (fun () -> "Found type : " ^ P.typToString cO cD cPhi (tA, LF.id) ^ 
                       "\n in context " ^ P.dctxToString cO cD cPhi) in 
      let _ = dprint (fun () -> " and range : " ^ P.dctxToString cO cD cPhi) in
      let s'' = elSub recT cO cD cPsi s' cPhi in
      let tS = elSpine recT cO cD cPsi spine (tA, s'')  in
        Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset u, s''), tS)

  | Apx.LF.Root (loc, Apx.LF.PVar (p,s'), spine) ->
      let (tA, cPhi) = Cwhnf.mctxPDec cD p in
      let s'' = elSub recT cO cD cPsi s' cPhi in
      let tS = elSpine recT cO cD cPsi spine (tA, s'')  in
        Int.LF.Root (Some loc, Int.LF.PVar (Int.LF.Offset p, s''), tS)

  | Apx.LF.Root (loc, Apx.LF.FVar x, spine) as m ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
           *
           *  . |- tA <= type
           *  This will be enforced during abstraction
           *)
        let s = mkShift recT cPsi in
        let tS = elSpine recT cO cD cPsi spine (tA, s) in
          Int.LF.Root (Some loc, Int.LF.FVar x, tS)
      with Not_found ->
        let (patternSpine, _l) = patSpine spine in
          if patternSpine then
            let s = mkShift recT cPsi in
            let (tS, tA) = elSpineSynth cD cPsi spine s sP in
              (* For type reconstruction to succeed, we must have
               *  . |- tA <= type  and cPsi |- tS : tA <= [s]tP
               *  This will be enforced during abstraction.
               *)
              FVar.add x tA;
              Int.LF.Root (Some loc, Int.LF.FVar x, tS)
          else
            let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
              add_fvarCnstr (m, v);
              Int.LF.Root (Some loc, Int.LF.MVar (v, LF.id), Int.LF.Nil)
      end

  (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) as m ->
      let _ = dprint (fun () -> "elTerm: FMVar " ^ R.render_name u) in  

      begin try
        (* For named free meta-variables which may occur in branches of case-expressions;
         * these named free meta-variables may be bound by the pattern.
         *)
        let (offset, (_tP, cPhi)) = Cwhnf.mctxMVarPos cD u in
        let s'' = elSub recT cO cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' --
             this check is delayed to reconstruction *)
          Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset offset, s''), Int.LF.Nil)

      with Cwhnf.Fmvar_not_found ->
        begin try
          let (_tP, cPhi) = FMVar.get u in
            (* For type reconstruction to succeed, we must have
             *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
             * meta-variables in cD. This will be enforced during abstraction *)
          let s'' = elSub recT cO cD cPsi s cPhi in
            (* We do not check here that tP approx. [s']tP' --
             * this check is delayed to reconstruction *)
            Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil)

        with Not_found ->
          if isPatSub s then
            (* 1) given cPsi and s synthesize the domain cPhi
             * 2) [s]^-1 ([s']tP) is the type of u
             *)

            let (cPhi, s'') = synDom cPsi s in
            let tP = Int.LF.TClo (Int.LF.TClo sP, Substitution.LF.invert s'') in
              (* For type reconstruction to succeed, we must have
               * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
               * This will be enforced during abstraction.
               *)
              FMVar.add u (tP, cPhi);
              Int.LF.Root (Some loc, Int.LF.FMVar (u, s''), Int.LF.Nil)
          else
            let v = Whnf.newMVar (cPsi, Int.LF.TClo sP) in
              add_fcvarCnstr (m, v);
              Int.LF.Root (Some loc, Int.LF.MVar (v, LF.id), Int.LF.Nil)
        end
      end


  | Apx.LF.Root (loc, Apx.LF.FPVar (p, s), spine) as m ->
      begin try
        (* For named free parameter variables that may occur in branches of case expressions;
         * these named free parameter variables may be bound by the pattern.
         *)
        let (offset, (tA, cPhi)) = Cwhnf.mctxPVarPos cD p  in

        let s'' = elSub recT cO cD cPsi s cPhi in
          (* We do not check here that tP approx. [s']tP' -- this check is delayed to reconstruction *)
          Int.LF.Root (Some loc,
                       Int.LF.PVar (Int.LF.Offset offset, s''),
                       elSpine recT cO cD cPsi spine (tA, s''))
      
      with Cwhnf.Fmvar_not_found ->
        begin try
          let (tA, cPhi) = FPVar.get p in
            (* For type reconstruction to succeed, we must have
             *    . ; cPsi |- tA <= type , i.e. cPsi and tA cannot depend on
             * meta-variables in cD. This will be enforced during abstraction *)
      
          let s'' = elSub recT cO cD cPsi s cPhi in
          let _ = dprint (fun () -> "Not checking: \n"
                                  ^ "  Given type  sP = " ^ P.typToString cO cD cPsi sP ^ "\n"
                                  ^ "  Inferred type  = " ^ P.typToString cO cD cPsi (tA, s'')) in
            (* We do not check here that tP approx. [s']tP' --
             * this check is delayed to reconstruction *)
            Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), elSpine recT cO cD cPsi spine (tA, s''))
      
        with Not_found ->
          begin match (spine, isPatSub s) with
            | (Apx.LF.Nil, true) ->
                (* 1) given cPsi and s, synthesize the domain cPhi
                 * 2) [s]^-1 ([s']tP) is the type of u
                 *)
                let (cPhi, s'') = synDom cPsi s in
                let si          = Substitution.LF.invert s'' in
                let tP          = Int.LF.TClo( Int.LF.TClo sP, si) in
                let _ = dprint (fun () -> "elTerm'    | (Apx.LF.Root (loc, Apx.LF.FPVar (p, s), spine) as m) ->\n"
                                        ^ "tP = " ^ P.typToString cO cD cPsi (tP, LF.id) ^ "\n"
                                        ^ "cPhi = " ^ P.dctxToString cO cD cPhi) in
                  (* For type reconstruction to succeed, we must have
                   * . ; cPhi |- tP <= type  and . ; cPsi |- s <= cPhi
                   * This will be enforced during abstraction.
                   *)
                  FPVar.add p (tP, cPhi);
                  Int.LF.Root (Some loc, Int.LF.FPVar (p, s''), Int.LF.Nil)
            
            | (Apx.LF.Nil, false) ->
                let q = Whnf.newPVar (cPsi, Int.LF.TClo sP) in
                  add_fcvarCnstr (m, q);
                  Int.LF.Root (Some loc, Int.LF.PVar (q, LF.id), Int.LF.Nil)
            
            | (_, _) -> (Printf.printf "elTerm': FPVar with non-pattern spine\n" ; raise NotImplemented)
          end
        end
      end

and elClosedTerm' recT cO cD cPsi r = match r with
  | Apx.LF.Root (loc, Apx.LF.Const c, spine) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      (* let s  = mkShift recT cPsi in *)
      let s = LF.id in
      let tS = elSpineI recT cO cD cPsi spine i (tA, s)  in
        Int.LF.Root (Some loc, Int.LF.Const c, tS)

  | Apx.LF.Root (loc, Apx.LF.BVar x, spine) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine recT cO cD cPsi spine (tA, LF.id) in
        Int.LF.Root (Some loc, Int.LF.BVar x, tS)

  | Apx.LF.Root (loc, Apx.LF.MVar (u, s), spine) ->
      let _ = dprint (fun () -> "elClosed: Looking for " ^ R.render_cvar cD u ^ " \n in context " ^ P.mctxToString cO cD) in 
      let (tA, cPhi) = Cwhnf.mctxMDec cD u in
      let s'' = elSub recT cO cD cPsi s cPhi in
      let tS = elSpine recT cO cD cPsi spine (tA, s'')  in
        Int.LF.Root (Some loc, Int.LF.MVar (Int.LF.Offset u, s''), tS)

  | Apx.LF.Root (loc, Apx.LF.PVar (p, s'), spine) ->
      let (tA, cPhi) = Cwhnf.mctxPDec cD p in
      let s'' = elSub recT cO cD cPsi s' cPhi in
      let tS = elSpine recT cO cD cPsi spine (tA, s'')  in
        Int.LF.Root (Some loc, Int.LF.PVar (Int.LF.Offset p, s''), tS)

  | _ ->
      raise (Violation "synthesis of term failed (use typing annotation)")

  (* TODO find a way to postpone type mismatch to reconstruction step *)

and frontToString _cO _cD _cPsi = function
  | Apx.LF.Head _head -> "head"
  | Apx.LF.Obj (Apx.LF.Tuple _) -> "tuple"
  | Apx.LF.Obj _m -> "obj"

and subToString cO cD cPsi = function
  | Apx.LF.EmptySub -> "."
  | Apx.LF.Id -> ".."
  | Apx.LF.Dot (front, s) -> subToString cO cD cPsi s ^ " " ^ frontToString cO cD cPsi front

(* elSub recT cO cD cPsi s cPhi = s'
 *
 * We elaborate the substitution s, but we do not check if it is
 * approximately well-typed.
 *)
and elSub recT cO cD cPsi s cPhi =
  let _ = dprint (fun () -> "elSub: " ^ "`" ^ subToString cO cD cPsi s ^ "';  `" ^ P.dctxToString cO cD cPhi ^ "'")
  in
  match (s, cPhi) with
  | (Apx.LF.EmptySub, Int.LF.Null) ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) -> Int.LF.Shift (Int.LF.CtxShift psi, d)
        | (None, d)     -> Int.LF.Shift (Int.LF.NoCtxShift, d)
      end

  | (Apx.LF.Id, Int.LF.CtxVar phi) ->
      begin match Context.dctxToHat cPsi with
        | (Some psi, d) ->
            if psi = phi then
              Int.LF.Shift(Int.LF.NoCtxShift, d)
            else
              raise (Violation ("elSub: Id must be associated with same ctxvar: "
                              ^ "`" ^ P.dctxToString cO cD cPhi ^ "' does not match `" ^ P.dctxToString cO cD cPsi ^ "'"))
        | _ ->
            raise (Violation "Id must be associated with ctxvar")
      end

  | (Apx.LF.Dot (Apx.LF.Head Apx.LF.Hole, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl(_x, tA))) ->
      begin match tA with
        | Int.LF.Atom _ ->
            let s' = mkShift recT cPsi in
            let ss = LF.invert s' in
            let u  = Whnf.newMVar (cPsi, Int.LF.TClo(tA, ss)) in
              Int.LF.Dot (Int.LF.Head (Int.LF.MVar(u, LF.id)), elSub recT cO cD cPsi s cPhi')
        | _ -> raise (Violation "Omitted arguments must be of atomic type; eta-expansion needed")
      end

  | (Apx.LF.Dot (Apx.LF.Head h, s),   Int.LF.DDec (cPhi', _decl)) ->
      (* NOTE: if decl = x:A, and cPsi(h) = A' s.t. A =/= A'
       *       we will fail during reconstruction / type checking
       *)
        Int.LF.Dot (Int.LF.Head (elHead recT cO cD cPsi h), elSub recT cO cD cPsi s cPhi')

  | (Apx.LF.Dot (Apx.LF.Obj m, s),   Int.LF.DDec (cPhi', Int.LF.TypDecl(_, tA))) ->
      let s' = elSub recT cO cD cPsi s cPhi' in
      let m' = elTerm recT cO cD cPsi m (tA, s') in
        Int.LF.Dot (Int.LF.Obj m', s')

  | (Apx.LF.Dot _, Int.LF.Null) ->      raise (Violation ("elSub (Dot _, Null)"))
  | (Apx.LF.Dot _, Int.LF.DDec _) ->      raise (Violation ("elSub (Dot _, DDec _)"))
  | (Apx.LF.Dot _, Int.LF.CtxVar _) ->      raise (Violation ("elSub (Dot _, CtxVar _)"))
  | (Apx.LF.Id, Int.LF.Null) ->      raise (Violation ("elSub (Id, Null)"))

  | (_s, cPhi) ->
      raise (Violation ("elSub: " ^ " substitution incompatible w/ `" ^ P.dctxToString cO cD cPhi ^ "'"))


and elHead recT cO cD cPsi = function
  | Apx.LF.BVar x ->
      Int.LF.BVar x

  | Apx.LF.Const c ->
      Int.LF.Const c

  | Apx.LF.MVar (u, s) ->
      let _ = dprint (fun () -> "elHead: Looking for " ^ R.render_cvar cD u ^ " \n in context " ^ P.mctxToString cO cD) in 
      let (_tA, cPhi) = Cwhnf.mctxMDec cD u in
        Int.LF.MVar (Int.LF.Offset u, elSub recT cO cD cPsi s cPhi)

  | Apx.LF.PVar (p, s) ->
      let (_tA, cPhi) = Cwhnf.mctxPDec cD p in
        Int.LF.PVar (Int.LF.Offset p, elSub recT cO cD cPsi s cPhi)

  | Apx.LF.FVar x ->
      Int.LF.FVar x

  | Apx.LF.FMVar (u, s) ->
        let (offset, (_tP, cPhi)) = Cwhnf.mctxMVarPos cD u  in
        Int.LF.MVar (Int.LF.Offset offset, elSub recT cO cD cPsi s cPhi)

  | Apx.LF.FPVar (p, s) ->
      let (offset, (_tA, cPhi)) = Cwhnf.mctxPVarPos cD p  in
        Int.LF.PVar (Int.LF.Offset offset, elSub recT cO cD cPsi s cPhi)

  | Apx.LF.Proj (head, i) ->
      let head' = elHead recT cO cD cPsi head in
        Int.LF.Proj (head', i)


(* elSpineI  recT cO cD cPsi spine i sA sP  = S
 * elSpineIW recT cO cD cPsi spine i sA sP  = S
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
and elSpineI recT cO cD cPsi spine i sA =
  elSpineIW recT cO cD cPsi spine i (Whnf.whnfTyp sA)

and elSpineIW recT cO cD cPsi spine i sA =
  if i = 0 then
    elSpine recT cO cD cPsi spine sA
  else
    match (sA, recT) with
      | ((Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s), PiRecon) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           *
           * tN = u[s']  and u::A'[.]
           *
           * s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
           *   and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)
           *)
          (* let (_, d) = Context.dctxToHat cPsi in

          let tN     = Whnf.etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift(Int.LF.NoCtxShift, d)) in   *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in
          let spine' = elSpineI recT cO cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

      | ((Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _), tB), s), PiboxRecon) ->
          (* cPsi' |- tA <= typ
           * cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A
           *
           * tN = u[s']  and u::P[Psi, x1:A1,....xn:An]  and A = Pi x1:A1 ... Pi xn:An.P
           *
           * s.t.  cPsi |- \x1...\xn. u[id] => [id]A  where cPsi |- id : cPsi
           *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in

          let spine' = elSpineI recT cO cD cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')
      (* other cases impossible by (soundness?) of abstraction *)

(* elSpine recT cO cD cPsi spine sA = S
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
and elSpine recT cO cD cPsi spine sA =
  elSpineW recT cO cD cPsi spine (Whnf.whnfTyp sA)

and elSpineW recT cO cD cPsi spine sA = match (spine, sA) with
  | (Apx.LF.Nil, (_tP , _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s)) ->
      let tM = elTerm recT cO cD cPsi m (tA, s) in
      let tS = elSpine recT cO cD cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      (Printf.printf "elSpineW: ill-typed\n";
      raise NotImplemented) (* TODO postpone error to reconstruction phase *)

(* see invariant for elSpineI *)
and elKSpineI recT cO cD cPsi spine i sK =
  if i = 0 then
    elKSpine recT cO cD cPsi spine sK
  else
    match sK with
      | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA), _), tK), s) ->
          (* let sshift = mkShift recT cPsi in *)
          (* let tN     = Whnf.etaExpandMV Int.LF.Null (tA,s) sshift in *)
          let tN     = Whnf.etaExpandMV cPsi (tA, s) LF.id in
          let spine' = elKSpineI recT cO cD cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

(* other cases impossible by (soundness?) of abstraction *)

(* see invariant for elSpine *)
and elKSpine recT cO cD cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (_tK, _s)) ->
      Int.LF.Nil (* errors are postponed to reconstruction phase *)

  | (Apx.LF.App (m, spine), (Int.LF.PiKind ((Int.LF.TypDecl (_, tA), _), tK), s)) ->
      let tM = elTerm recT cO cD cPsi m (tA, s) in
      let tS = elKSpine recT cO cD cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      (Printf.printf "elKSpine: spine ill-kinded\n";
      raise NotImplemented )(* TODO postpone error to reconstruction phase *)

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
  | (Apx.LF.Nil, (_tP, _s))  ->
      let ss = LF.invert s' in
      let tQ = Unify.pruneTyp cD (Context.dctxToHat cPsi,  sP, ss, Unify.MVarRef (ref None)) in 
      (* PROBLEM: [s'][ss] [s]P is not really P; in fact [ss][s]P may not exist;
       *  We using pruning to ensure that [ss][s]P does exist
       *)
        (Int.LF.Nil, tQ) 

  | (Apx.LF.App (Apx.LF.Root (loc, Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        (* cPsi |- tA : type
         * cPsi |- s' : cPsi'
         *)
      let ss = LF.invert s' in
      (* Is [ss]A  always guaranteed to exist? - bp *)
      let tA' = Unify.pruneTyp cD (Context.dctxToHat cPsi,  (tA, LF.id), ss, Unify.MVarRef (ref None)) in 
      (* let tA' = Whnf.normTyp (tA, ss) in *)

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth cD cPsi spine (Int.LF.Dot (Int.LF.Head(Int.LF.BVar x), s')) sP in

        (*  cPsi |- tS : [s', x]tB <- sP  (pre-dependent) *)

        (* cPsi, y:A |- tB' <- type (pre-dependent) *)

        (Int.LF.App (Int.LF.Root (Some loc, Int.LF.BVar x, Int.LF.Nil), tS),
         Int.LF.PiTyp ((Int.LF.TypDecl (Id.mk_name (Id.BVarName (Typ.gen_var_name tA')), tA'), Int.LF.Maybe), tB))

   (* other cases impossible *)

(* REVISE DEFINITION OF SCHEMA ELEMENTS:

   It would be more convenient if ctx were
   a dctx, since then we can do simple type-checking
   of the rest of the typrec. -bp

   TODO double check -bp
   *)

let rec projectCtxIntoDctx = function
  | Int.LF.Empty            -> Int.LF.Null
  | Int.LF.Dec (rest, last) -> Int.LF.DDec (projectCtxIntoDctx rest, last)

let rec elTypDeclCtx cO cD cPsi = function
  | Apx.LF.Empty ->
      Int.LF.Empty

  | Apx.LF.Dec (ctx, Apx.LF.TypDecl (name, typ)) ->
      let ctx'     = elTypDeclCtx cO cD cPsi ctx in
      let typDecl' = Int.LF.TypDecl (name, elTyp PiRecon cO cD cPsi typ) in
        Int.LF.Dec (ctx', typDecl')

let rec elSchElem cO (Apx.LF.SchElem (ctx, typRec)) =
   let cD = Int.LF.Empty in
   let el_ctx = elTypDeclCtx cO cD Int.LF.Null in
   let dctx = projectCtxIntoDctx (el_ctx ctx) in
   let typRec' = elTypRec PiRecon cO cD dctx typRec in
     Int.LF.SchElem(el_ctx ctx, typRec')

let rec elSchema cO (Apx.LF.Schema el_list) =
   Int.LF.Schema (List.map (elSchElem cO) el_list)

let rec elDCtx recT cO cD psi = match psi with
  | Apx.LF.Null -> Int.LF.Null

  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) -> Int.LF.CtxVar (Int.LF.CtxOffset offset)
  | Apx.LF.CtxVar (Apx.LF.CtxName psi)      -> Int.LF.CtxVar (Int.LF.CtxName psi)

  | Apx.LF.DDec (psi', Apx.LF.TypDecl (x, a)) ->
      let cPsi = elDCtx recT cO cD psi' in
      let tA   = elTyp recT cO cD cPsi a in
        Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))

let rec elCDecl recT cO cD cdecl = match cdecl with
  | Apx.LF.MDecl (u, a, psi) ->
      let cPsi = elDCtx recT cO cD psi in
      let tA   = elTyp recT cO cD cPsi a in
        Int.LF.MDecl (u, tA, cPsi)
  | Apx.LF.PDecl (u, a, psi) ->
      let cPsi = elDCtx recT cO cD psi in
      let tA   = elTyp recT cO cD cPsi a in
        Int.LF.PDecl (u, tA, cPsi)


let rec elMCtx recT cO delta = match delta with
  | Apx.LF.Empty -> Int.LF.Empty
  | Apx.LF.Dec (delta, cdec) ->
      let cD    = elMCtx recT cO delta in
      let cdec' = elCDecl recT cO cD cdec in
        Int.LF.Dec (cD, cdec')


(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr recT cO cD cnstr = match cnstr with
  | [] -> ()
  | ((Apx.LF.Root (loc, Apx.LF.FVar x, spine), Int.LF.Inst (r, cPsi, _, _)) :: cnstrs) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
           *  . |- tA <= type
           *  This will be enforced during abstraction.
           *)
        let sshift = mkShift recT cPsi in

        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let tS = elSpine recT cO cD cPsi spine (tA, sshift) in
          r := Some (Int.LF.Root (Some loc, Int.LF.FVar x, tS));
          solve_fvarCnstr recT cO cD cnstrs
      with Not_found ->
        raise (Error (None, LeftoverConstraints x))
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
 *   - destructively updates all meta-variables in O;
 *   - may raise Error, if no modal substitution r exists.
 *
 * Similar invariants and pre- and post-conditions for:
 *
 *  recKind cD cPsi (K,s) = K'
 *  recT  cD cPsi (A,s) = A'
 *)

let rec recTerm recT cO cD  cPsi sM sA =
  recTermW recT cO cD  cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW recT cO cD cPsi sM sA = match (sM, sA) with
  | ((Int.LF.Lam (_, _, tM), s'),   (Int.LF.PiTyp ((tA, _ ), tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
        recTerm recT cO cD  cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)


  | ((Int.LF.Root (loc, _, _), _) as sR,   (Int.LF.Atom _, _)) ->
      begin
        try
          let _ = dprint (fun () -> "recTerm: " ^
            P.mctxToString cO cD ^ "\n      |- " ^
            P.normalToString cO cD cPsi sR ^ "\n       : " ^
            P.typToString cO cD cPsi sA ^ "\n" ) in 

          let sP' = synTermW recT cO cD  cPsi sR in

          let _ = dprint (fun () -> " recTerm: synthesized " ^
            P.mctxToString cO cD ^ "\n |- " ^ 
            P.normalToString cO cD cPsi sR ^ "\n    of type " 
                            ^ P.typToString cO cD cPsi sP' ^ "\n") in  
            try
              Unify.unifyTyp cD  (Context.dctxToHat cPsi, sP', sA) 
            with Unify.Unify msg ->
              (Printf.printf "%s\n" msg;
              raise (Error (loc, TypMismatch (cO, cD, cPsi, sM, sA, sP'))))
      with SpineMismatch ->
        raise (Error (loc, (IllTyped (cO, cD, cPsi, sM, sA))))
      end
  
  | ((Int.LF.Root (loc, _, _), _),   _) ->
      (Printf.printf "recTerm: Root object of non-atomic type\n";
       raise (Error (loc, IllTyped (cO, cD, cPsi, sM, sA))))
  
  | ((Int.LF.Lam (loc, _, _), _),   _) ->
      (Printf.printf "recTerm: Lam object of atomic type\n";
       raise (Error (loc, IllTyped (cO, cD, cPsi, sM, sA))))

(* synTerm cO cD  cPsi sR = sP *)
and synTerm recT cO cD  cPsi sR =
   synTermW recT cO cD  cPsi (Whnf.whnf sR)

and synTermW recT cO cD  cPsi ((root, s') as sR) = match root with
    | Int.LF.Root (_, head, tS) ->
        let rec synHead = function
          | Int.LF.Const c ->
              let tA = (Term.get c).Term.typ in
              let sshift = mkShift recT cPsi in
                synSpine recT cO cD  cPsi (tS, s') (tA, sshift)
          
          | Int.LF.BVar x ->
              let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
                synSpine recT cO cD  cPsi (tS, s') (tA, LF.id)
          
          | Int.LF.MVar (Int.LF.Inst (_r, cPhi, tP', _cnstr), t) ->
              (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
              (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
              let s1 = (LF.comp t s') in
                recSub recT cO cD  cPsi s1 cPhi;
                (tP', s1)
          
          | Int.LF.MVar (Int.LF.Offset u, t) ->
              (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
              (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
              let s1 = (LF.comp t s') in
              let (tP', cPsi') = Cwhnf.mctxMDec cD u in
                recSub recT cO cD  cPsi s1 cPsi';
                (tP', s1)
          
          | Int.LF.FMVar (u, t) ->
              (* By invariant of whnf: tS = Nil *)
              let s1 = (LF.comp t s') in
              let (tP', cPhi) = FMVar.get u in
                recSub recT cO cD  cPsi s1 cPhi;
                (tP', s1)
          
          | Int.LF.FPVar (p, t) ->
              let s1 = (LF.comp t s') in
              let (tA', cPhi) = FPVar.get p in
                (* cPsi |- t : cPhi *)
                recSub recT cO cD  cPsi s1 cPhi;
                synSpine recT cO cD  cPsi (tS, s') (tA',t)
          
          | Int.LF.PVar (Int.LF.Offset p, t) ->
              let s1 = (LF.comp t s') in
              let (tA, cPsi') = Cwhnf.mctxPDec cD p in
                recSub recT cO cD  cPsi s1 cPsi';
                synSpine recT cO cD  cPsi (tS, s') (tA, t)
          
          | Int.LF.Proj (tuple_head, k) ->
              begin 
                dprint (fun () -> "synTermW \n"
                          ^ "  Proj(" ^ P.headToString cO cD cPsi tuple_head ^ ", #" ^ string_of_int k ^")"
                          ^ "  cO = " ^ P.octxToString cO) ;
                let (getTypeArg, (tTuple, cPhi)) = match tuple_head with
                | Int.LF.BVar x ->
                    let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
                      (Int.LF.BVar x
                     , synSpine recT cO cD  cPsi (tS, s') (tA, LF.id))

                | Int.LF.PVar (Int.LF.Offset p, t) ->
                    let s1 = (LF.comp t s') in
                    let (tA, cPsi') = Cwhnf.mctxPDec cD p in
                    let _ = dprint(fun()-> "   tA = " ^ P.typToString cO cD cPsi (tA, t)) in
                    let _ = dprint(fun()-> "cPsi' = " ^ P.dctxToString cO cD cPsi') in
                      recSub recT cO cD  cPsi s1 cPsi'
                    ; (Int.LF.PVar (Int.LF.Offset p, t)
                     , synSpine recT cO cD  cPsi (tS, s') (tA, t))

                | Int.LF.FPVar (p, t) ->
                    let s1 = (LF.comp t s') in
                    let (tA', cPhi) = FPVar.get p in
                    let _ = dprint(fun()-> "FPVar   tA' = " ^ P.typToString cO cD cPsi (tA', t)) in
                    let _ = dprint(fun()-> "FPVar  cPhi = " ^ P.dctxToString cO cD cPhi) in
                      (* cPsi |- t : cPhi *)
                      recSub recT cO cD  cPsi s1 cPhi
                    ; (Int.LF.FPVar (p, t)
                     , synSpine recT cO cD  cPsi (tS, s') (tA',t))
              in
                match tTuple with
                  | Int.LF.Sigma typRec ->
                      let _ = dprint(fun () -> "tTuple Sigma") in
                        Int.LF.getType getTypeArg (typRec, cPhi) k 1

                  | _ -> raise (Violation ("synTermW Proj not Sigma --"
                                          ^ P.typToString cO cD cPsi (tTuple, cPhi)))
              end
          
          | Int.LF.FVar x ->
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
              let _ = dprint (fun () -> "synTerm FVAR " ^  (P.normalToString cO cD cPsi sR)
                                ^ "\n\n" ) in 
              let (None , d) = Context.dctxToHat cPsi in
              let _ = dprint (fun () -> "of type " ^ 
                                (P.typToString cO cD cPsi (tA, Int.LF.Shift (Int.LF.NoCtxShift, d))) ^ " \n\n " )
              in 
              let s = mkShift PiRecon cPsi in 
                (* synSpine recT cO cD  cPsi (tS, s') (tA, Int.LF.Shift (Int.LF.NoCtxShift, d)) *)
                synSpine recT cO cD  cPsi (tS, s') (tA, s) 
        in
          synHead head

and synSpine recT cO cD  cPsi sS sA =
  synSpineW recT cO cD  cPsi sS (Whnf.whnfTyp sA)

and synSpineW recT cO cD  cPsi sS sA = match (sS, sA) with
  | ((Int.LF.Nil, _s), sP') ->
      sP'

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiTyp ((Int.LF.TypDecl (_, tA), _ ), tB), s)) ->
      let _  =  recTerm recT cO cD  cPsi (tM, s') (tA, s) in 
      let _ = dprint (fun () -> "\n synSpine: tM " ^ 
            (P.normalToString cO cD cPsi (tM, s')) ^ "\n    of type " 
                            ^ (P.typToString cO cD cPsi (tA, s)) ^ "\n\n") in  

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
      synSpine recT cO cD  cPsi (tS, s') (tB, Int.LF.Dot (Int.LF.Obj (Int.LF.Clo (tM,s')), s))

  | ((Int.LF.SClo (tS, s), s'), sA) ->
      synSpine recT cO cD  cPsi (tS, LF.comp s s') sA

  | ((Int.LF.App _, _), (Int.LF.Atom _, _)) ->
      Printf.printf "synSpineW: Type mismatch\n";
      raise SpineMismatch


and recSub recT cO cD cPsi_ s cPhi_ =
  dprint (fun () -> "recSub \n  "
            ^ P.dctxToString cO cD cPsi_ ^ "\n  "
            ^ P.subToString cO cD cPsi_ s ^ "\n  "
            ^ P.dctxToString cO cD cPhi_
         );
  match (cPsi_, s, cPhi_) with
(*  | (Int.LF.Shift (_, _n), _cPhi) ->
      (* We may need to expand cPhi further if n =/= 0 *)
      ()
*)

  (* Null  Null *)
  | (Int.LF.Null,  Int.LF.Shift (Int.LF.NoCtxShift, 0),
     Int.LF.Null) -> ()

  (* CtxVar  CtxVar *)
  | (Int.LF.CtxVar psi,  Int.LF.Shift (Int.LF.NoCtxShift, 0),
     Int.LF.CtxVar psi') ->
      if psi = psi' then
        ()
      else
        raise (Violation "Context variable mismatch")

  (* CtxVar  Null *)
  | (Int.LF.CtxVar psi,  Int.LF.Shift (Int.LF.CtxShift psi', 0),
     Int.LF.Null)  ->
      if psi = psi' then
        ()
      else
        raise (Violation "Context variable mismatch")

  (* Null  CtxVar *)          
  | (Int.LF.Null,  Int.LF.Shift (Int.LF.NegCtxShift psi, 0),
     Int.LF.CtxVar psi')  ->
      if psi = psi' then
        () 
      else
        raise (Violation "Substitution ill-typed -- negative shift on CtxVar")

  (* (cPsi, _:tX)  Null *)
  | (Int.LF.DDec (cPsi, _tX),  Int.LF.Shift (psi, k),
     Int.LF.Null)   ->
      if k > 0 then
        recSub recT cO cD  cPsi (Int.LF.Shift (psi, k - 1)) Int.LF.Null
      else
        raise (Violation "Substitution ill-typed")
  
  (* (cPsi, _:tX)  CtxVar *)
  | (Int.LF.DDec (cPsi, _tX),  Int.LF.Shift (phi, k),
     Int.LF.CtxVar psi) ->
      if k > 0 then
        recSub recT cO cD  cPsi (Int.LF.Shift (phi, k - 1)) (Int.LF.CtxVar psi)
      else
        raise (Violation ("Substitution ill-typed; k = %s" ^ string_of_int k))
          (* (SubIllTyped) *)
  
  (* cPsi  cPhi *)
  | (cPsi,  Int.LF.Shift (psi, k),
     cPhi) ->
      let s' = (Int.LF.Dot (Int.LF.Head (Int.LF.BVar (k + 1)), Int.LF.Shift (psi, k + 1))) in
        recSub recT cO cD  cPsi s' cPhi
  
  (* cPsi   (cPhi, _:tA) *)
  | (cPsi,  Int.LF.Dot (Int.LF.Head (Int.LF.BVar x), rest),
     Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA)))
    ->
      let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
      let _ = recSub recT cO cD  cPsi rest cPhi in 
        Unify.unifyTyp cD (Context.dctxToHat cPsi, (tA', LF.id), (tA, rest))

  (* cPsi   (cPhi, _:tA) *)
  | (cPsi,  Int.LF.Dot (Int.LF.Head (Int.LF.Proj (Int.LF.BVar x, projIndex)), rest),
     Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA)))
    ->
      begin 
        dprint (fun () -> "recSub Proj \n  "
                        ^ P.dctxToString cO cD cPsi ^ "\n  "
                        ^ P.subToString cO cD cPsi s ^ "\n  "
                        ^ P.dctxToString cO cD cPhi
        );
        let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in
          dprint (fun () -> "  got type: " ^ P.typToString cO cD cPsi (tA', LF.id));
          match Whnf.normTyp (tA', LF.id) with
            | Int.LF.Sigma tA'rec ->
                let _ = dprint (fun () -> "  got Sigma " ^ P.typRecToString cO cD cPsi (tA'rec, LF.id)) in
                let sA' = Int.LF.getType (Int.LF.BVar x) (tA'rec, LF.id) projIndex 1 in
                let _ = dprint (fun () -> "  got _." ^ string_of_int projIndex ^ " = " ^ P.typToString cO cD cPsi sA') in
                let _   = recSub recT cO cD  cPsi rest cPhi in
                  Unify.unifyTyp cD (Context.dctxToHat cPsi, sA', (tA, rest))              
            
            | tA' -> raise (Violation ("recSub _ (" ^ P.subToString cO cD cPsi s
                                       ^ ") _; type " ^ P.typToString cO cD cPsi (tA', LF.id)))
      end

  (* cPsi  (cPhi, _:tA) *)
  | (cPsi,  Int.LF.Dot (Int.LF.Obj tM, s),
     Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA)))
    ->
      recSub  recT cO cD  cPsi s cPhi;
      recTerm recT cO cD  cPsi (tM, LF.id) (tA, s)
  
  (* cPsi  ...Undef...  _ *)
  | (_cPsi,  Int.LF.Dot (Int.LF.Undef, _s),
     _) ->
      raise (Error (None, LeftoverUndef))
        
  | _ ->
      raise (Violation "Reconstruction of substitution undefined")

  (* needs other cases for Head h where h = MVar, Const, etc. -bp *)

let rec synKSpine loc recT cO cD  cPsi sS sK = match (sS, sK) with
  | ((Int.LF.Nil, _s), (Int.LF.Typ, _s')) -> ()

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiKind ((Int.LF.TypDecl (_, tA),_ ), tK), s)) ->
      let _ =   recTerm   recT cO cD cPsi (tM, s') (tA, s) in 
        synKSpine loc recT cO cD cPsi (tS, s') (tK, Int.LF.Dot (Int.LF.Obj (Int.LF.Clo (tM, s')), s))

  (* TODO confirm this is necessary, instead of having recKSpineW *)
  | ((Int.LF.SClo (tS, s),  s'), sK) ->
      synKSpine loc recT cO cD cPsi (tS, LF.comp s s') sK

  | _ -> 
      raise (Error (loc, (KindMismatch (cO, cPsi, sS, sK))))

let rec recTyp recT cO cD  cPsi sA = recTypW recT cO cD  cPsi (Whnf.whnfTyp sA)

and recTypW recT cO cD  cPsi sA = match sA with
  | (Int.LF.Atom (loc, a, tS),  s) ->
      let tK = (Typ.get a).Typ.kind in
      let sshift = mkShift recT cPsi in 
        synKSpine loc recT cO cD  cPsi (tS, s) (tK, sshift) 



  | (Int.LF.PiTyp ((Int.LF.TypDecl (_x, tA) as adec, _), tB),  s) ->
      recTyp recT cO cD  cPsi (tA, s);
      recTyp recT cO cD  (Int.LF.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s)

  | (Int.LF.Sigma arec,  s) ->
        recTypRec recT cO cD  cPsi (arec, s)

and recTypRec recT cO cD  cPsi (typRec, s) = match typRec with
  | Int.LF.SigmaLast lastA         -> recTyp recT cO cD  cPsi (lastA, s)
  | Int.LF.SigmaElem(_x, tA, recA) ->
      recTyp  recT cO cD  cPsi (tA, s);
      recTypRec recT cO cD
        (Int.LF.DDec (cPsi, LF.decSub (Int.LF.TypDecl (Id.mk_name Id.NoName, tA)) s))
        (recA, LF.dot1 s)

let recDec recT cO cD cPsi (decl, s) = match decl with
    | Int.LF.TypDecl (_, tA) ->
        recTyp recT cO cD cPsi (tA, s)
(* need to take cO and unify with schema elements -- similar to CtxApp checking *)

let rec recDCtx recT cO cD cPsi = match cPsi with
  | Int.LF.Null -> 
      ()

  | Int.LF.DDec (cPsi, tX) ->
      recDCtx recT cO cD cPsi;
      recDec recT cO cD cPsi (tX, LF.id)

  | Int.LF.CtxVar (Int.LF.CtxOffset psi_offset)  ->
      if psi_offset > (Context.length cO) then
        raise (Violation ("Context variable out of scope in context: " ^ P.dctxToString cO cD cPsi))

  | Int.LF.CtxVar (Int.LF.CtxName _c)  ->
      raise (Violation ("Unknown context variable in context: " ^ P.dctxToString cO cD cPsi))

let rec recCDecl recT cO cD cdecl = match cdecl with
  | Int.LF.MDecl (_u, tA, cPsi) ->
      (recDCtx recT cO cD cPsi ; 
       recTyp recT cO cD cPsi (tA, LF.id))

  | Int.LF.PDecl (_p, tA, cPsi) ->
      (recDCtx recT cO cD cPsi;
       recTyp recT cO cD cPsi (tA, LF.id))

let rec recMCtx recT cO cD = match cD with
  | Int.LF.Empty -> ()
  | Int.LF.Dec (cD, cdec) ->
      (recMCtx recT cO cD ;
       recCDecl recT cO cD cdec )


let rec recKind cD cPsi sK = match sK with
  | (Int.LF.Typ, _s) ->
      ()

  | (Int.LF.PiKind ((Int.LF.TypDecl(_x, tA) as adec, _ ), tK), s) ->
      recTyp PiRecon Int.LF.Empty cD cPsi (tA, s);
      recKind cD (Int.LF.DDec (cPsi, LF.decSub adec s)) (tK, LF.dot1 s)


(* ******************************************************************* *)
(* Shift mvars in approximate expression by k *)

let rec mshiftApxTerm m k d = match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, mshiftApxTerm m' k d) 
  | Apx.LF.Root (loc, h, s) -> 
      let h' = mshiftApxHead h k d in 
      let s' = mshiftApxSpine s k d in 
        Apx.LF.Root (loc, h', s')

and mshiftApxHead h k d = match h with
  | Apx.LF.MVar (offset, s) -> 
      if offset > d then 
        Apx.LF.MVar (offset + k, mshiftApxSub s k d)
      else 
        Apx.LF.MVar (offset, mshiftApxSub s k d)

  | Apx.LF.PVar (offset, s) -> 
      if offset > d then 
        Apx.LF.PVar (offset + k, mshiftApxSub s k d)
      else 
        Apx.LF.PVar (offset, mshiftApxSub s k d)

  | _ -> h

and mshiftApxSub s k d = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id       -> s
  | Apx.LF.Dot (Apx.LF.Head h, s) -> 
      let h' = mshiftApxHead h k d in 
      let s' = mshiftApxSub s k d in 
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) -> 
      let m' = mshiftApxTerm m k d in 
      let s' = mshiftApxSub s k d in 
        Apx.LF.Dot (Apx.LF.Obj m', s')


and mshiftApxSpine s k d = match s with 
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) -> 
      let s' = mshiftApxSpine s k d in 
      let m' = mshiftApxTerm m k d in 
        Apx.LF.App (m' , s')

let rec mshiftApxTyp a k d = match a with
  | Apx.LF.Atom (loc, c, spine) -> 
      Apx.LF.Atom (loc, c, mshiftApxSpine spine k d)

  | Apx.LF.PiTyp ((t_decl, dep), a) -> 
      let t_decl' = mshiftApxTypDecl t_decl k d in 
      let a' = mshiftApxTyp a k d in 
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = mshiftApxTypRec typ_rec k d in
        Apx.LF.Sigma typ_rec'

and mshiftApxTypDecl t_decl k d = match t_decl with
  | Apx.LF.TypDecl (x, a) -> 
      Apx.LF.TypDecl(x, mshiftApxTyp a k d)

and mshiftApxTypRec t_rec k d = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (mshiftApxTyp a k d)
  | Apx.LF.SigmaElem (x, a, t_rec) -> 
      let a' = mshiftApxTyp a k d in 
      let t_rec' = mshiftApxTypRec t_rec k d in 
        Apx.LF.SigmaElem (x, a', t_rec')

let rec mshiftApxDCtx psi k d = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar _ -> psi 
  | Apx.LF.DDec (psi, t_decl) -> 
      let psi' = mshiftApxDCtx psi k d in 
      let t_decl' = mshiftApxTypDecl t_decl k d in 
        Apx.LF.DDec (psi', t_decl')


let rec mshiftApxExp e k d = match e with
  | Apx.Comp.Syn i         -> Apx.Comp.Syn (mshiftApxExp' i k d)
  | Apx.Comp.Fun (f, e)    -> Apx.Comp.Fun (f, mshiftApxExp e k d)
  | Apx.Comp.CtxFun (g, e) -> Apx.Comp.CtxFun (g, mshiftApxExp e k d)
  | Apx.Comp.MLam (u, e)   -> Apx.Comp.MLam (u, mshiftApxExp e k (d+1))
  | Apx.Comp.Pair.(e1, e2)      -> 
      let e1' = mshiftApxExp e1 k d in 
      let e2' = mshiftApxExp e2 k d in 
        Apx.Comp.Pair (e1', e2')
  | Apx.Comp.LetPair (i, (x,y, e)) -> 
      let i' = mshiftApxExp' i k d in 
      let e' = mshiftApxExp  e k d in 
        Apx.Comp.LetPair (i', (x,y, e')) 

  | Apx.Comp.Box(phat, m) -> 
      Apx.Comp.Box (phat, mshiftApxTerm m k d)
  | Apx.Comp.Case (i, branch) -> 
      Apx.Comp.Case (mshiftApxExp' i k d, mshiftApxBranches branch k d)

and mshiftApxExp' i k d = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.Const _c -> i
  | Apx.Comp.Apply (i, e) -> 
      let i' = mshiftApxExp' i k d in 
      let e' = mshiftApxExp e k d in 
        Apx.Comp.Apply (i', e')
  | Apx.Comp.CtxApp (i, psi) -> 
      let i' = mshiftApxExp' i k d in 
      let psi' = mshiftApxDCtx psi  k d in 
        Apx.Comp.CtxApp (i', psi')

  | Apx.Comp.MApp (i, (phat, m)) -> 
      let i' = mshiftApxExp' i k d in 
      let m' = mshiftApxTerm m k d in
        Apx.Comp.MApp (i', (phat, m'))

  | Apx.Comp.BoxVal (psi, m) -> 
      let psi' = mshiftApxDCtx psi k d in 
      let m'   = mshiftApxTerm m k d in 
        Apx.Comp.BoxVal (psi', m')

(*  | Apx.Comp.Ann (e, tau) -> 
      let e' = mshiftApxExp e k d in 
      let tau' = mshiftApxCTyp tau k d in 
        Apx.Comp.Ann (e', tau')
    
*)


and mshiftApxBranches branches k d = match branches with
  | [] -> []
  | b::bs -> (mshiftApxBranch b k d)::(mshiftApxBranches bs k d)

and mshiftApxBranch b k d = 
  let rec length delta = match delta with
    | Apx.LF.Empty -> 0
    | Apx.LF.Dec (delta, _ ) -> 1 + length delta 
  in 
    (match b with
      | Apx.Comp.BranchBox (delta, (psi1, m, Some (a, psi)), e) ->
          let d' = length delta in 
            Apx.Comp.BranchBox (delta, (psi1, m, Some (a, psi)),
                                mshiftApxExp e k (d+d'))
              
      | (Apx.Comp.BranchBox (delta, (psi, r, None), e))  ->
          let d' = length delta in 
            Apx.Comp.BranchBox (delta, (psi, r, None),
                                mshiftApxExp e k (d+d')))
              
(* ******************************************************************* *)
(* Elaboration of computations *)
(* Given a type-level constant a of type K , it will generate the most general
   type a U1 ... Un *)
let mgTyp cPsi loc a kK =
  let rec genSpine sK = match sK with
    | (Int.LF.Typ, _s) ->
        Int.LF.Nil

    | (Int.LF.PiKind ((Int.LF.TypDecl (_, tA1), _ ), kK), s) ->
        let u  = Whnf.newMVar (cPsi , Int.LF.TClo (tA1,s)) in
        let tR = Int.LF.Root (None, Int.LF.MVar (u, LF.id), Int.LF.Nil) in
        let tS = genSpine (kK, Int.LF.Dot (Int.LF.Head (Int.LF.MVar (u, LF.id)), s)) in
          Int.LF.App (tR, tS)
  in
    Int.LF.Atom (loc, a, genSpine (kK, LF.id))

let rec genMApp (i, tau_t) = genMAppW (i, Cwhnf.cwhnfCTyp tau_t)

and genMAppW (i, tau_t) = match tau_t with
  | (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi), Int.Comp.Implicit), tau), theta) ->
      let psihat  = Context.dctxToHat cPsi in
      let tM'     = Whnf.etaExpandMV (C.cnormDCtx (cPsi, theta))  (C.cnormTyp (tA, theta), LF.id) LF.id in
        genMApp ((Int.Comp.MApp (i, (psihat, tM'))), (tau, Int.Comp.MDot (Int.Comp.MObj (psihat, tM'), theta)))

  | _ -> (i, tau_t)

let rec elCompTyp cO cD tau = match tau with
  | Apx.Comp.TypBox (a, psi) ->
      let cPsi = elDCtx PiboxRecon cO cD psi in
      let tA   = elTyp PiboxRecon cO cD cPsi a in
        Int.Comp.TypBox (tA, cPsi)

  | Apx.Comp.TypArr (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypArr (tau1', tau2')

  | Apx.Comp.TypCross (tau1, tau2) ->
      let tau1' = elCompTyp cO cD tau1 in
      let tau2' = elCompTyp cO cD tau2 in
        Int.Comp.TypCross (tau1', tau2')

  | Apx.Comp.TypCtxPi ((x, schema_cid) , tau) ->
      let tau' = elCompTyp (Int.LF.Dec (cO, Int.LF.CDecl (x, schema_cid))) cD tau in
        Int.Comp.TypCtxPi ((x, schema_cid), tau')

  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let cdecl' = elCDecl PiboxRecon cO cD cdecl  in
      let tau'   = elCompTyp cO (Int.LF.Dec (cD, cdecl')) tau in
        Int.Comp.TypPiBox ((cdecl', Int.Comp.Explicit), tau')

let rec elExp cO cD cG e theta_tau = elExpW cO cD cG e (C.cwhnfCTyp theta_tau)

and elExpW cO cD cG e theta_tau = match (e, theta_tau) with
  | (Apx.Comp.Syn i, _) ->
      let (i', _t) = genMApp (elExp' cO cD cG i) in
        Int.Comp.Syn i'

  | (Apx.Comp.Fun (x, e), (Int.Comp.TypArr (tau1, tau2), theta)) ->
      let e' = elExp cO cD (Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo (tau1, theta)))) e (tau2, theta) in
        Int.Comp.Fun (x, e')

  | (Apx.Comp.CtxFun (psi_name, e), (Int.Comp.TypCtxPi ((_, schema_cid), tau), theta)) ->
      let e' = elExp (Int.LF.Dec (cO, Int.LF.CDecl (psi_name, schema_cid))) cD cG e (tau, theta) in
        Int.Comp.CtxFun (psi_name, e')

  | (Apx.Comp.MLam (u, e) , (Int.Comp.TypPiBox((Int.LF.MDecl(_u, tA, cPsi), Int.Comp.Explicit), tau), theta))  ->
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
                     cG e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (u, e')

  | (e, (Int.Comp.TypPiBox((Int.LF.MDecl(u, tA, cPsi), Int.Comp.Implicit), tau), theta))  ->
      let e' = elExp cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, theta), C.cnormDCtx (cPsi, theta))))
                     cG e (tau, C.mvar_dot1 theta) in
        Int.Comp.MLam (u, e')

  | (Apx.Comp.Pair(e1, e2), (Int.Comp.TypCross (tau1, tau2), theta)) ->
      let e1' = elExp cO cD cG e1 (tau1, theta) in
      let e2' = elExp cO cD cG e2 (tau2, theta) in
        Int.Comp.Pair (e1', e2')

  | (Apx.Comp.LetPair (i, (x, y, e)), (tau, theta)) ->
      let (i', tau_theta') = elExp' cO cD cG i in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypCross (tau1, tau2), t) ->
              let cG1 = Int.LF.Dec (cG, Int.Comp.CTypDecl (x,  Int.Comp.TypClo (tau1, t))) in
              let cG2 = Int.LF.Dec (cG1, Int.Comp.CTypDecl (y, Int.Comp.TypClo (tau2, t))) in
              let e'  =  elExp cO cD cG2 e (tau, theta) in
                Int.Comp.LetPair (i', (x, y, e'))

          | _ -> raise (Error (None, CompMismatch (cO, cD, cG, i', Cross, tau_theta'))) (* TODO postpone to reconstruction *)
        end


  | (Apx.Comp.Box (psihat, tM), (Int.Comp.TypBox (tA, cPsi), theta)) ->
      let tM' = elTerm PiboxRecon cO cD (C.cnormDCtx (cPsi, theta)) tM (C.cnormTyp (tA, theta), LF.id) in
        Int.Comp.Box (psihat, tM')

  | (Apx.Comp.Case (i, branches), tau_theta) ->
      let (i', tau_theta') = genMApp (elExp' cO cD cG i) in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypBox (tP, cPsi), _theta') ->
              (* We don't check that each branch has approximate type tA[cPsi] - DOUBLE CHECK -bp  *)
              let branches' = List.map (function b -> elBranch cO cD cG b tau_theta (tP, cPsi)) branches in
                Int.Comp.Case (i', branches')

          | _ -> raise (Error (None, ValueRestriction (cO, cD, cG, i', tau_theta'))) (* TODO postpone to reconstruction *)
        end

  | _ ->
      (Printf.printf "elExp: ill-typed\n";
      raise NotImplemented (* TODO postpone error to reconstruction phase *))


and elExp' cO cD cG i = match i with
  | Apx.Comp.Var offset ->
      (Int.Comp.Var offset, (lookup cG offset, C.id))

  | Apx.Comp.Const prog ->
      (Int.Comp.Const prog, ((Comp.get prog).Comp.typ, C.id))

  | Apx.Comp.Apply (i, e) ->
      let (i', tau_theta') = genMApp (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypArr (tau2, tau), theta) ->
              let e' = elExp cO cD cG e (tau2, theta) in
                (Int.Comp.Apply (i', e'), (tau, theta))

          | _ -> 
              raise (Error (None, CompMismatch (cO, cD, cG, i', Arrow, tau_theta'))) (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.CtxApp (i, cPsi) ->
      let (i', tau_theta') = genMApp (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypCtxPi ((_psi, _sW), tau), theta) ->
              let cPsi'  = elDCtx PiboxRecon cO cD cPsi in
              let theta' = Cwhnf.csub_msub cPsi' 1 theta in
              let tau'   = Cwhnf.csub_ctyp cPsi' 1 tau in
                (Int.Comp.CtxApp (i', cPsi'), (tau', theta'))

          | _ -> 
              raise (Error (None, CompMismatch (cO, cD, cG, i', CtxPi, tau_theta'))) (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.MApp (i, (psihat, m)) ->
      let (i', tau_theta') = genMApp (elExp' cO cD cG i) in
        begin match tau_theta' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl (_, tA, cPsi), Int.Comp.Explicit), tau), theta) ->
              let tM'    = elTerm PiboxRecon cO cD (C.cnormDCtx (cPsi, theta)) m (C.cnormTyp (tA, theta), LF.id) in
              let theta' = Int.Comp.MDot (Int.Comp.MObj (psihat, tM'), theta) in
                (Int.Comp.MApp (i', (psihat, tM')), (tau, theta'))

          | _ ->
              raise (Error (None, CompMismatch (cO, cD, cG, i', PiBox, tau_theta'))) (* TODO postpone to reconstruction *)
        end

  | Apx.Comp.BoxVal (psi, r) ->
      let cPsi   = elDCtx PiboxRecon cO cD psi in
      let tR     = elClosedTerm' PiboxRecon cO cD cPsi r in
      let sP     = synTerm PiboxRecon cO cD cPsi (tR, LF.id) in
      let phat   = Context.dctxToHat cPsi in
      let tau    = Int.Comp.TypBox (Int.LF.TClo sP, cPsi) in
        (Int.Comp.Ann (Int.Comp.Box (phat, tR), tau), (tau, C.id))

  | Apx.Comp.Ann (e, tau) ->
      let tau' = elCompTyp cO cD tau in
      let e'   = elExp cO cD cG e (tau', C.id) in
        (Int.Comp.Ann (e', tau'), (tau', C.id))


(* We don't check that each box-expression has approximately
 *  the same type as the expression we analyze.
 *
 * TODO double check -bp
 *)
(* NOTE: Any context variable occurring in delta, psihat, a, psi is bound
 *  in cO !  So delta (and cD' and cD) do not contain it!
 *)

and elBranch cO cD cG branch (tau, theta) (Int.LF.Atom(loc, a, _spine) , _cPsi) = match branch with
  | (Apx.Comp.BranchBox (delta, (psi1, m, Some (a, psi)), e)) ->
      let cD'     = elMCtx PiboxRecon cO delta in
      let cPsi'   = elDCtx PiboxRecon cO cD' psi in
      let cPsi1   = elDCtx PiboxRecon cO cD' psi1 in

      (* Check that Psi1 = Psi' using Whnf.conv and or unify;
         if they are not equal, then we need to fail here, since we drop types in Psi1 later on. 
         Psi1 is only really useful if no typing annotation is given. -bp *)

      (* Check that Psi = Psi' using Whnf.conv and or unify;
         if they are not equal, then we need to fail; done in checkBranch -bp *)

      let psihat  =  Context.dctxToHat cPsi1 in

      let tA'     = elTyp PiboxRecon cO cD' cPsi' a in
      let tM'     = elTerm' PiboxRecon cO cD' cPsi' m (tA', LF.id) in

      let _   = dprint (fun () -> "elBranch: Elaborated pattern...\n" ^
                  (P.mctxToString cO cD') ^ "  ;   " ^
                  (P.dctxToString cO cD' cPsi') ^ "\n   |-   \n    "  ^
                  (P.normalToString cO cD' cPsi' (tM', LF.id)) ^ " \n has type " ^
                  (P.typToString  cO cD' cPsi' (tA', LF.id)) ^ " \n\n") in


      let _ = recTerm PiboxRecon cO cD' cPsi' (tM', LF.id) (tA', LF.id) in

      let _       = dprint (fun () -> "elBranch: Reconstructed pattern...\n" ^
                  (P.mctxToString cO cD') ^ "  ;   " ^
                  (P.dctxToString cO cD' cPsi') ^ "\n   |-   \n    "  ^
                  (P.normalToString cO cD' cPsi' (tM', LF.id)) ^ " \n has type " ^
                  (P.typToString cO cD' cPsi'  (tA', LF.id)) ^ " \n\n") in

      let (cD1', cPsi1', (phat', tM1'), tA1') =
        Abstract.abstrPattern cD' cPsi' (psihat, tM') tA' in

      let _       = dprint (fun () -> "elBranch: Reconstructed pattern (AFTER ABSTRACTION)...\n" ^
                  (P.mctxToString cO cD1') ^ "  ;   " ^
                  (P.dctxToString cO cD1' cPsi1') ^ "\n   |-   \n    "  ^
                  (P.normalToString cO cD1' cPsi1' (tM1', LF.id)) ^ " \n has type " ^
                  (P.typToString cO cD1' cPsi1'  (tA1', LF.id)) ^ " \n\n") in


      let n       = Context.length cD1' in
      let cD_i    = Context.append cD cD1' in
      let theta_i = C.mshift theta n in

      let _       = FMVar.clear () in
      let _       = FPVar.clear () in
      let k       = (Context.length cD') in 
      let k'      = n - k in
      let e'      = if k' = 0 then e else mshiftApxExp e k' k in 

      let e'      = elExp cO cD_i cG e' (tau, theta_i) in
      let _      = dprint (fun () -> "elBranch: Elaborated branch" ^
                             (P.mctxToString cO cD_i) ^ "  ;  " ^
                             (P.gctxToString cO cD_i cG) ^ "\n      |-    \n" ^
                             (P.expChkToString cO cD_i cG e') ^ "\n\n") in

        Int.Comp.BranchBox (cD1', (phat', tM1', (tA1', cPsi1')), e')




  | (Apx.Comp.BranchBox (delta, (psi, r, None), e))  ->
      let cD'     = elMCtx PiboxRecon cO delta in
      let  _      = recMCtx PiboxRecon cO cD' in
 
      let cPsi'   = elDCtx PiboxRecon cO cD' psi in
      let  _      = recDCtx PiboxRecon cO cD' cPsi' in 

      (* Need to reconstruct cPsi'  *)
      let tP0     = mgTyp cPsi' loc a (Typ.get a).Typ.kind  in

      let tR      = elTerm' PiboxRecon cO cD' cPsi' r  (tP0, LF.id) in
      (* TO BE ADDED: recDCtx cD' cPsi' schema *)
      let _   = dprint (fun () -> "elBranch: Elaborated pattern (rec-typ anno)...\n" ^
                  (P.mctxToString cO cD') ^ "  ;   " ^
                  (P.dctxToString cO cD' cPsi') ^ "\n   |-   \n    "  ^
                  (P.normalToString cO cD' cPsi' (tR, LF.id)) ^ " \n has type " ^
                  (P.typToString  cO cD' cPsi' (tP0, LF.id)) ^ " \n\n") in

      let psihat  = Context.dctxToHat cPsi' in

      let sP      = synTerm PiboxRecon cO cD' cPsi' (tR, LF.id) in


      let _       = dprint (fun () -> "elBranch: Reconstructed pattern (rec-typ anno)...\n" ^
                  (P.mctxToString cO cD') ^ "  ;   " ^
                  (P.dctxToString cO cD' cPsi') ^ "\n   |-   \n    "  ^
                  (P.normalToString cO cD' cPsi' (tR, LF.id)) ^ " \n has type " ^
                  (P.typToString cO cD' cPsi'  (tP0, LF.id)) ^ " \n\n") in

      let _       = begin try 
                      Unify.unifyTyp cD' (psihat, sP, (tP0, LF.id)) 
                    with Unify.Unify msg ->
                       (dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n"
                                  ^  "Inferred pattern type : "
                                  ^  (P.dctxToString cO Int.LF.Empty cPsi') ^
                                  "    |-    " ^
                                  (P.typToString cO Int.LF.Empty cPsi' sP) ^
                                  "\nExpected pattern type: "
                                  ^ (P.dctxToString cO Int.LF.Empty cPsi') ^
                                  "     |-    " ^
                                  (P.typToString cO Int.LF.Empty cPsi' (tP0, LF.id)))
                       ; raise (Violation "Pattern Type Clash (Approximate)")
                                        )
                   end 
      in            


      let (cD1', cPsi1', (phat', tR1'), tP1') =
          Abstract.abstrPattern cD' cPsi' (psihat, tR) (Int.LF.TClo(sP)) in

      let n       = Context.length cD1' in
      let cD_i    = Context.append cD cD1' in

      let theta_i = C.mshift theta n in

      let _       = FMVar.clear () in
      let _       = FPVar.clear () in


      let k       = (Context.length cD') in 
      let k'      = n - k in
      let e'      = if k' = 0 then e else mshiftApxExp e k' k in 

      let e'     = elExp cO cD_i cG e' (tau, theta_i) in
      let _      = dprint (fun () -> "elBranch: Elaborated branch" ^
                             (P.mctxToString cO cD_i) ^ "  ;  " ^
                             (P.gctxToString cO cD_i cG) ^ "\n      |-    \n" ^
                             (P.expChkToString cO cD_i cG e') ^ "\n\n") in
        Int.Comp.BranchBox (cD1', (phat', tR1', (tP1', cPsi1')), e')



(* ******************************************************************* *)
(* Reconstruction for computations *)
(* First version be identical to type checking computations *)

let rec length cD = match cD with
  | Int.LF.Empty -> 0
  | Int.LF.Dec (cD, _) -> 1 + length cD

let rec lookup cG k = match (cG, k) with
  | (Int.LF.Dec (_cG', Int.Comp.CTypDecl (_,  tau)), 1) ->  tau
  | (Int.LF.Dec ( cG', Int.Comp.CTypDecl (_,  _tau)), k) ->
      lookup cG' (k - 1)

let rec split tc d = match (tc, d) with
  | (tc, 0) -> tc
  | (Int.Comp.MDot (_ft, t), d) -> split t (d - 1)

let rec mctxToMSub cD = match cD with
  | Int.LF.Empty -> C.id
  | Int.LF.Dec (cD', Int.LF.MDecl(_, tA, cPsi)) ->
      let t     = mctxToMSub cD' in
      let cPsi' = Cwhnf.cnormDCtx (cPsi,t) in
      let tA'   = Cwhnf.cnormTyp (tA, t) in
      let u     = Whnf.newMVar (cPsi', tA') in
      let phat  = Context.dctxToHat cPsi in
        Int.Comp.MDot (Int.Comp.MObj (phat, Int.LF.Root (None, Int.LF.MVar (u, LF.id), Int.LF.Nil)) , t)

  | Int.LF.Dec(cD', Int.LF.PDecl(_, tA, cPsi)) ->
      let t    = mctxToMSub cD' in
      let p    = Whnf.newPVar (Cwhnf.cnormDCtx (cPsi, t), Cwhnf.cnormTyp (tA, t)) in
      let phat = Context.dctxToHat cPsi in
        Int.Comp.MDot (Int.Comp.PObj (phat, Int.LF.PVar (p, LF.id)) , t)

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
  | Int.Comp.TypBox (tA, cPsi) ->
      recDCtx PiboxRecon cO cD cPsi;
      recTyp PiboxRecon cO cD cPsi (tA, LF.id)

  | Int.Comp.TypArr (tau1, tau2) ->
      recCompTyp cO cD tau1;
      recCompTyp cO cD tau2

  | Int.Comp.TypCross (tau1, tau2) ->
      recCompTyp cO cD tau1;
      recCompTyp cO cD tau2

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
      let e' = check cO cD (Int.LF.Dec (cG, Int.Comp.CTypDecl (f, Int.Comp.TypClo (tau,t)))) e ttau in
        Int.Comp.Rec (f, e')

  | (Int.Comp.Fun (x, e), (Int.Comp.TypArr (tau1, tau2), t)) ->
      let e' = check cO cD (Int.LF.Dec (cG, Int.Comp.CTypDecl (x, Int.Comp.TypClo (tau1, t)))) e (tau2, t) in
      Int.Comp.Fun (x, e')

  | (Int.Comp.CtxFun(psi, e) , (Int.Comp.TypCtxPi ((_psi, schema), tau), t)) ->
      let e' = check (Int.LF.Dec (cO, Int.LF.CDecl (psi, schema))) cD cG e (tau, t) in
        Int.Comp.CtxFun (psi, e')

  | (Int.Comp.MLam (u, e), (Int.Comp.TypPiBox ((Int.LF.MDecl (_u, tA, cPsi), _ ), tau), t)) ->
      let e' = check cO (Int.LF.Dec (cD, Int.LF.MDecl (u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
                     cG e (tau, C.mvar_dot1 t) in
        Int.Comp.MLam(u, e')

  | (Int.Comp.Pair(e1, e2), (Int.Comp.TypCross (tau1, tau2), theta)) ->
      let e1' = check cO cD cG e1 (tau1, theta) in
      let e2' = check cO cD cG e2 (tau2, theta) in
        Int.Comp.Pair (e1' , e2')

  | (Int.Comp.LetPair(i, (x, y, e)), (tau, theta)) ->
      let (i', tau_theta') = syn cO cD cG i in
        begin match C.cwhnfCTyp tau_theta' with
          | (Int.Comp.TypCross (tau1, tau2), t) ->
              let cG1 = Int.LF.Dec(cG, Int.Comp.CTypDecl (x,  Int.Comp.TypClo(tau1, t))) in
              let cG2 = Int.LF.Dec(cG1, Int.Comp.CTypDecl (y, Int.Comp.TypClo(tau2, t))) in
              let e'  = check cO cD cG2 e (tau, theta) in
                Int.Comp.LetPair (i', (x, y, e'))

          | _ -> raise (Error (None, CompMismatch (cO, cD, cG, i', Cross, tau_theta')))
        end

  | (Int.Comp.Box (_phat, tM), (Int.Comp.TypBox (tA, cPsi), t)) ->
      (* Check.LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, LF.id) (C.cnormTyp (tA, t), LF.id) *)
      begin try
        let cPsi' = C.cnormDCtx (cPsi, t) in
        let tA'   = C.cnormTyp (tA, t) in

        let _     = dprint (fun () -> "Check: " ^ (P.mctxToString cO cD) ^ " \n ; " ^ (P.dctxToString cO cD cPsi') ^ "\n |- " ^ 
                              (P.normalToString cO cD cPsi' (tM, LF.id)) 
                              ^ "\n has type " ^ (P.typToString cO cD cPsi' (tA', LF.id)) ^ "\n\n") in  
          recTerm PiboxRecon cO cD  cPsi' (tM, LF.id) (tA', LF.id);
          e
      with Cwhnf.FreeMVar h ->
        raise (Violation ("Free meta-variable " ^ (P.headToString cO cD cPsi h)))
      end

  (* Matching of implicit argument *)
  | (Int.Comp.Case (Int.Comp.Ann(Int.Comp.Box(phat, tR), Int.Comp.TypBox(tA', cPsi')) as i, branches), (tau, t)) ->
      let _  = recTerm PiboxRecon cO cD cPsi' (tR, LF.id) (tA', LF.id) in
      let cA = (Whnf.normTyp (tA', LF.id), Whnf.normDCtx cPsi') in
      let branches = checkBranches (IndexObj(phat, tR)) cO cD cG branches cA (tau, t) in
        Int.Comp.Case (i, branches)

  (* Matching on data *)
  | (Int.Comp.Case (i, branches),  (tau, t)) ->
      let (i, tau') = syn cO cD cG i in
      let _         = dprint (fun () -> "Synthesized type of scrutinee in case expression") in 
        begin match C.cwhnfCTyp tau' with
          | (Int.Comp.TypBox (tA, cPsi),  t') ->
              let _ = dprint (fun () -> "Checking for leftover constraints") in 
                let branches' = checkBranches DataObj cO cD cG branches
                                              (C.cnormTyp (tA, t'),  C.cnormDCtx (cPsi, t'))
                                              (tau, t)
                in
                  Int.Comp.Case (i, branches')
          | _ -> raise (Error (None, ValueRestriction (cO, cD, cG, i, tau')))
        end

  | (Int.Comp.Syn i,  (tau, t)) ->
      let (i, tau_t') = syn cO cD cG i in
        (* if C.convCTyp (tau,t) tau_t' then *)
        try
          dprint (fun () -> "Unifying computation-level types\n") ; 
          Unify.unifyCompTyp cD (tau, t) (tau_t');
          dprint (fun () -> "Unified computation-level types\n") ; 
          (Int.Comp.Syn i)
        with _ ->
          raise (Error (None, CompIllTyped (cO, cD, cG, e, ttau)))

and check cO cD cG e (tau, t) =
  checkW cO cD cG e (C.cwhnfCTyp (tau, t))

and syn cO cD cG e = match e with
  | Int.Comp.Var x ->
      (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD ???!!! *)
      (e, (lookup cG x, C.id))

  | Int.Comp.Const prog ->
      (e, ((Comp.get prog).Comp.typ, C.id))

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
              let tau'  = C.cnormCTyp (tau1, t) in
              let e     = check cO cD cG e2 (tau2', C.id) in
                (* This is being on the safe side: Using (tau2, t) should work here *)
                (Int.Comp.Apply (i, e) , (tau', C.id))

          | _ -> 
              raise (Error (None, CompMismatch (cO, cD, cG, i, Arrow, tau)))
        end

  | Int.Comp.CtxApp (e, cPsi) ->
      let (i, tau) = syn cO cD cG e in
        begin match C.cwhnfCTyp tau with
          | (Int.Comp.TypCtxPi ((_psi, sW) , tau), t) ->
              let _ = Printf.printf "\nSchema checking omitted\n" in
                (* REVISIT: Sun Jan 11 17:48:52 2009 -bp *)
                (* let tau' =  Cwhnf.csub_ctyp cPsi 1 tau in
                   let t'   = Cwhnf.csub_msub cPsi 1 t in   *)
              let tau1 = Cwhnf.csub_ctyp cPsi 1 (Cwhnf.cnormCTyp (tau,t)) in
              let _ = recDCtx PiboxRecon cO cD cPsi in 
              let _ = Check.LF.checkSchema cO cD cPsi (Schema.get_schema sW) in 
                (Int.Comp.CtxApp (i, cPsi) , (tau1, Cwhnf.id))

          | _ -> 
              raise (Error (None, CompMismatch (cO, cD, cG, i, CtxPi, tau)))
        end

  | Int.Comp.MApp (e, (phat, tM)) ->
      let (i, tau') = syn cO cD cG e in
        begin match C.cwhnfCTyp tau' with
          | (Int.Comp.TypPiBox ((Int.LF.MDecl(_, tA, cPsi), _ (* Int.Comp.Explicit*) ), tau), t) ->
              recTerm PiboxRecon cO cD (C.cnormDCtx (cPsi, t)) (tM, LF.id) (C.cnormTyp (tA, t), LF.id);
              let t' = Int.Comp.MDot(Int.Comp.MObj (phat, tM), t) in
                (Int.Comp.MApp (i, (phat, tM)) , (tau, t'))
          | _ ->
              raise (Error (None, CompMismatch (cO, cD, cG, i, PiBox, tau')))
        end

  | Int.Comp.Ann (e, tau) ->
      let e' = check cO cD cG e (tau, C.id) in
        (Int.Comp.Ann (e', tau) , (tau, C.id))


and checkBranches caseTyp cO cD cG branches tAbox ttau =
    List.map (fun branch -> checkBranch caseTyp cO cD cG branch tAbox ttau) branches

and checkBranch caseTyp cO cD cG branch (tA, cPsi) (tau, t) =
  match branch with
    | Int.Comp.BranchBox (cD1, (phat, tM1, (tA1, cPsi1)), e1) ->
        let _ = Check.LF.check cO cD1 cPsi1 (tM1, LF.id) (tA1, LF.id) in
       (* This is a double-check, since reconstruction was done during elaboration of branch
        *)
        let _ = dprint (fun () -> "Check Branch...\n") in 
        let d1  = length cD1     in
        let _d  = length cD      in
        let t1  = mctxToMSub cD1 in    (* {cD1} |- t1 <= cD1             *)
        let t'  = mctxToMSub cD  in    (* {cD}  |- t' <= cD              *)
        let tc  = extend t' t1   in    (* {cD1, cD} |- t', t1 <= cD, cD1 *)

        let _  = begin match caseTyp with
                   | IndexObj (_phat, tM') ->
                       begin try Unify.unify cD1 (phat, (C.cnorm (tM', t'), LF.id), (tM1, LF.id))
                       with Unify.Unify msg ->
                         (dprint (fun () -> "Unify ERROR: " ^  msg  ^ "\n") ;
                           raise (Violation "Pattern matching on index argument failed"))
                       end
                   | DataObj -> ()
                 end  in

        let cPsi1' = C.cnormDCtx (cPsi1, t1) in 
        let tA1'   = C.cnormTyp (tA1, t1) in 
        let tM1'   = C.cnorm (tM1, t1) in 
        let cPsi'  = C.cnormDCtx (cPsi, t') in 
        let tA'    = C.cnormTyp (tA, t') in 

        let _  = begin try
                    (Unify.unifyDCtx Int.LF.Empty cPsi' cPsi1'
                   ; dprint (fun () -> "Unifying contexts done \n") ; 
                    Unify.unifyTyp Int.LF.Empty (phat, (tA', LF.id), (tA1', LF.id)))
                 with
                     Unify.Unify msg ->
                       begin
                         dprint (fun () -> "Unify ERROR: " ^   msg  ^ "\n"
                                   ^ " Inferred pattern type: "
                                   ^ P.dctxToString cO Int.LF.Empty cPsi1' ^
                                   "    |-    " ^
                                   P.typToString cO Int.LF.Empty cPsi1' (tA1', LF.id) ^
                                   "\nExpected pattern type: "
                                   ^ P.dctxToString cO Int.LF.Empty cPsi' ^
                                   "    |-    " ^
                                   P.typToString cO Int.LF.Empty cPsi' (tA', LF.id))
                         ; raise (Violation "Pattern Type Clash")
                       end
         end(*try-with*)
        in

      let _       = dprint (fun () -> "Pattern (after unifying)...\n" ^
                  (P.dctxToString cO Int.LF.Empty cPsi1') ^ "\n   |-   \n    "  ^
                  (P.normalToString cO Int.LF.Empty cPsi1' (tM1', LF.id)) ^ " \n has type " ^
                  (P.typToString cO Int.LF.Empty cPsi1'  (tA1', LF.id)) ^ "\n\n") in

        
        let (tc', cD1'') = Abstract.abstractMSub tc in  (* cD1' |- tc' <= cD, cD1 *)

        let _ = dprint (fun () -> "Abstraction of pattern in branch done...\n") in 


        let t'' = split tc' d1 in (* cD1' |- t'' <= cD  suffix *)
        let cG1 = C.cwhnfCtx (cG, t'') in

        let e1' = begin try C.cnormExp (e1, tc')
                    with Cwhnf.FreeMVar h ->
                      raise (Violation ("Encountered free meta-variable " ^ (P.headToString cO cD1'' cPsi1' h) ^
                                          " \n in expression " ^ (P.expChkToString cO cD1'' cG1 e1) ^ "\n"))
                  end  in

        let tau' = (tau, C.mcomp t t'')  in

        let _ = dprint (fun () ->  "Recon: Check branch\n" ^
                        P.mctxToString cO cD1'' ^ " ;\n " ^
                        P.gctxToString cO cD1'' cG1 ^ "\n   |- \n " ^
                        P.expChkToString cO cD1'' cG1 e1' ^ "\n has type " ^
                        P.compTypToString cO cD1'' (Cwhnf.cnormCTyp tau') ^ "\n" ) in

        let e1_r =  check cO cD1'' cG1 e1' tau' in

        let _ = dprint (fun () -> "Recon (DONE): Check branch\n" ^
                        P.mctxToString cO cD1'' ^ " ;\n " ^
                        P.gctxToString    cO cD1'' cG1 ^ "\n   |- \n " ^
                        P.expChkToString  cO cD1'' cG1 e1_r ^ "\n has type " ^
                        P.compTypToString cO cD1'' (Cwhnf.cnormCTyp tau') ^ " \n" ) in

        let e1''   = try Cwhnf.invExp (e1_r, tc') 0 with
                      Cwhnf.NonInvertible ->
                        raise (Violation "Reconstruction succeeded in that the expression is well-typed\n but we cannot uniquely generate the actual expression\n")
        in
          Int.Comp.BranchBox (cD1, (phat, tM1, (tA1, cPsi1)), e1'')

(* ------------------------------------------------------------------- *)

let recSgnDecl d = 
    let _        = reset_fvarCnstr () in 
    let _       = FMVar.clear () in
    let _       = FPVar.clear () in
    match d with
  | Ext.Sgn.Typ (_, a, extK)   ->
      let _        = dprint (fun () -> "\nIndexing type constant " ^ a.string_of_name) in
      let apxK     = index_kind (CVar.create ()) (BVar.create ()) extK in
      let _        = FVar.clear () in
      let _        = dprint (fun () -> "\nElaborating type constant " ^ a.string_of_name) in
      let tK       = elKind Int.LF.Null apxK in
      let _        = solve_fvarCnstr PiRecon (*cO=*)Int.LF.Empty Int.LF.Empty !fvar_cnstr in
      let _        = reset_fvarCnstr () in
      let _        = dprint (fun () -> "\nReconstructing type constant " ^ a.string_of_name) in
      let _        = recKind Int.LF.Empty Int.LF.Null (tK, LF.id) in
      let (tK', i) = Abstract.abstrKind tK in

      let _        = dprint (fun () ->  a.string_of_name ^ " : " ^  (P.kindToString Int.LF.Null (tK', LF.id))) in 
      let _        = Check.LF.checkKind Int.LF.Empty Int.LF.Empty Int.LF.Null tK' in
      let _        = dprint (fun () ->  "DOUBLE CHECK for type constant " ^a.string_of_name ^
                                        " successful!") in
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        Int.Sgn.Typ (a', tK')

  | Ext.Sgn.Const (_, c, extT) ->
      let apxT     = index_typ (CVar.create ()) (BVar.create ()) extT in
      let _        = dprint (fun () -> "\nReconstructing term constant " ^ c.string_of_name ^ "\n") in
      let _        = FVar.clear () in
      let cO       = Int.LF.Empty in
      let tA       = elTyp PiRecon cO Int.LF.Empty Int.LF.Null apxT in
      let _        = solve_fvarCnstr PiRecon cO Int.LF.Empty !fvar_cnstr in
      let cD       = Int.LF.Empty in

      let _       = dprint (fun () -> "\nElaboration of constant " ^ c.string_of_name ^ " : " ^
                                       P.typToString cO cD Int.LF.Null (tA, LF.id)) in

      let _        = recTyp PiRecon cO cD Int.LF.Null (tA, LF.id) in

      let _        = dprint (fun () -> "\nReconstruction (without abstraction) of constant " ^
                               c.string_of_name ^ " : " ^
                               P.typToString cO cD Int.LF.Null (tA, LF.id)) in

      let (tA', i) = Abstract.abstrTyp tA in
      let _        = dprint (fun () -> "\nReconstruction (with abstraction) of constant: " ^
                               c.string_of_name ^ " : " ^
                               (P.typToString cO cD Int.LF.Null (tA', LF.id)) ^ "\n\n") in
      let _        = Check.LF.checkTyp Int.LF.Empty Int.LF.Empty Int.LF.Null (tA', LF.id) in
      let _        = Printf.printf "\n DOUBLE CHECK for term constant  %s  successful!\n" c.string_of_name  in
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in
      let _        = Printf.printf "\n Added term constant  %s\n" c.string_of_name  in
        Int.Sgn.Const (c', tA')


  | Ext.Sgn.Schema (_, g, schema) ->
     (*  let _       = Printf.printf "\n Indexing schema  %s  \n" g.string_of_name  in  *)
      let apx_schema = index_schema schema in
      let _        = Printf.printf "\nReconstructing schema  %s\n" g.string_of_name  in
      let cO        = Int.LF.Empty in
      let sW         = elSchema cO apx_schema in
(*      let _        = Printf.printf "\n Elaboration of schema  %s \n = %s \n\n" g.string_of_name
                        (P.schemaToString sW) in   *)
      let cPsi       = Int.LF.Null in
      let cD         = Int.LF.Empty in
      let _          = Check.LF.checkSchema cO cD cPsi sW in
      let _        = Printf.printf "\nTYPE CHECK for schema  %s  successful\n" g.string_of_name  in
      let g'         = Schema.add (Schema.mk_entry g sW) in
        Int.Sgn.Schema (g', sW)


  | Ext.Sgn.Rec (_, f, tau, e) ->
      (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in   *)
      let apx_tau = index_comptyp (CVar.create ()) (CVar.create ()) tau in
      let _       = Printf.printf "Reconstructing function  %s\n" f.string_of_name  in
      let cD      = Int.LF.Empty in
      let cO      = Int.LF.Empty in

      let tau'    = elCompTyp cO cD apx_tau  in

      let _        = Printf.printf "Elaboration of function type %s \n : %s\n\n" f.string_of_name
                        (P.compTypToString cO cD tau') in  

      let _       = recCompTyp cO cD tau' in

      let (tau', _i) = Abstract.abstrCompTyp tau' in

      let  _      = Check.Comp.checkTyp cO cD tau' in

      let _       = Printf.printf "Checked computation type  %s  successfully\n\n"
                                  (P.compTypToString cO cD tau') in


      let vars'   = Var.extend  (Var.create ()) (Var.mk_entry f) in

      let apx_e   = index_exp (CVar.create ()) (CVar.create ()) vars' e in

      let cG      = Int.LF.Dec(Int.LF.Empty, Int.Comp.CTypDecl (f, tau'))  in

      let e'      = elExp cO cD cG apx_e (tau', C.id) in

      let _       = Printf.printf "\n Elaboration of function  %s\n     type:  %s\n   result:  %s\n" f.string_of_name
                         (P.compTypToString cO cD tau')
                         (P.expChkToString cO cD cG e') in
      
      let e_r     = check  cO cD cG e' (tau', C.id) in
      let e_r'    = Abstract.abstrExp e_r in

      let _       = dprint (fun () ->  "\n Reconstructed function " ^  f.string_of_name ^
                                       "\n type: " ^  (P.compTypToString cO cD tau') ^ "\n  result: " ^
                                       (P.expChkToString cO cD cG e_r') ^ "\n\n") in

      let _       = Check.Comp.check cO cD  cG e_r' (tau', C.id) in
      let _        = Printf.printf "DOUBLE CHECK of function  %s  successful!\n\n" f.string_of_name  in
      let f'      = Comp.add (Comp.mk_entry f tau' 0  e_r' ) in
        Int.Sgn.Rec (f', tau',  e_r' )


  | Ext.Sgn.Pragma(_, Ext.LF.NamePrag (typ_name, m_name, v_name)) ->
      begin match v_name with
        | None ->
            let cid_tp = Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name)) None in
              Int.Sgn.Pragma(Int.LF.NamePrag(cid_tp))
        | Some x ->
            let cid_tp = Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name))
                                                (Some (Gensym.VarData.name_gensym x)) in
              Int.Sgn.Pragma(Int.LF.NamePrag(cid_tp))
      end

let rec recSgnDecls = function
  | [] -> []

  | Ext.Sgn.Pragma(_, Ext.LF.NotPrag) :: not'd_decl :: rest ->
      (*   let internal_syntax_pragma = Int.Sgn.Pragma(Int.LF.NotPrag) in *)
      let not'd_decl_succeeds = 
        begin try
          (let _ = recSgnDecl not'd_decl in
             true)
        with
            _ -> (print_string ("Reconstruction fails for %not'd declaration\n"); false)
        end
      in
        if not'd_decl_succeeds then
          raise (Violation ("UNSOUND: reconstruction succeeded for %not'd declaration"))
        else recSgnDecls rest

  | [Ext.Sgn.Pragma(_, Ext.LF.NotPrag)] ->  (* %not declaration with nothing following *)
      []

  | decl :: rest ->
      let internal_decl = recSgnDecl decl in
      let internal_rest = recSgnDecls rest in
        internal_decl :: internal_rest

