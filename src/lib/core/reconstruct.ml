(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

(* TODO

   - Extension to deal with MVars, PVars
   - Extension to deal with substitutions
   - Extension to deal with A[Psi]
   - Extension to deal with psi_hat
   - Extension to deal with schemas

   - Cycle detection ?
   - Code walk for reconstruction
*)

open Store
open Store.Cid
open Syntax
open Substitution

open Id

module Apx = struct

  module LF = struct

    type kind =
      | Typ
      | PiKind of typ_decl * kind

    and typ_decl =
      | TypDecl of name * typ

    and sigma_decl =
      | SigmaDecl of name * typ_rec

    and ctyp_decl =
      | MDecl of  name * typ  * dctx
      | PDecl of  name * typ  * dctx

    and typ =
      | Atom  of cid_typ * spine
      | PiTyp of typ_decl * typ

    and typ_rec = typ list

    and normal =
      | Lam  of name * normal
      | Root of head * spine

    and head =
      | BVar  of offset
      | Const of cid_term
      | MVar  of offset * sub
      | PVar  of offset * sub
      | FVar  of name

    and spine =
      | Nil
      | App of normal * spine

    and sub =                       
      | Shift of offset             
      | Dot   of front * sub        

    and front =                     
      | Head of head                
      | Obj  of normal              

    and dctx =
      | Null
      | CtxVar   of offset
      | DDec     of dctx * typ_decl

    and 'a ctx =
      | Empty
      | Dec of 'a ctx * 'a

    and sch_elem =
      | SchElem of typ_decl ctx * sigma_decl

    and schema =
      | Schema of sch_elem list

    and psi_hat = offset option * offset 
  end

  module Comp = struct 

    type typ =
      | TypBox   of LF.typ  * LF.dctx        
      | TypArr   of typ * typ         
      | TypCtxPi of (name * cid_schema) * typ
      | TypPiBox of LF.ctyp_decl * typ 

    and exp_chk =
       | Syn    of exp_syn 
       | Fun    of name * exp_chk         (* fn   f => e         *)
       | CtxFun of name * exp_chk         (* FN   f => e         *)
       | MLam   of name * exp_chk         (* mlam f => e         *)
       | Box    of LF.psi_hat * LF.normal (* box (Psi hat. M)    *)
       | Case   of exp_syn * branch list

    and exp_syn =
       | Var    of name                               (* x              *)
       | Apply  of exp_syn * exp_chk                  (* i e            *)
       | CtxApp of exp_syn * LF.dctx                  (* i [Psi]        *)
       | MApp   of exp_syn * (LF.psi_hat * LF.normal) (* i [Psi hat. M] *)
       | Ann    of exp_chk * typ                      (* e : tau        *)

    and branch =
      | BranchBox of LF.ctyp_decl LF.ctx
          * (LF.psi_hat * LF.normal * (LF.typ * LF.dctx))
          * exp_chk

  end

end

module Unify = Unify.EmptyTrail

exception NotImplemented

type error =
  | ExpAppNotFun
  | ExpNilNotAtom
  | KindMisMatch
  | SubIllTyped
  | TypMisMatch of Int.LF.dctx * Int.LF.tclo * Int.LF.tclo
  | IllTyped    of Int.LF.dctx * Apx.LF.normal * Int.LF.tclo

exception Error of string

(* PHASE 0 : Indexing

   index_term names ext_m = m

   Translates an object ext_m in external syntax
   into an object m in approximate internal syntax.


   ASSUMPTION:

      ext_m is in beta-eta normal form
          m is in beta-eta normal form, i.e.
      all occurrences of free variables in m
      are eta-expanded.

   Generalization:
      Allow user to write terms which are not eta-expanded.
      this requires a change in the definition of FVar constructor.

      FVar of name

      would need to change to  FVar of name * sub * typ * dctx
      and may also need information about its type and context in
      which it was created;

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
      let offset = CVar.index_of_name cvars p in 
      let s'     = index_sub cvars bvars s in 
        Apx.LF.PVar (offset, s')
  | Ext.LF.MVar (_, u, s) -> 
      let offset = CVar.index_of_name cvars u in 
      let s'     = index_sub cvars bvars s in 
        Apx.LF.MVar (offset, s')

and index_spine cvars bvars = function
  | Ext.LF.Nil ->
      Apx.LF.Nil

  | Ext.LF.App (_, m, s) ->
      let m' = index_term  cvars bvars m
      and s' = index_spine cvars bvars s in
        Apx.LF.App (m', s')

(* THE FOLLOWING IS PROCESSING AN INCORRECT EXTERNAL SUBSTITUTION
   INTO A CORRECT APPROXIMATE SUBSTITUTION !!! *)
and index_sub cvars bvars = function 
  | Ext.LF.Id (_, _ ) -> Apx.LF.Shift 0

  | Ext.LF.Normal (_, s, n) -> 
      let s' = index_sub cvars bvars s in 
        begin match index_term cvars bvars n with 
          | Apx.LF.Root(h, Apx.LF.Nil) -> Apx.LF.Dot(Apx.LF.Head h, s')
          | m                               -> Apx.LF.Dot(Apx.LF.Obj  m, s')
        end

  | Ext.LF.Dot _         -> Apx.LF.Shift 0

let index_decl cvars bvars (Ext.LF.TypDecl(x, a)) = 
      let a'     = index_typ cvars bvars a in 
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
        (Apx.LF.TypDecl(x,a'), bvars')

let rec index_dctx cvars bvars = function 
  | Ext.LF.Null        -> (Apx.LF.Null , bvars)
  | Ext.LF.CtxVar psi_name  -> 
      let offset = CVar.index_of_name cvars psi_name in 
        (Apx.LF.CtxVar offset , bvars)
  | Ext.LF.DDec (psi, decl) -> 
      let (psi', bvars') = index_dctx cvars bvars psi in 
      let (decl', bvars'')  = index_decl cvars bvars' decl in 
        (Apx.LF.DDec(psi', decl'), bvars'')
  
let index_psihat explicit_psihat = 
  List.length explicit_psihat

let rec index_ctx index_dec cvars bvars = function 
  | Ext.LF.Empty        -> (Apx.LF.Empty , bvars)

  | Ext.LF.Dec (psi, dec) -> 
      let (psi', bvars') = index_ctx index_dec cvars bvars psi in 
      let (dec',bvars'') = index_dec cvars bvars' dec in 
        (Apx.LF.Dec(psi', dec'), bvars'')
  
let index_cdecl cvars = function
  | Ext.LF.MDecl(_, u, a, psi) -> 
      let (psi', bvars')  = index_dctx cvars (BVar.create ()) psi in 
      let  a'             = index_typ  cvars bvars' a in 
      let cvars'          = CVar.extend cvars (CVar.mk_entry u) in 
        (Apx.LF.MDecl(u, a', psi'), cvars')

  | Ext.LF.PDecl(_, p, a, psi) -> 
      let (psi', bvars')  = index_dctx cvars (BVar.create ()) psi in 
      let  a'             = index_typ  cvars bvars' a in 
      let cvars'          = CVar.extend cvars (CVar.mk_entry p) in 
        (Apx.LF.PDecl(p, a', psi') , cvars')


(* Translation of external schemas into approximate schemas *)
(* let rec index_elements el_list = match el_list with 
  | [] -> []
  | el::el_list' -> index_el el :: index_elements el_list'

and index_el (SchElem (_, typ_ctx, sigma_decl)) = 

let index_schema (Schema el_list) = 
  index_elemets el_list 
*)
(* Translation of external computations into approximate computations *)
let rec index_ctyp cvars  = function
  | Ext.Comp.TypBox (_, a, psi)    ->
      let (psi', bvars') = index_dctx cvars (BVar.create ()) psi in 
      let  a'            = index_typ cvars bvars' a   in
        Apx.Comp.TypBox(a', psi')

  | Ext.Comp.TypArr (_, tau, tau') -> 
      Apx.Comp.TypArr (index_ctyp cvars tau, index_ctyp cvars tau')

  | Ext.Comp.TypPiBox (cdecl, tau)    -> 
      let (cdecl', cvars') = index_cdecl cvars cdecl in 
        Apx.Comp.TypPiBox(cdecl', index_ctyp cvars' tau)

  | Ext.Comp.TypCtxPi (_, (ctx_name, schema_name), tau)    ->      
      let cvars'           = CVar.extend cvars (CVar.mk_entry ctx_name) in 
      let schema_cid       = Schema.index_of_name schema_name in 
      (* if exception Not_Found is raised, it means schema_name does not exist *)      
        Apx.Comp.TypCtxPi((ctx_name, schema_cid), index_ctyp cvars' tau)





(* ******************************************************************* *)
(* PHASE 1 : Elaboration and free variables typing                     *)

(* Free variable constraints: 

   fvar_cnstr  C := . | Root (FVar X, tS) & C 

   The constraints are generated when encountering
   a free variable X whose type is yet unknown and has a 
   non-pattern spine tS. This means we cannot easily infer
   the type of the free variable X. 
 
*)



let fvar_cnstr : ((Apx.LF.normal * Int.LF.cvar)  list) ref = ref []

let add_fvarCnstr  c = fvar_cnstr := c :: !fvar_cnstr

let reset_fvarCnstr () = (fvar_cnstr := [])

let rec raiseType cPsi tA = match cPsi with
  | Int.LF.Null -> tA
  | Int.LF.DDec (cPsi', decl) ->
      raiseType cPsi' (Int.LF.PiTyp (decl, tA))

(* patSpine s = bool

   if cPsi |- s : A <- P  and
      s is a pattern spine (simple approximate),
   i.e. it consists of distinct bound variables

   then
      return true;
      otherwise false.

*)
let patSpine spine =
  let rec patSpine' seen_vars spine = match spine with
    | Apx.LF.Nil ->
        (true, 0)

    | Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine) ->
        if not (List.mem x seen_vars) then 
          let (b,l) = patSpine' (x :: seen_vars) spine in 
            (b, l+1)
        else (false, 0)

    | _ ->  (false, 0)
  in
    patSpine' [] spine


(* etaExpandMV cPsi sA s' = tN 

    cPsi'  |- s'   <= cPsi 
    cPsi   |- [s]A <= typ

    cPsi'  |- tN   <= [s'][s]A

*)
let rec etaExpandMV cPsi sA s' = etaExpandMV' cPsi (Whnf.whnfTyp sA)  s'

and etaExpandMV' cPsi sA  s' = match sA with
  | (Int.LF.Atom (_a, _tS) as tP, s) -> 
      let u = Whnf.newMVar (cPsi, Int.LF.TClo(tP,s)) in        
         Int.LF.Root (Int.LF.MVar (u, s'), Int.LF.Nil)  

  | (Int.LF.PiTyp (Int.LF.TypDecl (x, _tA) as decl, tB), s) -> 
      Int.LF.Lam (x, etaExpandMV (Int.LF.DDec (cPsi, LF.decSub decl s)) (tB, LF.dot1 s) (LF.dot1 s'))

(* elKind  cPsi (k,s) = K

*)
let rec elKind cPsi k = match k with
  | Apx.LF.Typ ->
      Int.LF.Typ

  | Apx.LF.PiKind (Apx.LF.TypDecl (x, a), k) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tK    = elKind cPsi' k in
        Int.LF.PiKind (Int.LF.TypDecl (x, tA), tK)

(* elTyp cPsi a = A

   Pre-condition:
       Upsilon = set of free variables

   if |cPsi| |- a <= type and
      a is in beta-eta normal form
   then
       cPsi   |- A <- type (pre-dependent)
   and A is in beta-eta normal form.

   Effect:
       Upsilon' = FV(A)  where Upsilon' is an extension of Upsilon

*)
and elTyp cPsi a = match a with
  | Apx.LF.Atom (a, s) ->
      let tK = (Typ.get a).Typ.kind in
      let i  = (Typ.get a).Typ.implicit_arguments in
      let (_, d) = Context.dctxToHat cPsi in  
      (* let tS = elKSpineI cPsi s i (tK, Substitution.LF.id) in *)
      let tS = elKSpineI cPsi s i (tK, Int.LF.Shift d) in  
        Int.LF.Atom (a, tS)

  | Apx.LF.PiTyp (Apx.LF.TypDecl (x, a), b) ->
      let tA    = elTyp cPsi a in
      let cPsi' = (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA))) in
      let tB    = elTyp cPsi' b in
        Int.LF.PiTyp (Int.LF.TypDecl (x, tA), tB)

(* elTerm  cPsi m sA = M
   elTermW cPsi m sA = M  where sA = (A,s) is in whnf
                                m is in beta-eta normal form.
   if |cPsi| |- m <= |[s]A'|
       cPsi  |- s <= cPsi'
       cPsi' |- A <- type (pre-dependent)
   then
       cPsi |- M <- A     (pre-dependent)
   and M is in beta-eta normal form, i.e.
     all free variables are eta-expanded.

*)
and elTerm cPsi m sA = elTermW cPsi m (Whnf.whnfTyp sA)

and elTermW cPsi m sA = match (m, sA) with
  | (Apx.LF.Lam (x, m), (Int.LF.PiTyp (Int.LF.TypDecl (_x, _tA) as decl, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub decl s) in
      let tM    = elTerm cPsi' m (tB, LF.dot1 s) in
        Int.LF.Lam(x, tM)

  | (Apx.LF.Root (Apx.LF.Const c, spine), ((Int.LF.Atom _ as tP), s)) ->
      let tA = (Term.get c).Term.typ in
      let i  = (Term.get c).Term.implicit_arguments in
      let (_, d) = Context.dctxToHat cPsi in  
      let tS = elSpineI cPsi spine i (tA, Int.LF.Shift d) (tP, s) in 
        Int.LF.Root (Int.LF.Const c, tS)

  | (Apx.LF.Root (Apx.LF.BVar x, spine), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in 
        Int.LF.Root (Int.LF.BVar x, tS) 

  | (Apx.LF.Root (Apx.LF.FVar x, spine) as m, (Int.LF.Atom _ as tP, s)) ->
      begin try
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
      (* let tS = elSpine cPsi spine (tA, LF.id) (tP, s) in *)
        let (_, d) = Context.dctxToHat cPsi in 
      let tS = elSpine cPsi spine (tA, Int.LF.Shift d) (tP, s) in 
          Int.LF.Root (Int.LF.FVar x, tS)
      with Not_found ->
        let (patternSpine, _l) = patSpine spine in 
        if patternSpine then
        let (_, d) = Context.dctxToHat cPsi in 
        let (tS, tA) = elSpineSynth cPsi spine (Int.LF.Shift d) (tP, s) in
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

  | _ ->
      raise (Error "Ill-typed " (* (IllTyped (cPsi, m, sA)) *))

(* elSpineI  cPsi spine i sA sP  = S
   elSpineIW cPsi spine i sA sP  = S

     where sA = (A,s) and sP = (P,s')
       and sA and sP in whnf

   Pre-condition:
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; cPsi |- spine <- [s]A  (approx)
   then
      O' ; U' ; cPsi |- S <- [s]A : [s']P (pre-dependent)


   Post-condition:
     U' = extension of U containing all free variables of S
     O' = extension of O containing i new meta-variables
              for implicit arguments

   Comment: elSpineI will insert new meta-variables (as references)
     for omitted implicit type arguments; their type is pre-dependent.
*)
and elSpineI cPsi spine i sA sP =
  elSpineIW cPsi spine i (Whnf.whnfTyp sA) (Whnf.whnfTyp sP)

and elSpineIW cPsi spine i sA sP =
  if i = 0 then
    elSpine cPsi spine sA sP
  else
    match sA with
      | (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s) ->
          (* cPsi' |- tA <= typ
             cPsi  |- s  <= cPsi'      cPsi |- tN <= [s]A

             tN = u[s']  and u::A'[.]   

             s.t.  cPsi |- u[s'] => [s']A'  where cPsi |- s' : .
             and    [s]A = [s']A'. Therefore A' = [s']^-1([s]A)
             
          *)
          let (_, d) = Context.dctxToHat cPsi in      
          let tN     = etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift d) in 
          let spine' = elSpineI cPsi spine (i - 1) (tB, Int.LF.Dot (Int.LF.Obj tN, s)) sP in
            Int.LF.App (tN, spine')
      (* other cases impossible by (soundness?) of abstraction *)

(* elSpine  cPsi spine sA sP = S
   elSpineW cPsi spine sA sP = S
     where sA = (A,s) and sP = (P,s')
       and sA and sP in whnf

   Pre-condition:
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; cPsi |- spine <- [s]A  (approx)
   then
      O' ; U' ; cPsi |- S <- [s]A : [s']P (pre-dependent)


   Post-condition:
     U' = extension of U containing all free variables of S
     O' = extension of O containing new meta-variables of S

*)
and elSpine cPsi spine sA sP =
  elSpineW cPsi spine (Whnf.whnfTyp sA) (Whnf.whnfTyp sP)

and elSpineW cPsi spine sA sP = match (spine, sA) with
  | (Apx.LF.Nil, (Int.LF.Atom (a, _spine), _s)) ->
      let (Int.LF.Atom (a', _spine'), _s') = sP in
        if a = a' then
          Int.LF.Nil
        else
          raise (Error "Type mismatch " (* (TypMisMatch (cPsi, sA, sP)) *))

  | (Apx.LF.Nil, _) ->
      raise (Error "Expression not of atomic type" ) (* ExpNilNotAtom *)

  | (Apx.LF.App (m, spine), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) ->
      let tM = elTerm  cPsi m (tA, s) in
      let tS = elSpine cPsi spine (tB, Int.LF.Dot (Int.LF.Obj tM, s)) sP in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, sA) ->
      raise (Error ("Spine of atomic type " ^ 
                      (Pretty.Int.DefaultPrinter.typToString (Int.LF.TClo(sA)))))

(* see invariant for elSpineI *)
and elKSpineI cPsi spine i sK =
  if  i = 0 then
    elKSpine cPsi spine sK
  else
    match sK with
      | (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s) ->
          let (_, d) = Context.dctxToHat cPsi in 
          let tN     = etaExpandMV Int.LF.Null (tA,s) (Int.LF.Shift d) in
          let spine' = elKSpineI cPsi spine (i - 1) (tK, Int.LF.Dot (Int.LF.Obj tN, s)) in
            Int.LF.App (tN, spine')

      (* other cases impossible by (soundness?) of abstraction *)


(* see invariant for elSpine *)
and elKSpine cPsi spine sK = match (spine, sK) with
  | (Apx.LF.Nil, (Int.LF.Typ, _s)) ->
      Int.LF.Nil

  | (Apx.LF.Nil, _) ->
      raise (Error "Kind mismatch") (* KindMisMatch *)

  | (Apx.LF.App (m, spine), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) ->
      let tM = elTerm   cPsi m (tA, s) in
      let tS = elKSpine cPsi spine (tK, Int.LF.Dot (Int.LF.Obj tM, s)) in
        Int.LF.App (tM, tS)

  | (Apx.LF.App _, _) ->
      raise (Error "Non-empty spine of atomic type") (* ExpAppNotFun *)

(* elSpineSynth cPsi spine s' sP = (S, A') 

   Pre-condition:
     U = free variables
     O = meta-variables for implicit arguments

   Invariant:

   If O ; U ; Psi |- spine < [s]P
      and spine is a pattern spine
                  
              Psi |- s' <= .      |cPsi| = d  and s' = ^d

                
              Psi |- s   <= Psi'
                . |- ss' <= Psi

   then O ; U ; Psi |- S : [s']A' < [s]P

   Post-condition:
     U = containing all free variables of S (unchanged)
     O = containing new meta-variables of S (unchanged)

*)
and elSpineSynth cPsi spine s' sP = match (spine, sP) with
  | (Apx.LF.Nil, (tP, s))  ->
      let ss = LF.invert s' in 
        (* ensure that [ss] ([s]tP) exists ! *)
       (Int.LF.Nil, Int.LF.TClo(tP, LF.comp s ss)) 

  | (Apx.LF.App (Apx.LF.Root (Apx.LF.BVar x, Apx.LF.Nil), spine), sP) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
      (* cPsi |- tA : type 
         cPsi |- s' : cPsi'
       *)
      let ss = LF.invert s' in 
      let tA' = Whnf.normTyp (tA, ss) in 

      (*   cPsi |- s', x : cPsi', y:tA' *)
      let (tS, tB) = elSpineSynth cPsi spine (Int.LF.Dot(Int.LF.Head(Int.LF.BVar x), s')) sP in

      (*  cPsi |- tS : [s', x]tB <- sP  (pre-dependent) *)

      (* cPsi, y:A |- tB' <- type (pre-dependent) *)

         (Int.LF.App (Int.LF.Root (Int.LF.BVar x, Int.LF.Nil), tS),
          Int.LF.PiTyp (Int.LF.TypDecl (Id.mk_name None, tA'), tB))

   (* other cases impossible *)


(* ******************************************************************* *)
(* Solve free variable constraints *)

let rec solve_fvarCnstr cnstr = match cnstr with 
  | []  -> ()
  | ((Apx.LF.Root (Apx.LF.FVar x, spine) , Int.LF.Inst(r, cPsi, Int.LF.TClo(tP,s), _)) :: cnstrs) ->
     begin try 
        let tA = FVar.get x in
          (* For type reconstruction to succeed, we must have
             . |- tA <= type
             This will be enforced during abstraction *)
        let (_, d) = Context.dctxToHat cPsi in 
          
        (* let tS = elSpine cPsi spine (tA, LF.id) (tP,s) in *)
        let tS = elSpine cPsi spine (tA, Int.LF.Shift d) (tP,s) in 
          (r := Some (Int.LF.Root (Int.LF.FVar x, tS));
           solve_fvarCnstr cnstrs  
          )
     with Not_found ->
       raise (Error "Type reconstruction: Left-over constraints for free variables \n")
     end


(* ******************************************************************* *)
(* PHASE 2 : Reconstruction *)

(*  recTerm cPsi sM sA = ()

    Pre-condition:

    U = FV(M) (FV(A), FV(K) resp.)
    O = meta-variables in M (A, K, resp.)

   Invariant:
    If  O ; U ; cPsi |- [s']M <- [s]A (predependent)
        and there exists a modal substitution r
        s.t. O' |- r <= O
    then

       recTerm cPsi sM sA succeeds and

       O' ; [|r|]U ; [|r|]cPsi |- [|r|][s']M <= [|r|][s]A

   Post-condition:

     U' = [|r|]U
     O' s.t. O' |- r <= O , and

   Effect:
     - all meta-variables in O have been destructively updated.
     - may raise exception Error, if no modal substitution r exists.

Similar invariants and pre- and post-conditions for:

    recKind cPsi (K,s) = K'
    recTyp  cPsi (A,s) = A'

*)
let rec recKind cPsi sK = match sK with
  | (Int.LF.Typ, _s) ->
      ()

  | (Int.LF.PiKind (Int.LF.TypDecl(_x, tA) as adec, tK), s) -> (
      recTyp cPsi (tA, s);
      recKind (Int.LF.DDec (cPsi, LF.decSub adec s)) (tK, LF.dot1 s)
    )

and recTyp cPsi sA = recTypW cPsi (Whnf.whnfTyp sA)

and recTypW cPsi sA = match sA with
  | (Int.LF.Atom (a, tS) , s) ->
      let tK = (Typ.get a).Typ.kind in
        let (_, d) = Context.dctxToHat cPsi in 
      let tA' =  recKSpine cPsi (tS, s) (tK, Int.LF.Shift d) in 
        tA'


  | (Int.LF.PiTyp ((Int.LF.TypDecl (_x, tA) as adec), tB), s) -> (      
      recTyp cPsi (tA, s);
      recTyp (Int.LF.DDec (cPsi, LF.decSub adec s)) (tB, LF.dot1 s);
    )

and recTerm cPsi sM sA =
  recTermW cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

and recTermW cPsi sM sA = match (sM, sA) with
  | ((Int.LF.Lam (_, tM), s'), (Int.LF.PiTyp (tA, tB), s)) ->
      let cPsi' = Int.LF.DDec (cPsi, LF.decSub tA s) in
        recTerm cPsi' (tM, LF.dot1 s') (tB, LF.dot1 s)

  | ((Int.LF.Root (Int.LF.Const c, tS), s'), (Int.LF.Atom _ as tP, s)) ->
      let tA = (Term.get c).Term.typ in
      let (_, d) = Context.dctxToHat cPsi in 
        recSpine cPsi (tS, s') (tA, Int.LF.Shift d) (tP, s)

  | ((Int.LF.Root (Int.LF.BVar x, tS), s'), (Int.LF.Atom _ as tP, s)) ->
      let Int.LF.TypDecl (_, tA) = Context.ctxDec cPsi x in
        recSpine cPsi (tS, s') (tA, LF.id) (tP, s)

  | ((Int.LF.Root (Int.LF.MVar (Int.LF.Inst (_r, cPhi, tP', _cnstr), t), _tS), s'), (Int.LF.Atom _ as tP, s)) ->
     (* By invariant of whnf: tS = Nil  and r will be lowered and is uninstantiated *)
     (* Dealing with constraints is postponed, Dec  2 2008 -bp *)
      let s1 = (LF.comp t s') in
        (recSub cPsi s1 cPhi;
         Unify.unifyTyp (Context.dctxToHat cPsi, (tP', s1), (tP, s))
        )  

  | ((Int.LF.Root (Int.LF.FVar x, tS), s'), (Int.LF.Atom _ as tP, s)) ->
      (* x is in eta-expanded form and tA is closed
         type of FVar x : A[cPsi'] and FVar x should be
         associated with a substitution, since tA is not always
         closed.

         by invariant of whnf: s' = id
      *)
      let tA = FVar.get x in
      let (_, d) = Context.dctxToHat cPsi in  
        recSpine cPsi (tS, s') (tA, Int.LF.Shift d) (tP, s)    

and recSpine cPsi sS sA sP = 
  recSpineW cPsi sS (Whnf.whnfTyp sA) sP

and recSpineW cPsi sS sA sP = match (sS, sA) with
  | ((Int.LF.Nil, _s), (tP', s')) ->
      Unify.unifyTyp (Context.dctxToHat cPsi, sP, (tP', s'))  
      
  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiTyp (Int.LF.TypDecl (_, tA), tB), s)) -> (
      let _ = recTerm  cPsi (tM, s') (tA, s) in 
      (*   cPsi |-  s <= cPsi1     cPsi1 |- Pi x:tA .tB <= typ
                                   cPsi1 |- tA <= typ   
                                   cPsi1, x:tA |- tB <= typ

           cPsi |-  s'<= cPsi2     cPsi |- [s']tM <= tA'   tA' = [s]tA   
           
           cPsi2 |- tM <= tA2       [s']tA2 = tA' = [s]tA
       
           cPsi |-  [s']tM . s <= cPsi1, x: tA

      *)
      recSpine cPsi (tS, s') (tB, Int.LF.Dot (Int.LF.Obj (Int.LF.Clo (tM,s')), s)) sP 
    )

  | ((Int.LF.SClo (tS, s), s'), sA) -> 
      recSpine cPsi (tS, LF.comp s s') sA sP

and recKSpine cPsi sS sK = match (sS, sK) with
  | ((Int.LF.Nil, _s), (Int.LF.Typ, _s')) ->
      ()

  | ((Int.LF.App (tM, tS), s'), (Int.LF.PiKind (Int.LF.TypDecl (_, tA), tK), s)) -> (
      recTerm   cPsi (tM, s') (tA, s);
      recKSpine cPsi (tS, s') (tK, Int.LF.Dot (Int.LF.Obj tM, s))
    )

  | ((Int.LF.SClo (tS, s),  s'), sK) -> 
      recKSpine cPsi (tS, LF.comp s s') sK

and recSub cPsi s cPhi = match (s, cPhi) with
  | (Int.LF.Shift _n, _cPhi) ->
      (* We may need to expand cPhi further if n =/= 0 *)
      ()

  | (Int.LF.Dot (Int.LF.Head Int.LF.BVar x, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) ->
      let Int.LF.TypDecl (_, tA') = Context.ctxDec cPsi x in 
        recSub  cPsi s cPhi;
        Unify.unifyTyp (Context.dctxToHat cPsi, (tA', LF.id), (tA, s))


  | (Int.LF.Dot (Int.LF.Obj tM, s), Int.LF.DDec (cPhi, Int.LF.TypDecl (_, tA))) -> (
      recSub  cPsi s cPhi;
      recTerm cPsi (tM, LF.id) (tA, s)
    )

  | (Int.LF.Dot (Int.LF.Undef, _s), _) ->
      raise (Error "Found Undef")

  (* needs other cases for Head(h) where h = MVar, Const, etc. -bp *)

let recSgnDecl d = match d with
  | Ext.Sgn.Typ (_, a, extK)   ->
      let apxK     = index_kind (CVar.create ()) (BVar.create ()) extK in
      let _        = FVar.clear () in
      let tK       = elKind Int.LF.Null apxK in
      let _        = solve_fvarCnstr !fvar_cnstr in
      let _        = reset_fvarCnstr () in 
      let _        = recKind Int.LF.Null (tK, LF.id) in
      let (tK', i) = Abstract.abstrKind tK in
      (* let _        = Printf.printf "\n Reconstruction (wih abstraction) of constant %s \n %s \n\n" a.string_of_name
        (Pretty.Int.DefaultPrinter.kindToString tK') in *)
      let _        = Check.LF.checkKind Int.LF.Empty Int.LF.Null tK' in  
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" a.string_of_name  in 
      let a'       = Typ.add (Typ.mk_entry a tK' i) in
        (* why does Term.add return a' ? -bp *)
        (* because (a : name) and (a' : cid_typ) *)
        Int.Sgn.Typ (a', tK')

  | Ext.Sgn.Const (_, c, extT) ->
      let apxT     = index_typ (CVar.create ()) (BVar.create ()) extT in
      let _        = Printf.printf "\n Reconstruct constant : %s  \n" c.string_of_name  in 
      let _        = FVar.clear () in
      let tA       = elTyp Int.LF.Null apxT in
      let _        = solve_fvarCnstr !fvar_cnstr in
      let _        = reset_fvarCnstr () in 
      (* let _        = Printf.printf "\n Elaboration of constant %s \n : %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))) in  *)
      let _        = recTyp Int.LF.Null (tA, LF.id) in
      (* let _        = Printf.printf "\n Reconstruction (without abstraction) of constant %s \n %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA, LF.id))) in *)

      let (tA', i) = Abstract.abstrTyp tA in 
      (*let _        = Printf.printf "\n Reconstruction (with abstraction) of constant %s \n %s \n\n" c.string_of_name
        (Pretty.Int.DefaultPrinter.typToString (Whnf.normTyp (tA', LF.id))) in *)
      let _        = Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', LF.id) in  
      let _        = Printf.printf "\n DOUBLE CHECK for constant : %s  successful! \n" c.string_of_name  in 
      (* why does Term.add return a c' ? -bp *)
      let c'       = Term.add (Term.mk_entry c tA' i) in 
        Int.Sgn.Const (c', tA')



