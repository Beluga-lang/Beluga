(* -------------------------------------------------------------*)
(* PHASE 0 : Indexing
 *
 * index_term names ext_m = (m, fvars)
 *
 * Translates an object ext_m in external syntax
 * into an object m in approximate internal syntax.
 *
 * ASSUMPTION:
 *
 *    ext_m is in beta normal form
 *        m is in beta normal form, i.e.
 *
 * BP: 7 Dec, 2011: collecting the free variables seems irrelevant.
 *)

open Id
open Store
open Store.Cid
open Syntax


module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer
module RR = Pretty.Int.NamedRenderer


let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

type free_cvars = 
    FMV of Id.name | FPV of Id.name | FSV of Id.name

let rec lookup_fv fvars m = begin  match (fvars, m) with 
     ([], _ ) -> false
  | (FMV n :: fvars' , FMV m) -> 
      if n = m then true
      else lookup_fv fvars' (FMV m) 

  | (FPV p :: fvars' , FPV q) -> 
      if p = q then true
      else lookup_fv fvars' m 
  | (FPV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m

end

let rec get_ctxvar psi = match psi with
  | Ext.LF.Null -> None
  | Ext.LF.CtxVar (_loc, psi_name) -> Some psi_name
  | Ext.LF.DDec (psi, _ ) -> get_ctxvar psi


let rec get_ctxvar_mobj mO = match mO with
  | Ext.Comp.MetaCtx (_, cPsi) -> get_ctxvar cPsi 
  | Ext.Comp.MetaObjAnn (_, cPsi, _tM) -> get_ctxvar cPsi 
  | _ -> None

let rec length_typ_rec t_rec = match t_rec with 
  | Ext.LF.SigmaLast _ -> 1 
  | Ext.LF.SigmaElem (x, _ , rest ) -> 
      (print_string (R.render_name x ^ "  ");
      1 + length_typ_rec rest )

(* index_of cQ n = i
   where cQ = cQ1, Y, cQ2 s.t. n = Y and length cQ2 = i
*)

let rec index_of cQ n = match cQ with
  | [] -> 
      raise (Error.Violation "index_of for a free variable does not exist -- should be impossible")
        (* impossible due to invariant on collect *)
  | (x, _ )::cQ' -> if x = n then 1 else (index_of cQ' n) + 1



let rec index_kind cvars bvars fvars = function
  | Ext.LF.Typ _ ->
      (Apx.LF.Typ, fvars)

  | Ext.LF.ArrKind (_, a, k) ->
      let x            = Id.mk_name Id.NoName
      and (a', fvars1) = index_typ cvars bvars fvars a in
      let (ctxOpt, bvars) = bvars in 
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (k', fvars2) = index_kind cvars (ctxOpt, bvars') fvars1 k in
        (Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.No), k') , fvars2)

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let (a', fvars1) = index_typ cvars bvars fvars a in 
      let (ctxOpt, bvars) = bvars in 
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (k', fvars2) = index_kind cvars (ctxOpt, bvars') fvars1 k in
        (Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), k') , fvars2)

and index_typ cvars bvars fvars = function
  | Ext.LF.Atom (loc, a, s) ->
      begin try 
        let a' = Typ.index_of_name a
        and (s', fvars') = index_spine cvars bvars fvars s in
          (Apx.LF.Atom (loc, a', s') , fvars')
      with Not_found ->
       raise (Error.Error (Some loc, Error.UnboundName a))
      end
    

  | Ext.LF.ArrTyp (_loc, a, b) ->
      let x            = Id.mk_name Id.NoName
      and (a', fvars1) = index_typ cvars bvars fvars a in
      let (ctxOpt, bvars) = bvars in 
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (b', fvars2) = index_typ cvars (ctxOpt, bvars') fvars1 b in
        (Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.No), b') , fvars2)

  | Ext.LF.PiTyp (_loc, Ext.LF.TypDecl (x, a), b) ->
      let (a', fvars1)  = index_typ cvars bvars  fvars a in
      let (ctxOpt, bvars) = bvars in 
      let bvars'        = BVar.extend bvars (BVar.mk_entry x) in
      let (b', fvars2)  = index_typ cvars (ctxOpt, bvars') fvars1 b in
        (Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), b') , fvars2)
  
  | Ext.LF.Sigma (_, typRec) ->
      let (typRec', fvars') = index_typ_rec cvars bvars fvars typRec in
      (Apx.LF.Sigma typRec' , fvars')

and index_typ_rec cvars bvars fvars = function
  | Ext.LF.SigmaLast a -> 
      let (last, fvars') = index_typ cvars bvars fvars a in 
        (Apx.LF.SigmaLast last , fvars')
  | Ext.LF.SigmaElem (x, a, rest) ->
      let (a', fvars1)    = index_typ cvars bvars fvars a in
      let (ctxOpt, bvars0) = bvars in 
      let bvars'          = BVar.extend bvars0 (BVar.mk_entry x) in
      let (rest', fvars2) = index_typ_rec cvars (ctxOpt, bvars') fvars1 rest in
        (Apx.LF.SigmaElem (x, a', rest') , fvars2)

and index_tuple cvars bvars fvars = function
  | Ext.LF.Last m -> 
      let (m', fvars') = index_term cvars bvars fvars m in 
        (Apx.LF.Last m', fvars')
  | Ext.LF.Cons (m, rest) ->
      let (m', fvars1) = index_term cvars bvars fvars m in
      let (rest', fvars2) = index_tuple cvars bvars fvars1 rest in
        (Apx.LF.Cons (m', rest') , fvars2)

and index_term cvars ((_, _ ) as bvars) fvars = function
  | Ext.LF.Lam (loc, x, m) ->
      let (ctxOpt, bvars) = bvars in 
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let (m', fvars')     = index_term cvars (ctxOpt, bvars') fvars m in
        (Apx.LF.Lam (loc, x, m') , fvars')

  | Ext.LF.Tuple (loc, tuple) ->
      let (tuple', fvars') = index_tuple cvars bvars fvars tuple in
        (Apx.LF.Tuple (loc, tuple') , fvars')

  | Ext.LF.Root (loc, h, s) ->
      let (h', fvars1) = index_head  cvars bvars fvars h in
      let (s', fvars2) = index_spine cvars bvars fvars1 s in
        (Apx.LF.Root (loc, h', s') , fvars2)

and index_head cvars bvars fvars = function
  | Ext.LF.Name (_, n) ->
      (* let _        = dprint (fun () -> "Indexing name " ^ n.string_of_name)
         in *)
      let (_, bvars) = bvars in 
      begin try
        (Apx.LF.BVar (BVar.index_of_name bvars n) , fvars)
      with Not_found -> try
        (Apx.LF.Const (Term.index_of_name n) , fvars)
      with Not_found -> 
        (dprint (fun () -> "FVar " ^ n.string_of_name );
        (Apx.LF.FVar n , fvars))
          
      end

  | Ext.LF.ProjName (loc, k, n) ->
      let (bvar, fvars') = index_head cvars bvars fvars (Ext.LF.Name (loc, n)) in
        (Apx.LF.Proj(bvar, k), fvars')

  | Ext.LF.PVar (_, p, s) ->
      begin try
        let offset = CVar.index_of_name cvars p in
        let (s' , fvars') = index_sub cvars bvars fvars s in
          (Apx.LF.PVar (Apx.LF.Offset offset, s') , fvars')
      with Not_found ->
        let _ = dprint (fun () -> "PVar Not_found " ^ R.render_name p) in
        let (s', fvars')     = index_sub cvars bvars fvars s in
          (Apx.LF.FPVar (p, s') , FPV p :: fvars' )
      end

  | Ext.LF.ProjPVar (loc, k, (p, s)) ->
      let (pvar, fvars') = index_head cvars bvars fvars (Ext.LF.PVar (loc, p, s)) in
        (Apx.LF.Proj (pvar, k), fvars')

        
  | Ext.LF.Hole _loc -> 
      (Apx.LF.Hole , fvars)

  | Ext.LF.MVar (_, u, s) ->
      if lookup_fv fvars (FMV u) then 
        let (s', fvars')     = index_sub cvars bvars fvars s in
          (Apx.LF.FMVar (u, s') , fvars')
      else 
        begin try
          let offset = CVar.index_of_name cvars u in
          let (s', fvars')     = index_sub cvars bvars fvars s in
            (Apx.LF.MVar (Apx.LF.Offset offset, s') , fvars')
        with Not_found ->
          let (s', fvars')     = index_sub cvars bvars fvars s in
            (Apx.LF.FMVar (u, s') , FMV u :: fvars')
        end

  | Ext.LF.SVar (loc, n, _sigma) -> 
      let _        = dprint (fun () -> "Indexing head : SVar " ^ n.string_of_name) in 
        raise (Error.Error (Some loc, Error.UnboundName n))

and index_spine cvars bvars fvars = function
  | Ext.LF.Nil ->
      (Apx.LF.Nil , fvars)

  | Ext.LF.App (_, m, s) ->
      let (m', fvars')  = index_term  cvars bvars fvars m in
      let (s', fvars'') = index_spine cvars bvars fvars' s in
        (Apx.LF.App (m', s') , fvars'')

and index_sub cvars bvars fvars = function
  | Ext.LF.Id loc -> 
      begin match bvars with 
        | (None, _ ) -> raise (Error.Error (Some loc , Error.UnboundIdSub))
        | (Some ctxvar, _ ) -> (Apx.LF.Id ctxvar, fvars)
      end

  | Ext.LF.Dot (_, s, Ext.LF.Head h) ->
      let (s', fvars')  = index_sub cvars bvars fvars s  in
      let (h', fvars'') = index_head cvars bvars fvars' h in
        (Apx.LF.Dot (Apx.LF.Head h', s') , fvars'')

  | Ext.LF.Dot (_, s, Ext.LF.Normal m) ->
      let (s', fvars')  = index_sub cvars bvars fvars s  in
      let (m', fvars'') = index_term cvars bvars fvars' m in
        (Apx.LF.Dot (Apx.LF.Obj  m', s') , fvars'')

  | Ext.LF.EmptySub _ ->
      (Apx.LF.EmptySub, fvars)

        

let index_decl cvars bvars fvars (Ext.LF.TypDecl(x, a)) =
  let (a', fvars') = index_typ cvars bvars fvars a in
  let (ctxOpt, bvars) = bvars in 
  let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDecl (x,a'), (ctxOpt, bvars'), fvars')

let rec index_dctx ctx_vars cvars ((_ctxOpt, _bvs) as bvars) fvars = function
  | Ext.LF.Null        -> (Apx.LF.Null , bvars, fvars)

  | Ext.LF.CtxVar (loc, psi_name)  ->
      begin try
        let offset = CVar.index_of_name ctx_vars psi_name in
          (Apx.LF.CtxVar (Apx.LF.CtxOffset offset) , bvars, fvars)
      with Not_found ->
        raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
        (* (Apx.LF.CtxVar (Apx.LF.CtxName psi_name) , bvars) *)
      end
  | Ext.LF.DDec (psi, decl) ->
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars bvars fvars psi in
      let (decl', bvars'', fvars'')  = index_decl cvars bvars' fvars' decl in
        (Apx.LF.DDec (psi', decl'), bvars'', fvars'')

(* Order of psihat? -bp
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
      |  x :: psihat ->
          begin try
            let ctx_var = CVar.index_of_name ctx_vars x in
            let (d, bvars) = index_hat bv psihat in
              ((Some (Int.LF.CtxOffset ctx_var), d) , bvars)
          with Not_found ->
            let (d, bvars ) = index_hat bv explicit_psihat in
              ((None, d) , bvars)
          end
    end


let rec index_ctx cvars ( (_ , _ ) as bvars) fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty , bvars, fvars)

  | Ext.LF.Dec (psi, dec) ->
      let (psi', bvars', fvars')   = index_ctx  cvars bvars fvars psi in
      let (dec', bvars'', fvars'') = index_decl cvars bvars' fvars' dec in
        (Apx.LF.Dec (psi', dec'), bvars'', fvars'')

let index_cdecl ctx_vars cvars fvars = function
  | Ext.LF.MDecl (loc, u, a, psi) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fvars psi in
      let (a', fvars'')          = index_typ  cvars bvars' fvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry u) in
        (Apx.LF.MDecl (u, a', psi'), ctx_vars, cvars', fvars'')

  | Ext.LF.PDecl (loc, p, a, psi) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 

      let (psi', bvars', fvars') = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fvars psi in
      let (a', fvars')           = index_typ  cvars bvars' fvars' a in
      let cvars'         = CVar.extend cvars (CVar.mk_entry p) in
        (Apx.LF.PDecl (p, a', psi') , ctx_vars, cvars', fvars')

  | Ext.LF.SDecl (loc, s, phi, psi) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 

      let (psi', _bvars', fvars') = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fvars psi in
      let ctxOpt' = begin match get_ctxvar phi with
                   | None -> None 
                   | Some phi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars phi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName phi_name))
                     end
                   end in 


      let (phi', _bvars', fvars'') = index_dctx ctx_vars cvars (ctxOpt', BVar.create ()) fvars' phi in
      let _ = dprint (fun () -> "Extend cvars with " ^ R.render_name s) in 
      let cvars'         = CVar.extend cvars (CVar.mk_entry s) in
        (Apx.LF.SDecl (s, phi', psi') , ctx_vars, cvars', fvars'')

  | Ext.LF.CDecl (loc , ctx_name, schema_name) -> 
    begin try 
      let ctx_vars'        = CVar.extend ctx_vars (CVar.mk_entry ctx_name) in
      let schema_cid       = Schema.index_of_name schema_name in
        (Apx.LF.CDecl (ctx_name, schema_cid), ctx_vars', cvars, fvars)
    with 
        Not_found -> raise (Error.Error (Some loc, Error.UnboundCtxSchemaName schema_name))
    end


let rec index_mctx ctx_vars cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty, Apx.LF.Empty , ctx_vars, cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (omega', delta', ctx_vars', cvars', fvars') = index_mctx ctx_vars cvars fvars delta in
      let (cdec', ctx_vars', cvars'', fvars'') = index_cdecl ctx_vars' cvars' fvars' cdec in
        begin match cdec' with 
          | Apx.LF.CDecl _ -> (Apx.LF.Dec(omega', cdec'), delta', ctx_vars', cvars'', fvars'')
          | _       -> (omega', Apx.LF.Dec (delta', cdec'), ctx_vars', cvars'', fvars'')
        end 



(* Records are not handled in a general manner
 * We need to change the datatype for typ_rec to be typ_decl ctx
 *)
let rec index_typrec cvars bvars fvars = function
  | Ext.LF.SigmaLast last_a ->
      let (last, fvars') = index_typ cvars bvars fvars last_a in 
      (Apx.LF.SigmaLast last, fvars')

  | Ext.LF.SigmaElem (x, a, arec) ->
      let (a', fvars') = index_typ cvars bvars fvars a in
      let (ctxOpt, bvars) = bvars in 
      let  bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let (arec', fvars'') = index_typrec cvars (ctxOpt, bvars') fvars' arec in 
        (Apx.LF.SigmaElem (x, a', arec'), fvars'')


(* Translation of external schemas into approximate schemas *)
let rec index_elements el_list = List.map index_el el_list

and index_el (Ext.LF.SchElem (_, typ_ctx, typ_rec)) =
  let cvars = (CVar.create ()) in
  let bvars = (None, BVar.create ()) in
  let fvars = [] in 
  let (typ_ctx', bvars', _ ) = index_ctx cvars bvars fvars typ_ctx in
  let _ = dprint (fun () ->  ("\n[index_el] ext block has length " ^ string_of_int (length_typ_rec typ_rec) ^ "\n")) in 
  let (typ_rec', _ )         = index_typrec cvars bvars' fvars typ_rec in
    Apx.LF.SchElem (typ_ctx', typ_rec')


let index_schema (Ext.LF.Schema el_list) =
  Apx.LF.Schema (index_elements el_list)


(* Translation of external computations into approximate computations *)

let rec index_meta_obj ctx_vars cvars fvars = function 
  | Ext.Comp.MetaCtx (l, cpsi) -> 
      let ctxOpt = begin match get_ctxvar cpsi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some l, Error.UnboundCtxName psi_name))
                     end
                   end in 
      let (cPsi, _bvars, fvars') = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fvars cpsi in 
        (Apx.Comp.MetaCtx (Some l, cPsi), fvars')

  | Ext.Comp.MetaObj (l, phat, m) -> 
      let (psihat' , bvars) = index_psihat ctx_vars phat in 
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  

      let (m', fvars') = index_term cvars (ctxOpt, bvars) fvars m in  
        (Apx.Comp.MetaObj (Some l, psihat', m'), fvars)

  | Ext.Comp.MetaObjAnn (l, cpsi, m) -> 
      let ctxOpt = begin match get_ctxvar cpsi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some l, Error.UnboundCtxName psi_name))
                     end
                   end in 
      let (cPsi, bvars, fvars') = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fvars cpsi in 
      let (m', fvars'') = index_term cvars  bvars fvars' m in  
        (Apx.Comp.MetaObjAnn (Some l, cPsi, m'), fvars'')

and index_meta_spine ctx_vars cvars fvars = function
  | Ext.Comp.MetaNil -> 
      (Apx.Comp.MetaNil , fvars)

  | Ext.Comp.MetaApp (m, s) ->
      let (m', fvars')  = index_meta_obj  ctx_vars cvars fvars m in
      let (s', fvars'') = index_meta_spine ctx_vars cvars fvars' s in
        (Apx.Comp.MetaApp (m', s') , fvars'')


let rec index_compkind ctx_vars cvars fmvars = function 
  | Ext.Comp.Ctype loc -> Apx.Comp.Ctype loc
(*  | Ext.Comp.ArrKind (loc, mT, cK) ->  *)
    
  | Ext.Comp.PiKind (loc, (cdecl , dep), cK) -> 
      let (cdecl', ctx_vars', cvars', fmvars') = index_cdecl ctx_vars cvars fmvars cdecl in 
      let dep' = match dep with Ext.Comp.Explicit -> Apx.Comp.Explicit | Ext.Comp.Implicit -> Apx.Comp.Implicit in 
      let cK' = index_compkind ctx_vars' cvars' fmvars' cK in 
        Apx.Comp.PiKind (loc, (cdecl', dep'), cK')

let rec index_comptyp ctx_vars cvars  fmvars = 
  function
  | Ext.Comp.TypBase (loc, a, ms) -> 
      begin try
        let a' = CompTyp.index_of_name a in 
        let (ms', _fv) = index_meta_spine ctx_vars cvars fmvars ms in 
          Apx.Comp.TypBase (loc, a', ms')
      with Not_found -> 
        raise (Error.Error (loc, Error.UnboundName a))
      end 
  | Ext.Comp.TypBox (loc, a, psi)    ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 
      begin try 
        let Ext.LF.Atom (_ , name, Ext.LF.Nil) = a in 
        let offset = CVar.index_of_name ctx_vars name in           
        let (psi', _ , _ ) = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fmvars
          psi in
        let _ = dprint (fun () -> "Indexing TypSub -- turning TypBox into TypSub") in
          Apx.Comp.TypSub (loc, Apx.LF.CtxVar (Apx.LF.CtxOffset offset), psi')
      with _  -> 
        let (psi', bvars', _ ) = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fmvars psi in
        let (a', _ )           = index_typ cvars bvars' fmvars a   in
          Apx.Comp.TypBox (loc, a', psi')
      end 

  | Ext.Comp.TypSub (loc, phi, psi)    ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in  
      let (psi', _ , _ ) = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fmvars psi in
      let (phi', _ , _ ) = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fmvars phi in
        Apx.Comp.TypSub (loc, phi', psi')


  | Ext.Comp.TypArr (_loc, tau, tau') ->
      Apx.Comp.TypArr (index_comptyp ctx_vars cvars fmvars tau, 
                       index_comptyp ctx_vars cvars fmvars tau')

  | Ext.Comp.TypCross (_loc, tau, tau') ->
      Apx.Comp.TypCross (index_comptyp ctx_vars cvars fmvars tau, 
                         index_comptyp ctx_vars cvars fmvars tau')

  | Ext.Comp.TypPiBox (_loc, cdecl, tau)    ->
      let (cdecl', ctx_vars', cvars', _) = index_cdecl ctx_vars cvars fmvars cdecl in
        Apx.Comp.TypPiBox (cdecl', index_comptyp ctx_vars' cvars' fmvars tau)

  | Ext.Comp.TypCtxPi (loc, (ctx_name, schema_name, dep), tau)    ->
    begin try 
      let ctx_vars'        = CVar.extend ctx_vars (CVar.mk_entry ctx_name) in
      let schema_cid       = Schema.index_of_name schema_name in
        (* if exception Not_found is raised, it means schema_name does not exist *)
      let apxdep = match dep with Ext.Comp.Explicit -> Apx.Comp.Explicit | Ext.Comp.Implicit -> Apx.Comp.Implicit in 
        Apx.Comp.TypCtxPi ((ctx_name, schema_cid, apxdep), index_comptyp ctx_vars' cvars fmvars tau)
    with 
        Not_found -> raise (Error.Error (Some loc, Error.UnboundCtxSchemaName schema_name))
    end

  | Ext.Comp.TypBool -> Apx.Comp.TypBool

let rec index_exp ctx_vars cvars vars ((fmvars, fvars) as fvs) = function
  | Ext.Comp.Syn (loc , i)   ->
      Apx.Comp.Syn (loc, index_exp' ctx_vars cvars vars fvs i)

  | Ext.Comp.Fun (loc, x, e) ->
      let vars' = Var.extend vars (Var.mk_entry x) in
        Apx.Comp.Fun (loc, x, index_exp ctx_vars cvars vars' fvs e)

  | Ext.Comp.CtxFun (loc, psi_name, e) ->
      let ctx_vars' = CVar.extend ctx_vars (CVar.mk_entry psi_name) in
        Apx.Comp.CtxFun (loc, psi_name, index_exp ctx_vars' cvars vars fvs e)

  | Ext.Comp.MLam (loc, u, e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry u) in
        Apx.Comp.MLam (loc, u, index_exp ctx_vars cvars' vars fvs e)

  | Ext.Comp.Pair (loc, e1, e2) ->
      let e1 = index_exp ctx_vars cvars vars fvs e1 in
      let e2 = index_exp ctx_vars cvars vars fvs e2 in
        Apx.Comp.Pair (loc, e1, e2)

  | Ext.Comp.LetPair (loc, i, (x, y, e)) ->
      let i' = index_exp' ctx_vars cvars vars fvs i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let vars2 = Var.extend vars1 (Var.mk_entry y) in
      let e' = index_exp ctx_vars cvars vars2 fvs e in
        Apx.Comp.LetPair(loc, i', (x,y,e'))

  | Ext.Comp.Let (loc, i, (x, e)) ->
      let i' = index_exp' ctx_vars cvars vars fvs i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let e' = index_exp ctx_vars cvars vars1 fvs e in
        Apx.Comp.Let (loc, i', (x,e'))

  (* SVars are parsed as terms but are actually substitutions *)
  | Ext.Comp.Box (loc1, psihat, Ext.LF.Root(loc2, Ext.LF.SVar(loc3,s, sigma), spine)) -> 
      let (psihat' , bvars) = index_psihat ctx_vars psihat in 
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  
 
      let rec create_sub s spine = match spine with
        | Ext.LF.Nil -> s
        | Ext.LF.App (loc, m', spine') -> 
            let (m', _ ) = index_term cvars (ctxOpt, bvars) [] m' in 
             create_sub (Apx.LF.Dot (Apx.LF.Obj m', s)) spine' 
      in 
      let (sigma', _ ) =  index_sub cvars (ctxOpt, bvars) [] sigma in 
        begin try
          let offset = CVar.index_of_name cvars s in
            Apx.Comp.SBox (loc1, psihat', 
                           create_sub (Apx.LF.SVar (Apx.LF.Offset offset, sigma')) spine )
        with Not_found -> 
          raise (Error.Error (Some loc3, Error.UnboundName s))
        end 


  | Ext.Comp.Box (loc, psihat, m) ->
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  

      let (m', _ ) = index_term cvars (ctxOpt, bvars) [] (* fvs *) m in  
        Apx.Comp.Box (loc, psihat', m')


  | Ext.Comp.SBox (loc, psihat,s) -> 
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  

      let (s', _ ) = index_sub cvars (ctxOpt, bvars) [] s in 
        Apx.Comp.SBox (loc, psihat', s')

  | Ext.Comp.Case (loc, prag, i, branches) ->
      let i' = index_exp' ctx_vars cvars vars fvs i in
      let branches' = List.map (function b -> index_branch ctx_vars cvars vars fvs b) branches in
        Apx.Comp.Case (loc, prag, i', branches')


  | Ext.Comp.If (loc, i, e1, e2) -> 
      let i' = index_exp' ctx_vars cvars vars fvs i in
      let e1' = index_exp ctx_vars cvars vars fvs e1 in
      let e2' = index_exp ctx_vars cvars vars fvs e2 in
        Apx.Comp.If(loc, i', e1', e2')

and index_exp' ctx_vars cvars vars ((fmvars, fvars) as fvs) = function
  | Ext.Comp.Var (loc, x) ->
      begin try
        Apx.Comp.Var (Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (Comp.index_of_name x)
      with Not_found ->
        raise (Error.Error (Some loc, Error.UnboundCompName x))
      end

  | Ext.Comp.Apply (loc, i, e) ->
      let i' = index_exp' ctx_vars cvars vars fvs i in
      let e' = index_exp  ctx_vars cvars vars fvs e in
        Apx.Comp.Apply (loc, i', e')

  | Ext.Comp.CtxApp (loc, i, psi) ->
      let i'   = index_exp' ctx_vars cvars vars fvs i in
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in   
      let (psi', _ , _ ) = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fmvars psi in
        Apx.Comp.CtxApp (loc, i', psi')

  | Ext.Comp.MApp (loc, i, (psihat, m)) ->
      let i'      = index_exp' ctx_vars cvars vars fvs i in
      let (psihat', bvars) = index_psihat ctx_vars psihat in
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  
      let (m', _ ) = index_term cvars (ctxOpt, bvars) fmvars m in
        Apx.Comp.MApp (loc, i', Apx.Comp.MetaObj (Some loc, psihat', m'))

  | Ext.Comp.MAnnApp (loc, i, (psi, m)) ->
      let i'      = index_exp' ctx_vars cvars vars fvs i in
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in   
      let (psi', bvars, _ ) = index_dctx ctx_vars cvars  (ctxOpt, BVar.create ()) [] (* fmvars *) psi in
      let (m', _ ) = index_term cvars bvars fmvars m in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Ext.Comp.BoxVal (loc, psi, m) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in   
      let (psi', bvars, _ ) = index_dctx ctx_vars cvars  (ctxOpt, BVar.create ()) [] (* fmvars *) psi in
      let (m', _ ) = index_term cvars bvars fmvars m in 
        Apx.Comp.BoxVal (loc, psi', m') 

  | Ext.Comp.Ann (_loc, e, tau) ->
      Apx.Comp.Ann (index_exp  ctx_vars cvars vars fvs e,
                         index_comptyp ctx_vars cvars fmvars tau)

  | Ext.Comp.Equal (loc, i, i') ->
      let i1 = index_exp' ctx_vars cvars vars fvs i in 
      let i2 = index_exp' ctx_vars cvars vars fvs i' in 
        Apx.Comp.Equal (loc, i1, i2)

  | Ext.Comp.Boolean (loc , b) -> Apx.Comp.Boolean (loc, b)

(* and index_pattern ctx_vars mvars ((fmvars, fvars) as fvs) pat = match pat with
  | Ext.Comp.PatEmtpy (_ , cPsi) -> 
      let ctxOpt = begin match get_ctxvar cPsi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
      end in 
      let (psi', bvars', fvars') = index_dctx ctx_vars cvars (ctxOpt, BVar.create ()) fvars psi in
      let 
(Apx.Comp.PatEmpty, fvs)
  | Ext.Comp.PatTrue loc ->  (Apx.Comp.PatTrue loc, fvs)
  | Ext.Comp.PatFalse loc -> (Apx.Comp.PatFalse loc, fvs)
  | Ext.Comp.Pair (loc, pat1, pat2) -> 
      let (pat1', fvs1) = index_pattern ctx_vars mvars vars fvs in 
      let (pat2', fvs2) = index_pattern ctx_vars mvars vars fvs1 in 
        (Apx.Comp.PatPair (loc, pat1', pat2') , fvs2)
  | Ext.Comp.PatVar (loc, x) -> (Apx.Comp.PatVar (loc, x), (fmvars, x::fvars))
*)
and index_mobj ctxvars mvars fmvars (ctxOpt, mO) = match mO with 
  | Ext.Comp.MetaCtx (loc, cPsi) -> 
    let (cPsi', _bvars, fmvars')  = index_dctx ctxvars mvars (ctxOpt, BVar.create ()) fmvars cPsi in
      (Apx.Comp.MetaCtx (Some loc, cPsi') , fmvars')
      
  | Ext.Comp.MetaObj (loc, phat, tM) ->  raise (Error.Error (Some loc, Error.PatCtxRequired))
  | Ext.Comp.MetaObjAnn (loc, cPsi, tM) -> 
    let (cPsi', bvars, fmvars1)  = index_dctx ctxvars mvars (ctxOpt, BVar.create ()) fmvars cPsi in
    let (tM', fmvars2)           = index_term mvars bvars fmvars1 tM in 
      (Apx.Comp.MetaObjAnn (Some loc, cPsi', tM') , fmvars2)


and index_branch ctx_vars mvars vars (fmvars, fvars) branch = match branch with
(*  | Ext.Comp.EmptyBranch (loc, delta, pat) -> 
    let empty_fmvars = [] in 
(*      if containsEmptyPat pat then  *)
    let (omega, delta', ctx_vars', mvars', fmvars1)  =  
      index_mctx ctx_vars' (CVar.create()) empty_fmvars delta in 
    let (pat', fmvars, fmvars) = index_pattern ctx_vars' mvars' (fmvars1 ,
                                                                empty_fmvars) pat
    in 
*)
  | Ext.Comp.Branch (loc, _cD, Ext.Comp.PatEmpty _ , _e) -> 
      raise (Error.Error (Some loc, Error.CompEmptyPattBranch))
  | Ext.Comp.Branch (loc, cD, Ext.Comp.PatMetaObj (loc', mO), e) -> 
    let empty_fmvars = [] in 
    let _ = dprint (fun () -> "index_branch") in 
    let (ctx_vars', ctxOpt1) = begin match get_ctxvar_mobj mO with 
                     | None -> (CVar.create ()  , None)
                     | Some psi_name -> 
                         let ctx_vars = CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) in 
                           (ctx_vars, Some (Apx.LF.CtxOffset 1))
                    end in
    
    let (omega, cD', ctx_vars', mvars', fmvars1)  = 
      index_mctx ctx_vars' ctx_vars' empty_fmvars cD in
    let (mO', fmvars2) = index_mobj ctx_vars' mvars' fmvars1 (ctxOpt1, mO) in 
    let cvars_all        = CVar.append mvars' mvars in
    let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
    let fmvars3 = List.append fmvars2 fmvars in 
    let e'               = index_exp ctxvars_all cvars_all vars (fmvars3, fvars) e in
      Apx.Comp.Branch (loc, omega, cD', Apx.Comp.PatMetaObj (loc', mO'), e')

(*  | Ext.Comp.BranchBox (loc, cD, pat, e) -> 
    (* Context Declarations are part of cD *)
    (* bp: collecting fmvars used for scope checking *)
    let empty_fmvars = [] in 
    let (omega, delta', ctx_vars', mvars', fmvars1)  =   
      index_mctx ctx_vars' (CVar.create()) empty_fmvars delta in 
    let (pat', fmvars, fvars) = 
      (* patterns should be linear in fvars; they may be non-linear in fmvars *)
      index_pattern ctx_vars' mvars' fmvars1 pat in 
    let mvars_all        = CVar.append mvars' mvars in
    let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
    let e' = index_exp ctx_vars_all mvars_all vars (fmvars, fvars) in 
      Apx.Comp.BranchBox (loc, delta', pat', e')
*)

  (* The subsequent two cases are only relevant for the old syntax;
     they are redundant in the new syntax *)
  | Ext.Comp.BranchBox(loc, delta, (psi1, pattern, Some (a, psi))) ->
    let empty_fmvars = [] in 
    let _ = dprint (fun () -> "index_branch") in 
    (* this trick of getting the context variable occurring in a pattern
       doesn't work anymore in the presence of substitution patterns and 
       substitution variables; substitution variables may have type h[h']
       where h' may occur in psi1 but h doesn't occur anywhere... *)
    let ctx_vars' = begin match get_ctxvar psi1 with 
                     | None -> CVar.create () 
                     | Some psi_name -> CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) 
                    end in
    
    let (omega, delta', ctx_vars', cvars', fmvars1)  = 
      index_mctx ctx_vars' ctx_vars' empty_fmvars delta in
    (* let ctxOpt1 = Some (Apx.LF.CtxOffset 1) in  *)
    let ctxOpt1 =  begin match get_ctxvar psi1 with
                   | None -> None 
                   | Some psi_name -> begin try
                       let offset = CVar.index_of_name ctx_vars' psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end  
                   end in 
    let (psi1', bvars, fmvars2)   = index_dctx ctx_vars' cvars' (ctxOpt1, BVar.create ()) fmvars1 psi1 in 
    let (m'opt, fmvars3)       = match pattern with
                                     | Ext.Comp.EmptyPattern -> (None, fmvars2)
                                     | Ext.Comp.NormalPattern (m, e) ->
                                         let (m', fmvars3) = index_term cvars' bvars fmvars2 m in
                                           (Some m', fmvars3)
    in
      (* bp: computing ctxOpt seems redundant; reuse ctxOpt1 *)
(*    let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars' psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in   
    let (psi', _bvars, fmvars4)   = index_dctx ctx_vars' cvars' (ctxOpt, BVar.create ()) fmvars3 psi in *)
    let (psi', _bvars, fmvars4)   = index_dctx ctx_vars' cvars' (ctxOpt1, BVar.create ()) fmvars3 psi in
    (* _bvars = bvars *)
    let (a', fmvars5)             = index_typ cvars' bvars fmvars4 a in 

    let mvars_all        = CVar.append cvars' mvars in
    let ctxvars_all      = CVar.append ctx_vars' ctx_vars in

    let fmvars6 = List.append fmvars5 fmvars in

    let pattern' =
      match (pattern, m'opt) with
        | (Ext.Comp.EmptyPattern, None) -> Apx.Comp.EmptyPattern
        | (Ext.Comp.NormalPattern (_, e), Some m') -> Apx.Comp.NormalPattern (m', index_exp ctxvars_all mvars_all vars (fmvars6, fvars) e)
    in
      Apx.Comp.BranchBox (loc, omega, delta', (psi1', pattern', Some (a', psi')))

  | Ext.Comp.BranchBox (loc, delta, (psi, pattern, None)) ->
    let empty_fmvars = [] in 
    let ctx_vars' = begin match get_ctxvar psi with 
                     | None -> CVar.create () 
                     | Some psi_name -> CVar.extend (CVar.create ()) (CVar.mk_entry psi_name) 
                    end in

    let (omega, delta', ctx_vars', cvars', fmvars1)  = 
      index_mctx ctx_vars' (CVar.create()) empty_fmvars delta in
    let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name ctx_vars' psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in    

    let (psi1', bvars, fmvars2)    = index_dctx ctx_vars' cvars' (ctxOpt, BVar.create ()) fmvars1 psi in

      begin match pattern with 
        | Ext.Comp.EmptyPattern ->
            Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.EmptyPattern, None))
            
        | Ext.Comp.NormalPattern (Ext.LF.Root(_, Ext.LF.SVar (loc, s, sigma), Ext.LF.Nil),  e) -> 
            let (s_var, fmvars3) = begin try
                          let offset = CVar.index_of_name cvars' s in
                          let (sigma' , fmvars') = index_sub cvars' bvars fmvars2 sigma in
                            (Apx.LF.SVar (Apx.LF.Offset offset, sigma') , fmvars')
                        with Not_found ->
                          let _ = dprint (fun () -> "SVar Not_found " ^ R.render_name s) in
                          let (sigma', fmvars')     = index_sub mvars bvars fmvars sigma in
                          let _ = dprint (fun () -> "Created FSVar " ^ R.render_name s) in
                            (Apx.LF.FSVar (s, sigma') , FSV s :: fmvars' )
                        end in 

            let cvars_all        = CVar.append cvars' mvars in
            let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
            let e'               = index_exp ctxvars_all cvars_all vars (fmvars3, fvars) e in
              Apx.Comp.BranchSBox (loc, omega, delta', (psi1', s_var, None), e')



        | Ext.Comp.NormalPattern (m, e)  -> 
            let (m', fmvars3)     = index_term cvars' bvars fmvars2 m in
            let cvars_all        = CVar.append cvars' mvars in
            let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
            let fmvars4 = List.append fmvars3 fmvars in 
            let e'               = index_exp ctxvars_all cvars_all vars (fmvars4, fvars) e in
              Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.NormalPattern (m', e'), None))
                
      end

let kind     = index_kind (CVar.create ()) (None, BVar.create ()) []
let typ      = index_typ  (CVar.create ()) (None, BVar.create ()) []
let schema   = index_schema
let compkind = index_compkind (CVar.create ()) (CVar.create ()) []
let comptyp  = index_comptyp   (CVar.create ()) (CVar.create ()) []
let exp      = fun vars -> fun e -> index_exp (CVar.create ()) (CVar.create ()) vars ([],[]) e
let exp'     = fun vars -> fun i -> index_exp' (CVar.create ()) (CVar.create ()) vars ([],[]) i
