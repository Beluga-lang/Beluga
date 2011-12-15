
(* -------------------------------------------------------------*)
(*  Indexing
 *
 * index_term names ext_m = (m, fvars)
 *
 * Translates an object ext_m in external syntax
 * into an object m in approximate internal syntax.
 *
 * ASSUMPTION:
 *
 *    ext_m is in beta normal form
 *
 *)

open Id
open Store
open Store.Cid
open Syntax


module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer
module RR = Pretty.Int.NamedRenderer


let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

let closed = true

type free_cvars = 
    FMV of Id.name | FPV of Id.name | FSV of Id.name | FCV of Id.name 


type fcvars = free_cvars list * bool 

let rec lookup_fv fvars m = begin  match (fvars, m) with 
     ([], _ ) -> false
  | (FMV n :: fvars' , FMV m) -> 
      if n = m then true
      else lookup_fv fvars' (FMV m) 
  | (FPV p :: fvars' , FPV q) -> 
      if p = q then true
      else lookup_fv fvars' m 
  | (FCV n :: fvars' , FCV m) -> 
      if n = m then true
      else lookup_fv fvars' (FCV m) 

  | (FPV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FCV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m
  | (FCV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FCV _ ) -> lookup_fv fvars' m
  | (FPV _ :: fvars' , FCV _ ) -> lookup_fv fvars' m

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

and index_head cvars bvars ((fvars, closed_flag) as fvs) = function
  | Ext.LF.Name (_, n) ->
      (* let _        = dprint (fun () -> "Indexing name " ^ n.string_of_name)
         in *)
      let (_, bvars) = bvars in 
      begin try
        (Apx.LF.BVar (BVar.index_of_name bvars n) , fvs)
      with Not_found -> try
        (Apx.LF.Const (Term.index_of_name n) , fvs)
      with Not_found -> 
        dprint (fun () -> "FVar " ^ n.string_of_name );
        (Apx.LF.FVar n , fvs)         
      end

  | Ext.LF.ProjName (loc, k, n) ->
      let (bvar, fvs') = index_head cvars bvars fvs (Ext.LF.Name (loc, n)) in
        (Apx.LF.Proj(bvar, k), fvs')

  | Ext.LF.PVar (loc, p, s) ->
      begin try
        let offset = CVar.index_of_name cvars p in
        let (s' , fvs') = index_sub cvars bvars fvs s in
          (Apx.LF.PVar (Apx.LF.Offset offset, s') , fvs')
      with Not_found ->
	if closed_flag then 
	  raise (Error.Error (Some loc, Error.UnboundName p))
	else 
          let _ = dprint (fun () -> "PVar Not_found " ^ R.render_name p) in
          let (s', (fvars', closed_flag))  = index_sub cvars bvars fvs s in
            (Apx.LF.FPVar (p, s') , (FPV p :: fvars' , closed_flag))	
      end

  | Ext.LF.ProjPVar (loc, k, (p, s)) ->
      let (pvar, fvs') = index_head cvars bvars fvs (Ext.LF.PVar (loc, p, s)) in
        (Apx.LF.Proj (pvar, k), fvs')

        
  | Ext.LF.Hole _loc -> 
      (Apx.LF.Hole , fvs)

  | Ext.LF.MVar (loc, u, s) ->
      if lookup_fv fvars (FMV u) then 
        let (s', fvs')     = index_sub cvars bvars fvs s in
          (Apx.LF.FMVar (u, s') , fvs')
      else 
        begin try
          let offset = CVar.index_of_name cvars u in
          let (s', fvs')     = index_sub cvars bvars fvs s in
            (Apx.LF.MVar (Apx.LF.Offset offset, s') , fvs')
        with Not_found ->
	if closed_flag then 
	  raise (Error.Error (Some loc, Error.UnboundName u))
	else 
          let (s', (fvars', closed_flag))     = index_sub cvars bvars fvs s in
            (Apx.LF.FMVar (u, s') , (FMV u :: fvars' , closed_flag))
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

let rec index_dctx cvars ((_ctxOpt, _bvs) as bvars) fvars = function
  | Ext.LF.Null        -> (Apx.LF.Null , bvars, fvars)

  | Ext.LF.CtxVar (loc, psi_name)  ->
      begin try
        let offset = CVar.index_of_name cvars psi_name in
          (Apx.LF.CtxVar (Apx.LF.CtxOffset offset) , bvars, fvars)
      with Not_found ->
        raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
      end
  | Ext.LF.DDec (psi, decl) ->
      let (psi', bvars', fvars')    = index_dctx cvars bvars fvars psi in
      let (decl', bvars'', fvars'') = index_decl cvars bvars' fvars' decl in
        (Apx.LF.DDec (psi', decl'), bvars'', fvars'')

(* Order of psihat? -bp
   It's not clear how to know that the last name is a bound variable
   or if it is a name of a context variable...
*)
let index_psihat cvars extphat =
  let bv = BVar.create () in

  let rec index_hat bvars = function
    | [] -> (0, bvars)
    | x :: psihat ->
        let bvars' = BVar.extend bvars (BVar.mk_entry x) in
        let (l, bvars'') = index_hat bvars' psihat in
          (l + 1, bvars'')

  in
    begin match extphat with
      | [] -> ((None, 0), bv)
      |  x :: psihat ->
          begin try
            let ctx_var = CVar.index_of_name cvars x in
            let (d, bvars) = index_hat bv psihat in
              ((Some (Int.LF.CtxOffset ctx_var), d) , bvars)
          with Not_found ->
            let (d, bvars ) = index_hat bv extphat in
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

let index_cdecl cvars fvars = function
  | Ext.LF.MDecl (loc, u, a, psi) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 
      let (psi', bvars', fvars') = index_dctx cvars (ctxOpt, BVar.create ()) fvars psi in
      let (a', fvars'')          = index_typ  cvars bvars' fvars' a in
      let cvars'                 = CVar.extend cvars (CVar.mk_entry u) in
        (Apx.LF.MDecl (u, a', psi'), cvars', fvars'')

  | Ext.LF.PDecl (loc, p, a, psi) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 

      let (psi', bvars', fvars') = index_dctx cvars (ctxOpt, BVar.create ()) fvars psi in
      let (a', fvars')           = index_typ  cvars bvars' fvars' a in
      let cvars'                 = CVar.extend cvars (CVar.mk_entry p) in
        (Apx.LF.PDecl (p, a', psi') , cvars', fvars')

  | Ext.LF.SDecl (loc, s, phi, psi) ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 

      let (psi', _bvars', fvars') = index_dctx cvars (ctxOpt, BVar.create ()) fvars psi in
      let ctxOpt' = begin match get_ctxvar phi with
                   | None -> None 
                   | Some phi_name ->  begin try
                       let offset = CVar.index_of_name cvars phi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName phi_name))
                     end
                   end in 


      let (phi', _bvars', fvars'') = index_dctx cvars (ctxOpt', BVar.create ()) fvars' phi in
      let _              = dprint (fun () -> "Extend cvars with " ^ R.render_name s) in 
      let cvars'         = CVar.extend cvars (CVar.mk_entry s) in
        (Apx.LF.SDecl (s, phi', psi') , cvars', fvars'')

  | Ext.LF.CDecl (loc , ctx_name, schema_name) -> 
    begin try 
      let cvars'        = CVar.extend cvars (CVar.mk_entry ctx_name) in
      let schema_cid    = Schema.index_of_name schema_name in
        (Apx.LF.CDecl (ctx_name, schema_cid), cvars', fvars)
    with 
        Not_found -> raise (Error.Error (Some loc, Error.UnboundCtxSchemaName schema_name))
    end


let rec index_mctx cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty, Apx.LF.Empty, cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (omega', delta', cvars', fvars') = index_mctx cvars fvars delta in 
      let (cdec', cvars'', fvars'') = index_cdecl cvars' fvars' cdec in
        begin match cdec' with 
          | Apx.LF.CDecl _ -> (Apx.LF.Dec(omega', cdec'), delta', cvars'', fvars'')
          | _       -> (omega', Apx.LF.Dec (delta', cdec'), cvars'', fvars'')
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
  let (typ_ctx', bvars', _ ) = index_ctx cvars bvars (fvars,not closed) typ_ctx in
  let _ = dprint (fun () ->  ("\n[index_el] ext block has length " ^ string_of_int (length_typ_rec typ_rec) ^ "\n")) in 
  let (typ_rec', _ )         = index_typrec cvars bvars' (fvars, not closed) typ_rec in
    Apx.LF.SchElem (typ_ctx', typ_rec')


let index_schema (Ext.LF.Schema el_list) =
  Apx.LF.Schema (index_elements el_list)


(* Translation of external computations into approximate computations *)

let rec index_meta_obj cvars fvars = function 
  | Ext.Comp.MetaCtx (l, cpsi) -> 
      let ctxOpt = begin match get_ctxvar cpsi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some l, Error.UnboundCtxName psi_name))
                     end
                   end in 
      let (cPsi, _bvars, fvars') = index_dctx cvars (ctxOpt, BVar.create ()) fvars cpsi in 
        (Apx.Comp.MetaCtx (Some l, cPsi), fvars')

  | Ext.Comp.MetaObj (l, phat, m) -> 
      let (psihat' , bvars) = index_psihat cvars phat in 
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
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some l, Error.UnboundCtxName psi_name))
                     end
                   end in 
      let (cPsi, bvars, fvars') = index_dctx cvars (ctxOpt, BVar.create ()) fvars cpsi in 
      let (m', fvars'') = index_term cvars  bvars fvars' m in  
        (Apx.Comp.MetaObjAnn (Some l, cPsi, m'), fvars'')

and index_meta_spine cvars fvars = function
  | Ext.Comp.MetaNil -> 
      (Apx.Comp.MetaNil , fvars)

  | Ext.Comp.MetaApp (m, s) ->
      let (m', fvars')  = index_meta_obj  cvars fvars m in
      let (s', fvars'') = index_meta_spine cvars fvars' s in
        (Apx.Comp.MetaApp (m', s') , fvars'')


let rec index_compkind cvars fcvars = function 
  | Ext.Comp.Ctype loc -> Apx.Comp.Ctype loc
    
  | Ext.Comp.PiKind (loc, (cdecl , dep), cK) -> 
      let (cdecl', cvars', fcvars') = index_cdecl cvars fcvars cdecl in 
      let dep' = match dep with Ext.Comp.Explicit -> Apx.Comp.Explicit | Ext.Comp.Implicit -> Apx.Comp.Implicit in 
      let cK' = index_compkind cvars' fcvars' cK in 
        Apx.Comp.PiKind (loc, (cdecl', dep'), cK')

let rec index_comptyp cvars  fcvars = 
  function
  | Ext.Comp.TypBase (loc, a, ms) -> 
      begin try
        let a' = CompTyp.index_of_name a in 
        let (ms', _fv) = index_meta_spine cvars fcvars ms in 
          Apx.Comp.TypBase (loc, a', ms')
      with Not_found -> 
        raise (Error.Error (loc, Error.UnboundName a))
      end 
  | Ext.Comp.TypBox (loc, a, psi)    ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in 
      begin try 
        let Ext.LF.Atom (_ , name, Ext.LF.Nil) = a in 
        let offset = CVar.index_of_name cvars name in           
        let (psi', _ , _ ) = index_dctx cvars (ctxOpt, BVar.create ()) fcvars
          psi in
        let _ = dprint (fun () -> "Indexing TypSub -- turning TypBox into TypSub") in
          Apx.Comp.TypSub (loc, Apx.LF.CtxVar (Apx.LF.CtxOffset offset), psi')
      with _  -> 
        let (psi', bvars', _ ) = index_dctx cvars (ctxOpt, BVar.create ()) fcvars psi in
        let (a', _ )           = index_typ cvars bvars' fcvars a   in
          Apx.Comp.TypBox (loc, a', psi')
      end 

  | Ext.Comp.TypSub (loc, phi, psi)    ->
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in  
      let (psi', _ , _ ) = index_dctx cvars (ctxOpt, BVar.create ()) fcvars psi in
      let (phi', _ , _ ) = index_dctx cvars (ctxOpt, BVar.create ()) fcvars phi in
        Apx.Comp.TypSub (loc, phi', psi')


  | Ext.Comp.TypArr (_loc, tau, tau') ->
      Apx.Comp.TypArr (index_comptyp cvars fcvars tau, 
                       index_comptyp cvars fcvars tau')

  | Ext.Comp.TypCross (_loc, tau, tau') ->
      Apx.Comp.TypCross (index_comptyp cvars fcvars tau, 
                         index_comptyp cvars fcvars tau')

  | Ext.Comp.TypPiBox (_loc, cdecl, tau)    ->
      let (cdecl', cvars', _) = index_cdecl cvars fcvars cdecl in
        Apx.Comp.TypPiBox (cdecl', index_comptyp cvars' fcvars tau)

  | Ext.Comp.TypCtxPi (loc, (ctx_name, schema_name, dep), tau)    ->
    begin try 
      let cvars'        = CVar.extend cvars (CVar.mk_entry ctx_name) in
      let schema_cid    = Schema.index_of_name schema_name in
        (* if exception Not_found is raised, it means schema_name does not exist *)
      let apxdep = match dep with Ext.Comp.Explicit -> Apx.Comp.Explicit | Ext.Comp.Implicit -> Apx.Comp.Implicit in 
        Apx.Comp.TypCtxPi ((ctx_name, schema_cid, apxdep), index_comptyp cvars' fcvars tau)
    with 
        Not_found -> raise (Error.Error (Some loc, Error.UnboundCtxSchemaName schema_name))
    end

  | Ext.Comp.TypBool -> Apx.Comp.TypBool

let rec index_exp cvars vars fcvars = function
  | Ext.Comp.Syn (loc , i)   ->
      Apx.Comp.Syn (loc, index_exp' cvars vars fcvars i)

  | Ext.Comp.Fun (loc, x, e) ->
      let vars' = Var.extend vars (Var.mk_entry x) in
        Apx.Comp.Fun (loc, x, index_exp cvars vars' fcvars e)

  | Ext.Comp.CtxFun (loc, psi_name, e) ->
        let cvars' = CVar.extend cvars (CVar.mk_entry psi_name) in 
        Apx.Comp.CtxFun (loc, psi_name, index_exp cvars' vars fcvars e) 

  | Ext.Comp.MLam (loc, u, e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry u) in
        Apx.Comp.MLam (loc, u, index_exp cvars' vars fcvars e)

  | Ext.Comp.Pair (loc, e1, e2) ->
      let e1 = index_exp cvars vars fcvars e1 in
      let e2 = index_exp cvars vars fcvars e2 in
        Apx.Comp.Pair (loc, e1, e2)

  | Ext.Comp.LetPair (loc, i, (x, y, e)) ->
      let i' = index_exp' cvars vars fcvars i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let vars2 = Var.extend vars1 (Var.mk_entry y) in
      let e' = index_exp cvars vars2 fcvars e in
        Apx.Comp.LetPair(loc, i', (x,y,e'))

  | Ext.Comp.Let (loc, i, (x, e)) ->
      let i' = index_exp' cvars vars fcvars i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let e' = index_exp cvars vars1 fcvars e in
        Apx.Comp.Let (loc, i', (x,e'))

  (* SVars are parsed as terms but are actually substitutions *)
  | Ext.Comp.Box (loc1, psihat, Ext.LF.Root(loc2, Ext.LF.SVar(loc3,s, sigma), spine)) -> 
      let (psihat' , bvars) = index_psihat cvars psihat in 
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  
 
      let rec create_sub s spine = match spine with
        | Ext.LF.Nil -> s
        | Ext.LF.App (loc, m', spine') -> 
            let (m', _ ) = index_term cvars (ctxOpt, bvars) fcvars  m' in 
             create_sub (Apx.LF.Dot (Apx.LF.Obj m', s)) spine' 
      in 
      let (sigma', _ ) =  index_sub cvars (ctxOpt, bvars) fcvars sigma in 
        begin try
          let offset = CVar.index_of_name cvars s in
            Apx.Comp.SBox (loc1, psihat', 
                           create_sub (Apx.LF.SVar (Apx.LF.Offset offset, sigma')) spine )
        with Not_found -> 
          raise (Error.Error (Some loc3, Error.UnboundName s))
        end 


  | Ext.Comp.Box (loc, psihat, m) ->
      let (psihat', bvars) = index_psihat cvars psihat in
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  

      let (m', _ ) = index_term cvars (ctxOpt, bvars) fcvars m in  
        Apx.Comp.Box (loc, psihat', m')


  | Ext.Comp.SBox (loc, psihat,s) -> 
      let (psihat', bvars) = index_psihat cvars psihat in
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  

      let (s', _ ) = index_sub cvars (ctxOpt, bvars) fcvars s in 
        Apx.Comp.SBox (loc, psihat', s')

  | Ext.Comp.Case (loc, prag, i, branches) ->
      let i' = index_exp' cvars vars fcvars i in
      let branches' = List.map (function b -> index_branch cvars vars fcvars b) branches in
        Apx.Comp.Case (loc, prag, i', branches')


  | Ext.Comp.If (loc, i, e1, e2) -> 
      let i' = index_exp' cvars vars fcvars i in
      let e1' = index_exp cvars vars fcvars e1 in
      let e2' = index_exp cvars vars fcvars e2 in
        Apx.Comp.If(loc, i', e1', e2')

and index_exp' cvars vars fcvars = function
  | Ext.Comp.Var (loc, x) ->
      begin try
        Apx.Comp.Var (Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (Comp.index_of_name x)
      with Not_found ->
        raise (Error.Error (Some loc, Error.UnboundCompName x))
      end

  | Ext.Comp.Apply (loc, i, e) ->
      let i' = index_exp' cvars vars fcvars i in
      let e' = index_exp  cvars vars fcvars e in
        Apx.Comp.Apply (loc, i', e')

  | Ext.Comp.CtxApp (loc, i, psi) ->
      let i'   = index_exp' cvars vars fcvars i in
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in   
      let (psi', _ , _ ) = index_dctx cvars (ctxOpt, BVar.create ()) fcvars psi in
        Apx.Comp.CtxApp (loc, i', psi')

  | Ext.Comp.MApp (loc, i, (psihat, m)) ->
      let i'      = index_exp' cvars vars fcvars i in
      let (psihat', bvars) = index_psihat cvars psihat in
      let ctxOpt = begin match psihat' with
                   | None , _  -> None 
                   | Some (Int.LF.CtxOffset psi) , _  ->  Some (Apx.LF.CtxOffset psi)
                   | Some (Int.LF.CtxName psi)  , _   ->  Some (Apx.LF.CtxName psi)
                   end in  
      let (m', _ ) = index_term cvars (ctxOpt, bvars) fcvars m in
        Apx.Comp.MApp (loc, i', Apx.Comp.MetaObj (Some loc, psihat', m'))

  | Ext.Comp.MAnnApp (loc, i, (psi, m)) ->
      let i'      = index_exp' cvars vars fcvars i in
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
                   end in   
      let (psi', bvars, _ ) = index_dctx cvars  (ctxOpt, BVar.create ()) fcvars psi in
      let (m', _ ) = index_term cvars bvars fcvars m in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Ext.Comp.BoxVal (loc, psi, m) ->
      let (fcvs, _cf ) = fcvars in 
      let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name ->  
		       if lookup_fv fcvs (FCV psi_name) then 
			 Some (Apx.LF.CtxName psi_name)
		       else 
			 raise (Error.Error (Some loc, Error.UnboundCtxName  psi_name))
                     end 
		    in   
      let (psi', bvars, _ ) = index_dctx cvars  (ctxOpt, BVar.create ()) fcvars  psi in
      let (m', _ ) = index_term cvars bvars fcvars m in 
        Apx.Comp.BoxVal (loc, psi', m') 

  | Ext.Comp.Ann (_loc, e, tau) ->
      Apx.Comp.Ann (index_exp  cvars vars fcvars e,
                         index_comptyp cvars fcvars tau)

  | Ext.Comp.Equal (loc, i, i') ->
      let i1 = index_exp' cvars vars fcvars i in 
      let i2 = index_exp' cvars vars fcvars i' in 
        Apx.Comp.Equal (loc, i1, i2)

  | Ext.Comp.Boolean (loc , b) -> Apx.Comp.Boolean (loc, b)

(* and index_pattern mvars ((fcvars, fvars) as fcvars) pat = match pat with
  | Ext.Comp.PatEmtpy (_ , cPsi) -> 
      let ctxOpt = begin match get_ctxvar cPsi with
                   | None -> None 
                   | Some psi_name ->  begin try
                       let offset = CVar.index_of_name cvars psi_name in
                         Some (Apx.LF.CtxOffset offset)
                     with Not_found ->
                       raise (Error.Error (Some loc, Error.UnboundCtxName psi_name))
                     end
      end in 
      let (psi', bvars', fvars') = index_dctx cvars (ctxOpt, BVar.create ()) fvars psi in
      let 
(Apx.Comp.PatEmpty, fcvars)
  | Ext.Comp.PatTrue loc ->  (Apx.Comp.PatTrue loc, fcvars)
  | Ext.Comp.PatFalse loc -> (Apx.Comp.PatFalse loc, fcvars)
  | Ext.Comp.Pair (loc, pat1, pat2) -> 
      let (pat1', fcvars1) = index_pattern mvars vars fcvars in 
      let (pat2', fcvars2) = index_pattern mvars vars fcvars1 in 
        (Apx.Comp.PatPair (loc, pat1', pat2') , fcvars2)
  | Ext.Comp.PatVar (loc, x) -> (Apx.Comp.PatVar (loc, x), (fcvars, x::fvars))
*)
and index_mobj cvars fcvars (ctxOpt, mO) = match mO with 
  | Ext.Comp.MetaCtx (loc, cPsi) -> 
    let (cPsi', _bvars, fcvars')  = index_dctx cvars (ctxOpt, BVar.create ()) fcvars cPsi in
      (Apx.Comp.MetaCtx (Some loc, cPsi') , fcvars')
      
  | Ext.Comp.MetaObj (loc, phat, tM) ->  raise (Error.Error (Some loc, Error.PatCtxRequired))
  | Ext.Comp.MetaObjAnn (loc, cPsi, tM) -> 
    let (cPsi', bvars, fcvars1)  = index_dctx cvars (ctxOpt, BVar.create ()) fcvars cPsi in
    let (tM', fcvars2)           = index_term cvars bvars fcvars1 tM in 
      (Apx.Comp.MetaObjAnn (Some loc, cPsi', tM') , fcvars2)


and index_branch cvars vars (fcvars, _ ) branch = match branch with
(*  | Ext.Comp.EmptyBranch (loc, delta, pat) -> 
    let empty_fcvars = [] in 
(*      if containsEmptyPat pat then  *)
    let (omega, delta', ctx_vars', mvars', fcvars1)  =  
      index_mctx ctx_vars' (CVar.create()) empty_fcvars delta in 
    let (pat', fcvars, fcvars) = index_pattern ctx_vars' mvars' (fcvars1 ,
                                                                empty_fcvars) pat
    in 
*)
  | Ext.Comp.Branch (loc, _cD, Ext.Comp.PatEmpty _ , _e) -> 
      raise (Error.Error (Some loc, Error.CompEmptyPattBranch))
  | Ext.Comp.Branch (loc, cD, Ext.Comp.PatMetaObj (loc', mO), e) -> 
    let empty_fcvars = [] in 
    let _ = dprint (fun () -> "index_branch") in 
    let (fcvars', ctxOpt1) = begin match get_ctxvar_mobj mO with 
                     | None -> (empty_fcvars  , None)
                     | Some psi_name -> 
                         let fcvars =  FCV psi_name :: empty_fcvars in 
                           (fcvars, Some (Apx.LF.CtxName psi_name))
                    end in
    
    let (omega, cD', cvars1, fcvars1)  = 
      index_mctx (CVar.create()) (fcvars', not closed) cD in
    let (mO', (fcvars2, _)) = index_mobj cvars1 fcvars1 (ctxOpt1, mO) in 
    let cvars_all      = CVar.append cvars1 cvars in
    let fcvars3        = List.append fcvars2 fcvars in 
    let e'             = index_exp cvars_all vars (fcvars3, closed) e in
      Apx.Comp.Branch (loc, omega, cD', Apx.Comp.PatMetaObj (loc', mO'), e')

(*  | Ext.Comp.BranchBox (loc, cD, pat, e) -> 
    (* Context Declarations are part of cD *)
    (* bp: collecting fcvars used for scope checking *)
    let empty_fcvars = [] in 
    let (omega, delta', ctx_vars', mvars', fcvars1)  =   
      index_mctx ctx_vars' (CVar.create()) empty_fcvars delta in 
    let (pat', fcvars, fvars) = 
      (* patterns should be linear in fvars; they may be non-linear in fcvars *)
      index_pattern ctx_vars' mvars' fcvars1 pat in 
    let mvars_all        = CVar.append mvars' mvars in
    let ctxvars_all      = CVar.append ctx_vars' ctx_vars in
    let e' = index_exp ctx_vars_all mvars_all vars (fcvars, fvars) in 
      Apx.Comp.BranchBox (loc, delta', pat', e')
*)

  (* The subsequent two cases are only relevant for the old syntax;
     they are redundant in the new syntax *)
  | Ext.Comp.BranchBox(loc, delta, (psi1, pattern, Some (a, psi))) ->
    let empty_fcvars = [] in 
    let _ = dprint (fun () -> "index_branch") in 
    let fcvars' = begin match get_ctxvar psi1 with 
                     | None -> empty_fcvars
                     | Some psi_name -> FCV psi_name :: empty_fcvars
                    end in
    
    let (omega, delta', cvars1, ((fcvs1, _ ) as fcvars1))  = 
      index_mctx  cvars (fcvars', not closed) delta in
    let ctxOpt1 =  begin match get_ctxvar psi1 with
                   | None -> None 
                   | Some psi_name -> 
		       if lookup_fv fcvs1 (FCV psi_name) then 
			 Some (Apx.LF.CtxName psi_name)
		       else 
			 raise (Error.Error (Some loc, Error.UnboundCtxName  psi_name))
                   end in 
    let (psi1', bvars, fcvars2)  = index_dctx cvars1 (ctxOpt1, BVar.create ()) fcvars1 psi1 in 
    let (m'opt, fcvars3)       = match pattern with
                                     | Ext.Comp.EmptyPattern -> (None, fcvars2)
                                     | Ext.Comp.NormalPattern (m, e) ->
                                         let (m', fcvars3) = index_term cvars1 bvars fcvars2 m in
                                           (Some m', fcvars3)
    in
    let (psi', _bvars, fcvars4)   = index_dctx cvars1 (ctxOpt1, BVar.create ()) fcvars3 psi in
    (* _bvars = bvars *)
    let (a', (fcvars5, _))        = index_typ cvars1 bvars fcvars4 a in 

    let cvars_all        = CVar.append cvars1 cvars in

    let fcvars6 = List.append fcvars5 fcvars in

    let pattern' =
      match (pattern, m'opt) with
        | (Ext.Comp.EmptyPattern, None) -> Apx.Comp.EmptyPattern
        | (Ext.Comp.NormalPattern (_, e), Some m') -> 
	    Apx.Comp.NormalPattern (m', index_exp cvars_all vars (fcvars6, closed) e)
    in
      Apx.Comp.BranchBox (loc, omega, delta', (psi1', pattern', Some (a', psi')))

  | Ext.Comp.BranchBox (loc, delta, (psi, pattern, None)) ->
    let empty_fcvars = [] in 
    let fcvars' = begin match get_ctxvar psi with 
                     | None -> empty_fcvars
                     | Some psi_name -> FCV psi_name :: empty_fcvars
                    end in

    let (omega, delta', cvars', ((fcvars1, _ ) as fcvs1))  = 
      index_mctx cvars (fcvars', not closed) delta in
    let ctxOpt = begin match get_ctxvar psi with
                   | None -> None 
                   | Some psi_name -> 
		       if lookup_fv fcvars1 (FCV psi_name) then 
			 Some (Apx.LF.CtxName psi_name)
		       else 
			 raise (Error.Error (Some loc, Error.UnboundCtxName  psi_name))
                   end in 
    let (psi1', bvars, fcvars2)    = index_dctx cvars' (ctxOpt, BVar.create ()) fcvs1 psi in

      begin match pattern with 
        | Ext.Comp.EmptyPattern ->
            Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.EmptyPattern, None))         

        | Ext.Comp.NormalPattern (m, e)  -> 
            let (m', (fcvars3, _))     = index_term cvars' bvars fcvars2 m in
            let cvars_all        = CVar.append cvars' cvars in
            let fcvars4 = List.append fcvars3 fcvars in 
            let e'               = index_exp cvars_all vars (fcvars4, closed) e in
              Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.NormalPattern (m', e'), None))
                
      end

let kind     = index_kind (CVar.create ()) (None, BVar.create ()) ([], closed)
let typ      = index_typ  (CVar.create ()) (None, BVar.create ()) ([], closed)
let schema   = index_schema
let compkind = index_compkind (CVar.create ())  ([], not closed)
let comptyp  = index_comptyp  (CVar.create ()) ([], not closed)
let exp      = fun vars -> fun e -> index_exp (CVar.create ()) vars ([], closed) e
let exp'     = fun vars -> fun i -> index_exp' (CVar.create ()) vars ([], closed) i
