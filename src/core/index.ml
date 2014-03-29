
(* -------------------------------------------------------------*)
(*  indexing
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
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer


let (dprint, _) = Debug.makeFunctions (Debug.toFlags [11])

let term_closed = true

type error =
  | UnboundName          of Id.name
  | UnboundCtxName       of Id.name
  | UnboundCtxSchemaName of Id.name
  | UnboundCompName      of Id.name
  | UnboundCompConstName of Id.name
  | PatCtxRequired
  | CompEmptyPattBranch
  | UnboundIdSub
  | PatVarNotUnique
  | IllFormedCompTyp

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | UnboundName n ->
          Format.fprintf ppf
	    "Unbound data-level variable (ordinary or meta-variable) or constructor: %s."
	    (R.render_name n)
      | UnboundCtxName n ->
          Format.fprintf ppf "Unbound context variable: %s." (R.render_name n)
      | UnboundCtxSchemaName n ->
          Format.fprintf ppf "Unbound context schema: %s." (R.render_name n)
      | UnboundCompName n ->
          Format.fprintf ppf "Unbound computation-level variable: %s." (R.render_name n)
      | UnboundCompConstName n ->
          Format.fprintf ppf "Unbound computation-level constructor: %s." (R.render_name n)
      | PatCtxRequired ->
          Format.fprintf ppf
	    "The context in a pattern must be a proper context, where a variable declaration must carry its type."
      | CompEmptyPattBranch ->
          Format.fprintf ppf "If the pattern in a branch is empty, there should be no branch body."
      | UnboundIdSub ->
          Format.fprintf ppf "Identity substitution used without context variable."
      | PatVarNotUnique ->
          Format.fprintf ppf "Pattern variable not linear."
      | IllFormedCompTyp ->
	Format.fprintf ppf "Ill-formed computation-level type."))


type free_cvars =
    FMV of Id.name | FPV of Id.name | FSV of Id.name | FCV of Id.name

type fcvars = free_cvars list * bool

let rec nearestFCVar fvars = begin match fvars with
  | [] -> None
  | FCV psi :: fvs -> Some (Apx.LF.CtxName psi)
  | _ :: fvs -> nearestFCVar fvs
end

let rec fcvarsToString fcvars = match fcvars with
  | [] -> ""
  | FMV m :: fcvars -> ", FMV " ^ R.render_name m ^ fcvarsToString fcvars
  | FPV m :: fcvars -> ", FPV " ^ R.render_name m ^ fcvarsToString fcvars
  | FCV m :: fcvars -> ", FCV " ^ R.render_name m ^ fcvarsToString fcvars
  | FSV m :: fcvars -> ", FSV " ^ R.render_name m ^ fcvarsToString fcvars

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
  | (FSV n :: fvars' , FSV m) ->
      if n = m then true
      else lookup_fv fvars' (FSV m)

  | (FPV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FCV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FSV _ :: fvars' , FMV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m
  | (FCV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m
  | (FSV _ :: fvars' , FPV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FCV _ ) -> lookup_fv fvars' m
  | (FPV _ :: fvars' , FCV _ ) -> lookup_fv fvars' m
  | (FSV _ :: fvars' , FCV _ ) -> lookup_fv fvars' m
  | (FMV _ :: fvars' , FSV _ ) -> lookup_fv fvars' m
  | (FPV _ :: fvars' , FSV _ ) -> lookup_fv fvars' m
  | (FCV _ :: fvars' , FSV _ ) -> lookup_fv fvars' m
end

let rec get_ctxvar psi = match psi with
  | Ext.LF.Null -> None
  | Ext.LF.CtxVar (_loc, psi_name) -> Some psi_name
  | Ext.LF.DDec (psi, _ ) -> get_ctxvar psi


let get_ctxvar_mobj mO = match mO with
  | Ext.Comp.MetaCtx (_, cPsi) -> get_ctxvar cPsi
  | Ext.Comp.MetaObjAnn (_, cPsi, _tM) -> get_ctxvar cPsi
  | _ -> None

let rec length_typ_rec t_rec = match t_rec with
  | Ext.LF.SigmaLast _ -> 1
  | Ext.LF.SigmaElem (x, _ , rest ) ->
      (print_string (R.render_name x ^ "  ");
      1 + length_typ_rec rest )

let rec index_kind cvars bvars fvars = function
  | Ext.LF.Typ _ ->
      (Apx.LF.Typ, fvars)

  | Ext.LF.ArrKind (_, a, k) ->
      let x            = Id.mk_name Id.NoName
      and (a', fvars1) = index_typ cvars bvars fvars a in
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (k', fvars2) = index_kind cvars bvars' fvars1 k in
        (Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.No), k') , fvars2)

  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
      let (a', fvars1) = index_typ cvars bvars fvars a in
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (k', fvars2) = index_kind cvars bvars' fvars1 k in
        (Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), k') , fvars2)

and index_typ cvars bvars fvars = function
  | Ext.LF.Atom (loc, a, s) ->
    begin
      try
        let a' = Typ.index_of_name a in
	let (s', fvars') = index_spine cvars bvars fvars s in
        (Apx.LF.Atom (loc, a', s') , fvars')
      with Not_found ->
	raise (Error (loc, UnboundName a))
    end

  | Ext.LF.ArrTyp (_loc, a, b) ->
      let x            = Id.mk_name Id.NoName
      and (a', fvars1) = index_typ cvars bvars fvars a in
      let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
      let (b', fvars2) = index_typ cvars bvars' fvars1 b in
        (Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.No), b') , fvars2)

  | Ext.LF.PiTyp (_loc, Ext.LF.TypDecl (x, a), b) ->
      let (a', fvars1)  = index_typ cvars bvars  fvars a in
      let bvars'        = BVar.extend bvars (BVar.mk_entry x) in
      let (b', fvars2)  = index_typ cvars bvars' fvars1 b in
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
      let bvars'          = BVar.extend bvars (BVar.mk_entry x) in
      let (rest', fvars2) = index_typ_rec cvars bvars' fvars1 rest in
        (Apx.LF.SigmaElem (x, a', rest') , fvars2)

and index_tuple cvars bvars fvars = function
  | Ext.LF.Last m ->
      let (m', fvars') = index_term cvars bvars fvars m in
        (Apx.LF.Last m', fvars')
  | Ext.LF.Cons (m, rest) ->
      let (m', fvars1) = index_term cvars bvars fvars m in
      let (rest', fvars2) = index_tuple cvars bvars fvars1 rest in
        (Apx.LF.Cons (m', rest') , fvars2)

and index_term cvars bvars fvars = function
  | Ext.LF.Lam (loc, x, m) ->
      let bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let (m', fvars')     = index_term cvars bvars' fvars m in
        (Apx.LF.Lam (loc, x, m') , fvars')

  | Ext.LF.Tuple (loc, tuple) ->
      let (tuple', fvars') = index_tuple cvars bvars fvars tuple in
        (Apx.LF.Tuple (loc, tuple') , fvars')

  | Ext.LF.Root (loc, h, s) ->
      let (h', fvars1) = index_head  cvars bvars fvars h in
      let (s', fvars2) = index_spine cvars bvars fvars1 s in
        (Apx.LF.Root (loc, h', s') , fvars2)

  | Ext.LF.Ann (loc, m, a) ->
    let (a', fvars') = index_typ cvars bvars fvars a in
    let (m', fvars'') = index_term cvars bvars fvars' m in
    (Apx.LF.Ann (loc, m', a'), fvars'')

and index_head cvars bvars ((fvars, closed_flag) as fvs) = function
  | Ext.LF.Name (_, n) ->
      (* let _        = dprint (fun () -> "Indexing name " ^ n.string_of_name)
         in *)
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
      if lookup_fv fvars (FPV p) then
        let (s', (fvars', closed_flag))  = index_sub cvars bvars fvs s in
          (Apx.LF.FPVar (p, s') , (fvars' , closed_flag))
      else
        begin try
          let offset = CVar.index_of_name cvars (CVar.PV p) in
          let (s' , fvs') = index_sub cvars bvars fvs s in
            (Apx.LF.PVar (Apx.LF.Offset offset, s') , fvs')
        with Not_found ->
	  if closed_flag then
	    ((* if lookup_fv fvars (FPV p) then
                let (s', (fvars', closed_flag))  = index_sub cvars bvars fvs s in
                (Apx.LF.FPVar (p, s') , (fvars' , closed_flag))
	        else *)
	      raise (Error (loc, UnboundName p))
	    )
	  else
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
          let offset = CVar.index_of_name cvars (CVar.MV u) in
          let (s', fvs')     = index_sub cvars bvars fvs s in
            (Apx.LF.MVar (Apx.LF.Offset offset, s') , fvs')
        with Not_found ->
	  if closed_flag then
	    (* if lookup_fv fvars (FMV u) then
               let (s', (fvars', closed_flag))     = index_sub cvars bvars fvs s in
		 (Apx.LF.FMVar (u, s') , (fvars' , closed_flag))
	     else *)
	       raise (Error (loc, UnboundName u))
	  else
            let (s', (fvars', closed_flag))     = index_sub cvars bvars fvs s in
              (Apx.LF.FMVar (u, s') , (FMV u :: fvars' , closed_flag))
        end

  (* | Ext.LF.SVar (loc, n, _sigma) -> *)
  (*     let _        = dprint (fun () -> "Indexing head : SVar " ^ n.string_of_name) in *)
  (*       raise (Error (loc, UnboundName n)) *)

and index_spine cvars bvars fvars = function
  | Ext.LF.Nil ->
      (Apx.LF.Nil , fvars)

  | Ext.LF.App (_, m, s) ->
      let (m', fvars')  = index_term  cvars bvars fvars m in
      let (s', fvars'') = index_spine cvars bvars fvars' s in
        (Apx.LF.App (m', s') , fvars'')

and index_sub cvars bvars ((fvs, closed_flag )  as fvars) = function
  | Ext.LF.Id loc ->
      let psi =
	begin try Apx.LF.CtxOffset (CVar.nearest_cvar cvars)
	with Not_found ->  (match nearestFCVar fvs with
			      | None -> raise (Error (loc ,
							    UnboundIdSub))
			      | Some psi -> psi
			   )
	end
      in
	(dprint (fun () ->
		   match psi with
		     | Apx.LF.CtxOffset offset ->
			 "[index_sub] id : domain has index " ^ R.render_offset offset
		     | Apx.LF.CtxName psi ->
			 "[index_sub] id : domain has index " ^ R.render_name psi)
	;
	(Apx.LF.Id psi, fvars))

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

  | Ext.LF.SVar (loc, u, s) ->
      if lookup_fv fvs (FSV u) then
        let (s', fvs')     = index_sub cvars bvars fvars s in
          (Apx.LF.FSVar (u, s') , fvs')
      else
        begin try
          let offset = CVar.index_of_name cvars (CVar.SV u) in
          let (s', fvs') = index_sub cvars bvars fvars s in
          let _ = dprint (fun () -> "[index_sub] s = " ^ string_of_int offset) in
            (Apx.LF.SVar (Apx.LF.Offset offset, s') , fvs')
        with Not_found ->
	  if closed_flag then
	    (* if lookup_fv fvars (FMV u) then
               let (s', (fvars', closed_flag))     = index_sub cvars bvars fvs s in
		 (Apx.LF.FMVar (u, s') , (fvars' , closed_flag))
	     else *)
	       raise (Error (loc, UnboundName u))
	  else
            let (s', (fvars', closed_flag))     = index_sub cvars bvars fvars s in
              (Apx.LF.FSVar (u, s') , (FSV u :: fvars' , closed_flag))
        end


let index_decl cvars bvars fvars (Ext.LF.TypDecl(x, a)) =
  let (a', fvars') = index_typ cvars bvars fvars a in
  let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDecl (x,a'), bvars', fvars')

let rec index_dctx cvars bvars ((fvs, closed) as fvars) = function
  | Ext.LF.Null        -> (Apx.LF.Null , bvars, fvars)

  | Ext.LF.CtxVar (loc, psi_name)  ->
      if lookup_fv fvs (FCV psi_name) then
	(Apx.LF.CtxVar (Apx.LF.CtxName psi_name), bvars, (fvs, closed))
      else
	begin try
          let offset = CVar.index_of_name cvars (CVar.CV psi_name) in
            (Apx.LF.CtxVar (Apx.LF.CtxOffset offset) , bvars, fvars)
	with Not_found ->
	if closed then
	     raise (Error (loc, UnboundName psi_name))
	else
	  (Apx.LF.CtxVar (Apx.LF.CtxName psi_name), bvars, ((FCV psi_name :: fvs),  closed))
	end
  | Ext.LF.DDec (psi, decl) ->
      let (psi', bvars', fvars')    = index_dctx cvars bvars fvars psi in
      let (decl', bvars'', fvars'') = index_decl cvars bvars' fvars' decl in
        (Apx.LF.DDec (psi', decl'), bvars'', fvars'')

(* Order of psihat? -bp
   It's not clear how to know that the last name is a bound variable
   or if it is a name of a context variable...
*)
let index_psihat cvars fcvars extphat =
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
	   let (fvs, _ ) = fcvars in
	     if lookup_fv fvs (FCV x) then
               let (d, bvars) = index_hat bv psihat in
		 ((Some (Int.LF.CtxName x), d) , bvars)
	     else
               begin try
		 let ctx_var = CVar.index_of_name cvars (CVar.CV x) in
		 let (d, bvars) = index_hat bv psihat in
		 let _ = dprint (fun () -> "[index_psihat] offset = " ^
				   R.render_offset ctx_var ) in
		   ((Some (Int.LF.CtxOffset ctx_var), d) , bvars)
               with Not_found ->
		 let (d, bvars ) = index_hat bv extphat in
		   ((None, d) , bvars)
               end
    end

let rec index_ctx cvars bvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty , bvars, fvars)

  | Ext.LF.Dec (psi, dec) ->
      let (psi', bvars', fvars')   = index_ctx  cvars bvars fvars psi in
      let (dec', bvars'', fvars'') = index_decl cvars bvars' fvars' dec in
        (Apx.LF.Dec (psi', dec'), bvars'', fvars'')

let index_cdecl cvars fvars = function
  | Ext.LF.MDecl (loc, u, a, psi) ->
      let (psi', bvars', fvars') = index_dctx cvars (BVar.create ()) fvars psi in
      let (a', fvars'')          = index_typ  cvars bvars' fvars' a in
      let cvars'                 = CVar.extend cvars (CVar.mk_entry (CVar.MV u)) in
        (Apx.LF.MDecl (u, a', psi'), cvars', fvars'')

  | Ext.LF.PDecl (loc, p, a, psi) ->
      let (psi', bvars', fvars') = index_dctx cvars (BVar.create ()) fvars psi in
      let (a', fvars')           = index_typ  cvars bvars' fvars' a in
      let cvars'                 = CVar.extend cvars (CVar.mk_entry (CVar.PV p)) in
        (Apx.LF.PDecl (p, a', psi') , cvars', fvars')

  | Ext.LF.SDecl (loc, s, phi, psi) ->
      let (psi', _bvars', fvars') = index_dctx cvars (BVar.create ()) fvars psi in
      let (phi', _bvars', fvars'') = index_dctx cvars (BVar.create ()) fvars' phi in
      let _              = dprint (fun () -> "Extend cvars with " ^ R.render_name s) in
      let cvars'         = CVar.extend cvars (CVar.mk_entry (CVar.SV s)) in
        (Apx.LF.SDecl (s, phi', psi') , cvars', fvars'')

  | Ext.LF.CDecl (loc , ctx_name, schema_name) ->
    begin try

      let cvars'        = CVar.extend cvars (CVar.mk_entry (CVar.CV ctx_name)) in
      let schema_cid    = Schema.index_of_name schema_name in
        (Apx.LF.CDecl (ctx_name, schema_cid), cvars', fvars)
    with
        Not_found -> raise (Error (loc, UnboundCtxSchemaName schema_name))
    end


let rec index_mctx cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty, Apx.LF.Empty, cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (omega', delta', cvars', fvars') = index_mctx cvars fvars delta in
      let (cdec', cvars'', fvars'') = index_cdecl cvars' fvars' cdec in
        begin match cdec' with
          | Apx.LF.CDecl _ -> (omega', Apx.LF.Dec (delta', cdec'), cvars'', fvars'')
              (* (Apx.LF.Dec(omega', cdec'), delta', cvars'', fvars'') *)
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
      let  bvars' = BVar.extend bvars (BVar.mk_entry x) in
      let (arec', fvars'') = index_typrec cvars bvars' fvars' arec in
        (Apx.LF.SigmaElem (x, a', arec'), fvars'')


(* Translation of external schemas into approximate schemas *)
let rec index_elements el_list = List.map index_el el_list

and index_el (Ext.LF.SchElem (_, typ_ctx, typ_rec)) =
  let cvars = (CVar.create ()) in
  let bvars = BVar.create () in
  let fvars = [] in
  let (typ_ctx', bvars', _ ) = index_ctx cvars bvars (fvars,not term_closed) typ_ctx in
  let _ = dprint (fun () ->  ("\n[index_el] ext block has length " ^ string_of_int (length_typ_rec typ_rec) ^ "\n")) in
  let (typ_rec', _ )         = index_typrec cvars bvars' (fvars, not term_closed) typ_rec in
    Apx.LF.SchElem (typ_ctx', typ_rec')


let index_schema (Ext.LF.Schema el_list) =
  Apx.LF.Schema (index_elements el_list)


(* Translation of external computations into approximate computations *)

let rec index_meta_obj cvars fcvars = function
  | Ext.Comp.MetaCtx (l, cpsi) ->
      let (cPsi, _bvars, fcvars') = index_dctx cvars (BVar.create ()) fcvars cpsi in
        (Apx.Comp.MetaCtx (l, cPsi), fcvars')

  | Ext.Comp.MetaObj (l, phat, m) ->
      let (psihat' , bvars) = index_psihat cvars fcvars phat in
      let (m', fcvars') = index_term cvars bvars fcvars m in
        (Apx.Comp.MetaObj (l, psihat', m'), fcvars)

  | Ext.Comp.MetaObjAnn (l, cpsi, m) ->
      let (cPsi, bvars, fcvars') = index_dctx cvars (BVar.create ()) fcvars cpsi in
      let (m', fcvars'') = index_term cvars  bvars fcvars' m in
        (Apx.Comp.MetaObjAnn (l, cPsi, m'), fcvars'')

  | Ext.Comp.MetaSObj (l, phat, m) ->
      let (psihat' , bvars) = index_psihat cvars fcvars phat in
      let (m', fcvars') = index_sub cvars bvars fcvars m in
        (Apx.Comp.MetaSub (l, psihat', m'), fcvars)

  | Ext.Comp.MetaSObjAnn (l, cpsi, m) ->
      let (cPsi, bvars, fcvars') = index_dctx cvars (BVar.create ()) fcvars cpsi in
      let (m', fcvars'') = index_sub cvars  bvars fcvars' m in
        (Apx.Comp.MetaSubAnn (l, cPsi, m'), fcvars'')

and index_meta_spine cvars fcvars = function
  | Ext.Comp.MetaNil ->
      (Apx.Comp.MetaNil , fcvars)

  | Ext.Comp.MetaApp (m, s) ->
      let (m', fcvars')  = index_meta_obj  cvars fcvars m in
      let (s', fcvars'') = index_meta_spine cvars fcvars' s in
        (Apx.Comp.MetaApp (m', s') , fcvars'')

let rec index_compkind cvars fcvars = function
  | Ext.Comp.Ctype loc -> Apx.Comp.Ctype loc

  | Ext.Comp.PiKind (loc, (cdecl , dep), cK) ->
      let (cdecl', cvars', fcvars') = index_cdecl cvars fcvars cdecl in
      let dep' = match dep with Ext.Comp.Explicit -> Apx.Comp.Explicit | Ext.Comp.Implicit -> Apx.Comp.Implicit in
      let cK' = index_compkind cvars' fcvars' cK in
        Apx.Comp.PiKind (loc, (cdecl', dep'), cK')


let rec index_comptyp cvars  ((fcvs, closed) as fcvars) =
  function
  | Ext.Comp.TypBase (loc, a, ms) ->
      begin try
        let a' = CompTyp.index_of_name a in
        let (ms', fcvars') = index_meta_spine cvars fcvars ms in
	  (Apx.Comp.TypBase (loc, a', ms'), fcvars')
      with Not_found -> try
        let a' = CompCotyp.index_of_name a in
        let (ms', fcvars') = index_meta_spine cvars fcvars ms in
	  (Apx.Comp.TypCobase (loc, a', ms'), fcvars')
      with Not_found ->
        begin try
          let a' = CompTypDef.index_of_name a in
          let (ms', fcvars') = index_meta_spine cvars fcvars ms in
            (Apx.Comp.TypDef (loc, a', ms'), fcvars')
        with Not_found ->
          raise (Error (loc, UnboundName a))
        end
      end
  | Ext.Comp.TypBox (loc, a, psi) ->
    begin match a with
      | Ext.LF.Atom (_ , name, Ext.LF.Nil)
          when (try ignore (CVar.index_of_name cvars (CVar.CV name)); true with Not_found -> false) ->
        let offset = CVar.index_of_name cvars (CVar.CV name) in
        let (psi', _ , fcvars1) = index_dctx cvars (BVar.create ()) fcvars psi in
        let _ = dprint (fun () -> "Indexing TypSub -- turning TypBox into TypSub") in
        (Apx.Comp.TypSub (loc, Apx.LF.CtxVar (Apx.LF.CtxOffset offset), psi'), fcvars1)
      | _ ->
        let (psi', bvars', fcvars') = index_dctx cvars (BVar.create ()) fcvars psi in
        let (a', fcvars'' )         = index_typ cvars bvars' fcvars' a   in
        (Apx.Comp.TypBox (loc, a', psi'), fcvars'')
    end

  | Ext.Comp.TypSub (loc, phi, psi)    ->
      let (psi', _ , fcvars1 ) = index_dctx cvars (BVar.create ()) fcvars psi in
      let (phi', _ , fcvars2 ) = index_dctx cvars (BVar.create ()) fcvars1 phi in
        (Apx.Comp.TypSub (loc, phi', psi'), fcvars2)


  | Ext.Comp.TypArr (_loc, tau, tau') ->
      let (tau1, fcvars1) = index_comptyp cvars fcvars tau in
      let (tau2, fcvars2) = index_comptyp cvars fcvars1 tau' in
      (Apx.Comp.TypArr (tau1, tau2), fcvars2)


  | Ext.Comp.TypCross (_loc, tau, tau') ->
      let (tau1, fcvars1) = index_comptyp cvars fcvars tau in
      let (tau2, fcvars2) = index_comptyp cvars fcvars1 tau' in
	(Apx.Comp.TypCross (tau1, tau2), fcvars2)


  | Ext.Comp.TypPiBox (_loc, (cdecl, dep), tau)    ->
      let (cdecl', cvars', fcvars1) = index_cdecl cvars fcvars cdecl in
      let (tau', fcvars2) = index_comptyp cvars' fcvars1 tau in
      let apxdep = match dep with
	  Ext.Comp.Explicit -> Apx.Comp.Explicit
	| Ext.Comp.Implicit -> Apx.Comp.Implicit in
        (Apx.Comp.TypPiBox ((cdecl', apxdep), tau'), fcvars2)

  | Ext.Comp.TypBool -> (Apx.Comp.TypBool, fcvars)

  | Ext.Comp.TypPBox (loc, _, _) -> raise (Error (loc, IllFormedCompTyp))
  | Ext.Comp.TypCtx (loc, _) -> raise (Error (loc, IllFormedCompTyp))

let rec index_exp cvars vars fcvars = function
  | Ext.Comp.Syn (loc , i)   ->
      Apx.Comp.Syn (loc, index_exp' cvars vars fcvars i)

  | Ext.Comp.Fun (loc, x, e) ->
      let vars' = Var.extend vars (Var.mk_entry x) in
        Apx.Comp.Fun (loc, x, index_exp cvars vars' fcvars e)

  | Ext.Comp.Cofun (loc, copatterns) ->
      let copatterns' =
        List.map (function (sp, e) ->
                    let (sp', fcvars') = index_copat_spine cvars vars fcvars sp in
                      (sp', index_exp cvars vars fcvars' e))
          copatterns
      in
        Apx.Comp.Cofun (loc, copatterns')

  | Ext.Comp.MLam (loc, (psi_name, Ext.Comp.CObj), e) ->
        let cvars' = CVar.extend cvars (CVar.mk_entry (CVar.CV psi_name)) in
        Apx.Comp.MLam (loc, psi_name, index_exp cvars' vars fcvars e)

  | Ext.Comp.MLam (loc, (u, Ext.Comp.MObj), e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry (CVar.MV u)) in
        Apx.Comp.MLam (loc, u, index_exp cvars' vars fcvars e)

  | Ext.Comp.MLam (loc, (u, Ext.Comp.PObj), e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry (CVar.PV u)) in
        Apx.Comp.MLam (loc, u, index_exp cvars' vars fcvars e)

  | Ext.Comp.MLam (loc, (u, Ext.Comp.SObj), e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry (CVar.SV u)) in
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

  | Ext.Comp.Box (loc, m)  ->
      let (m', fcvars')  = index_meta_obj  cvars fcvars m in
        Apx.Comp.Box (loc, m')

  | Ext.Comp.Case (loc, prag, i, branches) ->
      let i' = index_exp' cvars vars fcvars i in
      let _ = dprint (fun () -> "index case") in
      let branches' = List.map (function b -> index_branch cvars vars fcvars b) branches in
        Apx.Comp.Case (loc, prag, i', branches')

  | Ext.Comp.If (loc, i, e1, e2) ->
      let i' = index_exp' cvars vars fcvars i in
      let e1' = index_exp cvars vars fcvars e1 in
      let e2' = index_exp cvars vars fcvars e2 in
        Apx.Comp.If(loc, i', e1', e2')

  | Ext.Comp.Hole (loc) -> Apx.Comp.Hole (loc)

and index_exp' cvars vars fcvars = function
  | Ext.Comp.Var (loc, x) ->
      begin try
        Apx.Comp.Var (Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (Comp.index_of_name x)
      with Not_found -> try
        Apx.Comp.DataConst (CompConst.index_of_name x)
      with Not_found -> try
        Apx.Comp.DataDest (CompDest.index_of_name x)
      with Not_found ->
        raise (Error (loc, UnboundCompName x))
      end
  | Ext.Comp.DataConst (loc, c) ->
    begin
      try
	Apx.Comp.DataConst (CompConst.index_of_name c)
      with Not_found -> try
        Apx.Comp.DataDest (CompDest.index_of_name c)
      with Not_found -> raise (Error (loc, UnboundCompConstName  c))
    end
  | Ext.Comp.Apply (loc, i, e) ->
      let i' = index_exp' cvars vars fcvars i in
      let e' = index_exp  cvars vars fcvars e in
        Apx.Comp.Apply (loc, i', e')

  | Ext.Comp.MApp (loc, i, mO) ->
      let i'      = index_exp' cvars vars fcvars i in
      let (mobj', _ )  = index_meta_obj cvars fcvars mO in
        Apx.Comp.MApp (loc, i', mobj')

  | Ext.Comp.BoxVal (loc, psi, m) ->
      let (psi', bvars, _ ) = index_dctx cvars  (BVar.create ()) fcvars  psi in
      let (m', _ ) = index_term cvars bvars fcvars m in
        Apx.Comp.BoxVal (loc, psi', m')
  | Ext.Comp.PairVal (loc, i1, i2) ->
      let i1' = index_exp' cvars vars fcvars i1 in
      let i2' = index_exp' cvars vars fcvars i2 in
	Apx.Comp.PairVal (loc, i1', i2')

  | Ext.Comp.Ann (_loc, e, tau) ->
      let (tau', _ ) =  index_comptyp cvars fcvars tau in
      Apx.Comp.Ann (index_exp  cvars vars fcvars e, tau' )

  | Ext.Comp.Equal (loc, i, i') ->
      let i1 = index_exp' cvars vars fcvars i in
      let i2 = index_exp' cvars vars fcvars i' in
        Apx.Comp.Equal (loc, i1, i2)

  | Ext.Comp.Boolean (loc , b) -> Apx.Comp.Boolean (loc, b)


and index_pattern_mobj cvars fcvars  mO = match mO with
  | Ext.Comp.MetaCtx (loc, cPsi) ->
    let (cPsi', _bvars, fcvars')  = index_dctx cvars (BVar.create ()) fcvars cPsi in
      (Apx.Comp.MetaCtx (loc, cPsi') , fcvars')

  | Ext.Comp.MetaObj (loc, phat, tM) ->
      raise (Error (loc, PatCtxRequired))
  | Ext.Comp.MetaObjAnn (loc, cPsi, tM) ->
    let (cPsi', bvars, fcvars1)  = index_dctx cvars (BVar.create ()) fcvars cPsi in
    let (tM', fcvars2)           = index_term cvars bvars fcvars1 tM in
      (Apx.Comp.MetaObjAnn (loc, cPsi', tM') , fcvars2)
  | Ext.Comp.MetaSObj (loc, phat, s) ->  raise (Error (loc, PatCtxRequired))
  | Ext.Comp.MetaSObjAnn (loc, cPsi, s) ->
    let (cPsi', bvars, fcvars1)  = index_dctx cvars (BVar.create ()) fcvars cPsi in
    let (s', fcvars2)           = index_sub cvars bvars fcvars1 s in
      (Apx.Comp.MetaSubAnn (loc, cPsi', s') , fcvars2)

and index_copat_spine cvars vars fcvars sp = match sp with
  | Ext.Comp.CopatNil loc -> (Apx.Comp.CopatNil loc, fcvars)
  | Ext.Comp.CopatApp (loc, name, sp') ->
      let (sp'', fcvars') = index_copat_spine cvars vars fcvars sp' in
        (Apx.Comp.CopatApp (loc, CompDest.index_of_name name, sp''), fcvars')
  | Ext.Comp.CopatMeta (loc, metaobj, sp') ->
      let (metaobj', fcvars') = index_meta_obj cvars fcvars metaobj in
      let (sp'', fcvars'') = index_copat_spine cvars vars fcvars' sp' in
        (Apx.Comp.CopatMeta (loc, metaobj', sp''), fcvars'')

and index_pattern cvars ((fvs, closed) as fcvars) fvars pat = match pat with
  | Ext.Comp.PatTrue loc -> (Apx.Comp.PatTrue loc, fcvars, fvars)
  | Ext.Comp.PatFalse loc -> (Apx.Comp.PatFalse loc, fcvars, fvars)
  | Ext.Comp.PatVar (loc, x) ->
      begin try
	let _x = Var.index_of_name fvars x in
	  raise (Error (loc, PatVarNotUnique))
      with Not_found ->
	let fvars' = Var.extend fvars (Var.mk_entry x) in
	  (Apx.Comp.PatFVar (loc, x), fcvars, fvars')
	    (* (Apx.Comp.PatVar (loc, name, offset), fcvars, fvars') *)
      end
  | Ext.Comp.PatPair (loc, pat1, pat2) ->
      let (pat1, fcvars1, fvars1) = index_pattern cvars fcvars fvars pat1 in
      let (pat2, fcvars2, fvars2) = index_pattern cvars fcvars1 fvars1 pat2 in
	(Apx.Comp.PatPair (loc, pat1, pat2), fcvars2, fvars2)
  | Ext.Comp.PatConst (loc, c, pat_spine) ->
      let cid = begin try CompConst.index_of_name c
                with
		    Not_found -> raise (Error (loc, UnboundName c))
                end in
      let (pat_spine', fcvars', fvars')  = index_pat_spine cvars fcvars fvars pat_spine in
	(Apx.Comp.PatConst (loc, cid, pat_spine'), fcvars', fvars')

  | Ext.Comp.PatMetaObj (loc, mO) ->
    let (mO', fcvars1) = index_pattern_mobj cvars fcvars mO in
      (Apx.Comp.PatMetaObj (loc, mO') , fcvars1, fvars)
  | Ext.Comp.PatEmpty (loc, cpsi) ->
      let (cPsi, _bvars, fcvars ) = index_dctx cvars (BVar.create ()) fcvars cpsi in
	(Apx.Comp.PatEmpty (loc, cPsi), fcvars, fvars)

  | Ext.Comp.PatAnn (loc, pat, tau) ->
      let (pat', fcvars', fvars') = index_pattern cvars fcvars fvars pat in
      let (tau', fcvars'') = index_comptyp cvars fcvars' tau in
	(Apx.Comp.PatAnn (loc, pat', tau') , fcvars'', fvars')

and index_pat_spine cvars fcvars fvars pat_spine = match pat_spine with
  | Ext.Comp.PatNil loc -> (Apx.Comp.PatNil loc, fcvars, fvars)
  | Ext.Comp.PatApp (loc, pat, pat_spine) ->
      let (pat', fcvars1, fvars1) = index_pattern cvars fcvars fvars pat in
      let (pat_spine', fcvars2, fvars2) = index_pat_spine cvars fcvars1 fvars1 pat_spine in
	(Apx.Comp.PatApp (loc, pat', pat_spine'), fcvars2, fvars2)


(* reindex pattern *)
and reindex_pattern fvars pat = match pat with
  | Apx.Comp.PatTrue loc -> Apx.Comp.PatTrue loc
  | Apx.Comp.PatFalse loc -> Apx.Comp.PatFalse loc
  | Apx.Comp.PatFVar (loc, x) ->
      (* all free variable names must be in fvars *)
      let offset = Var.index_of_name fvars x in
	Apx.Comp.PatVar (loc, x, offset)

  | Apx.Comp.PatPair (loc, pat1, pat2) ->
      let pat1 = reindex_pattern fvars pat1 in
      let pat2 = reindex_pattern fvars pat2 in
	Apx.Comp.PatPair (loc, pat1, pat2)
  | Apx.Comp.PatConst (loc, c, pat_spine) ->
      let pat_spine'  = reindex_pat_spine  fvars pat_spine in
	Apx.Comp.PatConst (loc, c, pat_spine')

  | Apx.Comp.PatMetaObj (loc, mO) -> pat

  | Apx.Comp.PatEmpty (loc, cpsi) -> pat

  | Apx.Comp.PatAnn (loc, pat, tau) ->
      let pat' = reindex_pattern fvars pat in
	Apx.Comp.PatAnn (loc, pat', tau)

and reindex_pat_spine fvars pat_spine = match pat_spine with
  | Apx.Comp.PatNil loc -> Apx.Comp.PatNil loc
  | Apx.Comp.PatApp (loc, pat, pat_spine) ->
      let pat' = reindex_pattern fvars pat in
      let pat_spine' = reindex_pat_spine fvars pat_spine in
	Apx.Comp.PatApp (loc, pat', pat_spine')

and index_branch cvars vars (fcvars, _ ) branch = match branch with
  | Ext.Comp.EmptyBranch (loc, cD, Ext.Comp.PatEmpty (loc', cpsi)) ->
    let empty_fcvars = [] in
    let fcvars' = begin match get_ctxvar cpsi with
                     | None -> empty_fcvars
                     | Some psi_name ->
                          FCV psi_name :: empty_fcvars
                    end in
    let (omega, cD', cvars1, fcvars1)  =
      index_mctx (CVar.create()) (fcvars', not term_closed) cD in
    let (cPsi', _bvars, fcvars2) = index_dctx cvars1 (BVar.create ()) fcvars1 cpsi in
      Apx.Comp.EmptyBranch (loc, cD', Apx.Comp.PatEmpty (loc', cPsi'))

  | Ext.Comp.EmptyBranch (loc, cD,
			  Ext.Comp.PatAnn (loc1, Ext.Comp.PatEmpty (loc2, cpsi), tau)) ->
    let empty_fcvars = [] in
    let fcvars' = begin match get_ctxvar cpsi with
                     | None -> empty_fcvars
                     | Some psi_name ->
                          FCV psi_name :: empty_fcvars
                    end in
    let (omega, cD', cvars1, fcvars1)  =
      index_mctx (CVar.create()) (fcvars', not term_closed) cD in
    let (cPsi', _bvars, fcvars2) = index_dctx cvars1 (BVar.create ()) fcvars1 cpsi in
    let (tau', fcvars1) = index_comptyp cvars1 fcvars2 tau in
      Apx.Comp.EmptyBranch(loc, cD',
			   Apx.Comp.PatAnn (loc1, Apx.Comp.PatEmpty (loc2, cPsi'), tau'))

  | Ext.Comp.Branch (loc, _cD, Ext.Comp.PatEmpty _ , _e) ->
      (dprint (fun () -> "[index_branch] PatEmpty " ) ;
      raise (Error (loc, CompEmptyPattBranch)))
  | Ext.Comp.Branch (loc, cD, Ext.Comp.PatMetaObj (loc', mO), e) ->
    let empty_fcvars = [] in
    let _ = dprint (fun () -> "index_branch") in
    (* computing fcvars' is unnecessary? -bp *)
    let fcvars' = begin match get_ctxvar_mobj mO with
                     | None -> empty_fcvars
                     | Some psi_name ->
                          FCV psi_name :: empty_fcvars
                    end in

    let (omega, cD', cvars1, fcvars1)  =
      index_mctx (CVar.create()) (fcvars', not term_closed) cD in
    let (mO', (fcvars2, _)) = index_pattern_mobj cvars1 fcvars1 mO in
    let _ = dprint (fun () -> "fcvars in pattern = " ^ fcvarsToString fcvars2) in
    let cvars_all  = CVar.append cvars1 cvars in
    let fcvars3    = List.append fcvars2 fcvars in
    let e'         = index_exp cvars_all vars (fcvars3, term_closed) e in
      Apx.Comp.Branch (loc, omega, cD', Apx.Comp.PatMetaObj (loc', mO'), e')

  | Ext.Comp.Branch (loc, cD, pat, e) ->
      let empty_fcvars = [] in
      let _ = dprint (fun () -> "index_branch - pat") in
      let (omega, cD', cvars1, fcvars1)  =
	index_mctx (CVar.create()) (empty_fcvars, not term_closed) cD in
      let (pat', fcvars2, fvars2) = index_pattern cvars1 fcvars1 (Var.create ())  pat in
      let _ = dprint (fun () -> "index_pattern done") in
      let cvars_all  = CVar.append cvars1 cvars in
      let vars_all  = Var.append fvars2 vars in
      let pat'' = reindex_pattern fvars2 pat' in
      let _ = dprint (fun () -> "reindex_pattern done") in
      let (fcv2, _ ) = fcvars2 in
      let _ = dprint (fun () -> "fcvars in pattern = " ^ fcvarsToString fcv2) in
      let fcv3      = List.append fcv2 fcvars in
      let e'        = index_exp cvars_all vars_all (fcv3, term_closed) e in
	Apx.Comp.Branch (loc, omega, cD', pat'', e')

(*
  | Ext.Comp.BranchBox (loc, cD, pat) ->
    (* Context Declarations are part of cD *)
    (* bp: collecting fcvars used for scope checking *)
    let empty_fcvars = [] in
    let (omega, delta', _ctx_vars', cvars', fcvars1)  =
      index_mctx (CVar.create()) empty_fcvars delta in
    let (pat', fcvars, fvars) =
      (* patterns should be linear in fvars; they may be non-linear in fcvars *)
      index_pattern  mvars' fcvars1 pat in
    let cvars_all        = CVar.append cvars' cvars in
      Apx.Comp.BranchBox (loc, delta', pat')
*)

  (* The subsequent two cases are only relevant for the old syntax;
     they are redundant in the new syntax *)
  | Ext.Comp.BranchBox(loc, delta, (psi1, pattern, Some (a, psi))) ->
    let _ = dprint (fun () -> "index_branch - OBSOLETE CASE IN NEW SYNTAX") in
    let empty_fcvars = [] in
    let fcvars' = begin match get_ctxvar psi1 with
                     | None -> empty_fcvars
                     | Some psi_name -> FCV psi_name :: empty_fcvars
                    end in

    let (omega, delta', cvars1, ((fcvs1, _ ) as fcvars1))  =
      index_mctx  cvars (fcvars', not term_closed) delta in
    let _ctxOpt1 =  begin match get_ctxvar psi1 with
                   | None -> None
                   | Some psi_name ->
		       if lookup_fv fcvs1 (FCV psi_name) then
			 Some (Apx.LF.CtxName psi_name)
		       else
			 raise (Error (loc, UnboundCtxName  psi_name))
                   end in
    let (psi1', bvars, fcvars2)  = index_dctx cvars1 (BVar.create ()) fcvars1 psi1 in
    let (m'opt, fcvars3)       = match pattern with
                                     | Ext.Comp.EmptyPattern -> (None, fcvars2)
                                     | Ext.Comp.NormalPattern (m, e) ->
                                         let (m', fcvars3) = index_term cvars1 bvars fcvars2 m in
                                           (Some m', fcvars3)
    in
    let (psi', _bvars, fcvars4)   = index_dctx cvars1 (BVar.create ()) fcvars3 psi in
    (* _bvars = bvars *)
    let (a', (fcvars5, _))        = index_typ cvars1 bvars fcvars4 a in

    let cvars_all        = CVar.append cvars1 cvars in

    let fcvars6 = List.append fcvars5 fcvars in

    let pattern' =
      match (pattern, m'opt) with
        | (Ext.Comp.EmptyPattern, None) -> Apx.Comp.EmptyPattern
        | (Ext.Comp.NormalPattern (_, e), Some m') ->
	    Apx.Comp.NormalPattern (m', index_exp cvars_all vars (fcvars6, term_closed) e)
    in
      Apx.Comp.BranchBox (loc, omega, delta', (psi1', pattern', Some (a', psi')))

  | Ext.Comp.BranchBox (loc, delta, (psi, pattern, None)) ->
    let _ = dprint (fun () -> "index_branch - OBSOLETE CASE IN NEW SYNTAX") in
    let empty_fcvars = [] in
    let _ = dprint (fun () -> "index_branch") in
    let fcvars' = begin match get_ctxvar psi with
                     | None -> empty_fcvars
                     | Some psi_name -> FCV psi_name :: empty_fcvars
                    end in

    let (omega, delta', cvars', ((fcvars1, _ ) as fcvs1))  =
      index_mctx cvars (fcvars', not term_closed) delta in
    (* let ctxOpt = begin match get_ctxvar psi with
                   | None -> None
                   | Some psi_name ->
		       if lookup_fv fcvars1 (FCV psi_name) then
			 Some (Apx.LF.CtxName psi_name)
		       else
			 raise (Error (loc, UnboundCtxName  psi_name))
                   end in
    *)
    let (psi1', bvars, fcvars2)    = index_dctx cvars' (BVar.create ()) fcvs1 psi in

      begin match pattern with
        | Ext.Comp.EmptyPattern ->
            Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.EmptyPattern, None))

        | Ext.Comp.NormalPattern (m, e)  ->
            let (m', (fcvars3, _))     = index_term cvars' bvars fcvars2 m in
            let cvars_all        = CVar.append cvars' cvars in
            let fcvars4 = List.append fcvars3 fcvars in
            let e'               = index_exp cvars_all vars (fcvars4, term_closed) e in
              Apx.Comp.BranchBox (loc, omega, delta', (psi1', Apx.Comp.NormalPattern (m', e'), None))

      end
(*  | Ext.Comp.EmptyBranch (loc, delta, pat) ->
    let empty_fcvars = [] in
(*      if containsEmptyPat pat then  *)
    let (omega, delta', ctx_vars', mvars', fcvars1)  =
      index_mctx ctx_vars' (CVar.create()) empty_fcvars delta in
    let (pat', fcvars, fcvars) = index_pattern ctx_vars' mvars' (fcvars1 ,
                                                                empty_fcvars) pat
    in
*)


let comptypdef (cT, cK) =
  let cK' = index_compkind (CVar.create ())  ([], term_closed) cK in
  let rec unroll cK cvars = begin match cK with
    | Apx.Comp.Ctype _ -> cvars
    | Apx.Comp.PiKind (loc, (cdecl, dep), cK) ->
        let cvars' = match cdecl with
                       | Apx.LF.MDecl (u ,_a, _psi) -> CVar.extend cvars (CVar.mk_entry (CVar.MV u))
                       | Apx.LF.PDecl (p ,_a, _psi) -> CVar.extend cvars (CVar.mk_entry (CVar.PV p))
                       | Apx.LF.CDecl (psi,_sW) -> CVar.extend cvars (CVar.mk_entry (CVar.CV psi))
                      in
            unroll cK cvars'
   end in
   let (tau,_ ) = index_comptyp (unroll cK' (CVar.create ())) ([], term_closed) cT in
        (tau, cK')

let kind     = index_kind (CVar.create ()) (BVar.create ()) ([], term_closed)
let typ      = index_typ  (CVar.create ()) (BVar.create ()) ([], term_closed)
let schema   = index_schema
let compkind = index_compkind (CVar.create ())  ([], not term_closed)
let comptyp  tau =
  let (tau', _ ) = index_comptyp  (CVar.create ()) ([], not term_closed) tau in
    tau'

let exp      = fun vars -> fun e ->
(dprint (fun () -> "Indexing expression ... " );
 index_exp (CVar.create ()) vars ([], term_closed) e)
let exp'     = fun vars -> fun i -> index_exp' (CVar.create ()) vars ([], term_closed) i
