
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
  | MispacedOperator of Id.name
  | ParseError

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | MispacedOperator n ->
        Format.fprintf ppf ("Illegal use of operator %s.") (R.render_name n)

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
	       Format.fprintf ppf "Ill-formed computation-level type."
      | ParseError ->
        Format.fprintf ppf "Unable to parse operators into valid structure"))


type free_cvars = Id.name

type fcvars = free_cvars list * bool

let rec fcvarsToString fcvars = match fcvars with
  | [] -> ""
  | m :: fcvars -> ", FMV " ^ R.render_name m ^ fcvarsToString fcvars

let rec lookup_fv fvars m = begin  match (fvars, m) with
     ([], _ ) -> false
  | (n :: fvars' , m) ->
      if n = m then true
      else lookup_fv fvars' (m)
end

let rec get_ctxvar psi = match psi with
  | Ext.LF.Null -> None
  | Ext.LF.CtxVar (_loc, psi_name) -> Some psi_name
  | Ext.LF.DDec (psi, _ ) -> get_ctxvar psi
  | Ext.LF.CtxHole -> None


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

  | Ext.LF.AtomTerm(loc, n) ->
      begin match n with
        | Ext.LF.TList(loc2,nl) ->
            let Ext.LF.Root(_, Ext.LF.Name(_, a), s') = shunting_yard nl in
            index_typ cvars bvars fvars (Ext.LF.Atom (loc, a, s')) 
        | Ext.LF.Root(loc2, Ext.LF.Name(_,name), sp) -> 
            index_typ cvars bvars fvars (Ext.LF.Atom(loc2, name, sp))
      end

and locOfNormal = function
  | Ext.LF.Lam(l,_,_) -> l
  | Ext.LF.Root(l,_,_) -> l
  | Ext.LF.Tuple(l,_) -> l
  | Ext.LF.Ann(l,_,_) -> l
  | Ext.LF.TList(l,_) -> l
  | Ext.LF.LFHole l -> l

(* Adaptation of Dijkstra's 'shunting yard' algorithm for
 * parsing infix, postfix, and prefix operators from a list
 *
 * Preconditions:
 *    - All operators (constructors and typs) are contained in the store
 * 
 * Post: List of normals is converted to a Root with a head and a spine 
 *        - Head contains the name of the atom term that is to be indexed
 * 
*)
and shunting_yard (l : Ext.LF.normal list) : Ext.LF.normal =
  
  let get_pragma = function
    | Ext.LF.Root(_, Ext.LF.Name(_, name), Ext.LF.Nil) 
    | Ext.LF.Root(_, Ext.LF.PVar(_, name, _), Ext.LF.Nil)
    | Ext.LF.Root(_, Ext.LF.MVar(_, name, _), Ext.LF.Nil) -> 
      let Some x = Store.OpPragmas.getPragma name in x
  in
  let pragmaExists = function
    | Ext.LF.Root(_, Ext.LF.Name(_, name), Ext.LF.Nil) 
    | Ext.LF.Root(_, Ext.LF.PVar(_, name, _), Ext.LF.Nil)
    | Ext.LF.Root(_, Ext.LF.MVar(_, name, _), Ext.LF.Nil) -> 
      let args_expected = 
        try Typ.args_of_name name with _ -> 
        try Term.args_of_name name with _ -> 
          -1 in
        (Store.OpPragmas.pragmaExists name) && (args_expected > 0)
    | _ -> false
  in
  let lte (p : Store.OpPragmas.fixPragma) (o : Store.OpPragmas.fixPragma) : bool = 
    let p_p = p.Store.OpPragmas.precedence in
    let o_p = o.Store.OpPragmas.precedence in
    let p_a = match p.Store.OpPragmas.assoc with
      | Some a -> a
      | None -> !Store.OpPragmas.default in
    p_p < o_p ||
    (p_p = o_p && p_a = Ext.Sgn.Left)
(*      p.Store.OpPragmas.precedence < o.Store.OpPragmas.precedence ||
    (p.Store.OpPragmas.precedence = o.Store.OpPragmas.precedence && 
      ((o.Store.OpPragmas.assoc = None && !Store.OpPragmas.default = Ext.Sgn.Left) ||
       o.Store.OpPragmas.assoc = Some Ext.Sgn.Left))
 *)  in
  let rec normalListToSpine : Ext.LF.normal list -> Ext.LF.spine = function
    | [] -> Ext.LF.Nil
    | h::t -> Ext.LF.App(locOfNormal h, h, normalListToSpine t)
  in
  let rec parse : int * Ext.LF.normal list * (int * Ext.LF.normal) list * (int * Store.OpPragmas.fixPragma) list -> Ext.LF.normal = function
  | i, Ext.LF.TList(_, nl) :: t, y, z -> let h = parse (0,nl, [], []) in parse(i+1, t,(i,h)::y,z)
  | i, Ext.LF.Lam (loc, name, Ext.LF.TList(_, nl)) :: t, y, z -> 
    let h = parse (0, nl, [], []) in 
    parse(i+1, t, (i, Ext.LF.Lam(loc, name, h))::y, z)
  | i, h::t, exps, [] when pragmaExists h -> 
    let p = get_pragma h in
    parse(i+1, t, exps, [(i, p)])
  | i, h::t, exps, (x, o)::os when pragmaExists h -> 
    begin
      let p = get_pragma h in 
      if lte p o then begin match o.Store.OpPragmas.fix with
        | Ext.Sgn.Prefix ->
          let args_expected = 
            try Typ.args_of_name o.Store.OpPragmas.name with _ -> 
            try Term.args_of_name o.Store.OpPragmas.name with _ -> 
              failwith ("Unknown operator " ^ (o.Store.OpPragmas.name.Id.string_of_name)) in
          let (ops, es) = take args_expected exps in
          let loc = 
            if args_expected > 0 then 
              try let (_,x) = List.hd ops in locOfNormal x 
              with _ -> raise (Error(locOfNormal h, MispacedOperator o.Store.OpPragmas.name))
            else Syntax.Loc.ghost in
          let ops = List.map (fun (_,x) ->x) ops in
          let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name), normalListToSpine ops) in
          parse(i+1, h::t, (i, e')::es, os)

        | Ext.Sgn.Postfix -> 
          let (_, e)::es = exps in
          let loc = locOfNormal e in
          let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name), Ext.LF.App(loc, e, Ext.LF.Nil)) in
          parse(i+1, h::t, (i, e')::es, os)

        | Ext.Sgn.Infix -> 
          let (_, e2)::(_, e1)::es = exps in
          let loc = locOfNormal e1 in
          let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name), normalListToSpine [e1; e2]) in
          parse(i+1, h::t, (i, e')::es, os) 

      end else
        parse(i+1, t, exps, (i, p)::(x, o)::os)
    end
  | i, h ::t, y, z -> parse(i+1, t, (i, h)::y, z)
  | _, [], y, z -> 
    reconstruct (y, z)

  and reconstruct : (int * Ext.LF.normal) list * (int * Store.OpPragmas.fixPragma) list -> Ext.LF.normal = function
  | [(_, e)], [] -> e
  | exps, (i, o)::os when (o.Store.OpPragmas.fix = Ext.Sgn.Prefix) ->
    let args_expected = 
      try Typ.args_of_name o.Store.OpPragmas.name with _ -> 
      try Term.args_of_name o.Store.OpPragmas.name with _ -> 
        failwith ("Unknown operator " ^ (o.Store.OpPragmas.name.Id.string_of_name)) in
    let (ops, es) = take args_expected exps in
    let loc = 
      if args_expected > 0 then 
        try let (_,x) = List.hd ops in locOfNormal x
        with _ -> raise (Error(Syntax.Loc.ghost, MispacedOperator o.Store.OpPragmas.name))
      else Syntax.Loc.ghost in
    if List.for_all (fun (x, _) -> x > i) ops then begin
      let ops = List.map (fun (_, x) -> x) ops in
      let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name), normalListToSpine ops) in
      reconstruct((i, e')::es, os) end
    else raise (Error(loc, MispacedOperator o.Store.OpPragmas.name))

  | (i2, e2)::(i1, e1)::es, (i, o)::os when o.Store.OpPragmas.fix = Ext.Sgn.Infix ->
    let loc = locOfNormal e1 in
    if i2 > i && i > i1 then begin
      let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name), normalListToSpine [e1; e2]) in
      reconstruct((i, e')::es, os) end
    else raise (Error(loc, MispacedOperator o.Store.OpPragmas.name))

  | (i1, e)::es, (i, o)::os when o.Store.OpPragmas.fix = Ext.Sgn.Postfix -> 
    let loc = locOfNormal e in
    if i > i1 then begin
      let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name), Ext.LF.App(loc, e, Ext.LF.Nil)) in
      reconstruct((i, e')::es, os) end
    else raise (Error(loc, MispacedOperator o.Store.OpPragmas.name))

  | l, [] ->     
    let l' = List.rev l in
    let (_, Ext.LF.Root(loc, h, Ext.LF.Nil)) :: t = l' in 
    let t = List.map (fun (_,x) -> x) t in
    Ext.LF.Root(loc, h, normalListToSpine t)

  | a, b ->
    failwith "Error in indexing"

  and take = fun i l ->
    let rec aux n l c = match l with
      | h::t when n > 0 -> aux (n-1) t (h::c)
      | _  -> (c, l)
  in aux i l []
in try parse (0, l, [], []) 
  with 
  | (Error _) as e -> raise e
  | _ -> begin 
    let l = match List.hd l with 
      | Ext.LF.Lam(l, _, _) | Ext.LF.Root(l, _, _) | Ext.LF.Tuple(l, _)
      | Ext.LF.Ann(l, _, _) | Ext.LF.TList(l, _)   | Ext.LF.NTyp(l, _) | Ext.LF.LFHole l-> l
    in raise (Error(l, ParseError)) end

and index_typ_rec cvars bvars fvars = function
  | Ext.LF.SigmaLast(n, a) ->
      let (last, fvars') = index_typ cvars bvars fvars a in
        (Apx.LF.SigmaLast (n,last) , fvars')
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

  | Ext.LF.LFHole loc -> (Apx.LF.LFHole loc, fvars)


  | Ext.LF.Ann (loc, m, a) ->
    let (a', fvars') = index_typ cvars bvars fvars a in
    let (m', fvars'') = index_term cvars bvars fvars' m in
    (Apx.LF.Ann (loc, m', a'), fvars'')

  | Ext.LF.TList (loc, nl)->
    index_term cvars bvars fvars (shunting_yard nl )

and index_proj = function
  | Ext.LF.ByPos k -> Apx.LF.ByPos k
  | Ext.LF.ByName n -> Apx.LF.ByName n

and index_head cvars bvars ((fvars, closed_flag) as fvs) = function
  | Ext.LF.Name (_, n) ->
      let _ = dprint (fun () -> "Indexing name " ^ n.string_of_name) in
      begin try
        (Apx.LF.BVar (BVar.index_of_name bvars n) , fvs)
      with Not_found -> try
        (Apx.LF.Const (Term.index_of_name n) , fvs)
      with Not_found ->
        dprint (fun () -> "FVar " ^ n.string_of_name );
        (Apx.LF.FVar n , fvs)
      end

  | Ext.LF.Proj(loc, h, k) ->
      let (h', fvs') = index_head cvars bvars fvs h in
        (Apx.LF.Proj(h', index_proj k), fvs')

  | Ext.LF.PVar (loc, p, s) ->
      if lookup_fv fvars p then
        let (s', (fvars', closed_flag))  = index_sub cvars bvars fvs s in
          (Apx.LF.FPVar (p, s') , (fvars' , closed_flag))
      else
        begin try
          let offset = CVar.index_of_name cvars p in
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
              (Apx.LF.FPVar (p, s') , (p :: fvars' , closed_flag))
        end

  | Ext.LF.Hole _loc ->
      (Apx.LF.Hole , fvs)

  | Ext.LF.MVar (loc, u, s) ->
      if lookup_fv fvars (u) then
        let (s', fvs')     = index_sub cvars bvars fvs s in
          (Apx.LF.FMVar (u, s') , fvs')
      else
        begin try
          let offset = CVar.index_of_name cvars u in
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
              (Apx.LF.FMVar (u, s') , (u :: fvars' , closed_flag))
        end

  (* | Ext.LF.SVar (loc, n, _sigma) -> *)
  (*     let _        = dprint (fun () -> "Indexing head : SVar " ^ n.string_of_name) in *)
  (*       raise (Error (loc, UnboundName n)) *)

and index_spine cvars bvars fvars = function
  | Ext.LF.Nil ->
      (Apx.LF.Nil , fvars)

  | Ext.LF.App (_, m, s) ->
    match m with
      | Ext.LF.TList(loc, nl) -> 
        let n = shunting_yard nl in
        index_spine cvars bvars fvars (Ext.LF.App (loc, n, s))
      | _ ->
        let (m', fvars')  = index_term  cvars bvars fvars m in
        let (s', fvars'') = index_spine cvars bvars fvars' s in
          (Apx.LF.App (m', s') , fvars'')

and index_sub cvars bvars ((fvs, closed_flag )  as fvars) =
  let to_head_or_obj tM = match tM with
    | Apx.LF.Root (_,(Apx.LF.BVar _ as h), Apx.LF.Nil)
    | Apx.LF.Root (_,(Apx.LF.PVar _ as h), Apx.LF.Nil)
    | Apx.LF.Root (_,(Apx.LF.Proj _ as h), Apx.LF.Nil) -> Apx.LF.Head h
    | _ -> Apx.LF.Obj tM
  in 
  function
  | Ext.LF.RealId -> (Apx.LF.RealId, fvars)
  | Ext.LF.Id loc -> (Apx.LF.Id, fvars)

  | Ext.LF.Dot (_, s, Ext.LF.Head h) ->
      let (s', fvars')  = index_sub cvars bvars fvars s  in
      let (h', fvars'') = index_head cvars bvars fvars' h in
        (Apx.LF.Dot (Apx.LF.Head h', s') , fvars'')

  | Ext.LF.Dot (_, s, Ext.LF.Normal m) ->
      let (s', fvars')  = index_sub cvars bvars fvars s  in
      let (m', fvars'') = index_term cvars bvars fvars' m in
        (Apx.LF.Dot (to_head_or_obj m', s') , fvars'')

  | Ext.LF.EmptySub _ ->
      (Apx.LF.EmptySub, fvars)

  | Ext.LF.SVar (loc, u, s) ->
      if lookup_fv fvs (u) then
        let (s', fvs')     = index_sub cvars bvars fvars s in
          (Apx.LF.FSVar (u, s') , fvs')
      else
        begin try
          let offset = CVar.index_of_name cvars u in
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
              (Apx.LF.FSVar (u, s') , (u :: fvars' , closed_flag))
        end


let index_decl cvars bvars fvars = function
  | (Ext.LF.TypDecl(x, a)) ->
    let (a', fvars') = index_typ cvars bvars fvars a in
    let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDecl (x,a'), bvars', fvars')
  | (Ext.LF.TypDeclOpt x) ->
    let bvars'       = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDeclOpt x, bvars', fvars)

let rec index_dctx cvars bvars ((fvs, closed) as fvars) = function
  | Ext.LF.CtxHole     -> (Apx.LF.CtxHole, bvars, fvars)
  | Ext.LF.Null        -> (Apx.LF.Null , bvars, fvars)

  | Ext.LF.CtxVar (loc, psi_name)  ->
      if lookup_fv fvs (psi_name) then
	(Apx.LF.CtxVar (Apx.LF.CtxName psi_name), bvars, (fvs, closed))
      else
	begin try
          let offset = CVar.index_of_name cvars psi_name in
            (Apx.LF.CtxVar (Apx.LF.CtxOffset offset) , bvars, fvars)
	with Not_found ->
	if closed then
	     raise (Error (loc, UnboundName psi_name))
	else
	  (Apx.LF.CtxVar (Apx.LF.CtxName psi_name), bvars, ((psi_name :: fvs),  closed))
	end
  | Ext.LF.DDec (psi, decl) ->
      let (psi', bvars', fvars')    = index_dctx cvars bvars fvars psi in
      let (decl', bvars'', fvars'') = index_decl cvars bvars' fvars' decl in
        (Apx.LF.DDec (psi', decl'), bvars'', fvars'')

let index_svar_class = function
  | Ext.LF.Ren -> Apx.LF.Ren
  | Ext.LF.Subst -> Apx.LF.Subst

let rec index_ctx cvars bvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty , bvars, fvars)

  | Ext.LF.Dec (psi, dec) ->
      let (psi', bvars', fvars')   = index_ctx  cvars bvars fvars psi in
      let (dec', bvars'', fvars'') = index_decl cvars bvars' fvars' dec in
        (Apx.LF.Dec (psi', dec'), bvars'', fvars'')

let index_cltyp' cvars bvars fvars = function
  | Ext.LF.MTyp a -> 
    let (a, fvars) = index_typ  cvars bvars fvars a in
    (Apx.LF.MTyp a, fvars)
  | Ext.LF.PTyp a ->
    let (a, fvars) = index_typ cvars bvars fvars a in
    (Apx.LF.PTyp a, fvars)
  | Ext.LF.STyp (cl, phi) ->
    let (phi', _bvars', fvars) = index_dctx cvars (BVar.create ()) fvars phi in
    (Apx.LF.STyp (index_svar_class cl, phi'), fvars)

let index_cltyp cvars fvars = function
  | Ext.LF.ClTyp (loc, cl, psi) ->
      let (psi', bvars', fvars') = index_dctx cvars (BVar.create ()) fvars psi in
      let (cl', fvars'')          = index_cltyp'  cvars bvars' fvars' cl in
        (Apx.LF.ClTyp (cl', psi'), cvars, fvars'')
  | Ext.LF.CTyp (loc, schema_name) ->
      let schema_cid    = Schema.index_of_name schema_name in
      (Apx.LF.CTyp schema_cid, cvars, fvars)

let cltyp_to_cvar n _ = n

let index_cdecl cvars fvars = function
  | Ext.LF.Decl(u, cl, dep) ->
    let (cl', cvars, fvars') = index_cltyp cvars fvars cl in
    let cvars'               = CVar.extend cvars (CVar.mk_entry (cltyp_to_cvar u cl)) in
    let dep = match dep with Ext.LF.Maybe -> Apx.LF.Maybe | Ext.LF.No -> Apx.LF.No in
    (Apx.LF.Decl(u, cl', dep), cvars', fvars')

let rec index_mctx cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty, Apx.LF.Empty, cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (omega', delta', cvars', fvars') = index_mctx cvars fvars delta in
      let (cdec', cvars'', fvars'') = index_cdecl cvars' fvars' cdec in
      (omega', Apx.LF.Dec (delta', cdec'), cvars'', fvars'')


(* Records are not handled in a general manner
 * We need to change the datatype for typ_rec to be typ_decl ctx
 *)
let rec index_typrec cvars bvars fvars = function
  | Ext.LF.SigmaLast (n, last_a) ->
      let (last, fvars') = index_typ cvars bvars fvars last_a in
      (Apx.LF.SigmaLast(n, last), fvars')

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
        ((l, Apx.Comp.CObj (cPsi)), fcvars')

  | Ext.Comp.MetaObjAnn (l, cpsi, m) ->
      let (cPsi, bvars, fcvars') = index_dctx cvars (BVar.create ()) fcvars cpsi in
      let (m', fcvars'') = index_term cvars  bvars fcvars' m in
        ((l,Apx.Comp.ClObj (cPsi, Apx.Comp.MObj m')), fcvars'')

  | Ext.Comp.MetaSObjAnn (l, cpsi, m) ->
      let (cPsi, bvars, fcvars') = index_dctx cvars (BVar.create ()) fcvars cpsi in
      let (m', fcvars'') = index_sub cvars  bvars fcvars' m in
        ((l,Apx.Comp.ClObj (cPsi, Apx.Comp.SObj m')), fcvars'')

and index_meta_spine cvars fcvars = function
  | Ext.Comp.MetaNil ->
      (Apx.Comp.MetaNil , fcvars)

  | Ext.Comp.MetaApp (m, s) ->
      let (m', fcvars')  = index_meta_obj  cvars fcvars m in
      let (s', fcvars'') = index_meta_spine cvars fcvars' s in
        (Apx.Comp.MetaApp (m', s') , fcvars'')

let index_meta_typ cvars fcvars = function
  | Ext.Comp.MetaTyp (loc, a, psi) ->
        let (psi', bvars', fcvars') = index_dctx cvars (BVar.create ()) fcvars psi in
        let (a', fcvars'' )         = index_typ cvars bvars' fcvars' a   in
        ((loc,Apx.LF.ClTyp (Apx.LF.MTyp a', psi')), fcvars'')

 | Ext.Comp.MetaSubTyp (loc, phi, psi)    ->
      let (psi', _ , fcvars1 ) = index_dctx cvars (BVar.create ()) fcvars psi in
      let (phi', _ , fcvars2 ) = index_dctx cvars (BVar.create ()) fcvars1 phi in
        ((loc,Apx.LF.ClTyp (Apx.LF.STyp (Apx.LF.Subst,phi'), psi')), fcvars2)



let rec index_compkind cvars fcvars = function
  | Ext.Comp.Ctype loc -> Apx.Comp.Ctype loc

  | Ext.Comp.PiKind (loc, cdecl, cK) ->
      let (cdecl', cvars', fcvars') = index_cdecl cvars fcvars cdecl in
      let cK' = index_compkind cvars' fcvars' cK in
        Apx.Comp.PiKind (loc, cdecl', cK')


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
  | Ext.Comp.TypBox (loc, mU) ->
      let (mU', fcvars') = index_meta_typ cvars fcvars mU in
        (Apx.Comp.TypBox (loc, mU'), fcvars')

  | Ext.Comp.TypArr (_loc, tau, tau') ->
      let (tau1, fcvars1) = index_comptyp cvars fcvars tau in
      let (tau2, fcvars2) = index_comptyp cvars fcvars1 tau' in
      (Apx.Comp.TypArr (tau1, tau2), fcvars2)

  | Ext.Comp.TypCross (_loc, tau, tau') ->
      let (tau1, fcvars1) = index_comptyp cvars fcvars tau in
      let (tau2, fcvars2) = index_comptyp cvars fcvars1 tau' in
	(Apx.Comp.TypCross (tau1, tau2), fcvars2)

  | Ext.Comp.TypPiBox (_loc, cdecl, tau)    ->
      let (cdecl', cvars', fcvars1) = index_cdecl cvars fcvars cdecl in
      let (tau', fcvars2) = index_comptyp cvars' fcvars1 tau in
      (Apx.Comp.TypPiBox (cdecl', tau'), fcvars2)

  | Ext.Comp.TypBool -> (Apx.Comp.TypBool, fcvars)

  | Ext.Comp.TypInd (tau) ->
      let (tau1, fcvars1) = index_comptyp cvars fcvars tau in
	(Apx.Comp.TypInd tau1, fcvars1)

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
        Apx.Comp.Var (loc, Var.index_of_name vars x)
      with Not_found -> try
        Apx.Comp.Const (loc,Comp.index_of_name x)
      with Not_found -> try
        Apx.Comp.DataConst (loc, CompConst.index_of_name x)
      with Not_found -> try
        Apx.Comp.DataDest (loc, CompDest.index_of_name x)
      with Not_found ->
        raise (Error (loc, UnboundCompName x))
      end
  | Ext.Comp.DataConst (loc, c) ->
    begin
      try
	Apx.Comp.DataConst (loc, CompConst.index_of_name c)
      with Not_found -> try
        Apx.Comp.DataDest (loc, CompDest.index_of_name c)
      with Not_found -> raise (Error (loc, UnboundCompConstName  c))
    end
  | Ext.Comp.Apply (loc, i, e) ->
      let i' = index_exp' cvars vars fcvars i in
      let e' = index_exp  cvars vars fcvars e in
        Apx.Comp.Apply (loc, i', e')

  | Ext.Comp.BoxVal (loc, m0) ->
      let (mobj', _ )  = index_meta_obj cvars fcvars m0 in
        Apx.Comp.BoxVal (loc, mobj')

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
    let (mO', fcvars1) = index_meta_obj cvars fcvars mO in
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
                          psi_name :: empty_fcvars
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
                          psi_name :: empty_fcvars
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
                          psi_name :: empty_fcvars
                    end in

    let (omega, cD', cvars1, fcvars1)  =
      index_mctx (CVar.create()) (fcvars', not term_closed) cD in
    let (mO', (fcvars2, _)) = index_meta_obj cvars1 fcvars1 mO in
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


let comptypdef (cT, cK) =
  let cK' = index_compkind (CVar.create ())  ([], term_closed) cK in
  let rec unroll cK cvars = begin match cK with
    | Apx.Comp.Ctype _ -> cvars
    | Apx.Comp.PiKind (loc, Apx.LF.Decl(u, ctyp,dep), cK) ->
        let cvars' = CVar.extend cvars (CVar.mk_entry u) in
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

let hexp = fun cvars vars e ->
  if Store.CVar.length cvars = 0 then
    exp vars e
  else
    index_exp cvars vars ([], not term_closed) e
