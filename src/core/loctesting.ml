open Syntax.Ext
open Locs

module R = Store.Cid.DefaultRenderer

let rec store_locs (d : Sgn.decl) = match d with
| Sgn.Const (loc, n, _) -> Locs.add loc (Locs.mk_entry ("Const " ^ R.render_name n))
| Sgn.Typ (loc, n, _) -> Locs.add loc (Locs.mk_entry ("Typ " ^ R.render_name n))
(* | Sgn.CompTyp (loc, n, _) -> 
| Sgn.CompCotyp (loc, n, _) ->
| Sgn.CompConst (loc, n, _) ->
| Sgn.CompDest (loc, n, _) ->
| Sgn.CompTypAbbrev (loc, n, _, _) ->
| Sgn.Schema (loc, n, _) -> *)
| Sgn.Rec (_, recs) -> store_recs recs
| _ -> ()

and store_recs (recs : Comp.rec_fun list) = match recs with
| [] -> ()
| Comp.RecFun(_, _, _, _, e)::t -> store_chks e;
	store_recs t

and store_chks (e : Comp.exp_chk) = match e with
| Comp.Syn (loc, e') -> 
	Locs.add loc (Locs.mk_entry ("Syn")); 
	store_syns e'
| Comp.Fun (loc, n, e') -> 
	Locs.add loc (Locs.mk_entry ("Fun " ^ R.render_name n)); 
	store_chks e'
| Comp.MLam  (loc, (n, _), e') -> 
	Locs.add loc (Locs.mk_entry ("MLam " ^ R.render_name n)); 
	store_chks e'
| Comp.Box (loc, mO) -> 
	Locs.add loc (Locs.mk_entry ("Box")); 
	store_metaObj mO
| Comp.Case (loc, _, e', blist) -> 
	Locs.add loc (Locs.mk_entry ("Case")); 
	store_syns e'; 
	store_branches blist
| _ -> ()

and store_syns (e : Comp.exp_syn) = match e with
| Comp.Var (loc, n) -> Locs.add loc (Locs.mk_entry ("Var " ^ R.render_name n))
| Comp.Const (loc, n) -> Locs.add loc (Locs.mk_entry ("Const " ^ R.render_name n))
| Comp.Apply (loc, e1, e2) -> 
	Locs.add loc (Locs.mk_entry ("Apply"));
	store_syns e1;
	store_chks e2
| Comp.MApp (loc, e', mO) ->
	Locs.add loc (Locs.mk_entry ("MApp"));
	store_syns e';
	store_metaObj mO
| Comp.BoxVal (loc, m0) ->
	Locs.add loc (Locs.mk_entry ("BoxVal"));
	store_metaObj m0
| _ -> ()

and store_metaObj (mO : Comp.meta_obj) = match mO with
| Comp.MetaObj (loc, _, norm) -> 
	Locs.add loc (Locs.mk_entry ("MetaObj"));
	store_normal norm
| Comp.MetaObjAnn (loc, _, norm) -> 
	Locs.add loc (Locs.mk_entry ("MetaObjAnn"));
	store_normal norm
| _ -> ()

and store_branches (blist : Comp.branch list) = match blist with
| [] -> ()
| hd::tl ->
	store_branch hd;
	store_branches tl

and store_branch (b : Comp.branch) = match b with
| Comp.Branch (loc, _, Comp.PatMetaObj(loc', mO), e') -> 
	Locs.add loc (Locs.mk_entry ("Branch"));
	Locs.add loc' (Locs.mk_entry ("PatMetaObj"));
	store_metaObj mO;
	store_chks e'
| _ -> ()

and store_normal (norm : LF.normal) = match norm with
| LF.Lam (loc, n, norm') ->
	Locs.add loc (Locs.mk_entry ("Lam " ^ R.render_name n));
	store_normal norm';
| LF.Root (loc, h, s) -> 
	Locs.add loc (Locs.mk_entry ("Root"));
	store_head h;
	store_spine s;
| _ -> ();

and store_head (h : LF.head) = match h with
| LF.Name (loc, n) -> Locs.add loc (Locs.mk_entry ("Name " ^ R.render_name n))
| LF.MVar (loc, n, _) -> Locs.add loc (Locs.mk_entry ("MVar " ^ R.render_name n))
| _ -> ();

and store_spine (s : LF.spine) = match s with
| LF.Nil -> ()
| LF.App (loc, norm, s') ->
	Locs.add loc (Locs.mk_entry ("App"));
	store_normal norm;
	store_spine s'
