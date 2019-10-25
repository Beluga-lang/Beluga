
module I = Syntax.Int
module E = Syntax.Ext

open Store

(** Adds one entry to a LF bound variables list. *)
let (++) bvars x = BVar.(extend bvars (mk_entry x))

(** Adds one entry to a contextual variables list. *)
let (+++) cvars x = CVar.(extend cvars (mk_entry x))

(** Looks up an LF bound variable. *)
let (!) bvars x = BVar.get bvars x

(** Looks up a contextual variable. *)
let (!!) cvars x = CVar.get cvars x

module LF = struct
  let mctx cD = assert false
  let mfront cvars mf = assert false

  let dctx cvars cPsi = assert false
end

(** Adds one entry to a computational variables list. *)
let (++++) vars x = Var.(extend vars (mk_entry x))

(** Looks up one computation variable. *)
let (!!!) vars x = Var.get vars x

module Comp = struct
  let meta_obj cvars (loc, cM) = (loc, LF.mfront cvars cM)

  let pattern cvars vars = function
    | I.Comp.PatEmpty (loc, cPsi) ->
       let cPsi' = LF.dctx cvars cPsi in
       E.Comp.(PatMetaObj (loc, (loc, ClObj (cPsi', E.LF.(term (PatEmpty loc))))))

  let rec exp cvars vars = function
    | I.Comp.Syn (loc, i) ->
       let i' = exp' cvars vars i in
       E.Comp.Syn (loc, i')
    | I.Comp.Fn (loc, x, e) ->
       let e' = exp cvars (vars ++++ x) e in
       E.Comp.Fn (loc, x, e')
    | I.Comp.Fun (loc, fbs) ->
       assert false
    | I.Comp.MLam (loc, x, e) ->
       let e' = exp (cvars +++ x) vars e in
       E.Comp.MLam (loc, x, e')
    | I.Comp.Pair (loc, e1, e2) ->
       let e1' = exp cvars vars e1 in
       let e2' = exp cvars vars e2 in
       E.Comp.Pair (loc, e1', e2')
    | I.Comp.LetPair (loc, i, (x, y, e)) ->
       let i' = exp' cvars vars i in
       let e' = exp cvars (vars ++++ x ++++ y) e in
       E.Comp.LetPair (loc, i', (x, y, e'))
    | I.Comp.Let (loc, i, (x, e)) ->
       let i' = exp' cvars vars i in
       let e' = exp cvars (vars ++++ x) e in
       E.Comp.Let (loc, i', (x, e'))
    | I.Comp.Box (loc, mObj) ->
       let mObj' = meta_obj cvars mObj in
       E.Comp.Box (loc, mObj')
    | I.Comp.Case (loc, prag, i, bs) ->
       let i' = exp' cvars vars i in
       let bs' = branches bs in
       E.Comp.Case (loc, prag, i', bs')
    | I.Comp.Hole (loc, _, name) ->
       E.Comp.Hole (loc, HoleId.option_of_name name)

  and exp' cvars vars = function
    | I.Comp.Var (loc, k) ->
       let open Var in
       let x = (!!! vars k).name in
       E.Comp.Name (loc, x)
    | I.Comp.DataConst (loc, cid) ->
       let x = Cid.CompConst.((get cid).name) in
       E.Comp.Name (loc, x)
    | I.Comp.Obs (loc, e, t, cid) ->
       let x = Cid.CompDest.((get cid).name) in
       let e' = exp cvars vars e in
       E.Comp.Apply (loc, E.Comp.Name (loc, x), e')
    | I.Comp.Const (loc, cid) ->
       let x = Cid.Comp.((get cid).name) in
       E.Comp.Name (loc, x)
    | I.Comp.Apply (loc, i, e) ->
       let i' = exp' cvars vars i in
       let e' = exp cvars vars e in
       E.Comp.Apply (loc, i', e')
    | I.Comp.MApp (loc, i, (loc', mf)) ->
       let i' = exp' cvars vars i in
       let mf' = LF.mfront cvars mf in
       E.Comp.Apply (loc, i', E.Comp.Box (loc', (loc', mf')))
    | I.Comp.AnnBox (cM, _cT) ->
       let cM' = meta_obj cvars cM in
       E.Comp.BoxVal (fst cM, cM')
    | I.Comp.PairVal (loc, i1, i2) ->
       let i1' = exp' cvars vars i1 in
       let i2' = exp' cvars vars i2 in
       E.Comp.PairVal (loc, i1', i2')

  and branches bs = List.map branch bs

  and branch = function
    | I.Comp.EmptyBranch (loc, cD, pat, _) ->
       let cD' = LF.mctx cD in
       let cvars = CVar.of_mctx cD in
       let pat' = pattern cvars (Var.create ()) pat in
       E.Comp.EmptyBranch (loc, cD', pat')

    | I.Comp.Branch (loc, cD, cG, pat, t, e) ->
       let vars = Var.of_gctx cG in
       let cvars = CVar.of_mctx cD in
       let pat' = pattern cvars vars pat in
       let e' = exp cvars vars e in
       E.Comp.Branch (loc, I.LF.Empty, pat', e')

  let thm cvars vars = assert false
end
