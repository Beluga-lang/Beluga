open Support

module I = Syntax.Int
module E = Syntax.Ext
module Loc = Syntax.Loc

open Store

(** Adds one entry to a LF bound variables list. *)
let (++) bvars x = BVar.(extend bvars (mk_entry x))

(** Adds one entry to a contextual variables list. *)
let (+++) cvars x = CVar.(extend cvars (mk_entry x))

(** Looks up an LF bound variable. *)
let (!) bvars x = BVar.( (get bvars x).name )

(** Looks up a contextual variable. *)
let (!!) cvars x = CVar.( (get cvars x).name )

module LF = struct
  let mctx cD = assert false
  let dctx cvars cPsi = assert false

  let rec normal cvars bvars : I.LF.normal -> E.LF.normal = function
    | I.LF.Lam (loc, x, tM) ->
       let tM' = normal cvars (bvars ++ x) tM in
       E.LF.Lam (loc, x, tM')
    | I.LF.Root (loc, tH, tS) ->
       let tH' = head loc cvars bvars tH in
       let tS' = spine cvars bvars tS in
       E.LF.Root (loc, tH', tS')
    | I.LF.LFHole (loc, _, name) ->
       E.LF.LFHole (loc, HoleId.option_of_name name)
    | I.LF.Clo (tM, s) ->
       Misc.not_implemented "[erase] [normal] Clo"
    | I.LF.Tuple (loc, t) ->
       let t' = tuple cvars bvars t in
       E.LF.Tuple (loc, t')

  and head loc cvars bvars : I.LF.head -> E.LF.head = function
    | I.LF.BVar k ->
       let x = ! bvars k in
       E.LF.Name (loc, x, None)
    | I.LF.Const cid ->
       let x = Cid.Term.( (get cid).name ) in
       E.LF.Name (loc, x, None)
    | I.LF.MMVar _ | I.LF.MPVar _ ->
       Error.violation "[erase] [head] not normal (encountered MMVar or MPVar)"
    | I.LF.MVar (v, s) ->
       let x = cvar cvars v in
       let s' = sub cvars bvars s in
       E.LF.Name (loc, x, Some s')
    | I.LF.PVar (k, s) ->
       let x = !! cvars k in
       let s' = sub cvars bvars s in
       (* XXX this will not print correctly because of the hash sign! -je *)
       E.LF.Name (loc, x, Some s')
    | I.LF.AnnH (h, _) -> head loc cvars bvars h
    | I.LF.Proj (h, k) -> (* the name of the projection, if any, is missing! -je *)
       let h' = head loc cvars bvars h in
       let p = E.LF.ByPos k in
       E.LF.Proj (loc, h', p)
    | I.LF.FVar name ->
       E.LF.Name (loc, name, None)
    | I.LF.FPVar (name, s) | I.LF.FMVar (name, s) ->
       let s' = sub cvars bvars s in
       E.LF.Name (loc, name, Some s')
    | I.LF.HClo (k1, k2, s) ->
       Misc.not_implemented "[erase] [head] HClo"
    | I.LF.HMClo (k1, _) ->
       Error.violation "[erase] [head] not normal (encountered HMClo)"

  and cvar cvars = function
    | I.LF.Offset k -> !! cvars k
    | I.LF.Inst _ -> Error.violation "[erase] [cvar] not normal (encountered MVar inst)"

  and spine cvars bvars : I.LF.spine -> E.LF.spine = function
    | I.LF.Nil -> E.LF.Nil
    | I.LF.App (tM, tS) ->
       let tM' = normal cvars bvars tM in
       let tS' = spine cvars bvars tS in
       (* TODO can we instead change `App` to carry a loc? -je *)
       E.LF.App (Loc.ghost, tM', tS')
    | I.LF.SClo (tS, s) ->
       Error.violation "[erase] [spine] not normal?"

  and sub cvars bvars s : E.LF.sub = assert false
  and tuple cvars bvars t : E.LF.tuple = assert false

  let clobj loc cvars bvars = function
    | I.LF.MObj tM ->
       let tM' = normal cvars bvars tM in
       E.LF.term tM'
    | I.LF.PObj tH ->
       let tH' = head loc cvars bvars tH in
       let loc = E.LF.loc_of_head tH' in
       E.LF.(term (Root (loc, tH', Nil)))
    | I.LF.SObj tS ->
       sub cvars bvars tS

  let mfront loc cvars = function
    | I.LF.ClObj (psi_hat, cM) ->
       let cPsi = Context.hatToDCtx psi_hat in
       let bvars = BVar.of_dctx cPsi in
       (* clobj gets erased to a *substitution*: we are undoing the
          disambiguation of substitutions to terms.
          (See remark in synext.ml)
        *)
       let s = clobj loc cvars bvars cM in
       let cPsi' = dctx cvars cPsi in
       E.LF.ClObj (cPsi', s)

    | I.LF.CObj cPsi ->
       let cPsi' = dctx cvars cPsi in
       E.LF.CObj cPsi'

    | I.LF.MV k ->
       (* not entirely clear how to convert these back; do they ever
          appear normally? *)
       Error.violation "[erase] idk MV"
                                   (* CVar.get cvars k  *)
    | I.LF.MUndef ->
       (* straight up impossible because a NF program would not
          contain any partial inverse substitutions. *)
       Error.violation "[erase] MUndef"
end

(** Adds one entry to a computational variables list. *)
let (++++) vars x = Var.(extend vars (mk_entry x))

(** Looks up one computation variable. *)
let (!!!) vars x = Var.get vars x

module Comp = struct
  let meta_obj cvars (loc, cM) = (loc, LF.mfront loc cvars cM)

  let pattern cvars vars pat = assert false

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
       let mf' = LF.mfront loc' cvars mf in
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
    | I.Comp.Branch (loc, cD, cG, pat, t, e) ->
       let vars = Var.of_gctx cG in
       let cvars = CVar.of_mctx cD in
       let pat' = pattern cvars vars pat in
       let e' = exp cvars vars e in
       E.Comp.Branch (loc, I.LF.Empty, pat', e')

  let thm cvars vars = assert false
end
