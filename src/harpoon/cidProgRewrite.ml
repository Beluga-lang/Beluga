(** Contains a family a functions for rewriting references to theorems
    (Beluga programs or Harpoon proofs).

    This is used after translation to replace all references for
    recursive calls with calls to the translated functions.
 *)

open Beluga
open Syntax.Int.Comp

type cid_map = Id.cid_prog -> Id.cid_prog

let rec exp_chk f = function
  | Syn (loc, i) -> Syn (loc, exp_syn f i)
  | Fn (loc, x, e) -> Fn (loc, x, exp_chk f e)
  | Fun (loc, fbs) -> Fun (loc, fun_branches f fbs)
  | MLam (loc, u, e, plicity) -> MLam (loc, u, exp_chk f e, plicity)
  | Pair (loc, e1, e2) -> Pair (loc, exp_chk f e1, exp_chk f e2)
  | LetPair (loc, i, (x1, x2, e)) ->
     LetPair (loc, exp_syn f i, (x1, x2, exp_chk f e))
  | Let (loc, i, (x, e)) -> Let (loc, exp_syn f i, (x, exp_chk f e))
  | Box (loc, cM, cU) -> Box (loc, cM, cU)
  | Case (loc, prag, i, bs) ->
     Case (loc, prag, exp_syn f i, List.map (branch f) bs)
  | Impossible (loc, i) -> Impossible (loc, exp_syn f i)
  | Hole (loc, id, name) -> Hole (loc, id, name)

and exp_syn f = function
  | Var (loc, k) -> Var (loc, k)
  | DataConst (loc, cid) -> DataConst (loc, cid)
  | Obs (loc, e, t, cid) -> Obs (loc, exp_chk f e, t, cid)
  | Const (loc, cid) -> Const (loc, f cid)
  | Apply (loc, i, e) -> Apply (loc, exp_syn f i, exp_chk f e)
  | MApp (loc, i, cM, cU, plicity) ->
     MApp (loc, exp_syn f i, cM, cU, plicity)
  | AnnBox (cM, cU) -> AnnBox (cM, cU)
  | PairVal (loc, i1, i2) ->
     PairVal (loc, exp_syn f i1, exp_syn f i2)

and branch f (Branch (loc, cD_pref, (cD_b, cG_b), pat, t, e)) =
  Branch (loc, cD_pref, (cD_b, cG_b), pat, t, exp_chk f e)

and fun_branches f = function
  | NilFBranch loc -> NilFBranch loc
  | ConsFBranch (loc, (cD, cG, patS, e), bs) ->
     ConsFBranch
       (loc, (cD, cG, patS, exp_chk f e), fun_branches f bs)
