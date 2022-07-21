(** Contains a family a functions for rewriting references to theorems
    (Beluga programs or Harpoon proofs).

    This is used after translation to replace all references for
    recursive calls with calls to the translated functions.
 *)

open Support
open Beluga
open Syntax.Int.Comp

type cid_map = Id.cid_prog -> Id.cid_prog

let rec exp f = function
  | Fn (loc, x, e) -> Fn (loc, x, exp f e)
  | Fun (loc, fbs) -> Fun (loc, fun_branches f fbs)
  | MLam (loc, u, e, plicity) -> MLam (loc, u, exp f e, plicity)
  | Tuple (loc, es) ->
    let es' = List2.map (exp f) es in
    Tuple (loc, es')
  | LetTuple (loc, i, (ns, e)) ->
     LetTuple (loc, exp f i, (ns, exp f e))
  | Let (loc, i, (x, e)) -> Let (loc, exp f i, (x, exp f e))
  | Box (loc, cM, cU) -> Box (loc, cM, cU)
  | Case (loc, prag, i, bs) ->
     Case (loc, prag, exp f i, List.map (branch f) bs)
  | Impossible (loc, i) -> Impossible (loc, exp f i)
  | Hole (loc, id, name) -> Hole (loc, id, name)
  | Var (loc, k) -> Var (loc, k)
  | DataConst (loc, cid) -> DataConst (loc, cid)
  | Obs (loc, e, t, cid) -> Obs (loc, exp f e, t, cid)
  | Const (loc, cid) -> Const (loc, f cid)
  | Apply (loc, i, e) -> Apply (loc, exp f i, exp f e)
  | AnnBox _ as a -> a
  | MApp (loc, i, cM, cU, plicity) ->
     MApp (loc, exp f i, cM, cU, plicity)

and branch f (Branch (loc, cD_pref, (cD_b, cG_b), pat, t, e)) =
  Branch (loc, cD_pref, (cD_b, cG_b), pat, t, exp f e)

and fun_branches f = function
  | NilFBranch loc -> NilFBranch loc
  | ConsFBranch (loc, (cD, cG, patS, e), bs) ->
     ConsFBranch
       (loc, (cD, cG, patS, exp f e), fun_branches f bs)
