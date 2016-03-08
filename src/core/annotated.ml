open Id
open Pragma
open Syntax

module LF = struct

  type tclo = Int.LF.typ * Int.LF.sub

  type mfront =
    | ClObj of Int.LF.psi_hat * clobj
    | CObj of Int.LF.dctx
    | MV of offset

   and clobj =
     | MObj of normal
     | PObj of Int.LF.head
     | SObj of Int.LF.sub

   and normal =
     | Lam of Loc.t * name * normal * tclo * string option
     | Root of Loc.t * Int.LF.head * spine * tclo * string option
     | LFHole of Loc.t * tclo * string option
     | Clo of (normal * Int.LF.sub)
     | Tuple of Loc.t * tuple * tclo * string option

   and tuple =
     | Last of normal
     | Cons of normal * tuple

   and spine =
     | Nil
     | App of normal * spine
     | SClo of (spine * Int.LF.sub)

end

module Comp = struct

  type tclo = Int.Comp.typ * Int.LF.msub

  type meta_obj = Loc.t * LF.mfront

  type exp_chk =
    | Rec of Loc.t * name * exp_chk * tclo * string option
    | Fun of Loc.t * name * exp_chk * tclo * string option
    | Cofun of Loc.t * (copattern_spine * exp_chk) list * tclo * string option
    | MLam of Loc.t * name * exp_chk * tclo * string option
    | Pair of Loc.t * exp_chk * exp_chk * tclo * string option
    | Let of Loc.t * exp_syn * (name * exp_chk) * tclo * string option
    | LetPair of Loc.t * exp_syn * (name * name * exp_chk) * tclo * string option
    | Box of Loc.t * meta_obj * tclo * string option
    | Case of Loc.t * case_pragma * exp_syn * branch list * tclo * string option
    | Syn of Loc.t * exp_syn * tclo * string option
    | If of Loc.t * exp_syn * exp_chk * exp_chk * tclo * string option
    | Hole of Loc.t * (unit -> int) * tclo * string option

   and exp_syn =
    | Var of Loc.t * offset * tclo * string option
    | DataConst of Loc.t * cid_comp_const * tclo * string option
    | DataDest of Loc.t * cid_comp_dest * tclo * string option
    | Const of Loc.t * cid_prog * tclo * string option
    | Apply of Loc.t * exp_syn * exp_chk * tclo * string option
    | MApp of Loc.t * exp_syn * meta_obj * tclo * string option
    | Ann of exp_chk * Int.Comp.typ * tclo * string option
    | Equal of Loc.t * exp_syn * exp_syn * tclo * string option
    | PairVal of Loc.t * exp_syn * exp_syn * tclo * string option
    | Boolean of bool * tclo * string option

   and pattern =
     | PatEmpty of Loc.t * Int.LF.dctx * tclo * string option
     | PatMetaObj of Loc.t * meta_obj * tclo * string option
     | PatPair of Loc.t * pattern * pattern * tclo * string option
     | PatConst of Loc.t * cid_comp_const * pattern_spine * tclo * string option
     | PatVar of Loc.t * offset * tclo * string option
     | PatTrue of Loc.t * tclo * string option
     | PatFalse of Loc.t * tclo * string option
     | PatAnn of Loc.t * pattern * Int.Comp.typ * tclo * string option

   and pattern_spine =
     | PatNil of tclo * string option
     | PatApp of Loc.t * pattern * pattern_spine * tclo * string option

   and branch =
     | EmptyBranch of Loc.t * Int.LF.ctyp_decl Int.LF.ctx * pattern * Int.LF.msub
     | Branch of Loc.t * Int.LF.ctyp_decl Int.LF.ctx
		 * Int.Comp.gctx * pattern * Int.LF.msub * exp_chk

   and copattern_spine =
     | CopatNil of Loc.t
     | CopatApp of Loc.t * cid_comp_dest * copattern_spine
     | CopatMeta of Loc.t * meta_obj * copattern_spine
end
