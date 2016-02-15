open Id
open Pragma
open Syntax

module Comp = struct

  type tclo = Int.Comp.typ * Int.LF.msub

  type exp_chk =
    | Rec of Loc.t * name * exp_chk * tclo
    | Fun of Loc.t * name * exp_chk * tclo
    | MLam of Loc.t * name * exp_chk * tclo
    | Pair of Loc.t * exp_chk * exp_chk * tclo
    | Let of Loc.t * exp_syn * (name * exp_chk) * tclo
    | LetPair of Loc.t * exp_syn * (name * name * exp_chk) * tclo
    | Box of Loc.t * Int.Comp.meta_obj * tclo
    | Case of Loc.t * case_pragma * exp_syn * branch list * tclo
    | Syn of Loc.t * exp_syn * tclo
    | If of Loc.t * exp_syn * exp_chk * exp_chk * tclo
    | Hole of Loc.t * (unit -> int) * tclo

   and exp_syn =
    | Var of Loc.t * offset * tclo
    | DataConst of Loc.t * cid_comp_const * tclo
    | DataDest of Loc.t * cid_comp_dest * tclo
    | Const of Loc.t * cid_prog * tclo
    | Apply of Loc.t * exp_syn * exp_chk * tclo
    | MApp of Loc.t * exp_syn * Int.Comp.meta_obj * tclo
    | Ann of exp_chk * Int.Comp.typ * tclo
    | Equal of Loc.t * exp_syn * exp_syn * tclo
    | PairVal of Loc.t * exp_syn * exp_syn * tclo
    | Boolean of bool * tclo

   and pattern =
     | PatMetaObj of Loc.t * Int.Comp.meta_obj * tclo
     | PatPair of Loc.t * pattern * pattern * tclo
     | PatConst of Loc.t * cid_comp_const * pattern_spine * tclo
     | PatVar of Loc.t * offset * tclo
     | PatTrue of Loc.t * tclo
     | PatFalse of Loc.t * tclo
     | PatAnn of Loc.t * pattern * Int.Comp.typ * tclo

   and pattern_spine =
     | PatNil of tclo
     | PatApp of Loc.t * pattern * pattern_spine * tclo

   and branch =
     | EmptyBranch of Loc.t * Int.LF.ctyp_decl Int.LF.ctx * pattern * Int.LF.msub
     | Branch of Loc.t * Int.LF.ctyp_decl Int.LF.ctx
		 * Int.Comp.gctx * pattern * Int.LF.msub * exp_chk
end
