open Id
open Pragma
open Syntax

type plicity =
  | ImpTerm
  | ExpTerm

module Comp = struct

  type tclo = Int.Comp.typ * Int.LF.msub

  type exp_chk =
    | Rec of Loc.t * name * exp_chk * tclo * plicity
    | Fun of Loc.t * name * exp_chk * tclo * plicity
    | MLam of Loc.t * name * exp_chk * tclo * plicity
    | Pair of Loc.t * exp_chk * exp_chk * tclo * plicity
    | Let of Loc.t * exp_syn * (name * exp_chk) * tclo * plicity
    | LetPair of Loc.t * exp_syn * (name * name * exp_chk) * tclo * plicity
    | Box of Loc.t * Int.Comp.meta_obj * tclo * plicity
    | Case of Loc.t * case_pragma * exp_syn * branch list * tclo * plicity
    | Syn of Loc.t * exp_syn * tclo * plicity
    | If of Loc.t * exp_syn * exp_chk * exp_chk * tclo * plicity
    | Hole of Loc.t * (unit -> int) * tclo * plicity

   and exp_syn =
    | Var of Loc.t * offset * tclo * plicity
    | DataConst of Loc.t * cid_comp_const * tclo * plicity
    | DataDest of Loc.t * cid_comp_dest * tclo * plicity
    | Const of Loc.t * cid_prog * tclo * plicity
    | Apply of Loc.t * exp_syn * exp_chk * tclo * plicity
    | MApp of Loc.t * exp_syn * Int.Comp.meta_obj * tclo * plicity
    | Ann of exp_chk * Int.Comp.typ * tclo * plicity
    | Equal of Loc.t * exp_syn * exp_syn * tclo * plicity
    | PairVal of Loc.t * exp_syn * exp_syn * tclo * plicity
    | Boolean of bool * tclo * plicity

   and pattern =
     | TheresNothingHere

   and branch =
     | Branch of Loc.t * Int.LF.ctyp_decl Int.LF.ctx
		 * Int.Comp.gctx * pattern * Int.LF.msub * exp_chk
end
