open Id
open Pragma

module Loc = Camlp4.PreCast.Loc

module Comp = struct
  type exp_chk =
    | Rec of Loc.t * name * exp_chk
	     * Syntax.Int.Comp.tclo
    | Fun of Loc.t * name * exp_chk
	     * Syntax.Int.Comp.tclo
    | MLam of Loc.t * name * exp_chk
	      * Syntax.Int.Comp.tclo
    | Pair of Loc.t * exp_chk * exp_chk
	      * Syntax.Int.Comp.tclo
    | Let of Loc.t * exp_syn * (name * exp_chk)
	     * Syntax.Int.Comp.tclo
    | LetPair of Loc.t * exp_syn * (name * name * exp_chk)
		 * Syntax.Int.Comp.tclo
    | Box of Loc.t * Syntax.Int.Comp.meta_obj
	     * Syntax.Int.Comp.tclo
    | Case of Loc.t * case_pragma * exp_syn * branch list
	      * Syntax.Int.Comp.tclo
    | Syn of Loc.t * exp_syn
	     * Syntax.Int.Comp.tclo
    | If of Loc.t * exp_syn * exp_chk * exp_chk
	    * Syntax.Int.Comp.tclo
    | Hole of Loc.t * (unit -> int)
	      * Syntax.Int.Comp.tclo

   and exp_syn =
     | Var of Loc.t * offset
	      * Syntax.Int.Comp.tclo
     | DataConst of Loc.t * cid_comp_const
		    * Syntax.Int.Comp.tclo
     | DataDest of Loc.t * cid_comp_dest
		   * Syntax.Int.Comp.tclo
     | Const of Loc.t * cid_prog
		* Syntax.Int.Comp.tclo
     | Apply of Loc.t * exp_syn * exp_chk
		* Syntax.Int.Comp.tclo
     | MApp of Loc.t * exp_syn * Syntax.Int.Comp.meta_obj
	       * Syntax.Int.Comp.tclo
     | PairVal of Loc.t * exp_syn * exp_syn
		  * Syntax.Int.Comp.tclo
     | Ann of exp_chk * Syntax.Int.Comp.typ
	      * Syntax.Int.Comp.tclo
     | Equal of Loc.t * exp_syn * exp_syn
		* Syntax.Int.Comp.tclo
     | Boolean of bool
		  * Syntax.Int.Comp.tclo

   and branch =
     | EmptyBranch of Loc.t * Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
		      * pattern * Syntax.Int.LF.msub
		      * Syntax.Int.Comp.tclo
     | Branch of Loc.t * Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
		 * Syntax.Int.Comp.gctx * pattern * Syntax.Int.LF.msub
		 * exp_chk
		 * Syntax.Int.Comp.tclo

   and pattern =
     | PatEmpty of Loc.t * Syntax.Int.LF.dctx
		   * Syntax.Int.Comp.tclo
     | PatMetaObj of Loc.t * Syntax.Int.Comp.meta_obj
		     * Syntax.Int.Comp.tclo
     | PatPair of Loc.t * pattern * pattern
		  * Syntax.Int.Comp.tclo
     | PatConst of Loc.t * cid_comp_const * pattern_spine
		   * Syntax.Int.Comp.tclo
     | PatVar of Loc.t * offset
		 * Syntax.Int.Comp.tclo
     | PatTrue of Loc.t
		  * Syntax.Int.Comp.tclo
     | PatFalse of Loc.t
		   * Syntax.Int.Comp.tclo
     | PatAnn of Loc.t * pattern * Syntax.Int.Comp.typ
		 * Syntax.Int.Comp.tclo

   and pattern_spine =
     | PatNil of Syntax.Int.Comp.tclo
     | PatApp of Loc.t * pattern * pattern_spine
		 * Syntax.Int.Comp.tclo

end
