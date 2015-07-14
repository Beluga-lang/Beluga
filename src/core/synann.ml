(* Syntax for a tree annotated with types *)

open Id
open Pragma


module Loc = Camlp4.PreCast.Loc

module LF = struct

	type normal =
	    | Lam  of Loc.t * name * normal * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)
	    | Root of Loc.t * head * spine * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)
	    | LFHole of Loc.t * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)
	   	| Clo  of (normal * Syntax.Int.LF.sub) * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)
	    | Tuple of Loc.t * tuple * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)
	
	and head =

	    | BVar  of offset * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | Const of cid_term * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | MMVar of Syntax.Int.LF.mm_var_inst * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | MPVar of Syntax.Int.LF.mm_var_inst * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | MVar  of (Syntax.Int.LF.cvar * Syntax.Int.LF.sub) * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | PVar  of Syntax.Int.LF.offsetsub * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | AnnH  of head * Syntax.Int.LF.typ * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | Proj  of Syntax.Int.LF.head * int * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | FVar  of name * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | FMVar of Syntax.Int.LF.fvarsub * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | FPVar of Syntax.Int.LF.fvarsub * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | HClo  of offset * offset * Syntax.Int.LF.sub * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ
	    | HMClo of offset * Syntax.Int.LF.mm_var_inst * Syntax.Int.LF.mctx * Syntax.Int.LF.dctx * Syntax.Int.LF.typ

	and spine =
	    | Nil
	    | App  of normal * spine * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)
	    | SClo of (spine * Syntax.Int.LF.sub) * (Syntax.Int.LF.typ * Syntax.Int.LF.sub)

	and tuple =
	    | Last of normal
	    | Cons of normal * tuple	    
					  						  
	and mfront =    	                          
	  	| ClObj of Syntax.Int.LF.psi_hat * clobj * (Syntax.Int.LF.ctyp * Syntax.Int.LF.msub)
	  	| CObj of Syntax.Int.LF.dctx * (Syntax.Int.LF.ctyp * Syntax.Int.LF.msub)
	  	| MV   of offset * (Syntax.Int.LF.ctyp * Syntax.Int.LF.msub)
	  	| MUndef 

	and clobj =
    	| MObj of normal * (Syntax.Int.LF.cltyp * Syntax.Int.LF.msub)
    	| PObj of head * (Syntax.Int.LF.cltyp * Syntax.Int.LF.msub)
    	| SObj of Syntax.Int.LF.sub * (Syntax.Int.LF.cltyp * Syntax.Int.LF.msub)

end

module Comp = struct

	type tclo = Syntax.Int.Comp.typ * Syntax.Int.LF.msub

	type meta_obj = Loc.t * LF.mfront

	type exp_chk =
		| Syn    of Loc.t * exp_syn * Syntax.Int.LF.mctx * tclo
		| Rec    of Loc.t * name * exp_chk * Syntax.Int.LF.mctx * tclo
		| Fun    of Loc.t * name * exp_chk * Syntax.Int.LF.mctx * tclo
		| Cofun  of Loc.t * (copattern_spine * exp_chk) list * Syntax.Int.LF.mctx * tclo
		| MLam   of Loc.t * name * exp_chk * Syntax.Int.LF.mctx * tclo
		| Pair   of Loc.t * exp_chk * exp_chk * Syntax.Int.LF.mctx * tclo
		| LetPair of Loc.t * exp_syn * (name * name * exp_chk) * Syntax.Int.LF.mctx * tclo
		| Let    of Loc.t * exp_syn * (name * exp_chk) * Syntax.Int.LF.mctx * tclo
		| Box    of Loc.t * meta_obj * Syntax.Int.LF.mctx * tclo
		| Case   of Loc.t * case_pragma * exp_syn * branch list * Syntax.Int.LF.mctx * tclo
		| If     of Loc.t * exp_syn * exp_chk * exp_chk * Syntax.Int.LF.mctx * tclo
		| Hole   of Loc.t * (unit -> int) * Syntax.Int.LF.mctx * tclo

	and exp_syn =
 		| Var    of Loc.t * offset * tclo
 		| DataConst of Loc.t * cid_comp_const * tclo
 		| DataDest of Loc.t * cid_comp_dest * tclo
 		| Const  of Loc.t * cid_prog * tclo
 		| Apply  of Loc.t * exp_syn * exp_chk * tclo
 		| MApp   of Loc.t * exp_syn * meta_obj * tclo
 		| Ann    of exp_chk * Syntax.Int.Comp.typ * tclo
 		| Equal  of Loc.t * exp_syn * exp_syn * tclo
 		| PairVal of Loc.t * exp_syn * exp_syn * tclo
 		| Boolean of bool * tclo

	and branch =
	    | EmptyBranch of Loc.t * Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx * pattern * Syntax.Int.LF.msub
	    | Branch of Loc.t * Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx  * Syntax.Int.Comp.gctx * pattern * Syntax.Int.LF.msub * exp_chk

	and pattern =
	    | PatEmpty   of Loc.t * Syntax.Int.LF.dctx * tclo
	    | PatMetaObj of Loc.t * meta_obj * tclo
	    | PatConst of Loc.t * cid_comp_const * pattern_spine * tclo
	    | PatFVar   of Loc.t * name * tclo
	    | PatVar   of Loc.t * offset * tclo
	    | PatPair  of Loc.t * pattern * pattern * tclo
	    | PatTrue  of Loc.t * tclo
	    | PatFalse of Loc.t * tclo
	    | PatAnn   of Loc.t * pattern * Syntax.Int.Comp.typ * tclo

 	and pattern_spine =
	    | PatNil of tclo
	    | PatApp of Loc.t * pattern * pattern_spine * tclo

 	and copattern_spine =
	    | CopatNil of Loc.t
	    | CopatApp of Loc.t * cid_comp_dest * copattern_spine
	    | CopatMeta of Loc.t * meta_obj * copattern_spine

end
