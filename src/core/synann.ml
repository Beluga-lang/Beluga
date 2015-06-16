(* Syntax for a tree annotated with types *)

open Id
open Pragma


module Loc = Camlp4.PreCast.Loc

(** Internal Computation Syntax *)
module Comp = struct

	type tclo = Syntax.Int.Comp.typ * Syntax.Int.LF.msub	

	type exp_chk =
		| Syn    of Loc.t * exp_syn * tclo
		| Rec    of Loc.t * name * exp_chk * tclo
		| Fun    of Loc.t * name * exp_chk * tclo
		(* | Cofun  of Loc.t * (copattern_spine * exp_chk) list * tclo *)
		| MLam   of Loc.t * name * exp_chk * tclo
		| Pair   of Loc.t * exp_chk * exp_chk * tclo
		| LetPair of Loc.t * exp_syn * (name * name * exp_chk) * tclo
		| Let    of Loc.t * exp_syn * (name * exp_chk) * tclo
		| Box    of Loc.t * Syntax.Int.Comp.meta_obj * tclo
		| Case   of Loc.t * case_pragma * exp_syn * Syntax.Int.Comp.branch list * tclo
		| If     of Loc.t * exp_syn * exp_chk * exp_chk * tclo
		| Hole   of Loc.t * (unit -> int) * tclo
	and exp_syn =
 		| Var    of Loc.t * offset * tclo
 		| DataConst of Loc.t * cid_comp_const * tclo
 		| DataDest of Loc.t * cid_comp_dest * tclo
 		| Const  of Loc.t * cid_prog * tclo
 		| Apply  of Loc.t * exp_syn * exp_chk * tclo
 		| MApp   of Loc.t * exp_syn * Syntax.Int.Comp.meta_obj * tclo
 		| Ann    of exp_chk * Syntax.Int.Comp.typ * tclo
 		| Equal  of Loc.t * exp_syn * exp_syn * tclo
 		| PairVal of Loc.t * exp_syn * exp_syn * tclo
 		| Boolean of bool * tclo

end
