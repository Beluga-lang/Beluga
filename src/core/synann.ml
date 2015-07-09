(* Syntax for a tree annotated with types *)

open Id
open Pragma


module Loc = Camlp4.PreCast.Loc

module LF = struct

	type depend =
	    | No
	    | Maybe
	    | Inductive

	and typ_decl =
	    | TypDecl of name * typ
	    | TypDeclOpt of name

	and cltyp =
	    | MTyp of typ
	    | PTyp of typ
	    | STyp of svar_class * dctx

	and svar_class = 
	    | Ren
	    | Subst

	and ctyp =
	    | ClTyp of cltyp * dctx
	    | CTyp of cid_schema option

	and ctyp_decl =
	    | Decl of name * ctyp * depend
	    | DeclOpt of name

	and typ =
	    | Atom  of Loc.t * cid_typ * spine
	    | PiTyp of (typ_decl * depend) * typ
	    | Sigma of typ_rec
	    | TClo  of (typ * sub)

	and normal =
	    | Lam  of Loc.t * name * normal
	    | Root of Loc.t * head * spine
	    | LFHole of Loc.t
	   	| Clo  of (normal * sub)
	    | Tuple of Loc.t * tuple
	
	and head =
	    | BVar  of offset
	    | Const of cid_term
	    | MMVar of mm_var_inst
	    | MPVar of mm_var_inst
	    | MVar  of (cvar * sub)
	    | PVar  of offsetsub
	    | AnnH  of head * typ
	    | Proj  of head * int
	    | FVar  of name
	    | FMVar of fvarsub
	    | FPVar of fvarsub
	    | HClo  of offset * offset * sub
	    | HMClo of offset * mm_var_inst

  	and fvarsub = name * sub
	and offsetsub = offset * sub

	and spine =
	    | Nil
	    | App  of normal * spine
	    | SClo of (spine * sub)

	and sub =
	    | Shift of offset
	    | SVar  of offset * int * sub
	    | FSVar of offset * fvarsub
	    | Dot   of front * sub
	    | MSVar of offset * mm_var_inst
	    | EmptySub
	    | Undefs

	and front =
	    | Head of head
	    | Obj  of normal
	    | Undef

	and tuple =
	    | Last of normal
	    | Cons of normal * tuple	    
					  						  
	and mfront =    	                          
	  	| ClObj of Syntax.Int.LF.psi_hat * clobj * (Syntax.Int.LF.ctyp * Syntax.Int.LF.msub)
	  	| CObj of Syntax.Int.LF.dctx * (Syntax.Int.LF.ctyp * Syntax.Int.LF.msub)
	  	| MV   of offset * (Syntax.Int.LF.ctyp * Syntax.Int.LF.msub)
	  	| MUndef 

	and clobj =
    	| MObj of Syntax.Int.LF.normal * (Syntax.Int.LF.cltyp * Syntax.Int.LF.msub)
    	| PObj of Syntax.Int.LF.head * (Syntax.Int.LF.cltyp * Syntax.Int.LF.msub)
    	| SObj of Syntax.Int.LF.sub * (Syntax.Int.LF.cltyp * Syntax.Int.LF.msub)

	and msub =
	    | MShift of int
	    | MDot   of mfront * msub

	and cvar =
    	| Offset of offset
    	| Inst   of mm_var	

	and mm_var = name * iterm option ref * mctx * ctyp * cnstr list ref * depend
	and mm_var_inst' = mm_var * msub
	and mm_var_inst = mm_var_inst' * sub

	and iterm =
	    | INorm of normal
	    | IHead of head
	    | ISub of sub
	    | ICtx of dctx	

	and constrnt =
    	| Queued
    	| Eqn of mctx * dctx * iterm * iterm

  	and cnstr = constrnt ref

	and dctx =
    	| Null
    	| CtxVar   of ctx_var
    	| DDec     of dctx * typ_decl

    and ctx_var =
	    | CtxName   of name
	    | CtxOffset of offset
	    | CInst  of mm_var_inst'

	and 'a ctx =
    	| Empty
    	| Dec of 'a ctx * 'a

	and psi_hat = ctx_var option * offset

	and typ_rec =
	    |  SigmaLast of name option * typ
	    |  SigmaElem of name * typ * typ_rec

	and mctx = ctyp_decl ctx

end

module Comp = struct

	type tclo = Syntax.Int.Comp.typ * Syntax.Int.LF.msub

	type meta_typ = LF.ctyp

	type meta_obj = Loc.t * LF.mfront

	type meta_spine =
	    | MetaNil
	    | MetaApp of meta_obj * meta_spine

	type typ =
	    | TypBase   of Loc.t * cid_comp_typ * meta_spine
	    | TypCobase of Loc.t * cid_comp_cotyp * meta_spine
	    | TypDef    of Loc.t * cid_comp_typ * meta_spine
	    | TypBox of Loc.t * Syntax.Int.Comp.meta_typ 
	    | TypArr    of typ * typ
	    | TypCross  of typ * typ
	    | TypPiBox  of LF.ctyp_decl * typ
	    | TypClo    of typ *  LF.msub
	    | TypBool 
	    | TypInd of typ 

	type args =
	    | M  of meta_obj
	    | V  of offset
	    | E  
	    | DC

	type ctyp_decl =
	    | WfRec of name * args list * typ
	    | CTypDecl    of name * typ
	    | CTypDeclOpt of name

	type gctx = ctyp_decl LF.ctx

	type exp_chk =
		| Syn    of Loc.t * exp_syn * tclo
		| Rec    of Loc.t * name * exp_chk * tclo
		| Fun    of Loc.t * name * exp_chk * tclo
		| Cofun  of Loc.t * (copattern_spine * exp_chk) list * tclo
		| MLam   of Loc.t * name * exp_chk * tclo
		| Pair   of Loc.t * exp_chk * exp_chk * tclo
		| LetPair of Loc.t * exp_syn * (name * name * exp_chk) * tclo
		| Let    of Loc.t * exp_syn * (name * exp_chk) * tclo
		| Box    of Loc.t * meta_obj * tclo
		| Case   of Loc.t * case_pragma * exp_syn * branch list * tclo
		| If     of Loc.t * exp_syn * exp_chk * exp_chk * tclo
		| Hole   of Loc.t * (unit -> int) * tclo

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
	    | EmptyBranch of Loc.t * Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx * Syntax.Int.Comp.pattern * Syntax.Int.LF.msub
	    | Branch of Loc.t * Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx  * Syntax.Int.Comp.gctx * Syntax.Int.Comp.pattern * Syntax.Int.LF.msub * exp_chk

 	and copattern_spine =
	    | CopatNil of Loc.t
	    | CopatApp of Loc.t * cid_comp_dest * copattern_spine
	    | CopatMeta of Loc.t * meta_obj * copattern_spine

end
