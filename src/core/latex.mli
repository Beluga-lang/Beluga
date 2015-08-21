open Syntax
open Id

exception LatexException of string

val gen_latex : bool ref

type latex =
| LatexDummy
| Command of name * int * string option
| Rule of name * Ext.LF.ctyp_decl Ext.LF.ctx * Ext.LF.dctx * Ext.LF.typ list * Ext.LF.typ
| Proof of name * theorem * scrutinee * proof_case list (* we perform induction on the exp_syn *)

and scrutinee = 
| ScrutDummy
| Scrut of Int.Comp.exp_syn

and theorem = Theorem of tterm list * tterm list * tterm

and tterm = 
| TheoremTerm of name option * Int.LF.mctx * (Int.Comp.typ * Int.LF.msub)
| TheoremForall of name * Int.LF.mctx * Int.LF.ctyp_decl

and proof_case = 
| CaseDummy
| ProofCase of name * proof_step list (* name of the rule being analyzed *)

and proof_step =
| StepDummy
| Assumption (* of ... *)
| Inversion of string * string
| RuleApp (* of ... *)
| IH (* of ... *) (* Special case of RuleApp? *)
| Subcase (* of ... *)

val proof_command : Id.name -> Ext.LF.kind -> unit
val proof_rule : Ext.LF.mctx -> Ext.LF.dctx -> Id.name -> Ext.LF.typ -> unit
val proof : Synann.Comp.exp_chk -> unit