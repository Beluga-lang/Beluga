open Syntax
open Id

exception LatexException of string

(* The current case depth *)
val proof_name : string ref

type latex =
| LatexDummy
| Command of name * int * string option
| Rule of name * Ext.LF.typ list
| Proof of name * goal * scrutinee * proof_case list (* we perform induction on the exp_syn *)

and scrutinee = 
| ScrutDummy
| Scrut of Int.Comp.exp_syn

and goal = goal_term list

and goal_term = 
| GoalTerm of name option * (Int.Comp.typ * Int.LF.msub)
| GoalForall of name * Int.LF.ctyp_decl

and proof_case = name * proof_step list (* name of the rule being analyzed *)

and proof_step =
| StepDummy
| Assumption (* of ... *)
| Inversion (* of ... *)
| RuleApp (* of ... *)
| IH (* of ... *) (* Special case of RuleApp? *)
| Subcase (* of ... *)

val proof_command : Id.name -> Ext.LF.kind -> latex
val proof_rule : Ext.LF.mctx -> Ext.LF.dctx -> Id.name -> Ext.LF.typ -> latex
val proof : Int.LF.mctx -> Int.Comp.gctx -> Id.name -> Int.Comp.exp_chk -> Int.Comp.typ * Int.LF.msub -> latex