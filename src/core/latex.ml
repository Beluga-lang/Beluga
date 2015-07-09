open Syntax
open Id
open Printf

module C = Whnf
module PE = Pretty.Ext.DefaultPrinter
module PI = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

exception LatexException of string

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

and proof_case = 
| CaseDummy
| ProofCase of name * proof_step list (* name of the rule being analyzed *)

and proof_step =
| StepDummy
| Assumption (* of ... *)
| Inversion (* of ... *)
| RuleApp (* of ... *)
| IH (* of ... *) (* Special case of RuleApp? *)
| Subcase (* of ... *)

let proof_name = ref ""

(* Only called from Sgn.Typ *)
let proof_command n extK = 
	let rec depth k = match k with
	| Ext.LF.Typ _ -> 0
	| Ext.LF.ArrKind (_, _, k') -> 1 + depth k'
	| Ext.LF.PiKind (_, _, k') -> 1 + depth k'
	in
	let _ = fprintf stdout "Command (%s, %d, None)\n" (R.render_name n) (depth extK) in
	Command (n, depth extK, None)

(* Only called from Sgn.Const *)
let proof_rule cD cG n typ = 
	let rec list_of_typ t = match t with
	| Ext.LF.ArrTyp (_, t1, t2) -> t1::(list_of_typ t2)
	| _ -> [t]	
	in 
	let _ = fprintf stdout "Rule (%s, %s)\n" (R.render_name n) ("[" ^ (String.concat "; " (List.map (PE.typToString cD cG) (list_of_typ typ))) ^ "]") in
	Rule (n, list_of_typ typ)

let rec proof

(* 	
	n is the name of the proof from Rec
	e, t = Fun, TypArr or MLam, TypPiBox 
	e', t' = Case, t'
*)
(* let rec proof cD cG n e ttau =
	let _ = proof_name := (R.render_name n) in
	let cIH = Int.LF.Empty in
	let (g, cD', (cG', cIH'), e', ttau') = proof_goal cD (cG, cIH) e ttau in
		let _ = fprintf stdout "Proof (%s, %s)\n" !proof_name 
		("[" ^ (String.concat "; " 
				(List.map 
					(fun x -> match x with 						
						| GoalTerm (n', ttau) -> 
							begin
								match n' with
								| None -> sprintf "%s" (PI.subCompTypToString cD' ttau)
								| Some n'' -> sprintf "%s : %s" (R.render_name n'') (PI.subCompTypToString cD' ttau)	
							end				
						| GoalForall (_, Int.LF.Decl(n', mtyp, _)) -> sprintf "%s : %s" (R.render_name n') (PI.mtypToString cD' mtyp) 			
					)
				g
				)
			) ^ "]"
		) in		
		Proof (n, g, ScrutDummy, [])

and proof_goal cD (cG, cIH) e ttau = match e, ttau with
(* This case is for implicit MLams, which are ignored, so just skip over them *)
| Int.Comp.MLam (_, u, e'), (Int.Comp.TypPiBox ((Int.LF.Decl(_, cU, Int.LF.Maybe)), tau), theta) ->	
	proof_goal 
	(Int.LF.Dec (cD, Int.LF.Decl (u, C.cnormMTyp (cU, theta), Int.LF.Maybe))) (* cD *)
	(C.cnormCtx (cG, Int.LF.MShift 1), C.cnormCtx (cIH, Int.LF.MShift 1))  (* cG, cIH *)
	e' (* e *)
	(tau, C.mvar_dot1 theta) (* ttau *)
(* MLams quantify over stuff *)
| Int.Comp.MLam (_, u, e'), (Int.Comp.TypPiBox ((Int.LF.Decl(n, cU, Int.LF.No)) as cdec, tau), theta) ->	
	begin		
		match (e', (tau, theta)) with
		| Int.Comp.Case _, _ ->
			let cD' = Int.LF.Dec (cD, Int.LF.Decl (u, C.cnormMTyp(cU, theta), Int.LF.No)) in
				let (cG', cIH') = (C.cnormCtx (cG, Int.LF.MShift 1), C.cnormCtx (cIH, Int.LF.MShift 1)) in
				([GoalForall(n, cdec); GoalTerm(None, (tau, theta))], cD', (cG', cIH'), e', (tau, theta))
		| _ ->			
			let cD' = Int.LF.Dec (cD, Int.LF.Decl (u, C.cnormMTyp(cU, theta), Int.LF.No)) in
				let (cG', cIH') = (C.cnormCtx (cG, Int.LF.MShift 1), C.cnormCtx (cIH, Int.LF.MShift 1)) in
					let (goals, cD'', (cG'', cIH''), e'', t') = proof_goal cD' (cG', cIH') e' (tau, theta) in
						((GoalForall(n, cdec))::goals, cD'', (cG'', cIH''), e'', t') 
		
	end
(* Functions label premises *)
| Int.Comp.Fun (_, n, e'), (Int.Comp.TypArr (t1, t2), theta) -> 	
	begin 
		match e', (t2, theta) with		
		| Int.Comp.Case _, _ ->
			let (cG', cIH') = (Int.LF.Dec (cG, Int.Comp.CTypDecl (n, Int.Comp.TypClo (t1, theta))), (Total.shift cIH)) in
				([GoalTerm(Some n, (t1, theta)); GoalTerm(None, (t2, theta))], cD, (cG', cIH'), e', (t2, theta))
		|  _ -> 			
			let (cG', cIH') = (Int.LF.Dec (cG, Int.Comp.CTypDecl (n, Int.Comp.TypClo (t1, theta))), (Total.shift cIH)) in
				let (goals, cD', (cG'', cIH''), e'', t') = proof_goal cD (cG', cIH') e' (t2, theta) in	
					((GoalTerm(Some n, (t1, theta))::goals), cD', (cG'', cIH''), e'', t')
	end
(* Error case *)
| _ -> raise (LatexException ("Non Fun/MLam argument passed to proof_goal: " ^ PI.expChkToString cD cG e))

(* and proof_case cD (cG, cIH) e ttau = match e, ttau with
| Int.Comp.Case (loc, prag, Int.Comp.Ann (Int.Comp.Box (_, (l,cM)), (Int.Comp.TypBox (_, mT) as tau0_sc)), branches), (tau, t)) ->

| Int.Comp.Case (loc, prag, i, branches), (tau, t)) ->
| _ -> raise (LatexException "Non Case argument passed to proof_case")
 *)
(* Sort into modules, less confusing later on? *)
module LF = struct

end

module Comp = struct

end

module Sgn = struct

end *)