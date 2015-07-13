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
| Proof of name * theorem * scrutinee * proof_case list (* we perform induction on the exp_syn *)

and scrutinee = 
| ScrutDummy
| Scrut of Int.Comp.exp_syn

and theorem = t_term list

and t_term = 
| TheoremTerm of name option * Int.LF.mctx * (Int.Comp.typ * Int.LF.msub)
| TheoremForall of name * Int.LF.mctx * Int.LF.ctyp_decl

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

let rec _chop_end l = match l with
| [] -> raise (LatexException "[Latex] Unable to empty list.")
| [x] -> ([], x)
| hd::tl -> 
	let (l', x) = _chop_end tl in (hd::l', x)

let rec proof e_ann = 
	let (theorem, e') = proof_theorem e_ann in
	(* let (t_premises, t_conclusion) = chop_end theorem in *)
	let _ = 
	List.iter 
	(fun x -> match x with 
		|TheoremForall (_, cD, Syntax.Int.LF.Decl (n', mtyp, _)) -> print_string (sprintf "TFA(%s : %s)\n" (R.render_name n') (PI.mtypToString cD mtyp)) 
		|TheoremTerm (n', cD, ttau) ->
			begin
				match n' with
				| None -> print_string (sprintf "TTConc(%s)\n" (PI.subCompTypToString cD ttau))
				| Some n'' -> print_string (sprintf "TTPrem(%s : %s)\n" (R.render_name n'') (PI.subCompTypToString cD ttau))
			end
	)
	theorem in
	(* let cases = proof_cases e' in	 *)
	()

and proof_theorem e = match e with
| Synann.Comp.MLam (_, u, e', _, (Syntax.Int.Comp.TypPiBox ((Syntax.Int.LF.Decl (_, cU, Int.LF.Maybe)), tau), theta)) ->
	begin
		match e' with
		| Synann.Comp.Case (_, _, _, _, _, ttau) ->  ([], e')
		| _ -> let (tlist, e'') = proof_theorem e' in (tlist, e'')	
	end
| Synann.Comp.MLam (_, u, e', cD, (Syntax.Int.Comp.TypPiBox ((Syntax.Int.LF.Decl (_, cU, Int.LF.No)) as cdec, tau), theta)) ->
	begin
		match e' with
		| Synann.Comp.Case (_, _, _, _, cD', ttau) -> 
			((TheoremForall (u, cD, cdec))::(TheoremTerm (None, cD', ttau))::[], e)			
		| _ -> 
			let (tlist, e'') = proof_theorem e' in ((TheoremForall (u, cD, cdec))::tlist, e'')
	end	
| Synann.Comp.Fun (_, n, e', cD, (Int.Comp.TypArr (t1, t2), theta)) ->
	begin
		match e' with
		| Synann.Comp.Case (_, _, _, _, cD', ttau) -> 
			((TheoremTerm (Some n, cD, (t1, theta)))::(TheoremTerm (None, cD', (t2, theta)))::[], e')			
		| _ -> 
			let (tlist, e'') = proof_theorem e' in ((TheoremTerm (Some n, cD, (t1, theta)))::tlist, e'')
	end
| _ -> raise (LatexException "Non MLam/Fun expression passed to proof_theorem")


and proof_case e = 
(* | Int.Comp.Case (loc, prag, Int.Comp.Ann (Int.Comp.Box (_, (l,cM)), (Int.Comp.TypBox (_, mT) as tau0_sc)), branches), (tau, t)) -> *)
| Int.Comp.Case (loc, prag, i, branches, cD, (tau, t)) ->

| _ -> raise (LatexException "Non Case argument passed to proof_case")

and proof_branches b = List.map proof_branch b

and proof_branch b = match b with
| 

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