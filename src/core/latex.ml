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
	let _ = proof_case e' in
	(* let cases = proof_cases e' in	 *)
	()

(* Need to write cases for Syn + Box *)
and proof_theorem e = match e with
| Synann.Comp.MLam (_, u, e', _, (Syntax.Int.Comp.TypPiBox ((Syntax.Int.LF.Decl (_, cU, Int.LF.Maybe)), tau), theta)) ->
	begin
		match e' with
		| Synann.Comp.Case (_, _, _, _, _, ttau) ->  ([], e')
		| _ -> let (tlist, e'') = proof_theorem e' in (tlist, e'')	
	end
| Synann.Comp.MLam (_, u, e', cD, (Syntax.Int.Comp.TypPiBox ((Syntax.Int.LF.Decl (_, cU, _)) as cdec, tau), theta)) ->
	begin
		match e' with
		| Synann.Comp.Case (_, _, _, _, cD', ttau) -> print_string "Case statement\n";
			((TheoremForall (u, cD, cdec))::(TheoremTerm (None, cD', ttau))::[], e')			
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
(* These cases should never be reached, but this is more useful than a general exception *)
| Synann.Comp.Syn _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestSyn\n")
| Synann.Comp.MLam _ -> raise (LatexException "Unsupported MLam in proof_theorem\n")
| Synann.Comp.Rec _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestRec\n")
| Synann.Comp.Cofun _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestCofun\n")
| Synann.Comp.Pair _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestPair\n")
| Synann.Comp.LetPair _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestLetPair\n")
| Synann.Comp.Let _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestLet\n")
| Synann.Comp.Box _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestBox\n")
| Synann.Comp.Case _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestCase\n")
| Synann.Comp.If _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestIf\n")
| Synann.Comp.Hole _ -> raise (LatexException "Non MLam/Fun passed to proof_theorem: TestHole\n")


and proof_case e = match e with(* return scrut + case list *)
| Synann.Comp.Case (loc, prag, i, branches, cD, ttau) -> proof_branches branches
(* These cases should never be reached, but this is more useful than a general exception *)
| Synann.Comp.Syn _ -> raise (LatexException "Non Case passed to proof_case: Syn\n")
| Synann.Comp.Fun _ -> raise (LatexException "Non Case passed to proof_case: Fun\n")
| Synann.Comp.MLam _ -> raise (LatexException "Non Case passed to proof_case: MLam\n")
| Synann.Comp.Rec _ -> raise (LatexException "Non Case passed to proof_case: Rec\n")
| Synann.Comp.Cofun _ -> raise (LatexException "Non Case passed to proof_case: Cofun\n")
| Synann.Comp.Pair _ -> raise (LatexException "Non Case passed to proof_case: Pair\n")
| Synann.Comp.LetPair _ -> raise (LatexException "Non Case passed to proof_case: LetPair\n")
| Synann.Comp.Let _ -> raise (LatexException "Non Case passed to proof_case: Let\n")
| Synann.Comp.Box _ -> raise (LatexException "Non Case passed to proof_case: Box\n")
(* | Synann.Comp.Case _ -> raise (LatexException "Unsupported case passed to proof_case.\n") *)
| Synann.Comp.If _ -> raise (LatexException "Non Case passed to proof_case: If\n")
| Synann.Comp.Hole _ -> raise (LatexException "Non Case passed to proof_case: Hole\n")

and proof_branches b = List.map proof_branch b

and proof_branch b = match b with
| Synann.Comp.EmptyBranch (loc, cD1', pat, t1) -> print_string "TestEmptyBranch\n"
| Synann.Comp.Branch (loc, cD1', _cG, Synann.Comp.PatMetaObj (loc', mO, ttau'), t1, e1) -> print_string "TestBranch\n"
| Synann.Comp.Branch (loc, cD1', cG1, pat, t1, e1) -> proof_pattern pat

(* How do we deal with patterns?
	Annotated patterns are easy, shed the typing and recurse on the pattern itself
	The pattern should some kind of rule
 *)
and proof_pattern pat = match pat with (* this returns steps *)
| Synann.Comp.PatMetaObj (loc, mO, ttau) -> (* print_string "TestPatMetaObj\n"; *) proof_metaobj mO
| Synann.Comp.PatEmpty (loc, cPsi, ttau) -> print_string "TestPatEmpty\n"
| Synann.Comp.PatConst (loc, c, pat_spine, ttau) -> print_string "TestPatConst\n"
| Synann.Comp.PatVar (loc, k, ttau) -> print_string "TestPatVar\n"
| Synann.Comp.PatPair (loc, pat1, pat2, ttau) -> print_string "\nTestPatPair\n"
| Synann.Comp.PatTrue (loc, ttau) -> print_string "TestPatTrue\n"
| Synann.Comp.PatFalse (loc, ttau) -> print_string "TestPatFalse\n"
| Synann.Comp.PatAnn (loc, pat, tau, ttau) -> (* print_string "TestPatAnn\n"; *) proof_pattern pat

and proof_metaobj (loc, mO) = match mO with (* this returns steps *)
| Synann.LF.ClObj (phat, tM, ttau) -> (* print_string "TestClObj\n"; *)
	begin
		match tM with
		| Synann.LF.MObj (Synann.LF.Root(_, h, tS, cD, cPsi, sA), ttau') -> (* print_string "TestMObj\n"; *)
			let (rule_name, imp_args) = extract_rule h in
			(* let _ = print_string ("Rule " ^ R.render_cid_term rule_name ^ " has " ^ string_of_int imp_args ^ " implict arguments.\n") in *)
			let _ = extract_args (skip_imp_args imp_args tS) in
			()
		| Synann.LF.SObj (tM, ttau') -> print_string "TestSObj\n"
		| Synann.LF.PObj (h, ttau') -> print_string "TestPObj\n"
		| Synann.LF.MObj _ -> print_string "Unsupported MObj\n"
	end		
| Synann.LF.CObj (cPsi, ttau) -> print_string "TestCObj\n" 
| Synann.LF.MV (u, ttau) -> print_string "TestMV\n"

(* name this better *)
and extract_rule h = match h with 
| Synann.LF.Const (c, cD, cPsi, sA) -> 
	print_string ("Const " ^ (R.render_cid_term c) ^ "\n");
	(c, Store.Cid.Term.get_implicit_arguments c)
| Synann.LF.MVar ((c, s), cD, cPsi, sA) -> 	raise (LatexException "Unsupported head passed to extract_rule: MVar\n")
| Synann.LF.BVar _ -> raise (LatexException "Unsupported head passed to extract_rule: BVar\n")
| Synann.LF.MMVar _ -> raise (LatexException "Unsupported head passed to extract_rule: MMVar\n")
| Synann.LF.MPVar _ -> raise (LatexException "Unsupported head passed to extract_rule: MPVar\n")
| Synann.LF.PVar _ -> raise (LatexException "Unsupported head passed to extract_rule: PVar\n")
| Synann.LF.AnnH _ -> raise (LatexException "Unsupported head passed to extract_rule: AnnH\n")
| Synann.LF.Proj _ -> raise (LatexException "Unsupported head passed to extract_rule: Proj\n")
| Synann.LF.FVar _ -> raise (LatexException "Unsupported head passed to extract_rule: FVar\n")
| Synann.LF.FMVar _ -> raise (LatexException "Unsupported head passed to extract_rule: FMVar\n")
| Synann.LF.FPVar _ -> raise (LatexException "Unsupported head passed to extract_rule: FPVar\n")
| Synann.LF.HClo _ -> raise (LatexException "Unsupported head passed to extract_rule: HClo\n")
| Synann.LF.HMClo _ -> raise (LatexException "Unsupported head passed to extract_rule: HMClo\n")

and skip_imp_args imp_args tS = match imp_args, tS with
| 0, tS -> tS
| n, Synann.LF.Nil -> raise (LatexException "Too many implict arguments to skip\n")
| n, Synann.LF.App (tM, tS', _) -> 
	(* let Synann.LF.Root (_, , _, _, _, _) = tM in *)
	(* print_string ("Skipping imp_arg: " ^  string_of_head h ^ "\tNumber of imp args left: " ^ string_of_int n ^ "\n"); *)
	skip_imp_args (n - 1) tS'
| n, Synann.LF.SClo ((tS', _), _) -> skip_imp_args n tS'

and extract_args tS = 	
	begin
		match tS with
		| Synann.LF.Nil -> []
		| Synann.LF.App (tM, tS'', _) -> 
			begin
				match tM with
				| Synann.LF.Root (_, h, tS3, cD, cPsi, tA) -> print_string (string_of_head h ^ "\n"); print_string (string_of_spine tS3 ^ "\n")
				| Synann.LF.Lam (_, n, tM', cD, cPsi, tA) -> print_string (sprintf "(\\%s.%s)" (R.render_name n) (proof_normal tM'))
				| Synann.LF.LFHole _ -> raise (LatexException "Unhandled normal: LFHole\n")
				| Synann.LF.Clo _ -> raise (LatexException "Unhandled normal: Clo\n")
				| Synann.LF.Tuple _ -> raise (LatexException "Unhandled normal: Tuple\n")
			end;
			extract_args tS''
		| Synann.LF.SClo ((tS', _), _) -> extract_args tS'
	end

and proof_normal tM = match tM with
| Synann.LF.Root (_, h, tS, cD, cPsi, tA) -> 
	begin
		match tS with
		| Synann.LF.Nil -> sprintf "%s" (proof_head h)
		| _ -> sprintf "%s %s" (proof_head h) (proof_spine tS)
	end	
| Synann.LF.Lam (_, n, tM', cD, cPsi, tA) -> print_string "print lambda\n"; sprintf "\\%s.%s" (R.render_name n) (proof_normal tM')
| Synann.LF.LFHole (_, cD, cPsi, tA) -> "_"
| Synann.LF.Clo _ -> raise (LatexException "Unsupported normal passed to proof_normal: Tuple\n")
| Synann.LF.Tuple (_, tup, cD, cPsi, tA) -> sprintf "<%s>" (proof_tuple tup)

and proof_head h = match h with
| Synann.LF.BVar _ -> raise (LatexException "Unhandled head passed to proof_head: BVar\n")
| Synann.LF.Const (c, cD, cPsi, sA) -> sprintf "%s : %s" (R.render_cid_term c) (PI.typToString cD cPsi (sA, Syntax.Int.LF.EmptySub))
| Synann.LF.MVar ((c, s), cD, cPsi, sA) -> sprintf "%s : %s" (PI.headToString cD cPsi (Syntax.Int.LF.MVar (c,s))) (PI.typToString cD cPsi (sA, Syntax.Int.LF.EmptySub))
| Synann.LF.MMVar _ -> raise (LatexException "Unhandled head passed to proof_head: MMVar\n")
| Synann.LF.MPVar _ -> raise (LatexException "Unhandled head passed to proof_head: MPVar\n")
| Synann.LF.PVar _ -> raise (LatexException "Unhandled head passed to proof_head: PVar\n")
| Synann.LF.AnnH _ -> raise (LatexException "Unhandled head passed to proof_head: AnnH\n")
| Synann.LF.Proj _ -> raise (LatexException "Unhandled head passed to proof_head: Proj\n")
| Synann.LF.FVar _ -> raise (LatexException "Unhandled head passed to proof_head: FVar\n")
| Synann.LF.FMVar _ -> raise (LatexException "Unhandled head passed to proof_head: FMVar\n")
| Synann.LF.FPVar _ -> raise (LatexException "Unhandled head passed to proof_head: FPVar\n")
| Synann.LF.HClo _ -> raise (LatexException "Unhandled head passed to proof_head: HClo\n")
| Synann.LF.HMClo _ -> raise (LatexException "Unhandled head passed to proof_head: HMClo\n")

and proof_spine tS = match tS with
| Synann.LF.Nil -> ""
| Synann.LF.App (tM, tS, sA) -> sprintf "%s %s" (proof_normal tM) (proof_spine tS)
| Synann.LF.SClo ((tS, theta), sA) -> proof_spine tS

and proof_tuple tup = match tup with
| Synann.LF.Last (tM) -> sprintf "%s" (proof_normal tM)
| Synann.LF.Cons (tM, tup') -> sprintf "%s, %s" (proof_normal tM) (proof_tuple tup')

and string_of_head h = match h with
| Synann.LF.MVar ((c, s), cD, cPsi, sA) -> (PI.headToString cD cPsi (Syntax.Int.LF.MVar (c,s))) ^ " : " ^ (PI.typToString cD cPsi (sA, Syntax.Int.LF.EmptySub))
(* | Synann.LF.BVar _ -> "BVar head\n"
| Synann.LF.Const _ -> "Const head\n"
| Synann.LF.MMVar _ -> "MMVar head\n"
| Synann.LF.MPVar _ -> "MPVar head\n"
| Synann.LF.PVar _ -> "PVar head\n"
| Synann.LF.AnnH _ -> "AnnH head\n"
| Synann.LF.Proj _ -> "Proj head\n"
| Synann.LF.FVar _ -> "FVar head\n"
| Synann.LF.FMVar _ -> "FMVar head\n"
| Synann.LF.FPVar _ -> "FPVar head\n"
| Synann.LF.HClo _ -> "HClo head\n"
| Synann.LF.HMClo _ -> "HMClo head\n" *)

and string_of_spine tS = match tS with
| Synann.LF.Nil -> "Nil spine"
| Synann.LF.App _ -> "App spine"
| Synann.LF.SClo _ -> "SClo spine"

(* and annNormToInt tM = match tM with
| Synann.LF.Lam (loc, n, tM', cD, cPsi, ttau) -> 
	let (_, _, tM'') = annNormToInt tM in
	(cD, cPsi, Syntax.Int.LF.Lam (loc, n, tM''))
| Synann.LF.Root (loc, h, tS, cD, cPsi, ttau) -> (cD, cPsi, Syntax.Int.LF.Root (loc, h, tS))
| Synann.LF.LFHole (loc, cD, cPsi, ttau) -> (cD, cPsi, Syntax.Int.LF.LFHole (loc))
| Synann.LF.Clo ((n, s), cD, cPsi, ttau) -> (cD, cPsi, Syntax.Int.LF.Clo ((n, s)))
| Synann.LF.Tuple (loc, tuple, cD, cPsi, ttau) -> (cD, cPsi, Syntax.Int.LF.Tuple (loc, tuple))
 *)
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