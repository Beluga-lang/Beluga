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
| Inversion of string * string (* rule * argument *)
| RuleApp (* of ... *)
| IH (* of ... *) (* Special case of RuleApp? *)
| Subcase (* of ... *)

(* Utilities *)
let rec chop_end l = match l with
| [] -> raise (LatexException "[Latex] Unable to split empty list.")
| [x] -> ([], x)
| hd::tl -> 
	let (l', x) = chop_end tl in (hd::l', x)

(* 
let string_explode s =
	let rec exp = 
let rec string_implode ss = match ss with
| [] -> ""
| hd::tl -> (Char.escaped hd)^(string_implode tl)
 *)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l

let strip_underscore s = implode (List.filter (fun c -> c <> '_') (explode s))

let escape_underscore s =
	let rec esc_us l = 
		begin
			match l with
			| [] -> []
			| '_'::tl -> '\\'::'_'::(esc_us tl)
			| hd::tl -> hd::(esc_us tl)
		end
in implode (esc_us (explode s))

(* Latex printing functions *)
let rec latex_of_command (Command(n, x, fmt)) = 
	let no_us_name = (strip_underscore (R.render_name n)) in
	let esc_us_name = (escape_underscore (R.render_name n)) in	
	let new_name = sprintf "bel%s" no_us_name in
	begin
		match fmt with
		| None -> 
			begin
				match x with
				| 0 -> sprintf "\\newcommand{%s}[%d]{%s}\n" new_name x esc_us_name
				| _ -> sprintf "\\newcommand{%s}[%d]{%s %s}\n" new_name x esc_us_name (gen_arg_list x)
			end			
		| Some fmt' -> sprintf "\\newcommand{%s}[%d]{%s}\n" new_name x (escape_underscore fmt')
	end

and gen_arg_list n = match n with
| 0 -> ""
| m -> sprintf "%s %s" (gen_arg_list (n - 1)) (sprintf "#%d" m)

let rec latex_of_rule (Rule(n, cD, cG, prems, conc)) =
	sprintf "\\infer[%s]{%s}{%s}\n" 
	(escape_underscore (R.render_name n)) 
	(escape_underscore (PE.typToString cD cG conc)) 
	(string_of_prems cD cG prems)

and string_of_prems cD cG prems = 
	String.concat " && " (List.map escape_underscore (List.map (PE.typToString cD cG) prems))

let rec latex_of_theorem t_faprems t_termprems t_conc = match t_faprems with
| [] -> sprintf "If %s then %s\n" (string_of_tterm_list t_termprems) (string_of_tterm t_conc)
| _ -> 
	begin
		match t_termprems with
		| [] -> sprintf "%s.%s\n" (string_of_tterm_list t_faprems) (string_of_tterm t_conc)
		| _ -> sprintf "%s.If %s then %s\n" (string_of_tterm_list t_faprems) (string_of_tterm_list t_termprems) (string_of_tterm t_conc)
	end

and string_of_tterm tterm = match tterm with
| TheoremTerm (n, cD, ttau) -> 
	begin
		match n with
		| None -> sprintf "%s" (PI.subCompTypToString cD ttau)
		| Some n' -> sprintf "%s : %s" (R.render_name n') (PI.subCompTypToString cD ttau)
	end
| TheoremForall (n, cD, cdec) -> sprintf "\\forall %s : %s" (R.render_name n) (PI.cdeclToString cD cdec)

and string_of_tterm_list tterm_list = match tterm_list with
| [] -> ""
| [tterm] -> string_of_tterm tterm
| hd::tl ->
	begin
		match hd with
		| TheoremTerm _ -> sprintf "%s and %s" (string_of_tterm hd) (string_of_tterm_list tl)
		| TheoremForall _ -> sprintf "%s.%s" (string_of_tterm hd) (string_of_tterm_list tl)
	end

(* Proof generating functions *)
let proof_command n extK = 
	let rec depth k = match k with
	| Ext.LF.Typ _ -> 0
	| Ext.LF.ArrKind (_, _, k') -> 1 + depth k'
	| Ext.LF.PiKind (_, _, k') -> 1 + depth k'
	in
	(* let _ = fprintf stdout "Command (%s, %d, None)\n" (R.render_name n) (depth extK) in *)
	print_string (latex_of_command (Command (n, depth extK, None)))

(* Only called from Sgn.Const *)
let proof_rule cD cG n typ = 
	let rec list_of_typ t = match t with
	| Ext.LF.ArrTyp (_, t1, t2) -> t1::(list_of_typ t2)
	| _ -> [t]	
	in 
	(* let _ = fprintf stdout "Rule (%s, %s)\n" (R.render_name n) ("[" ^ (String.concat "; " (List.map (PE.typToString cD cG) (list_of_typ typ))) ^ "]") in *)
	let (prems, conc) = chop_end (list_of_typ typ) in
	print_string (latex_of_rule (Rule (n, cD, cG, prems, conc)))

let rec split_prems premises = match premises with
| [] -> ([], [])
| (TheoremTerm _ as hd)::tl -> 
	let (fas, terms) = split_prems tl in
		(fas,hd::terms)
| (TheoremForall _ as hd)::tl -> 
	let (fas, terms) = split_prems tl in
		(hd::fas,terms)

let rec proof e_ann = 
	let (theorem, e') = proof_theorem e_ann in
	let (t_premises, t_conclusion) = chop_end theorem in	
	let (t_faprems, t_termprems) = split_prems t_premises in	
	let _ = print_string (latex_of_theorem t_faprems t_termprems t_conclusion) in
	(* let _ = proof_case e' in *)
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
		| Synann.Comp.Case (_, _, _, _, cD', ttau) ->
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

and proof_branches b = String.concat "\n" (List.map proof_branch b)

and proof_branch b = match b with
| Synann.Comp.EmptyBranch (loc, cD1', pat, t1) -> "TestEmptyBranch\n"
| Synann.Comp.Branch (loc, cD1', _cG, Synann.Comp.PatMetaObj (loc', mO, ttau'), t1, e1) -> "TestBranch\n"
| Synann.Comp.Branch (loc, cD1', cG1, pat, t1, e1) -> (proof_pattern pat) ^ (proof_exp_chk e1)

(* How do we deal with patterns?
	Annotated patterns are easy, shed the typing and recurse on the pattern itself
	The pattern should some kind of rule
 *)
and proof_pattern pat = match pat with (* this returns steps *)
| Synann.Comp.PatMetaObj (loc, mO, ttau) -> (* print_string "TestPatMetaObj\n"; *) proof_metaobj mO
| Synann.Comp.PatAnn (loc, pat, tau, ttau) -> (* print_string "TestPatAnn\n"; *) proof_pattern pat
| Synann.Comp.PatEmpty (loc, cPsi, ttau) -> "TestPatEmpty\n"
| Synann.Comp.PatConst (loc, c, pat_spine, ttau) -> "TestPatConst\n"
| Synann.Comp.PatVar (loc, k, ttau) -> "TestPatVar\n"
| Synann.Comp.PatPair (loc, pat1, pat2, ttau) -> "\nTestPatPair\n"
| Synann.Comp.PatTrue (loc, ttau) -> "TestPatTrue\n"
| Synann.Comp.PatFalse (loc, ttau) -> "TestPatFalse\n"

(* Rewrite the following to build proof objects instead of printing strings *)
and proof_metaobj (loc, mO) = match mO with (* this returns steps *)
| Synann.LF.ClObj (phat, tM, ttau) -> (* print_string "TestClObj\n"; *)
	begin
		match tM with
		| Synann.LF.MObj (Synann.LF.Root(_, h, tS, cD, cPsi, sA), ttau') -> (* print_string "TestMObj\n"; *)
			let (rule_name, imp_args) = extract_rule h in			
			let args = extract_args (skip_imp_args imp_args tS) in
			let test = List.map (fun s -> Inversion (rule_name, s)) args in
			let rec inv_list_str l = match l with | [] -> "" | Inversion(rule, arg)::tl -> (sprintf "%s by inversion on %s\n" arg rule)^(inv_list_str tl) in
			print_string (inv_list_str test);
			inv_list_str test			
			(* print_string (sprintf "%s %s\n" rule_name args) *)
		| Synann.LF.SObj (tM, ttau') -> raise (LatexException "Unsupported normal passed to proof_metaobj: SObj\n")
		| Synann.LF.PObj (h, ttau') -> raise (LatexException "Unsupported normal passed to proof_metaobj: PObj\n")
		| Synann.LF.MObj _ -> raise (LatexException "Unsupported MObj passed to proof_metaobj\n")
	end		
| Synann.LF.CObj (cPsi, ttau) -> raise (LatexException "Unsupported mfront passed to proof_metaobj: CObj\n")
| Synann.LF.MV (u, ttau) -> raise (LatexException "Unsupported mfront passed to proof_metaobj: MV\n")

(* name this better *)
and extract_rule h = match h with 
| Synann.LF.Const (c, cD, cPsi, sA) -> (R.render_cid_term c, Store.Cid.Term.get_implicit_arguments c)
| Synann.LF.MVar ((c, s), cD, cPsi, sA) -> 	raise (LatexException "Unsupported head passed to extract_rule: MVar\n")
| Synann.LF.BVar _ -> raise (LatexException "Unsupported head passed to extract_rule: BVar\n")
| Synann.LF.MMVar _ -> raise (LatexException "Unupported head passed to extract_rule: MMVar\n")
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
| n, Synann.LF.App (tM, tS', _) -> skip_imp_args (n - 1) tS'
| n, Synann.LF.SClo ((tS', _), _) -> skip_imp_args n tS'
| _, Synann.LF.Nil -> raise (LatexException "Too many implict arguments to skip\n")

and extract_args tS = match tS with
| Synann.LF.Nil -> (* "" *) 
	[]
| Synann.LF.App (tM, tS'', _) -> (* sprintf "%s %s" (proof_normal tM) (extract_args tS'') *)
	(proof_normal tM)::(extract_args tS'')
| Synann.LF.SClo ((tS', _), _) -> 
	extract_args tS'	

(* Handle typing for lambdas *)
and proof_normal tM = match tM with
| Synann.LF.Root (_, h, tS, cD, cPsi, tA) -> 
	begin
		match tS with
		| Synann.LF.Nil -> sprintf "%s" (proof_head h)
		| _ -> sprintf "%s %s" (proof_head h) (proof_spine tS)
	end	
| Synann.LF.Lam (_, n, tM', cD, cPsi, tA) -> sprintf "\\%s.(%s)" (R.render_name n) (proof_normal tM')
| Synann.LF.LFHole (_, cD, cPsi, tA) -> "_"
| Synann.LF.Clo _ -> raise (LatexException "Unsupported normal passed to proof_normal: Tuple\n")
| Synann.LF.Tuple (_, tup, cD, cPsi, tA) -> sprintf "<%s>" (proof_tuple tup)

and proof_head h = match h with
| Synann.LF.BVar _ -> raise (LatexException "Unhandled head passed to proof_head: BVar\n")
| Synann.LF.Const (c, cD, cPsi, sA) -> sprintf "%s" (R.render_cid_term c)
| Synann.LF.MVar ((c, s), cD, cPsi, sA) -> sprintf "%s : %s" (PI.headToString cD cPsi (Syntax.Int.LF.MVar (c,s))) (PI.typToString cD cPsi (sA, Syntax.Int.LF.Shift 0))
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

and proof_exp_chk e = match e with
| Synann.Comp.Syn (_, i, _, _) -> proof_exp_syn i
| Synann.Comp.Rec _ -> raise (LatexException "Unhandled exp_chk: Rec\n")
| Synann.Comp.Fun _ -> raise (LatexException "Unhandled exp_chk: Fun\n")
| Synann.Comp.Cofun _ -> raise (LatexException "Unhandled exp_chk: Cofun\n")
| Synann.Comp.MLam _ -> raise (LatexException "Unhandled exp_chk: MLam\n")
| Synann.Comp.Pair (_, e1, e2, cD, ttau) -> 
	(proof_exp_chk e1)^(proof_exp_chk e2)
| Synann.Comp.LetPair (_, i, (_, _, e'), _, _)->
	(proof_exp_syn i)^(proof_exp_chk e')
| Synann.Comp.Let (_, i, (_, e'), _, _) ->
	(proof_exp_syn i)^(proof_exp_chk e')
| Synann.Comp.Box (_, mO, _, _) ->
	proof_metaobj mO
| Synann.Comp.Case (_, _, i, branches, _, _) ->
	begin
		match branches with
		| [] -> raise (LatexException "No branches in subcase\n")
		| [b] -> proof_branch b (* Let *)
		| hd::tl -> proof_branches branches
	end
	(* proof_subcase branches *)
(* | Synann.Comp.If -> *)
(* | Synann.Comp.Hole -> *)

and proof_exp_syn e = match e with
| Synann.Comp.Var (_, x, cD, cG, ttau) -> 
	sprintf "%s : %s" (R.render_var cG x) (PI.subCompTypToString cD ttau)
| Synann.Comp.DataConst (_, c, cD, ttau) -> 
	sprintf "%s : %s" (R.render_cid_comp_const c) (PI.subCompTypToString cD ttau)
| Synann.Comp.DataDest (_, c, cD, ttau) ->
	sprintf "%s : %s" (R.render_cid_comp_dest c) (PI.subCompTypToString cD ttau)
| Synann.Comp.Const (_, prog, cD, ttau) ->
	sprintf "%s : %s" (R.render_cid_prog prog) (PI.subCompTypToString cD ttau)
| Synann.Comp.Apply (_, i, e, cD, ttau) ->
	sprintf "%s %s : %s" (proof_exp_syn i) (proof_exp_chk e) (PI.subCompTypToString cD ttau)
| Synann.Comp.MApp (_, i, mC, cD, ttau) ->
	sprintf "%s %s : %s" (proof_exp_syn i) (proof_metaobj mC) (PI.subCompTypToString cD ttau)
| Synann.Comp.Ann (e, _, cD, ttau) ->
	proof_exp_chk e
| Synann.Comp.Equal (_, i1, i2, cD, ttau) ->
	sprintf "%s == %s : %s" (proof_exp_syn i1) (proof_exp_syn i2) (PI.subCompTypToString cD ttau)
| Synann.Comp.PairVal (_, i1, i2, cD, ttau) ->
	sprintf "(%s, %s) : %s" (proof_exp_syn i1) (proof_exp_syn i2) (PI.subCompTypToString cD ttau)
| Synann.Comp.Boolean (b, cD, ttau) ->
	sprintf "Boolean : %s" (PI.subCompTypToString cD ttau)
