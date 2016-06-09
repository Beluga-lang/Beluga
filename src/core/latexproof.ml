module R = Store.Cid.DefaultRenderer
module P = Pretty.Int.DefaultPrinter
open Printf


let lines = ref []

module LaTeX = struct
  open Annotated

  let get_string (s : string option) : string =
    match s with
    | None -> "No type information found."
    | Some s' -> s'

  (***************************************************************************)
  let expSynToString cD cG i   =
    Annotate.PrettyAnn.expSynToString cD cG i

  let fresh_name_mctx cD x =
    Annotate.PrettyAnn.fresh_name_mctx cD x

  let fresh_name_gctx cG x =
    Annotate.PrettyAnn.fresh_name_gctx cG x
  (***************************************************************************)

  let rec parse_fun cD cG (e : Comp.exp_chk) : unit =
    match e with
    | Comp.Fun (_, x, e', tclo, str) ->
       (* let (Syntax.Int.Comp.TypArr (tau1, _), _) = tclo in *)
       (* let decl = Syntax.Int.Comp.CTypDecl (x, tau1) in *)
       let x = fresh_name_gctx cG x in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x) in
       parse_fun cD cG' e'
    | Comp.MLam (_, x, e', _, str) ->
       let x = fresh_name_mctx cD x in
       let cD' = Syntax.Int.LF.Dec (cD, Syntax.Int.LF.DeclOpt x) in
       let cG' = Whnf.cnormCtx (cG, Syntax.Int.LF.MShift 1) in
       parse_fun cD' cG' e'
    | Comp.Case _ -> parse_case cD cG e
    | _ -> print_string ("What the hell happened?") 

    and parse_case cD cG (e : Comp.exp_chk): unit =
      match e with
      | Comp.Case (_, _, i, branches, _, str) ->
	       lines := !lines @ [sprintf "\n\nCase %s of :\n\n" (expSynToString cD cG i)];
	      List.iter (parse_branch cD cG) branches
      | _ -> print_string ("What the hell happened?")

    and parse_branch cD cG (branch : Comp.branch) : unit =
      match branch with
      | Comp.EmptyBranch (_, _, pat, _) ->
	       parse_pattern cD cG pat
      | Comp.Branch (_, _, _, pat, _, e) ->
	       parse_pattern cD cG pat;
	       parse_expr cD cG e

    and parse_pattern cD cG (pat : Comp.pattern) : unit =
      match pat with
      | Comp.PatMetaObj (_, mO, _, str) ->
	       lines := !lines @ ["pat: " ^ get_string str]
      | Comp.PatConst (_, c, pat_spine, _, str) ->
	       lines := !lines @ [(R.render_cid_comp_const c)  ^ ":" ^ get_string str];
	       parse_pattern_spine cD cG pat_spine
      | Comp.PatAnn (_, pat, _, _, _) ->
	       parse_pattern cD cG pat

    and parse_pattern_spine cD cG (pat_spine : Comp.pattern_spine) : unit =
      match pat_spine with
      | Comp.PatNil _ -> ()
      | Comp.PatApp (_, pat, pat_spine', _, _) ->
	       parse_pattern cD cG pat;
	       parse_pattern_spine cD cG pat_spine'


    and parse_expr cD cG (e : Comp.exp_chk) : unit =
      match e with
      | Comp.Rec (_, n, e', _, str) ->
         let n = fresh_name_gctx cG n in
         let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt n) in
	       lines := !lines @ [(Id.render_name n) ^ ":" ^ get_string str];
	       parse_expr cD cG' e'
      | Comp.Fun (_, n, e', _, str) ->
         let n = fresh_name_gctx cG n in
         let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt n) in
	       lines := !lines @ [(Id.render_name n) ^ ":" ^ get_string str];
	       parse_expr cD cG' e'
      | Comp.MLam (_, n, e', _, str) ->
         let n = fresh_name_mctx cD n in
         let cD' = Syntax.Int.LF.Dec (cD, Syntax.Int.LF.DeclOpt n) in
         let cG' = Whnf.cnormCtx (cG, Syntax.Int.LF.MShift 1) in
	       lines := !lines @ [(Id.render_name n) ^ ":" ^ get_string str];
	       parse_expr cD' cG' e'
      | Comp.Case (_, _, i, branches, _, _) ->
	       (* Could be a let. Deal with it. *)
         lines := !lines @ [sprintf "\n\nSubcase %s of :\n\n" (expSynToString cD cG i)];
	       List.iter (parse_branch cD cG) branches
      | Comp.Box (_, _, _, str) ->
	       lines := !lines @ [get_string str]
      | _ -> 
         lines := !lines @ ["something else"]
end

let printLines l = 
  let rec printLines' l str = match l with
    | [] -> str
    | h::t -> printLines' t (str ^ h)
  in 
  printLines' l ""

let parse e cidProg =
  let entry = Store.Cid.Comp.get cidProg in
  let name = entry.Store.Cid.Comp.name in
  let tau = entry.Store.Cid.Comp.typ in
  let decl = Syntax.Int.Comp.CTypDecl (name, tau) in
  (* initial cG : type declaration (function name, function type) *)
  let cG = Syntax.Int.LF.Dec (Syntax.Int.LF.Empty, decl) in
  (* initial cD : LF.Empty *)
  let cD = Syntax.Int.LF.Empty in
  (* fill up lines *)
  let _ = LaTeX.parse_fun cD cG e in
  let str = printLines !lines in
  let _ = lines := [] in
  str

