module R = Store.Cid.DefaultRenderer
(***************************************************************************)
module P = Pretty.Int.DefaultPrinter
open Printf
(***************************************************************************)


let theorem = ref []
let lines = ref []

module LaTeX = struct
  open Annotated

  let get_string (s : string option) : string =
    match s with
    | None -> "No type information found."
    | Some s' -> s'

  (***************************************************************************)
  let subCompTypToString tclo = 
    P.subCompTypToString Syntax.Int.LF.Empty tclo
  (***************************************************************************)

  (*let rec parse_fun (e : Comp.exp_chk) : unit =
    match e with
    | Comp.Fun (_, x, e', _, str) ->
       theorem := !theorem @ [Id.render_name x ^ ":" ^ get_string str];
       parse_fun e'
    | Comp.MLam (_, x, e', _, str) ->
       theorem := !theorem @ [Id.render_name x ^ ":" ^ get_string str];
       parse_fun e'
    | Comp.Case _ -> parse_case e
    | _ -> print_string ("What the hell happened?") *)

(***************************************************************************)
let rec parse_fun (e : Comp.exp_chk) : unit =
    match e with
    | Comp.Fun (_, x, e', tclo, str) ->
       theorem := !theorem @ [Id.render_name x ^ ":" ^ get_string str];
       parse_fun e';
       printf "\nFUNCTION, tclo : %s, string : %s\n\n" (subCompTypToString tclo) (get_string str)
    | Comp.MLam (_, x, e', _, str) ->
       theorem := !theorem @ [Id.render_name x ^ ":" ^ get_string str];
       parse_fun e'
    | Comp.Case _ -> parse_case e
    | _ -> print_string ("What the hell happened?")
(***************************************************************************)

    and parse_case (e : Comp.exp_chk) : unit =
      match e with
      | Comp.Case (_, _, i, branches, _, _) ->
	 lines := !lines @ ["Case _ of"];
	 List.iter parse_branch branches
      | _ -> print_string ("What the hell happened?")

    and parse_branch (branch : Comp.branch) : unit =
      match branch with
      | Comp.EmptyBranch (_, _, pat, _) ->
	 parse_pattern pat
      | Comp.Branch (_, _, _, pat, _, e) ->
	 parse_pattern pat;
	 parse_expr e

    and parse_pattern (pat : Comp.pattern) : unit =
      match pat with
      | Comp.PatMetaObj (_, mO, _, str) ->
	 lines := !lines @ ["pat: " ^ get_string str]
      | Comp.PatConst (_, c, pat_spine, _, str) ->
	 lines := !lines @ [(R.render_cid_comp_const c)  ^ ":" ^ get_string str];
	 parse_pattern_spine pat_spine
      | Comp.PatAnn (_, pat, _, _, _) ->
	 parse_pattern pat

    and parse_pattern_spine (pat_spine : Comp.pattern_spine) : unit =
      match pat_spine with
      | Comp.PatNil _ -> ()
      | Comp.PatApp (_, pat, pat_spine', _, _) ->
	 parse_pattern pat;
	 parse_pattern_spine pat_spine'

    and parse_expr (e : Comp.exp_chk) : unit =
      match e with
      | Comp.Rec (_, n, e', _, str) ->
	 lines := !lines @ [(Id.render_name n) ^ ":" ^ get_string str];
	 parse_expr e'
      | Comp.Fun (_, n, e', _, str) ->
	 lines := !lines @ [(Id.render_name n) ^ ":" ^ get_string str];
	 parse_expr e'
      | Comp.MLam (_, n, e', _, str) ->
	 lines := !lines @ [(Id.render_name n) ^ ":" ^ get_string str];
	 parse_expr e'
      | Comp.Case (_, _, i, branches, _, _) ->
	 (* Could be a let. Deal with it. *)
	 lines := !lines @ ["Subcase _ of"];
	 List.iter parse_branch branches
      | Comp.Box (_, _, _, str) ->
	 lines := !lines @ [get_string str]
      | _ -> 
   lines := !lines @ ["something else"]
end

let parse e =
  LaTeX.parse_fun e;
  print_string ("Theorem\n");
  List.iter (fun x -> print_string (x ^ "\n")) !theorem;
  print_string ("Lines\n");
  List.iter (fun x -> print_string (x ^ "\n")) !lines
