module R = Store.Cid.DefaultRenderer

let theorem = ref []
let lines = ref []

module LaTeX = struct
  open Annotated

  let get_string (s : string option) : string =
    match s with
    | None -> "No type information found."
    | Some s' -> s'

  let rec parse_fun (e : Comp.exp_chk) : unit =
    match e with
    | Comp.Fun (_, x, e', _, str) ->
       theorem := (Id.render_name x ^ ":" ^ get_string str) :: !theorem;
       parse_fun e'
    | Comp.MLam (_, x, e', _, str) ->
       theorem := (Id.render_name x ^ ":" ^ get_string str) :: !theorem;
       parse_fun e'
    | Comp.Case _ -> parse_case e
    | _ -> print_string ("What the hell happened?")

    and parse_case (e : Comp.exp_chk) : unit =
      match e with
      | Comp.Case (_, _, i, branches, _, _) ->
	 lines := "Case _ of" :: !lines;
	 List.iter parse_branch (List.rev branches)
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
	 lines := ("" ^ get_string str) :: !lines
      | Comp.PatConst (_, c, pat_spine, _, str) ->
	 lines := ((R.render_cid_comp_const c)  ^ ":" ^ get_string str) :: !lines;
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
	 lines := ((Id.render_name n) ^ ":" ^ get_string str) :: !lines;
	 parse_expr e'
      | Comp.Fun (_, n, e', _, str) ->
	 lines := ((Id.render_name n) ^ ":" ^ get_string str) :: !lines;
	 parse_expr e'
      | Comp.MLam (_, n, e', _, str) ->
	 lines := ((Id.render_name n) ^ ":" ^ get_string str) :: !lines;
	 parse_expr e'
      | Comp.Case (_, _, i, branches, _, _) ->
	 (* Could be a let. Deal with it. *)
	 lines := "Subcase _ of" :: !lines;
	 List.iter parse_branch (List.rev branches)
      | Comp.Box (_, _, _, str) ->
	 lines := (get_string str) :: !lines
      | _ -> ()
end

let parse e =
  LaTeX.parse_fun e;
  print_string ("Theorem\n");
  List.iter (fun x -> print_string (x ^ "\n")) !theorem;
  print_string ("Lines\n");
  List.iter (fun x -> print_string (x ^ "\n")) !lines
