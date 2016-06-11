module R = Store.Cid.DefaultRenderer
module R' = Store.Cid.NamedRenderer
module P = Pretty.Int.DefaultPrinter
open Printf


let lines = ref []
(* name_ref is used to compare the name of functions against it, to differentiate a call to IH of a lemma *)
let name_ref = ref ""

module LaTeX = struct
  open Annotated

  let get_string (s : string option) : string =
    match s with
    | None -> "No type information found."
    | Some s' -> s'

  let subCompTypToLatex cD sA =
    P.subCompTypToLatex cD sA

  let typToLatex cD cPsi sA =
    P.typToLatex cD cPsi sA
  
  let expSynToString cD cG i =
    Annotate.PrettyAnn.expSynToString cD cG i

  let metaObjToString cD mO =
    Annotate.PrettyAnn.metaObjToString cD mO

  let normalToString cD cPsi m =
    Annotate.PrettyAnn.normalToString cD cPsi m

  let headToString cD cPsi tilde h =
    Annotate.PrettyAnn.headToString cD cPsi tilde h

  let phatToDCtx phat =
    Annotate.PrettyAnn.phatToDCtx phat

  let fresh_name_mctx cD x =
    Annotate.PrettyAnn.fresh_name_mctx cD x

  let fresh_name_gctx cG x =
    Annotate.PrettyAnn.fresh_name_gctx cG x

  let rec parse_fun cD cG (e : Comp.exp_chk) : unit =
    match e with
    | Comp.Fun (_, x, e', tclo, str) ->
       let x = fresh_name_gctx cG x in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x) in
       parse_fun cD cG' e'
    | Comp.MLam (_, x, e', _, str) ->
       let x = fresh_name_mctx cD x in
       let cD' = Syntax.Int.LF.Dec (cD, Syntax.Int.LF.DeclOpt x) in
       let cG' = Whnf.cnormCtx (cG, Syntax.Int.LF.MShift 1) in
       parse_fun cD' cG' e'
    | Comp.Case _ -> parse_case cD cG e

    and parse_case cD cG (e : Comp.exp_chk): unit =
      match e with
      | Comp.Case (_, _, i, branches, _, str) ->
         let scrutinee = (expSynToString cD cG i) in
	       lines := !lines @ [sprintf "By induction on %s.\n" scrutinee];
	       List.iter (parse_branch (sprintf "\\begin{case}\n{%s = " scrutinee) "\n\\end{case}\n" cD cG) branches


    and parse_branch str_begin str_end cD cG (branch : Comp.branch) : unit =

      let rec parse_pattern cD cG (pat : Comp.pattern) : unit =
        let get_tclo_from_normal m = match m with
           | LF.Root (_, h, LF.Nil, str1, tclo, str2) -> tclo
           | LF.Root (_, h, ms, str1, tclo, str2) -> tclo
        in
        (* TODO : inside normal could have another inversion : test2.bel [|- t_pred (t_succ D)] = d *)
        let rec parse_spine cD cPsi ms acc = match ms with
          | LF.App (m, LF.Nil, str) ->
              let tclo = get_tclo_from_normal m in
              (sprintf "$%s$ : $%s$\n" (normalToString cD cPsi m) (typToLatex cD cPsi tclo)) ^ acc
          | LF.App (m, ms, str) ->
              let tclo = get_tclo_from_normal m in
              parse_spine cD cPsi ms 
                ((sprintf "$%s$ : $%s$\n" (normalToString cD cPsi m) (typToLatex cD cPsi tclo)) ^ acc)
        in
        let parse_normal cD cPsi m = match m with
          | LF.Root (_, h, LF.Nil, str1, tclo, str2) -> ""
          | LF.Root (_, h, ms, str1, tclo, str2) ->
             parse_spine cD cPsi ms (sprintf "by $%s$" (headToString cD cPsi "~" h))
        in
        let parse_clobj cD cPsi tM = match tM with
          | LF.MObj m -> parse_normal cD cPsi m
        in
        let parse_metaObj cD (loc, mO) = match mO with
          | LF.ClObj (phat, tM) ->
             let cPsi = phatToDCtx phat in
             parse_clobj cD cPsi tM
        in
        match pat with
        | Comp.PatMetaObj (_, mO, tclo, str) ->
           let additional_info = parse_metaObj cD mO in
           (match additional_info with 
              | "" -> 
                lines := !lines @ 
                  [sprintf "%s}\n" (subCompTypToLatex cD tclo)]
              | _ ->
                lines := !lines @ 
                 [sprintf "%s\n\n%s}\n" (subCompTypToLatex cD tclo) additional_info])
        (*| Comp.PatConst (_, c, pat_spine, _, str) ->
           lines := !lines @
            [sprintf "constant"];
            (*(R.render_cid_comp_const c)  ^ ":" ^ get_string str*)
           parse_pattern_spine cD cG pat_spine*)
        | Comp.PatAnn (_, pat, _, _, _) ->
           parse_pattern cD cG pat

        (*and parse_pattern_spine cD cG (pat_spine : Comp.pattern_spine) : unit =
          match pat_spine with
            | Comp.PatNil _ -> ()
            | Comp.PatApp (_, pat, pat_spine', _, _) ->
               parse_pattern cD cG pat;
               parse_pattern_spine cD cG pat_spine'*)

      in match branch with
      | Comp.EmptyBranch (_, _, pat, _) ->
         lines := !lines @ [str_begin];
         parse_pattern cD cG pat;
         lines := !lines @ ["Empty branch"];
         lines := !lines @ [str_end]
      | Comp.Branch (_, cD1', cG, Comp.PatMetaObj (loc, mO, tclo, str), _, e) ->
         lines := !lines @ [str_begin];
         parse_pattern cD1' cG (Comp.PatMetaObj (loc, mO, tclo, str));
         parse_expr cD1' cG e;
         lines := !lines @ [str_end]
      | Comp.Branch (_, cD1', cG', pat, _, e) ->
         let cG_t = cG in
         let cG_ext = Context.append cG_t cG' in
         lines := !lines @ [str_begin];
         parse_pattern cD1' cG' pat;
         parse_expr cD1' cG_ext e;
         lines := !lines @ [str_end]


    and parse_real_let cD cG (i : Comp.exp_syn) (branch : Comp.branch) : unit =
      (* returns true if the justification is by IH, false else *)
      let rec induction_hyp cD cG i =
        match i with
          | Comp.Apply (_, i', _, _, _) ->
             induction_hyp cD cG i'
          | Comp.Var (_, x, _, _) -> 
             let name = R'.render_var cG x in
             if (!name_ref = name)
              then true
             else false
      in
      let rec parse_pattern just cD cG (pat : Comp.pattern) : unit =
        match pat with
        | Comp.PatMetaObj (_, mO, tclo, str) ->
           lines := !lines @ 
            [sprintf "$%s$ : %s %s\n" (metaObjToString cD mO) (subCompTypToLatex cD tclo) just]
        | Comp.PatAnn (_, pat, _, _, _) ->
           parse_pattern just cD cG pat
      in 
      let just = 
        (if (induction_hyp cD cG i)
          then ("by IH : " ^ (expSynToString cD cG i))
        else ("by " ^ (expSynToString cD cG i))
        ) in
      match branch with
      | Comp.EmptyBranch (_, _, pat, _) ->
         parse_pattern just cD cG pat;
         lines := !lines @ ["Empty branch"]
      | Comp.Branch (_, cD1', cG, Comp.PatMetaObj (loc, mO, tclo, str), _, e) ->
         parse_pattern just cD1' cG (Comp.PatMetaObj (loc, mO, tclo, str));
         parse_expr cD1' cG e
      | Comp.Branch (_, cD1', cG', pat, _, e) ->
         let cG_t = cG in
         let cG_ext = Context.append cG_t cG' in
            parse_pattern just cD1' cG' pat;
            parse_expr cD1' cG_ext e


    (* similar to parse_branch *)
    and parse_inversion cD cG (branch : Comp.branch) : unit =

      let rec parse_pattern cD cG (pat : Comp.pattern) : unit =
        let get_tclo_from_normal m = match m with
           | LF.Root (_, h, LF.Nil, str1, tclo, str2) -> tclo
           | LF.Root (_, h, ms, str1, tclo, str2) -> tclo
        in
        (* TODO : inside normal could have another inversion : test2.bel [|- t_pred (t_succ D)] = d *)
        let rec parse_spine just cD cPsi ms acc = match ms with
          | LF.App (m, LF.Nil, str) ->
              let tclo = get_tclo_from_normal m in
              (sprintf "$%s$ : $%s$ %s\n\n" (normalToString cD cPsi m) (typToLatex cD cPsi tclo) just) ^ acc
          | LF.App (m, ms, str) ->
              let tclo = get_tclo_from_normal m in
              parse_spine just cD cPsi ms 
                ((sprintf "$%s$ : $%s$ %s\n\n" (normalToString cD cPsi m) (typToLatex cD cPsi tclo) just) ^ acc)
        in
        let parse_normal cD cPsi m = match m with
          | LF.Root (_, h, LF.Nil, str1, tclo, str2) -> ""
          | LF.Root (_, h, ms, str1, tclo, str2) ->
             parse_spine (sprintf "by inversion using rule $%s$" (headToString cD cPsi "~" h)) cD cPsi ms ""
        in
        let parse_clobj cD cPsi tM = match tM with
          | LF.MObj m -> parse_normal cD cPsi m
        in
        let parse_metaObj cD (loc, mO) = match mO with
          | LF.ClObj (phat, tM) ->
             let cPsi = phatToDCtx phat in
             parse_clobj cD cPsi tM
        in
        match pat with
        | Comp.PatMetaObj (_, mO, tclo, str) ->
           lines := !lines @ 
            [sprintf "%s" (parse_metaObj cD mO)]
        | Comp.PatAnn (_, pat, _, _, _) ->
           parse_pattern cD cG pat

      in match branch with
      | Comp.EmptyBranch (_, _, pat, _) ->
         parse_pattern cD cG pat;
         lines := !lines @ ["Empty branch"]
      | Comp.Branch (_, cD1', cG, Comp.PatMetaObj (loc, mO, tclo, str), _, e) ->
         parse_pattern cD1' cG (Comp.PatMetaObj (loc, mO, tclo, str));
         parse_expr cD1' cG e
      | Comp.Branch (_, cD1', cG', pat, _, e) ->
         let cG_t = cG in
         let cG_ext = Context.append cG_t cG' in
            parse_pattern cD1' cG' pat;
            parse_expr cD1' cG_ext e


    (* TODO : print other cases that are not Case *)
    and parse_expr cD cG (e : Comp.exp_chk) : unit =
      let parse_normal cD cPsi m = match m with
        | LF.Root (_, h, LF.Nil, str1, tclo, str2) ->
           (headToString cD cPsi "~" h)
        | LF.Root (_, h, ms, str1, tclo, str2) ->
           (headToString cD cPsi "~" h)
      in
      let parse_clobj cD cPsi tM = match tM with
        | LF.MObj m -> parse_normal cD cPsi m
      in
      let parse_metaObj cD (loc, mO) = match mO with
        | LF.ClObj (phat, tM) ->
           let cPsi = phatToDCtx phat in
           parse_clobj cD cPsi tM
      in
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
         (match branches with
           | [branch] -> (match i with
              (* single branch and exp_syn = var -> inversion *)
              | Comp.Var _ ->
                 (*lines := !lines @ [sprintf "Inversion of %s: \n" (expSynToString cD cG i)];*)
                 parse_inversion cD cG branch
              (* single branch and exp_syn = Apply -> real let *)
              | Comp.Apply _ ->
                 (*lines := !lines @ [sprintf "Real let of %s: " (expSynToString cD cG i)];*)
                 parse_real_let cD cG i branch
              | _ -> 
                 lines := !lines @ [sprintf "Inversion OR real let of %s: " (expSynToString cD cG i)];
                 parse_inversion cD cG branch)
           (* multiple branches -> subcases *)
           | _ -> 
             let scrutinee = (expSynToString cD cG i) in
             List.iter (parse_branch (sprintf "\\begin{subcase}\n{%s = " scrutinee) "\\end{subcase}\n" cD cG) branches)
      | Comp.Box (_, mO, tclo, str) ->
         (* want to print head of normal of metaObj as a justification *)
	       lines := !lines @ [sprintf "%s\nby $%s$"(subCompTypToLatex cD tclo) (parse_metaObj cD mO)]
      | _ -> 
         (* TODO test.bel last line falls in this case *)
         lines := !lines @ ["something else"]
end

let printLines l = 
  let rec printLines' l str = match l with
    | [] -> str
    | h::t -> printLines' t (str ^ h ^ "\n")
  in 
  printLines' l ""

let parse e cidProg =
  let entry = Store.Cid.Comp.get cidProg in
  let name = entry.Store.Cid.Comp.name in
  let _ = name_ref := (Id.render_name name) in
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

