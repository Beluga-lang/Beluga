module R' = Store.Cid.NamedRenderer
module P = Pretty.Int.DefaultPrinter
open Printf


let lines = ref []
(* used to compare the name of functions against it :
   to differentiate a call to IH of a lemma *)
let name_ref = ref ""

(* - contains one entry for each case, one entry for each subcase
   - keyed by location : Branch of Loc.t * etc..
   - each value is a table of pairs (generated_name, origin_name)
      -> generated_name != origin_name
      -> the table is made to be recursed on until we get to the first name
 *)
let mainTable : (Camlp4.PreCast.Loc.t, (Id.name, Id.name) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

module LaTeX = struct
  open Annotated

  let phatToDCtx phat =
    Annotate.PrettyAnn.phatToDCtx phat

  let fresh_name_mctx cD x =
    Annotate.PrettyAnn.fresh_name_mctx cD x

  let fresh_name_gctx cG x =
    Annotate.PrettyAnn.fresh_name_gctx cG x

  let subCompTypToLatex ?table cD sA =
    P.subCompTypToLatex ?table cD sA

  let typToLatex ?table cD cPsi sA =
    P.typToLatex ?table cD cPsi sA
  
  let expSynToString cD cG i =
    Annotate.PrettyAnn.expSynToString cD cG i

  let expChkToString cD cG e =
    Annotate.PrettyAnn.expChkToString cD cG e

  let normalToString cD cPsi m =
    Annotate.PrettyAnn.normalToString cD cPsi m

  let headToString ?mathcal cD cPsi tilde h =
    Annotate.PrettyAnn.headToString ?mathcal cD cPsi tilde h

  (* CARE : not for general purpose !
     to use when we would use headToString in this file 
     but we don't want \TERM before the name *)
  let constantNameToString cD cPsi (h : Syntax.Int.LF.head) : string =
    let Syntax.Int.LF.Const c = h in
    let name = Id.render_name_latex (Store.Cid.Term.get ~fixName:true c).Store.Cid.Term.name in
      Id.cleanup_name_latex name

  (*let msubToString cD s =
    P.msubToString cD s*)

  (*let mctxToString cD =
    P.mctxToString cD*)

  (* returns the justification corresponding to a function call *)
  let fun_call_just cD cG (i : Comp.exp_syn) =
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
        (* DEBUGGING : if anything else, it's not a call to IH *)
        (*| _ -> false *)
    in
    (* returns a string "arg1 and arg2 etc.." *)
    let get_args cD cG i =
      let rec get_args' cD cG i acc =
        match i with
          | Comp.Apply (_, i', e', _, _) ->
              (match acc with 
                | "" -> get_args' cD cG i' (expChkToString cD cG e')
                | _  -> get_args' cD cG i' ((expChkToString cD cG e') ^ " and " ^ acc))
          | Comp.Var _ ->
              acc
        in 
          get_args' cD cG i "" 
    in
      (* the justification is either :
         - "by IH using arg1 and arg2 etc.."
         - "by name_of_fun arg1 arg2 etc.." *)
    if (induction_hyp cD cG i)
      then ("\\hfill by IH using " ^ (get_args cD cG i))
      else ("\\hfill by " ^ (expSynToString cD cG i))


  (* ex : X1/N, X1/X1, X63/X1 => 
     X1 -> N
     X63 -> X1 
     our recursive retrieve_name gives us back N for X63 
   *)
  let rec add_bindings cD cD1' msub table = match msub with
    | Syntax.Int.LF.MShift _ -> ()
    (*| Syntax.Int.LF.MDot (Syntax.Int.LF.MV u, msub') ->
       let key_name = Context.getNameMCtx cD1' u in
       let Syntax.Int.LF.Dec (cD', ctyp_decl) = cD in
       (match ctyp_decl with
          | Syntax.Int.LF.Decl (n, _, _) ->
             let value_name = n in
             Hashtbl.add table key_name value_name;
             add_bindings cD' cD1' msub' table
          | Syntax.Int.LF.DeclOpt n ->
             let value_name = n in
             Hashtbl.add table key_name value_name;
             add_bindings cD' cD1' msub' table)*)
    | Syntax.Int.LF.MDot (Syntax.Int.LF.ClObj (phat, tM), msub') ->
       (*let cPsi = phatToDCtx phat in*)
       let Syntax.Int.LF.MObj m = tM in
       (*let Syntax.Int.LF.Root (_, h, Syntax.Int.LF.Nil) = m in*)
       let Syntax.Int.LF.Root (_, h, _) = m in
       (match h with
          (* mfront is a meta variable *)
          | Syntax.Int.LF.MVar (c, s) ->
             (* the s might be useful for some proofs *)
             let Syntax.Int.LF.Offset u = c in
             let key_name = Context.getNameMCtx cD1' u in
             let Syntax.Int.LF.Dec (cD', ctyp_decl) = cD in
             (match ctyp_decl with
                | Syntax.Int.LF.Decl (n, _, _) ->
                   let value_name = n in
                   (* only add binding if key_name is not the same as value_name *)
                   if key_name = value_name 
                     then add_bindings cD' cD1' msub' table
                   else 
                     Hashtbl.add table key_name value_name;
                     add_bindings cD' cD1' msub' table
                | Syntax.Int.LF.DeclOpt n ->
                   let value_name = n in
                   Hashtbl.add table key_name value_name;
                   add_bindings cD' cD1' msub' table)
          (* mfront is not a meta variable, do nothing *)
          | _ -> 
             let Syntax.Int.LF.Dec (cD', _) = cD in
             add_bindings cD' cD1' msub' table)
    (* mfront is not a meta variable, do nothing *)
    | Syntax.Int.LF.MDot (_, msub') ->
       let Syntax.Int.LF.Dec (cD', _) = cD in
       add_bindings cD' cD1' msub' table


  let rec parse_fun cD cG (e : Comp.exp_chk) : unit =
    match e with
    | Comp.Fun (_, x, e', _, _) ->
       let x = fresh_name_gctx cG x in
       let cG' = Syntax.Int.LF.Dec (cG, Syntax.Int.Comp.CTypDeclOpt x) in
       parse_fun cD cG' e'
    | Comp.MLam (_, x, e', _, _) ->
       let x = fresh_name_mctx cD x in
       let cD' = Syntax.Int.LF.Dec (cD, Syntax.Int.LF.DeclOpt x) in
       let cG' = Whnf.cnormCtx (cG, Syntax.Int.LF.MShift 1) in
       parse_fun cD' cG' e'
    | Comp.Case _ -> parse_case cD cG e

    and parse_case cD cG (e : Comp.exp_chk): unit =
      match e with
      | Comp.Case (_, _, i, branches, _, _) ->
         let scrutinee = (expSynToString cD cG i) in
	       lines := !lines @ [sprintf "By induction on %s.\n" scrutinee];
	       List.iter 
          (parse_branch 
            (sprintf "\\begin{case}\n{%s $=" scrutinee) 
            "\n\\end{case}\n" 
            cD cG None)
          branches


    and parse_branch str_begin str_end cD cG location (branch : Comp.branch) : unit =

      let rec parse_pattern ?table cD cG (pat : Comp.pattern) : unit =

        let get_tclo_from_normal m = match m with
           | LF.Root (_, _, _, _, tclo, _) -> tclo
           | LF.Lam (_, _, _, _, tclo, _) -> tclo 
        in
        let rec parse_spine ?table cD cPsi ms acc = match ms with
          | LF.App (m, LF.Nil, _) ->
              let tclo = get_tclo_from_normal m in
              acc @ [sprintf "\\deduce[\\vspace{2pt}]{%s}{%s}"
                      (typToLatex ?table cD cPsi tclo)
                      (normalToString cD cPsi m)]
          | LF.App (m, ms, _) ->
              let tclo = get_tclo_from_normal m in
              parse_spine cD cPsi ms 
                (acc @ [sprintf "\\deduce[\\vspace{2pt}]{%s}{%s}"
                         (typToLatex ?table cD cPsi tclo)
                         (normalToString cD cPsi m)])
        in
        let parse_normal ?table cD cPsi m conclusion = 
          match m with
          (* no spine -> no premises *)
          | LF.Root (_, h, LF.Nil, _, tclo, _) -> 
             let ruleName = constantNameToString cD cPsi h in
             sprintf "\\infera{\\RULE%s}{%s}{}$ }\n" 
              ruleName conclusion
          | LF.Root (_, h, ms, _, tclo, _) ->
             let ruleName = constantNameToString cD cPsi h in
             let premises = parse_spine ?table cD cPsi ms [] in
             match premises with
               | p1::[] -> 
                  sprintf "\\infera{\\RULE%s}{%s}{%s}$ }\n" 
                   ruleName conclusion p1
               | p1::p2::[] -> 
                  sprintf "\\inferaa{\\RULE%s}{%s}{%s}{%s}$ }\n" 
                   ruleName conclusion p1 p2
               | p1::p2::p3::[] -> 
                  sprintf "\\inferaaa{\\RULE%s}{%s}{%s}{%s}{%s}$ }\n" 
                   ruleName conclusion p1 p2 p3
               | _ -> 
                  sprintf "\\infera{\\RULE%s}{%s}{Unsupported: 4+ ~ premises}$ }\n"
                   ruleName conclusion
        in
        let parse_clobj ?table cD cPsi tM conclusion = match tM with
          | LF.MObj m -> parse_normal ?table cD cPsi m conclusion
        in
        let parse_metaObj ?table cD (loc, mO) conclusion = match mO with
          | LF.ClObj (phat, tM) ->
             let cPsi = phatToDCtx phat in
             parse_clobj ?table cD cPsi tM conclusion

        in
        match pat with
        | Comp.PatMetaObj (_, mO, tclo, _) ->
           let conclusion = subCompTypToLatex ?table cD tclo in
           lines := !lines @ [parse_metaObj ?table cD mO conclusion]
        | Comp.PatAnn (_, pat, _, _, _) ->
           parse_pattern ?table cD cG pat

      in 
      match branch with
        (* Comp.EmptyBranch (loc, _, pat, _) ->
            lines := !lines @ [str_begin];
            parse_pattern cD cG pat;
            lines := !lines @ ["Empty branch"];
            lines := !lines @ [str_end]
        | Comp.Branch (loc, cD1', cG, Comp.PatMetaObj (loc', mO, tclo, str), msub, e) ->
            lines := !lines @ [str_begin];
            parse_pattern cD1' cG (Comp.PatMetaObj (loc', mO, tclo, str));
            parse_expr cD1' cG e (Some loc);
            lines := !lines @ [str_end]*)
        | Comp.Branch (loc, cD1', cG', pat, msub, e) ->
            let cG_t = cG in
            let cG_ext = Context.append cG_t cG' in
            if location = None
              then 
                (* case : create new table *)
                let _ =  Hashtbl.add mainTable loc (Hashtbl.create 0) in
                lines := !lines @ [str_begin];
                parse_pattern cD1' cG' pat;
                parse_expr cD1' cG_ext e (Some loc);
                lines := !lines @ [str_end]
              else 
                (* subcase : copy table of enclosing case *)
                let Some loc' = location in
                let _ = Hashtbl.add mainTable loc (Hashtbl.copy (Hashtbl.find mainTable loc')) in
                let tbl = Hashtbl.find mainTable loc in
                (* add bindings to table *)
                add_bindings cD cD1' msub tbl;
                lines := !lines @ [str_begin];
                (* call parse_pattern with table *)
                parse_pattern ~table:tbl cD1' cG' pat;
                parse_expr cD1' cG_ext e (Some loc);
                lines := !lines @ [str_end]



    and parse_real_let cD cG (i : Comp.exp_syn) (branch : Comp.branch) location : unit =

      let Some loc = location in
      let tbl = Hashtbl.find mainTable loc in

      (* used to handle real let + inversion :
         since normal is the left of a real let, it shouldn't have a spine *)
      let parse_normal cD cPsi m just =
        let LF.Root (_, h, LF.Nil, _, tclo, _) = m in
        match h with 
          (* inversion + real let, head is a constant *)
          | Syntax.Int.LF.Const _ ->
             sprintf "$%s$ %s and inversion using rule $\\RULE%s$\n"
              (typToLatex ~table:tbl cD cPsi tclo)
              just
              (constantNameToString cD cPsi h)
          (* real let only *)
          | _ ->
            sprintf "$\\proofderiv{%s}{%s}$ %s\n" 
              (headToString cD cPsi "" h)
              (typToLatex ~table:tbl cD cPsi tclo)
              just
      in
      let parse_clobj cD cPsi tM just = match tM with
        | LF.MObj m -> parse_normal cD cPsi m just
      in
      let parse_metaObj cD (loc, mO) just = match mO with
        | LF.ClObj (phat, tM) ->
           let cPsi = phatToDCtx phat in
            parse_clobj cD cPsi tM just
      in
      let just = fun_call_just cD cG i in
      (* prints "name_of_left_of_let : typ_of_left_of_let by justification" *)
      let rec parse_pattern just cD cG (pat : Comp.pattern) : unit =
        match pat with
        | Comp.PatMetaObj (_, mO, tclo, _) ->
           lines := !lines @ [parse_metaObj cD mO just]
        | Comp.PatAnn (_, pat, _, _, _) ->
           parse_pattern just cD cG pat

      in match branch with
      (* Comp.Branch (_, cD1', cG, Comp.PatMetaObj (loc, mO, tclo, str), msub, e) ->
         parse_pattern just cD1' cG (Comp.PatMetaObj (loc, mO, tclo, str));
         parse_expr cD1' cG e location *)
      | Comp.Branch (_, cD1', cG', pat, msub, e) ->
         let cG_t = cG in
         let cG_ext = Context.append cG_t cG' in
         (* add bindings to table *)
         add_bindings cD cD1' msub tbl;
         parse_pattern just cD1' cG' pat;
         parse_expr cD1' cG_ext e location


    and parse_inversion cD cG (branch : Comp.branch) location : unit =

      let Some loc = location in
      let tbl = Hashtbl.find mainTable loc in

      let rec parse_pattern cD cG (pat : Comp.pattern) : unit =

        let get_tclo_from_normal m = match m with
           | LF.Root (_, _, _, _, tclo, _) -> tclo
           | LF.Lam (_, _, _, _, tclo, _) -> tclo 
        in
        (* val print_inversions : string -> string list -> string *)
        let rec print_inversions just l = match l with
          | h::[] -> 
             sprintf "%s %s" 
              h just
          | h::t ->
             sprintf "%s\n\n%s" 
              h (print_inversions just t)
        in
        (* used for simple inversions *)
        let rec parse_spine cD cPsi ms acc = match ms with
          | LF.App (m, LF.Nil, _) ->
             let tclo = get_tclo_from_normal m in
              acc @ [sprintf "$\\proofderiv{%s}{%s}$" 
                      (normalToString cD cPsi m) 
                      (typToLatex ~table:tbl cD cPsi tclo)]
          | LF.App (m, ms, _) ->
              let tclo = get_tclo_from_normal m in
              parse_spine cD cPsi ms 
                (acc @ [sprintf "$\\proofderiv{%s}{%s}$" 
                         (normalToString cD cPsi m) 
                         (typToLatex ~table:tbl cD cPsi tclo)])
        in
        (* used for nested inversions *)
        let parse_normal_nested cD cPsi m name_outer_inversion = match m with
            (* no spine, simple inversion *)
            | LF.Root (_, h, LF.Nil, _, tclo, _) -> 
               sprintf "$\\proofderiv{%s}{%s}$ \\hfill by inversion using rule $\\RULE%s$\n"
                (normalToString cD cPsi m)
                (typToLatex ~table:tbl cD cPsi tclo)
                name_outer_inversion
            (* spine, nested inversions *)
            | LF.Root (_, h, ms, _, _, _) ->
               let inversion_list = parse_spine cD cPsi ms [] in
               let justification = 
                 sprintf "\\hfill by inversion using rules $\\RULE%s$ and $\\RULE%s$\n"
                  name_outer_inversion
                  (constantNameToString cD cPsi h) 
               in print_inversions justification inversion_list
        in
        let rec parse_spine_nested cD cPsi ms name_outer_inversion = match ms with
          | LF.App (m, LF.Nil, _) ->
             sprintf "%s\n"
              (parse_normal_nested cD cPsi m name_outer_inversion)
          | LF.App (m, ms, _) ->
             sprintf "%s\n\n%s"
              (parse_normal_nested cD cPsi m name_outer_inversion)
              (parse_spine_nested cD cPsi ms name_outer_inversion)
        in
        (* all the work is done here :
           - no spine -> print "type_of_head"
           - spine    -> for every normal in the spine print "type_of_normal : name_of_normal"
           add justification : "by inversion using rule name_of_head"
         *)
        let parse_normal cD cPsi m = match m with
          | LF.Root (_, h, LF.Nil, _, tclo, _) -> 
             sprintf "$%s$ \\hfill by inversion using rule $\\RULE%s$\n"
              (typToLatex ~table:tbl cD cPsi tclo)
              (constantNameToString cD cPsi h)
          (* simple inversion : first elem of spine has no spine *)
          | LF.Root (_, h, (LF.App (LF.Root (_, _, LF.Nil, _, _, _), _, _) as ms), _, tclo, _) ->
             let inversion_list = parse_spine cD cPsi ms [] in
             let justification = sprintf "\\hfill by inversion using rule $\\RULE%s$\n" 
                                  (constantNameToString cD cPsi h) 
             in print_inversions justification inversion_list
          (* nested inversions *)
          | LF.Root (_, h, ms, _, _, _) ->
             let name_outer_inversion = constantNameToString cD cPsi h in
             parse_spine_nested cD cPsi ms name_outer_inversion
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
        | Comp.PatMetaObj (_, mO, tclo, _) ->
           lines := !lines @ 
            [parse_metaObj cD mO]
        | Comp.PatAnn (_, pat, _, _, _) ->
           parse_pattern cD cG pat

      in match branch with
      (* Comp.Branch (_, cD1', cG, Comp.PatMetaObj (loc, mO, tclo, str), msub, e) -> 
         parse_pattern cD1' cG (Comp.PatMetaObj (loc, mO, tclo, str));
         parse_expr cD1' cG e location *)
      | Comp.Branch (_, cD1', cG', pat, msub, e) ->
         let cG_t = cG in
         let cG_ext = Context.append cG_t cG' in
         (* add bindings to table *)
         add_bindings cD cD1' msub tbl;
         parse_pattern cD1' cG' pat;
         parse_expr cD1' cG_ext e location


    and parse_expr cD cG (e : Comp.exp_chk) location : unit =

      let Some loc = location in
      let tbl = Hashtbl.find mainTable loc in

      (* box functions are used for the case e : Comp.Box *)
      (* returns string "arg1 and arg2 etc.."*)
      let rec parse_spine_box cD cPsi ms = match ms with
        | LF.App (m, LF.Nil, str) ->
           sprintf "$%s$"
            (normalToString cD cPsi m)
        | LF.App (m, ms, str) ->
           sprintf "$%s$ and %s"
            (normalToString cD cPsi m)
            (parse_spine_box cD cPsi ms)
      in
      (* returns string "by name_of_rule using arg1 and arg2 etc.." *)
      let parse_normal_box cD cPsi m = match m with
        | LF.Root (_, h, LF.Nil, _, tclo, _) ->
           (match h with 
             | Syntax.Int.LF.Const _ ->
                sprintf "\\hfill by $\\RULE%s$" 
                 (constantNameToString cD cPsi h)
             | _ ->
                sprintf "\\hfill by $%s$" 
                 (headToString ~mathcal:true cD cPsi "~" h))
        | LF.Root (_, h, ms, _, tclo, _) ->
           sprintf "\\hfill by $\\RULE%s$ using %s"
           (constantNameToString cD cPsi h)
           (parse_spine_box cD cPsi ms)
      in
      let parse_clobj_box cD cPsi tM = match tM with
        | LF.MObj m -> parse_normal_box cD cPsi m
      in
      let parse_metaObj_box cD (loc, mO) = match mO with
        | LF.ClObj (phat, tM) ->
           let cPsi = phatToDCtx phat in
           parse_clobj_box cD cPsi tM

      in match e with
      (* Comp.Rec (_, n, e', _, str) ->
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
	       parse_expr cD' cG' e'*)
      | Comp.Case (_, _, i, branches, _, _) ->
         (match branches with
           | [branch] -> (match i with
              (* single branch and exp_syn = Var -> inversion *)
              | Comp.Var _ ->
                 parse_inversion cD cG branch location
              (* single branch and exp_syn = Apply -> real let *)
              | Comp.Apply _ ->
                 parse_real_let cD cG i branch location
              (* CARE : not sure if it is correct to parse this as an inversion
                 example in lam.bel *)
              | Comp.Ann _ ->
                 parse_inversion cD cG branch location
              | _ -> 
                 lines := !lines @ [sprintf "Inversion OR real let of %s: " (expSynToString cD cG i)];
                 parse_inversion cD cG branch location)
           (* multiple branches -> subcases *)
           | _ -> 
             let scrutinee = (expSynToString cD cG i) in
             List.iter 
              (parse_branch 
                (sprintf "\\begin{subcase}\n{%s $= " scrutinee) 
                "\\end{subcase}\n" 
                cD cG location) 
              branches)
      | Comp.Box (_, mO, tclo, str) ->
         (* print head of normal of metaObj as a justification + arguments in spine (optional) *)
	       lines := !lines @ [sprintf "$%s$ %s" 
                            (subCompTypToLatex ~table:tbl cD tclo) 
                            (parse_metaObj_box cD mO)]
      | Comp.Syn (_, i, tclo, str) ->
         lines := !lines @ [sprintf "$%s$ %s" 
                            (subCompTypToLatex ~table:tbl cD tclo) 
                            (fun_call_just cD cG i)]
      | _ -> 
         lines := !lines @ ["Some weard expression."]
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
  (* initial cG : declaration containing function name *)
  let cG = Syntax.Int.LF.Dec (Syntax.Int.LF.Empty, Syntax.Int.Comp.CTypDeclOpt name) in
  (* initial cD *)
  let cD = Syntax.Int.LF.Empty in
  (* fill up lines *)
  let _ = LaTeX.parse_fun cD cG e in
  let str = printLines !lines in
  (* clear *)
  let _ = lines := [] in
  let _ = Hashtbl.clear mainTable in
  str

