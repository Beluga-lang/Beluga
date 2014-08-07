(* module Holes *)

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp


(****************************************************************)

let holes = DynArray.create ()

let none () = DynArray.empty holes

let collect (loc, cD, cG, (tau, theta)) =
  DynArray.add holes (loc, cD, cG, (tau, theta))

let ( ++ ) f g = function x -> f (g x)

let nameString n = n.Id.string_of_name

let ctypDeclToString cD ctypDecl =
  P.fmt_ppr_lf_ctyp_decl ~printing_holes:true cD Pretty.std_lvl Format.str_formatter ctypDecl ; 
  Format.flush_str_formatter ()

let isExplicit = function
  | LF.Decl(_, LF.MTyp (_, _, dep))
  | LF.Decl(_, LF.PTyp (_, _, dep))
  | LF.Decl(_, LF.STyp (_, _, dep))
  | LF.Decl(_, LF.CTyp (_, dep)) ->
      begin match dep with
        | LF.No -> true
        | LF.Maybe -> false
      end
  | _ -> true

let mctxToString =
  let shift = "\t" in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, ctypDecl) when (isExplicit ctypDecl || !Pretty.Control.printImplicit) ->
      "\n" ^ shift ^ ctypDeclToString LF.Empty ctypDecl
    | LF.Dec (cD, ctypDecl) when (isExplicit ctypDecl || !Pretty.Control.printImplicit)->
      let s = toString cD in
      s ^ "\n" ^ shift ^ ctypDeclToString cD ctypDecl
    | LF.Dec (cD, _ ) -> toString cD
  in toString ++ Whnf.normMCtx
 
let gctxToString cD =
  let shift = "\t" in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, Comp.CTypDecl (n, tau)) ->
      "\n" ^ shift ^ (nameString n) ^ ": " ^ P.compTypToString cD tau
    | LF.Dec (cG, Comp.CTypDecl (n, tau)) ->
      toString cG ^ "\n" ^ shift ^ (nameString n) ^ ": " ^ P.compTypToString cD tau
  in toString ++ Whnf.normCtx

let iterGctx (cD : LF.mctx) (cG : Comp.gctx) (tA : Comp.tclo) : Id.name list = 
  let rec aux acc c = function
    | LF.Empty -> acc
    | LF.Dec (cG', Comp.CTypDecl(n, tA')) ->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        let tA' = Whnf.cnormCTyp (tA', LF.MShift c) in
        Unify.StdTrail.unifyCompTyp cD tA (tA', LF.MShift 0);
        aux (n::acc) (c+1) cG'
      with | _ -> aux acc (c+1) cG' end
    | LF.Dec (cG', _) -> aux acc (c + 1) cG'
  in aux [] 1 cG

let printOne (loc, cD, cG, (tau, theta)) =
  let _ = Store.Cid.NamedHoles.reset () in
  let cD = (Whnf.normMCtx cD) in
  let cG = (Whnf.normCtx cG) in
  let l = iterGctx cD cG (tau, theta) in
  let b1 = "________________________________________________________________________________" in
  let b2 = "================================================================================" in
  let mctx = (mctxToString cD) in
  let gctx = (gctxToString cD cG) in
  let goal = (P.compTypToString cD (Whnf.cnormCTyp (tau, theta))) in
  if List.length l > 0 then
    Format.printf 
      "@\n%s@\n%s@\n    - Meta-Context: %s@\n%s@\n    - Context: %s@\n@\n%s\n    - Goal Type: %s@\n    - Variable%s of this type: %s@\n"
      (Loc.to_string loc) (b1) (mctx) (b1) (gctx) (b2) (goal) (if List.length l = 1 then "" else "s")
      (String.concat ", " (List.map (fun x -> Store.Cid.NamedHoles.getName x) l))
  else
    Format.printf 
      "@\n%s@\n%s@\n    - Meta-Context: %s@\n%s@\n    - Context: %s@\n@\n%s\n    - Goal Type: %s@\n"
      (Loc.to_string loc) (b1) (mctx) (b1) (gctx) (b2) (goal)

let printAll () =
  Store.Cid.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.Cid.NamedHoles.printingHoles := false;
