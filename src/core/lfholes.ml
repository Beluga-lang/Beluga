(* module Lfholes *)

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

let holes = DynArray.create ()

let none () = DynArray.empty holes

let collect (loc, cD, cPsi, typ) =
  DynArray.add holes (loc, cD, cPsi, typ)

let ( ++ ) f g = function x -> f (g x)

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

let cpsiToString cD cPsi = P.dctxToString cD (Whnf.normDCtx cPsi)

let iterMctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Id.name list = 
  (* let tA = Whnf.normTyp tA in *)
  let rec aux acc c = function
    | LF.Empty -> acc
    | LF.Dec (cD', LF.Decl(n, LF.MTyp(tA', cPsi', LF.No)))
    | LF.Dec (cD', LF.Decl(n, LF.PTyp(tA', cPsi', LF.No)))->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        let tA' = Whnf.cnormTyp (tA', LF.MShift c) in
        Unify.StdTrail.unifyTyp cD cPsi tA (tA', LF.EmptySub);
        aux (n::acc) (c+1) cD'
      with | _ -> aux acc (c+1) cD' end
    | LF.Dec (cD', _) -> aux acc (c + 1) cD'
  in aux [] 1 cD

let iterDctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Id.name list = 
  let rec aux acc c = function
    | LF.DDec(cPsi', LF.TypDecl(n, tA')) ->
      begin try 
        Unify.StdTrail.resetGlobalCnstrs ();
        (* let tA' = Whnf.cnormTyp (tA', LF.MShift c) in *)
        Unify.StdTrail.unifyTyp cD cPsi tA (tA', LF.EmptySub);
        aux (n::acc) (c+1) cPsi'
      with | _ -> aux acc (c+1) cPsi' end
    | LF.DDec(cPsi', _) -> aux acc (c+1) cPsi'
    | _ -> acc
  in
    aux [] 1 cPsi

let printOne (loc, cD, cPsi, typ) =
  let _ = Store.Cid.NamedHoles.reset () in
  let cD = (Whnf.normMCtx cD) in
  let cPsi  = (Whnf.normDCtx cPsi) in
  let l = (iterMctx cD cPsi typ)@(iterDctx cD cPsi typ) in
  let mctx =(mctxToString cD) in
  let dctx = (cpsiToString cD cPsi) in
  let goal = (P.typToString cD cPsi typ) in
  let b1 = "____________________________________________________________________________" in
  let b2 = "============================================================================" in
  let _ = if List.length l > 0 then
    Format.printf "@\n%s@\n  - Meta-Context: %s@\n%s@\n  - LF Context: %s@\n@\n%s@\n  - Goal Type: %s@\n  - Suggestion%s: %s@\n"
      (Loc.to_string loc) (mctx) (b1) (dctx) (b2) (goal)
      (if List.length l = 1 then "" else "s") (String.concat ", " (List.map (fun x -> Store.Cid.NamedHoles.getName x) l))
  else
    Format.printf "@\n%s@\n  - Meta-Context: %s@\n%s@\n  - LF Context: %s@\n@\n%s@\n  - Goal Type: %s@\n"
      (Loc.to_string loc) (mctx) (b1) (dctx) (b2) (goal)
  in ()

let printAll () =
  let _ = Store.Cid.NamedHoles.printingHoles := true in
  let _ = DynArray.iter printOne holes in
  Store.Cid.NamedHoles.printingHoles := false
