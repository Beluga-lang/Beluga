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

let printOne (loc, cD, cPsi, typ) =
  let l = iterMctx (Whnf.normMCtx cD) cPsi typ in
  let b1 = "____________________________________________________________________________" in
  let b2 = "============================================================================" in
  Store.Cid.NamedHoles.reset () ;
    Printf.printf "\n%s\n  - Meta-Context: %s\n%s\n  - LF Context: %s\n\n%s\n  - Goal Type: %s\n  - Suggestion(s): %s"
    (Loc.to_string loc)
    (mctxToString cD)
    (b1)
    (cpsiToString cD cPsi)
    (b2)
    (P.typToString cD cPsi typ)
    (String.concat ", " (List.map (fun x -> Store.Cid.NamedHoles.getName x) l))

let printAll () =
  Store.Cid.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.Cid.NamedHoles.printingHoles := false
