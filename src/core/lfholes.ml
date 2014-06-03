(* module Holes *)

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
  P.fmt_ppr_lf_ctyp_decl cD Pretty.std_lvl Format.str_formatter ctypDecl ; 
  Format.flush_str_formatter ()

let mctxToString =
  let shift = "\t" in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, ctypDecl) ->
      "\n" ^ shift ^ ctypDeclToString LF.Empty ctypDecl
    | LF.Dec (cD, ctypDecl) ->
      toString cD ^ "\n" ^ shift ^ ctypDeclToString cD ctypDecl
  in toString ++ Whnf.normMCtx

let cpsiToString cD cPsi = P.dctxToString cD (Whnf.normDCtx cPsi)

let printOne (loc, cD, cPsi, typ) =
  let b1 = "____________________________________________________________________________" in
  let b2 = "============================================================================" in
  Store.NamedHoles.reset () ;
    Printf.printf "\n%s\n    - Meta-Context: %s\n%s\n    - LF Context: %s\n\n%s\n    - Goal Type: %s\n"
    (Loc.to_string loc)
    (mctxToString cD)
    (b1)
    (cpsiToString cD cPsi)
    (b2)
    (P.typToString cD cPsi typ)

let printAll () =
  Store.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.NamedHoles.printingHoles := false;
