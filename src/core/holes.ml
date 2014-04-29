(* module Holes *)

module P = Pretty.Int.DefaultPrinter
module Loc = Camlp4.PreCast.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp



(**********************************************

cD : LF.mctx
cG : Comp.gctx
tau : Comp.typ
theta :LF.msub

***********************************************)


let holes = DynArray.create ()

let none () = DynArray.empty holes

let collect (loc, cD, cG, (tau, theta)) =
  DynArray.add holes (loc, cD, cG, (tau, theta))

let ( ++ ) f g = function x -> f (g x)

let nameString n = n.Id.string_of_name

let break = "____________________________________________________________________________\n"

let ctypDeclToString cD ctypDecl =
  P.fmt_ppr_lf_ctyp_decl cD Pretty.std_lvl Format.str_formatter ctypDecl ; 
  Format.flush_str_formatter ()

(*mctxToString cD*)
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

let printOne (loc, cD, cG, (tau, theta)) =
  Store.NamedHoles.reset () ;
  Printf.printf "\n%s\n
    - Meta-Context: %s\n____________________________________________________________________________\n
    - Context: %s\n\n============================================================================\n
    - Goal Type: %s\n"
    (Loc.to_string loc)
    (mctxToString cD)
    (gctxToString cD cG)
    (P.compTypToString cD (Whnf.cnormCTyp (tau, theta)))

let printAll () =
  Store.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.NamedHoles.printingHoles := false;
