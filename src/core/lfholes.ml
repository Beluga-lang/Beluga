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

let collect (loc, cD, cPsi, typ) =
  DynArray.add holes (loc, cD, cPsi, typ)

let ( ++ ) f g = function x -> f (g x)

let nameString n = n.Id.string_of_name

let ctypDeclToString cD ctypDecl =
  P.fmt_ppr_lf_ctyp_decl cD Pretty.std_lvl Format.str_formatter ctypDecl ; 
  Format.flush_str_formatter ()

(*mctxToString cD*)
let mctxToString =
  let shift = " " in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, ctypDecl) ->
      "\n" ^ shift ^ ctypDeclToString LF.Empty ctypDecl
    | LF.Dec (cD, ctypDecl) ->
      toString cD ^ "\n" ^ shift ^ ctypDeclToString cD ctypDecl
  in toString ++ Whnf.normMCtx
 

 (*****CHANGE*****)
let cpsiToString cD cPsi = P.dctxToString cD cPsi
  

let printOne (loc, cD, cPsi, typ) =
  Store.NamedHoles.reset () ;
  Printf.printf "\n%s\n- Meta-Context: %s\n- LF Context: %s\n- Type: %s\n"
    (Loc.to_string loc)
    (mctxToString cD)
    (cpsiToString cD cPsi)
    (P.typToString cD cPsi typ)

let printAll () =
  Store.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.NamedHoles.printingHoles := false;
