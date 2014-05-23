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

let cpsiToString cD cPsi = P.dctxToString cD (Whnf.normDCtx cPsi)

let printOne (loc, cD, cPsi, typ) =
  Store.NamedHoles.reset () ;
    Printf.printf "\n%s\n
     - Meta-Context: %s\n____________________________________________________________________________\n
     - LF Context: %s\n\n============================================================================\n
     - Goal Type: %s\n"
    (Loc.to_string loc)
    (mctxToString cD)
    (cpsiToString cD cPsi)
    (P.typToString cD cPsi typ)

let printAll () =
  Store.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.NamedHoles.printingHoles := false

let getNumHoles () = DynArray.length holes

let getHolePos i =
    try
      let  (loc, _, _, (_, _)) = DynArray.get holes i in Some loc
    with
      | DynArray.Invalid_arg (_, _, _) -> None

let printOneHole i =
  if none () then Printf.printf " - There are no lf holes.\n"
  else
    try
      printOne (DynArray.get holes i)
    with
      | DynArray.Invalid_arg (_, _, _) -> 
          if !Debug.chatter != 0 then
            Printf.printf " - There is no lf hole # %d.\n" i
