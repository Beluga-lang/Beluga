(* module Holes *)

module P = Pretty.Int.DefaultPrinter
module Loc = Camlp4.PreCast.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

let holes = DynArray.create ()

let none () = DynArray.empty holes

let collect (loc, cD, cG, (tau, theta)) =
  DynArray.add holes (loc, cD, cG, (tau, theta))

let ( ++ ) f g = function x -> f (g x)

let nameString n = n.Id.string_of_name

let ctypDeclToString cD ctypDecl =
  P.fmt_ppr_lf_ctyp_decl cD Pretty.std_lvl Format.str_formatter ctypDecl ;
  Format.flush_str_formatter ()

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

let gctxToString cD =
  let shift = " " in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, Comp.CTypDecl (n, tau)) ->
      "\n" ^ shift ^ (nameString n) ^ ": " ^ P.compTypToString cD tau
    | LF.Dec (cG, Comp.CTypDecl (n, tau)) ->
      toString cG ^ "\n" ^ shift ^ (nameString n) ^ ": " ^ P.compTypToString cD tau
  in toString ++ Whnf.normCtx

let printOne (loc, cD, cG, (tau, theta)) =
  Printf.printf "\n%s\n- Meta-Context: %s\n- Context: %s\n- Type: %s\n"
    (Loc.to_string loc)
    (mctxToString cD)
    (gctxToString cD cG)
    (P.compTypToString cD (Whnf.cnormCTyp (tau, theta)))

let printAll () =
  DynArray.iter printOne holes

let printOneHole i =
  try
    printOne (DynArray.get holes i)
  with
    | DynArray.Invalid_arg (_, _, _) -> if !Debug.chatter != 0 then
        Printf.printf "\nThere is not %d-th hole.\n" i
      else
        ()

let printNumHoles () =
  Printf.printf "\nThe number of holes is %d.\n" (DynArray.length holes)

let printHolePos i =
  try
    let  (loc, _, _, (_, _)) = DynArray.get holes i in
    let  (file_name, start_line, start_bol, start_off, stop_line, stop_bol, stop_off, _ghost) = Loc.to_tuple loc in
    Printf.printf "(\"%s\".(%d %d %d).(%d %d %d))\n" file_name start_line start_bol start_off stop_line stop_bol stop_off
  with
    | DynArray.Invalid_arg (_, _, _) -> if !Debug.chatter != 0 then
        Printf.printf "\nThere is no %d-th hole.\n" i
      else
        ()
