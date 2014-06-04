(* module Lfoles *)

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

let holes = DynArray.create ()

let stagedholes = DynArray.create ()

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
  Store.NamedHoles.printingHoles := false

let getNumHoles () = DynArray.length holes

let getHolePos i =
    try
      let  (loc, _, _, (_, _)) = DynArray.get holes i in Some loc
    with
      | DynArray.Invalid_arg (_, _, _) -> None

let getOneHole i = DynArray.get holes i

let printOneHole i =
  if none () then Printf.printf " - There are no lf holes.\n"
  else
    try
      printOne (DynArray.get holes i)
    with
      | DynArray.Invalid_arg (_, _, _) -> 
          if !Debug.chatter != 0 then
            Printf.printf " - There is no lf hole # %d.\n" i

let getStagedHoleNum loc =
    DynArray.index_of
      (fun (loc', _cD, _cG, (_tau, _mS)) -> if loc = loc' then true else false) stagedholes

let setStagedHolePos i l =
      let  (loc, cD, cG, tclo) = DynArray.get stagedholes i in
      DynArray.set stagedholes i (l, cD, cG, tclo)

(* loc -> loc' -> bool : is loc' within loc? *)
let locWithin loc loc' =
      let (file_name,
           start_line,
           start_bol,
           start_off,
           stop_line,
           stop_bol,
           stop_off,
           _ghost) = Loc.to_tuple loc in
      let (file_name',
           start_line',
           start_bol',
           start_off',
           stop_line',
           stop_bol',
           stop_off',
           _ghost') = Loc.to_tuple loc' in
      if (file_name = file_name') then
        (if (stop_line' < stop_line || (stop_line' = stop_line && stop_off' <= stop_off)) then
          (if (start_line' > start_line || (start_line' = start_line && start_off' >= start_off)) then
            (if (start_line' = start_line && (stop_line' = stop_line && (start_off' = start_off && start_bol <> start_bol'))) then
              false
            else
              true)
          else
            false)
        else
          false)
      else
        false

(* removes all holes located within the given loc (e.g. of a function being shadowed) *)
let destroyHoles loc =
  DynArray.filter
    (fun (loc', _cD, _cG, (_tau, _mS)) -> not (locWithin loc loc'))
      holes

let commitHoles () =
  DynArray.append (DynArray.copy stagedholes) holes;
  DynArray.clear stagedholes

let stashHoles () =
  DynArray.clear stagedholes
