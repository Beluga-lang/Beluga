(* module Holes *)

module P = Pretty.Int.DefaultPrinter
module Loc = Camlp4.PreCast.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp
module Cover = Coverage

type hole = Loc.t * LF.mctx * Comp.gctx * (Comp.typ * LF.msub)

let holes = DynArray.create ()

let stagedholes = DynArray.create ()

let none () = DynArray.empty holes

let collect (loc, cD, cG, (tau, theta)) =
  DynArray.add stagedholes (loc, cD, cG, (tau, theta))

let ( ++ ) f g = function x -> f (g x)

let nameString n = n.Id.string_of_name

let ctypDeclToString cD ctypDecl =
  P.fmt_ppr_lf_ctyp_decl ~print_status:true cD Pretty.std_lvl Format.str_formatter ctypDecl ; 
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

(** More holes **)

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

(* Should only be called with the loc of a hole *)
let getHoleNum loc =
    DynArray.index_of
      (fun (loc', _cD, _cG, (_tau, _mS)) -> if loc = loc' then true else false) holes

let getStagedHoleNum loc =
    DynArray.index_of
      (fun (loc', _cD, _cG, (_tau, _mS)) -> if loc = loc' then true else false) stagedholes

let setStagedHolePos i l =
      let  (loc, cD, cG, tclo) = DynArray.get stagedholes i in
      DynArray.set stagedholes i (l, cD, cG, tclo)

let (printOne : hole -> unit) (loc, cD, cG, (tau, theta)) =
  Store.NamedHoles.reset () ;
  let b1 = "____________________________________________________________________________" in
  let b2 = "============================================================================" in
  Printf.printf 
    "\n%s\n- Meta-Context: %s\n%s\n- Context: %s\n\n%s\n- Goal Type: %s\n"
    (Loc.to_string loc)
    (mctxToString cD)
    (b1)
    (gctxToString cD cG)
    (b2)
    (P.compTypToString cD (Whnf.cnormCTyp (tau, theta)))
(*    (P.expChkToString cD cG (Interactive.intro tau))
    (try (match (Interactive.split "s" cD cG) with
    | None -> "No variable s found"
    | Some exp -> (P.expChkToString cD cG exp))
    with _ -> "Can't split on s") *)

let printAll () =
  Store.NamedHoles.printingHoles := true;
  DynArray.iter printOne holes;
  Store.NamedHoles.printingHoles := false

let printOneHole i =
  if none () then Printf.printf " - There are no holes.\n"
  else
    try
      printOne (DynArray.get holes i)
    with
      | DynArray.Invalid_arg (_, _, _) -> 
          if !Debug.chatter != 0 then
            Printf.printf " - There is no hole # %d.\n" i


let getOneHole i = DynArray.get holes i

let getNumHoles () = DynArray.length holes

let getHolePos i =
    try
      let  (loc, _, _, (_, _)) = DynArray.get holes i in Some loc
    with
      | DynArray.Invalid_arg (_, _, _) -> None
