module S = Substitution.LF
open Syntax.Int
open Printf

type goal =
  | Atom of Comp.typ
  | Impl of goal * goal
  | All of LF.ctyp_decl * goal

type conjunction =
  | True
  | Conjunct of conjunction * goal

type clause =
  { tHead : Comp.typ         
  ; subGoals : conjunction }



module Convert = struct

  let rec typToClause' cG tM = match tM with
    | Comp.TypArr (tA, tB) ->
      typToClause' (Conjunct (cG, typToGoal tA)) tB
    | Comp.TypBox (_) as tA ->
      { tHead = tA
      ; subGoals = cG }
    | Comp.TypBase (_) as tA ->
      { tHead = tA
      ; subGoals = cG }

  and typToGoal tM = match tM with
    | Comp.TypPiBox (LF.Decl(_) as mtD, tM') ->
      All (mtD, typToGoal tM')
    | Comp.TypArr (tA, tB) ->
      Impl (typToGoal tA, typToGoal tB)
    | Comp.TypBox (_) as tA ->
      Atom (tA)
    | Comp.TypBase (_) as tA ->
      Atom (tA)

  let typToClause tM =
    typToClause' True tM


end



module Index = struct

  open Store

  (* (Id.cid_comp_typ, (Id.cid_comp_const, clause) DynArray) Hashtbl. *)
  let compTypes = Hashtbl.create 0 
  
  (* addCompTyp c = sgnClause DynArray.t
     Create a new entry for a comp type constant, c, in the `compTypes' table and
     return it's mapping, i.e. an empty DynArray.
  *)
  let addCompTyp cidCompTyp =
    Hashtbl.add compTypes cidCompTyp (DynArray.create ());
    Hashtbl.find compTypes cidCompTyp

  (* addSgnClause ctC, sCl = ()
     Add a new sgnClause, sCl, to the DynArray ctC.
  *)
  let addSgnClause compTypConst sgnClause =
    DynArray.add compTypConst sgnClause

  (* compileSgnClause c = (c, sCl)
     Retrieve Comp.typ for comp constant c, clausify it into sCl and
     return an sgnClause (c, sCl).
  *)
  let compileSgnClause cidCompConst =
    let compConstEntry = Cid.CompConst.get cidCompConst in
    let tM = compConstEntry.Cid.CompConst.typ in
    (cidCompConst, Convert.typToClause tM)

  (* compConstName c = Id.name
     Get the string representation of comp constant c.
  *)
  let compConstName cidCompConst =
    (Cid.CompConst.get cidCompConst).Cid.CompConst.name

  (* storeCompTypConst c = ()
     Add a new entry in `compTypes' for comp type constant c and fill the DynArray
     with the clauses corresponding to the comp constants associated with c.
     The revIter function serves to preserve the order of comp constants constants
     intrinsic to the Beluga source file, since the constructors for c are
     listed in reverse order.
  *)
  let storeCompTypConst cidCompTyp =
    let compTypEntry = Cid.CompTyp.get cidCompTyp in
    let compTypConstr = compTypEntry.Cid.CompTyp.constructors in
    let compTypConst = addCompTyp cidCompTyp in
    let regSgnClause cidCompConst =
      addSgnClause compTypConst (compileSgnClause cidCompConst) in
    let rec revIter f l = match l with
      | [] -> ()
      | h :: l' -> revIter f l' ; f h
    in 
    (* DEBUGGING INFO *)
    printf "%s\n" (Id.string_of_name compTypEntry.Cid.CompTyp.name);
	printf "%d\n" (List.length compTypConstr);
	(******************)
    revIter regSgnClause compTypConstr

  (* robStore () = ()
     Store all comp type constants in the `compTypes' table.
  *)
  let robStore () =
    try
      List.iter storeCompTypConst !(DynArray.get Cid.CompTyp.entry_list !(Modules.current))
    with _ -> printf "RobStore () failed !"
  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () = Hashtbl.clear compTypes


end



module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  
  (* val compTypToString : LF.mctx -> Comp.typ -> string *)
  let compTypToString cD tA  = 
    P.compTypToString cD tA

  (* val cdeclToString : LF.mctx -> LF.ctyp_decl -> string *)
  let cdeclToString cD cdecl =
    P.cdeclToString cD cdecl

  (* val goalToLatex : goal -> LF.mctx -> string *)
  let rec goalToLatex g cD = match g with
    | Atom (tA) -> "(" ^ (compTypToString cD tA) ^ ")"
    | Impl (g1, g2) ->
      sprintf "(if %s then %s)" 
       (goalToLatex g1 cD)
       (goalToLatex g2 cD)
    | All (cdecl, g) ->
      sprintf "(for all (%s), %s)" 
       (cdeclToString cD cdecl)
       (goalToLatex g (LF.Dec (cD, cdecl)))

  (* val sgnClauseToLatex : Id.cid_comp_const * clause -> string *)
  let sgnClauseToLatex (cidCompConst, sCl) =
    let name = Id.string_of_name (compConstName cidCompConst) in (* maybe use string_of_name_latex *)
    let conclusion = compTypToString LF.Empty sCl.tHead in 
    let rec printSubgoals cG = match cG with
      | Conjunct (True, g) ->
        goalToLatex g LF.Empty
      | Conjunct (cG', g) ->
        sprintf "%s and %s" (printSubgoals cG') (goalToLatex g LF.Empty)
    in 
    match sCl.subGoals with
      | True -> 
        sprintf "[%s] %s" name conclusion
      | Conjunct (_) as cG -> 
        sprintf "[%s] if %s then %s" name (printSubgoals cG) conclusion


  let printSignatureLatex mainFile =
    let outMaccros = open_out "latex/maccros.tex" in
    let outMain = open_out mainFile in
    (* takes as input one binding (k, v) of compTypes : 
       k : cidCompTyp, v : (cidCompConst, sCl) DynArray
    *)
    let compTypeFamilyToLatex k v = 
      fprintf outMain "Definition:\n\n";
      (* for each clause in v :
         - print a rule in the main file  *)
	  (* DEBUGGING INFO *)
	  fprintf outMain "%d\n" (DynArray.length v);
	  (******************)
      DynArray.iter (fun w -> fprintf outMain "- %s\n\n" (sgnClauseToLatex w)) v
    in
    (* preamble of maccros file *)
    fprintf outMaccros "\\input{prelude}\n\n";
    (* preamble of main file *)
    fprintf outMain "\\documentclass{article}\n\n\\input{maccros}\n\n\\begin{document}\n\n";
    (* conversion to LaTex and printing of maccros *)
    Hashtbl.iter compTypeFamilyToLatex compTypes;
    (* conclusion of main file *)
    fprintf outMain "\n\\end{document}";
    close_out outMaccros;
    close_out outMain;


end



(* Interface *)

let runLatex () =
  Index.robStore ();
  Printer.printSignatureLatex "latex/main.tex";
  Index.clearIndex ();
















