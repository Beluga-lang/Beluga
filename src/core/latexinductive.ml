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
  ; eVars : LF.mctx
  ; subGoals : conjunction }



module Convert = struct

  let rec typToClause' eV cG tM = match tM with
    | Comp.TypArr (tA, tB) ->
      typToClause' eV (Conjunct (cG, typToGoal tA)) tB
    | Comp.TypBox (_) as tA ->
      { tHead = tA
      ; eVars = eV
      ; subGoals = cG }
    | Comp.TypBase (_) as tA ->
      { tHead = tA
      ; eVars = eV
      ; subGoals = cG }
    | Comp.TypPiBox(mtD, tM') ->
      typToClause' (LF.Dec (eV, mtD)) cG tM'



  and typToGoal tM = match tM with
    | Comp.TypPiBox (mtD, tM') ->
      All (mtD, typToGoal tM')
    | Comp.TypArr (tA, tB) ->
      Impl (typToGoal tA, typToGoal tB)
    | Comp.TypBox (_) as tA ->
      Atom (tA)
    | Comp.TypBase (_) as tA ->
      Atom (tA)

  let typToClause tM =
    typToClause' LF.Empty True tM


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
    let compTypConstr = !(compTypEntry.Cid.CompTyp.constructors) in
    let compTypConst = addCompTyp cidCompTyp in
    let regSgnClause cidCompConst =
      addSgnClause compTypConst (compileSgnClause cidCompConst) in
    let rec revIter f l = match l with
      | [] -> ()
      | h :: l' -> revIter f l' ; f h
    in revIter regSgnClause compTypConstr

  (* robStore () = ()
     Store all comp type constants in the `compTypes' table.
  *)
  let robStore () =
    (*try*)
      List.iter storeCompTypConst !(DynArray.get Cid.CompTyp.entry_list !(Modules.current))
    (*with _ -> printf "RobStore () failed !"*)

  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () = Hashtbl.clear compTypes


end



module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  
  (* val compTypToLatex : LF.mctx -> Comp.typ -> string *)
  let compTypToLatex cD tA  = 
    P.compTypToLatex cD tA

  (* val cdeclToLatex : LF.mctx -> LF.ctyp_decl -> string *)
  let cdeclToLatex cD cdecl =
    P.cdeclToLatex cD cdecl

  (* val goalToLatex : goal -> LF.mctx -> string *)
  let rec goalToLatex g cD = match g with
    | Atom (tA) -> compTypToLatex cD tA
    | Impl (g1, g2) ->
      sprintf "if %s then %s" 
       (goalToLatex g1 cD)
       (goalToLatex g2 cD)
    | All (cdecl, g) ->
      sprintf "(for all %s, %s)" 
       (cdeclToLatex cD cdecl)
       (goalToLatex g (LF.Dec (cD, cdecl)))

  (* val sgnClauseToLatex : Id.cid_comp_const * clause -> string *)
  let sgnClauseToLatex (cidCompConst, sCl) =
    let name = Id.string_of_name_latex (compConstName cidCompConst) in 
    let conclusion = compTypToLatex sCl.eVars sCl.tHead in 
    let rec printSubgoals cG = match cG with
      | Conjunct (True, g) ->
        goalToLatex g sCl.eVars
      | Conjunct (cG', g) ->
        sprintf "%s and %s" (printSubgoals cG') (goalToLatex g sCl.eVars)
    in 
    match sCl.subGoals with
      | True -> 
        sprintf "\\begin{definition}\n[%s] %s\n\\end{definition}" 
          name conclusion
      | Conjunct (_) as cG -> 
        sprintf "\\begin{definition}\n[%s] If %s then %s\n\\end{definition}" 
          name (printSubgoals cG) conclusion


  let sgnClauseToMaccros (cidCompConst, sCl) =
    let name = Id.string_of_name_latex (compConstName cidCompConst) in
    let countSubgoals cG = 
      let rec countSubgoals' cG n = match cG with
        | Conjunct (cG', _) -> countSubgoals' cG' (n+1)
        | True -> n
      in countSubgoals' cG 0
    (* printArguments n = "\\;#1\\;#2 ... \\;#n" - only called with n > 0 *)
    in 
    let rec printArguments n = match n with
        | 1 -> "\\;#1"
        | n -> (printArguments (n-1)) ^ (sprintf "\\;#%d" n)
    in 
    let n = countSubgoals sCl.subGoals in
    (* pattern match on the number of goals in sCl.subGoals *)
    match n with 
      | 0 -> sprintf "\\newcommand{\\COMPCONST%s}{\\mathsf{%s}}" 
          name name
      | n -> sprintf "\\newcommand{\\COMPCONST%s}[%d]{\\mathsf{%s}%s}"
          name n name (printArguments n)


  let cidCompTypToMaccro cidCompTyp =
    (* get name of type constant *)
    let compTypEntry = Store.Cid.CompTyp.get cidCompTyp in
    let compTypName = compTypEntry.Store.Cid.CompTyp.name in
    let name = Id.string_of_name_latex compTypName in
    (* get number of arguments of compType constant *)
    let n = Store.Cid.CompTyp.args_of_name compTypName in
    let rec printArguments n = match n with
        | 1 -> "\\;#1"
        | n -> (printArguments (n-1)) ^ (sprintf "\\;#%d" n)
    in 
    match n with 
      | 0 -> sprintf "\\newcommand{\\COMPTYP%s}{\\mathsf{%s}}" 
              name name
      | n -> sprintf "\\newcommand{\\COMPTYP%s}[%d]{\\mathsf{%s}%s}" 
              name n name (printArguments n)


  let printSignatureLatex mainFile =
    let outMaccros = 
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 "latex/maccros.tex" 
    in
    let outMain =
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 mainFile 
    in
    (* takes as input one binding (k, v) of compTypes : 
       k : cidCompTyp, v : (cidCompConst, sCl) DynArray
    *)
    let compTypeFamilyToLatex k v = 
      (* print a maccro for the compTyp constant k in the maccros file *)
      fprintf outMaccros "\n%s\n\n" (cidCompTypToMaccro k);
      (* for each clause in v :
        - print a maccro for the comp constant in the maccros file
        - print a statement of the definition in the main file  *)
      DynArray.iter (fun w ->
        fprintf outMaccros "%s\n\n" (sgnClauseToMaccros w);
        fprintf outMain "%s\n\n" (sgnClauseToLatex w)) v
    in
    Hashtbl.iter compTypeFamilyToLatex compTypes;
    close_out outMaccros;
    close_out outMain

  let printCompTypesLatex mainFile =
    robStore ();
    printSignatureLatex mainFile;
    clearIndex ()


end




