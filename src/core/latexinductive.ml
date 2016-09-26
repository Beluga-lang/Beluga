(*module S = Substitution.LF*)
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

  (* val typToClause : LF.mctx -> conjunction -> Comp.typ -> clause *)
  let rec typToClause' eV cG tau = match tau with
    | Comp.TypArr (tauA, tauB) ->
      typToClause' eV (Conjunct (cG, typToGoal tauA)) tauB
    | Comp.TypBox (_) ->
      { tHead = tau
      ; eVars = eV
      ; subGoals = cG }
    | Comp.TypBase (_) ->
      { tHead = tau
      ; eVars = eV
      ; subGoals = cG }
    | Comp.TypPiBox (cdecl, tau') ->
      typToClause' (LF.Dec (eV, cdecl)) cG tau'

  and typToGoal tau = match tau with
    | Comp.TypPiBox (cdecl, tau') ->
      All (cdecl, typToGoal tau')
    | Comp.TypArr (tauA, tauB) ->
      Impl (typToGoal tauA, typToGoal tauB)
    | Comp.TypBox (_) ->
      Atom (tau)
    | Comp.TypBase (_) ->
      Atom (tau)

  let typToClause tau =
    typToClause' LF.Empty True tau


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
    let tau = compConstEntry.Cid.CompConst.typ in
    (cidCompConst, Convert.typToClause tau)

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
    try
      List.iter storeCompTypConst !(DynArray.get Cid.CompTyp.entry_list !(Modules.current))
    with _ -> ()

  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () = Hashtbl.clear compTypes


end



module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  (* val compTypToLatex : LF.mctx -> Comp.typ -> string *)
  let compTypToLatex cD tau  = 
    sprintf "$%s$" (P.compTypToLatex cD tau)

  (* val cdeclToLatex : LF.mctx -> LF.ctyp_decl -> string *)
  let cdeclToLatex cD cdecl =
    sprintf "$%s$" (P.cdeclToLatex cD cdecl)


  (* val goalToLatex : goal -> LF.mctx -> string *)
  let rec goalToLatex g cD = match g with
    | Atom (tau) -> compTypToLatex cD tau
    | Impl (g1, g2) ->
      sprintf "if %s then %s" 
       (goalToLatex g1 cD)
       (goalToLatex g2 cD)
    | All (cdecl, g) ->
      sprintf "[for all %s, %s]" 
       (cdeclToLatex cD cdecl)
       (goalToLatex g (LF.Dec (cD, cdecl)))

  (* prints explicit quantifiers in sCl.eVars *)
  let printForAlls cD = 
    let rec printForAlls' cD acc = match cD with
      | LF.Empty -> acc
      | LF.Dec (cD', cdecl) ->
        (match cdecl with
          (* explicit quantifier, print a for all *)
          | LF.Decl (_, _, LF.No) ->
            printForAlls' cD' ((sprintf "for all %s, " (cdeclToLatex cD' cdecl)) ^ acc)
          (* implicit quantifier, print nothing *)
          | LF.Decl (_, _, LF.Maybe) ->
             printForAlls' cD' acc)
     in printForAlls' cD ""

  let countSubgoals cG = 
      let rec countSubgoals' cG n = match cG with
        | Conjunct (cG', _) -> countSubgoals' cG' (n+1)
        | True -> n
      in countSubgoals' cG 0

  (* val printSubgoals : conjunction -> LF.mctx -> Id.name list -> string 
      - when printing inductive types, l = []
      - when printing the theorem name in recursive functions,
          l is a list of derivation names to be paired with goals 

          ex : x : [ |- exp nat]
           x is the derivation name
           [ |- exp nat] is the goal
  *)
  let rec printSubgoals cG cD l = match cG with
    | Conjunct (True, g) ->
      (match l with 
        | [] ->
          goalToLatex g cD
        | h::[] ->
         sprintf "%s :: %s" (Id.render_name h) (goalToLatex g cD))
    | Conjunct (cG', g) ->
      let n = countSubgoals cG in
      let revl = (List.rev l) in
      if (List.length l) == n then
        let last::revt = revl in
        let t = (List.rev revt) in
        sprintf "%s and %s :: %s" (printSubgoals cG' cD t) (Id.render_name last) (goalToLatex g cD)
      else 
        sprintf "%s and %s" (printSubgoals cG' cD l) (goalToLatex g cD)


  let clauseToLatex sCl l = 
    let conclusion = compTypToLatex sCl.eVars sCl.tHead in 
    let forAlls = printForAlls sCl.eVars in
    match sCl.subGoals with
      | True ->
        sprintf "%s%s" forAlls conclusion
      | Conjunct (_) as cG ->
        sprintf "%sif %s then %s" forAlls (printSubgoals cG sCl.eVars l) conclusion

  (* val sgnClauseToLatex Id.cid_comp_const * clause -> string *)
  let sgnClauseToLatex (cidCompConst, sCl) =
    let name = Id.string_of_name_latex (compConstName cidCompConst) in 
    sprintf "\\begin{definition}\n[%s] %s\n\\end{definition}" 
      name (clauseToLatex sCl [])

  (* printArguments n = "\\;#1\\;#2 ... \\;#n" - only called with n > 0 *)
  let rec printArguments n = match n with
    | 1 -> "\\;#1"
    | n -> (printArguments (n-1)) ^ (sprintf "\\;#%d" n)

  (* maccro : \newcommand{\COMPCONSTname}[number of args n]{\mathsf{name}\;#1\ ... \;#n} *)
  let sgnClauseToMaccros (cidCompConst, sCl) =
    let name = Id.string_of_name_latex (compConstName cidCompConst) in
    let cleanName = Id.cleanup_name_latex name in
    let n = countSubgoals sCl.subGoals in
    (* pattern match on the number of goals in sCl.subGoals *)
    match n with 
      | 0 -> sprintf "\\newcommand{\\COMPCONST%s}{\\mathsf{%s}}" 
          cleanName name
      | n -> sprintf "\\newcommand{\\COMPCONST%s}[%d]{\\mathsf{%s}%s}"
          cleanName n name (printArguments n)

  (* maccro : \newcommand{\COMPTYPname}[number of args n]{\mathsf{name}\;#1\ ... \;#n} *)
  let cidCompTypToMaccro cidCompTyp =
    let compTypEntry = Store.Cid.CompTyp.get cidCompTyp in
    let compTypName = compTypEntry.Store.Cid.CompTyp.name in
    let name = Id.string_of_name_latex compTypName in
    let cleanName = Id.cleanup_name_latex name in
    let n = Store.Cid.CompTyp.args_of_name compTypName in
    match n with 
      | 0 -> sprintf "\\newcommand{\\COMPTYP%s}{\\mathsf{%s}}" 
              cleanName name
      | n -> sprintf "\\newcommand{\\COMPTYP%s}[%d]{\\mathsf{%s}%s}" 
              cleanName n name (printArguments n)

  let printSignatureLatex mainFile maccrosFile =
    let outMaccros = 
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 maccrosFile
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
        - print a definition in the main file  *)
      DynArray.iter (fun w ->
        fprintf outMaccros "%s\n\n" (sgnClauseToMaccros w);
        fprintf outMain "%s\n\n" (sgnClauseToLatex w)) v
    in
    Hashtbl.iter compTypeFamilyToLatex compTypes;
    close_out outMaccros;
    close_out outMain

  let printCompTypesLatex mainFile maccrosFile =
    robStore ();
    printSignatureLatex mainFile maccrosFile;
    clearIndex ()


end




