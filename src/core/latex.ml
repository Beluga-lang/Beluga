module S = Substitution.LF
open Printf
open Syntax.Int

(* From Logic : 
   - kept type declarations
   - kept Shift module intact
   - took what I needed from Convert and Index
   - totally replaced Printer
   - runLatex () is called from Logic
 *)


type goal =                             (* Goals            *)
  | Atom of LF.typ                      (* g ::= A          *)
  | Impl of (res * LF.typ_decl) * goal  (*     | r => g'    *)
  | All of LF.typ_decl * goal           (*     | ∀x:A. g'   *)

and res =                               (* Residual Goals   *)
  | Head of LF.typ                      (* r ::= A          *)
  | And of goal * res                   (*     | g ∧ r'     *)
  | Exists of LF.typ_decl * res         (*     | ∃x:T. r'   *)

type conjunction =                      (* Subgoals         *)
  | True                                (* cG ::= True      *)
  | Conjunct of conjunction * goal      (*      | cG' ∧ g   *)

type clause =                    (* Horn Clause ::= eV |- A :- cG   *)
    { tHead : LF.typ             (* Head A : LF.Atom                *)
    ; eVars : LF.dctx            (* Context eV : EV's bound in A/cG *)
    ; subGoals : conjunction }   (* Subgoals cG : solv. cG => A     *)




module Shift : sig

  val shiftAtom : LF.typ -> (int * int * int) -> LF.typ

end = struct

  (* NB.

     Only BVar's in LF.Atom's are affected.
     Enclosed substitutions are not shifted.

     i: De Bruijn index.
     k: Shifting measure.

     Algorithm:

     BV bound by λ remain invariant.
      - i < lR |- BV(i) -> BV(i)

     BV bound by a dynamic scope are shifted by dS.
      - lR < i <= dR |- BV(i) -> BV(i + dS)

     BV bound to EV are shifted by k.
      - i > lR && i > dR |- BV(i) -> BV(i + k)
  *)

  let lR = ref 0               (* Range of Lambda Scope *)
  let dR = ref 0               (* Range of Dynamic Scope *)
  let dS = ref 0               (* Dynamic Shift *)

  let rec shiftTyp tM k = match tM with
    | LF.Atom (l, c, tS) ->
      LF.Atom (l, c, shiftSpine tS k)
    | x -> x

  and shiftSpine tS k = match tS with
    | LF.App (tN, tS) ->
      LF.App (shiftNormal tN k, shiftSpine tS k)
    | LF.SClo (tS, s) ->
      LF.SClo (shiftSpine tS k, s)
    | LF.Nil -> LF.Nil

  and shiftNormal tN k = match tN with
    | LF.Lam (l, n, tN') ->
      begin
        ignore (incr lR) ;
        let tM = LF.Lam (l, n, shiftNormal tN' k) in
        ignore (decr lR) ; tM
      end
    | LF.Root (l, tH, tS) ->
      LF.Root (l, shiftHead tH k, shiftSpine tS k)
    | LF.Clo (tN, s) ->
      LF.Clo (shiftNormal tN k, s)
    | LF.Tuple (l, tP) ->
      LF.Tuple (l, shiftTuple tP k)

  and shiftHead tH k = match tH with
    | LF.BVar (i) ->
      if i > !lR && i > !dR then
        LF.BVar (i + k)
      else if i > !lR && i <= !dR then
        LF.BVar (i + !dS)
      else
        LF.BVar (i)
    | LF.AnnH (tH, tM) ->
      LF.AnnH (shiftHead tH k, tM)
    | LF.Proj (tH, n) ->
      LF.Proj (shiftHead tH k, n)
    | x -> x

  and shiftTuple tP k = match tP with
    | LF.Last (tN) ->
      LF.Last (shiftNormal tN k)
    | LF.Cons (tN, tP') ->
      LF.Cons (shiftNormal tN k, shiftTuple tP' k)

  let shiftAtom tM (cS, dS', dR') =
    ignore (dR := dR' ; dS := dS') ; shiftTyp tM cS

end




module Convert = struct

  (* typToClause' eV cG M (cS, dS, dR) = clause
     Invariants:
       If BV(i) is free in M, then BV(i) is bound in (eV |- M).
       If M = PiTyp (x:A, No), then M ~ g.
  *)
  let rec typToClause' eV cG tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
      typToClause' (LF.DDec (eV, tD)) cG tM' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl(_, tA), LF.No), tB) ->
      typToClause' eV (Conjunct (cG, typToGoal tA (cS, dS, dR)))
        tB (cS + 1, dS, dR)
    | LF.Atom (_) as tA ->
      { tHead = (Shift.shiftAtom tA (-cS, -dS, dR))
      ; eVars = eV
      ; subGoals = cG }

  and typToGoal tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
      All (tD, typToGoal tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as tD, LF.No), tB) ->
      Impl ((typToRes tA (cS, dS, dR), tD), typToGoal tB
        (cS, dS, dR + 1))
    | LF.Atom (_) as tA ->
      Atom (Shift.shiftAtom tA (-cS, -dS, dR))

  and typToRes tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
      Exists (tD, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
      And (typToGoal tA (cS, dS, dR), typToRes tB
        (cS + 1, dS + 1, dR + 1))
    | LF.Atom (_) as tA ->
      Head (Shift.shiftAtom tA (-cS, -dS, dR))

  let typToClause tM =
    typToClause' LF.Null True tM (0, 0, 0)

  (* etaExpand Psi (A, s) = normal
     Invariants:
       Psi |- s : Phi
       Phi |- A : LF.typ

     Effects:
       None.
  *)
  let rec etaExpand cPsi sA =
    let (tA, s) = Whnf.whnfTyp sA
    in match tA with
      | LF.Atom (_) as tA ->
        let u = Whnf.newMVar None (cPsi, LF.TClo (tA, s)) LF.Maybe in
        LF.Root (Syntax.Loc.ghost, LF.MVar (u, S.id), LF.Nil)
      | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _), tB) ->
        LF.Lam (Syntax.Loc.ghost, x, etaExpand
          (LF.DDec (cPsi, S.decSub tD s)) (tB, S.dot1 s))


end




module Index = struct

  open Store

  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  (* addTyp c = sgnClause DynArray.t
     Create a new entry for a type constant, c, in the `types' table and
     return it's mapping, i.e. an empty DynArray.
  *)
  let addTyp cidTyp =                                  
    Hashtbl.add types cidTyp (DynArray.create ()) ;
    Hashtbl.find types cidTyp

  (* addSgnClause tC, sCl = ()
     Add a new sgnClause, sCl, to the DynArray tC.
  *)
  let addSgnClause typConst sgnClause =
    DynArray.add typConst sgnClause


  (* compileSgnClause c = (c, sCl)
     Retrieve LF.typ for term constant c, clausify it into sCl and
     return an sgnClause (c, sCl).
  *)
  let compileSgnClause cidTerm =
    let termEntry = Cid.Term.get cidTerm in
    let tM = termEntry.Cid.Term.typ in
    (cidTerm, Convert.typToClause tM)

  (* termName c = Id.name
     Get the string representation of term constant c.
  *)
  let termName cidTerm =
    (Cid.Term.get cidTerm).Cid.Term.name

  (* storeTypConst c = ()
     Add a new entry in `types' for type constant c and fill the DynArray
     with the clauses corresponding to the term constants associated with c.
     The revIter function serves to preserve the order of term constants
     intrinsic to the Beluga source file, since the constructors for c are
     listed in reverse order.
  *)
  let storeTypConst cidTyp =
    let typEntry = Cid.Typ.get cidTyp in
    let typConstr = !(typEntry.Cid.Typ.constructors) in
    let typConst = addTyp cidTyp in
    let regSgnClause cidTerm =
      addSgnClause typConst (compileSgnClause cidTerm) in
    let rec revIter f l = match l with
      | [] -> ()
      | h :: l' -> revIter f l' ; f h
    in revIter regSgnClause typConstr

  (* robStore () = ()
     Store all type constants in the `types' table.
  *)
  let robStore () =
    try
      List.iter storeTypConst !(DynArray.get Cid.Typ.entry_list !(Modules.current))
    with _ -> ()              

  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () = Hashtbl.clear types


end




module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  let typToLatex cPsi sM =                 
    P.typToLatex LF.Empty cPsi sM


  let rec goalToLatex cPsi (g, s) superScripts counter = match g with
    | Atom (tA) ->
      typToLatex cPsi (tA, s)                            
    | Impl ((r, tD), g') -> 
      (* we use counter to generate a new name for our assumption *)
      let assumptionName = match !counter with 
        | 0 -> "u"
        | 1 -> "v"
        | 2 -> "w"
        | num -> sprintf "u_%d" num
      in counter := !counter + 1;
      (* add assumption name to superScripts - at the end *)
      superScripts := (!superScripts)@[assumptionName];
      sprintf "\\deduce[\\vdots]{%s}{\\infera{%s}{%s}{}}"
       (goalToLatex (LF.DDec (cPsi, S.decSub tD s)) (g', S.dot1 s) superScripts counter)
       assumptionName
       (resToLatex cPsi (r, s) superScripts counter)
    | All (LF.TypDecl (x, tM) as tD, g') ->
      (* add name of quantified variable to superScripts - at the beginning *)
      let varName = Id.string_of_name_latex x in
      superScripts := varName::(!superScripts);
      (goalToLatex (LF.DDec (cPsi, S.decSub tD s)) (g', S.dot1 s) superScripts counter) 


  and resToLatex cPsi (r, s) superScripts counter = match r with
    | Head (tH) ->
      typToLatex cPsi (tH, s)
    | And (g, r') -> sprintf "%s \\supset %s"
    (* rarely used, example : ((tm A -> tm B) -> tm C) -> tm D *)
      (goalToLatex cPsi (g, s) superScripts counter) 
      (resToLatex cPsi (r', s) superScripts counter)
    | Exists (LF.TypDecl (_, tM), r') ->
    (* rarely used, simply prints the residual *)
      let tM' = Convert.etaExpand cPsi (tM, s)
      in (resToLatex cPsi (r', LF.Dot (LF.Obj tM', s)) superScripts counter)


  (* well defined up to three premises in the inference rule we want to generate *)
  let sgnClauseToLatex (cidTerm, sCl) = 
    let ruleName = Id.string_of_name_latex (termName cidTerm) in
    let conclusion = typToLatex sCl.eVars (sCl.tHead, S.id) in
    (* list of superscripts that will be used with our rule name, updated by goalToLatex calls *)
    let superScripts = ref [] in
    (* counter used to generate new assumption names : u, v, w, u3, u4, etc. *)
    let counter = ref 0 in
    (* function used to convert a superscript list [a1; a2] into the string " ^{a1,a2}" *)
    let sListToString l = 
      let rec sListToString' l = match l with
        | []    -> ""
        | h::[] -> h
        | h::t  -> h ^ "," ^ (sListToString' t)
      in 
      match l with 
        | [] -> ""
        | _  -> sprintf " ^{%s}" (sListToString' l)
    in 
    match sCl.subGoals with
      | True -> 
        sprintf "\\infera{\\RULE%s}{%s}{}" ruleName conclusion
      | Conjunct (True, g) ->
        let p1 = goalToLatex sCl.eVars (g, S.id) superScripts counter in
        let super = sListToString !superScripts in
        sprintf "\\infera{\\RULE%s%s}{%s}{%s}" ruleName super conclusion p1
      | Conjunct (Conjunct (True, g1), g2) ->
        let p1 = goalToLatex sCl.eVars (g1, S.id) superScripts counter in
        let p2 = goalToLatex sCl.eVars (g2, S.id) superScripts counter in
        let super = sListToString !superScripts in
        sprintf "\\inferaa{\\RULE%s%s}{%s}{%s}{%s}" ruleName super conclusion p1 p2
      | Conjunct (Conjunct (Conjunct (True, g1), g2), g3) ->
        let p1 = goalToLatex sCl.eVars (g1, S.id) superScripts counter in
        let p2 = goalToLatex sCl.eVars (g2, S.id) superScripts counter in
        let p3 = goalToLatex sCl.eVars (g3, S.id) superScripts counter in
        let super = sListToString !superScripts in 
        sprintf "\\inferaaa{\\RULE%s%s}{%s}{%s}{%s}{%s}" ruleName super conclusion p1 p2 p3 


  (* generates a maccro of the form \newcommand{\RULEcidTerm}{\ruleName{cidTerm}} *)
  let nameToRuleMaccro name =
    sprintf "\\newcommand{\\RULE%s}{\\ruleName{%s}}" name name

  (* generates two maccros for each term constant :
  \newcommand {\RULEcidTerm} {\ruleName{cidTerm}}
  \newcommand {\TERMcidTerm} [number of args] {\mathsf{cidTerm};args} *)
  let sgnClauseToMaccros (cidTerm, sCl) =
    let name = Id.string_of_name_latex (termName cidTerm) in
    let ruleMaccro = nameToRuleMaccro name in
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
      | 0 -> sprintf "%s\n\\newcommand{\\TERM%s}{\\mathsf{%s}}" 
          ruleMaccro name name
      | n -> sprintf "%s\n\\newcommand{\\TERM%s}[%d]{\\mathsf{%s}%s}"
          ruleMaccro name n name (printArguments n)


  let cidTypToMaccro cidTyp =
    (* get name of type constant *)
    let typEntry = Store.Cid.Typ.get cidTyp in
    let typName = typEntry.Store.Cid.Typ.name in
    let name = Id.string_of_name_latex typName in
    (* get number of arguments of type constant *)
    let n = Store.Cid.Typ.args_of_name typName in
    let rec printArguments n = match n with
        | 1 -> "\\;#1"
        | n -> (printArguments (n-1)) ^ (sprintf "\\;#%d" n)
    in 
    match n with 
      | 0 -> sprintf "\\newcommand{\\TYP%s}{\\mathsf{%s}}" 
              name name
      | n -> sprintf "\\newcommand{\\TYP%s}[%d]{\\mathsf{%s}%s}" 
              name n name (printArguments n)


  let printSignatureLatex mainFile =
    let outMaccros = open_out "latex/maccros.tex" in
    let outMain = open_out mainFile in
    (* takes as input one binding key/value of Types : k is a cidTyp, v is a DynArray of (cidTerm, sCl) *)
    let typeFamilyToLatex k v = 
      (* print a maccro for the type constant k in the maccros file *)
      fprintf outMaccros "\n%s\n\n" (cidTypToMaccro k);
      (* for each clause in v :
      - print a maccro for the term constant in the maccros file
      - print an inference rule in the main file  *)
      DynArray.iter (fun w -> 
        fprintf outMaccros "%s\n\n" (sgnClauseToMaccros w);
        fprintf outMain "%s\n\n" (sgnClauseToLatex w)) v
    in
    (* preamble of maccros file *)
    fprintf outMaccros "\\input{prelude}\n\n";
    (* preamble of main file *)
    fprintf outMain "\\documentclass{article}\n\n\\input{maccros}\n\n\\begin{document}\n\n";
    (* conversion to LaTex and printing of maccros *)
    Hashtbl.iter typeFamilyToLatex types;
    (* conclusion of main file *)
    fprintf outMain "\n\\end{document}";
    close_out outMaccros;
    close_out outMain;


end



(* Interface *)

let runLatex () =
  Index.robStore () ;
  Printer.printSignatureLatex "latex/main.tex";
  Index.clearIndex ();

