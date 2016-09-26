open Syntax.Int
open Printf


module Index = struct

  open Store

  (* Hashtbl.
     key : (Id.cid_prog * Loc.t)
     value : (Syntax.Int.Comp.typ * Annotated.Comp.exp_chk)
   *)
  let recTypes = Hashtbl.create 0

  (* Hashtbl.
     key : Id.name
     value : Annotated.Comp.exp_chk
     gets filled up in recsgn.ml
   *)
  let annotatedProofs = Hashtbl.create 0

  (* val addBinding : (Id.cid_prog * Loc.t) -> (Comp.Typ, Annotated.Comp.exp_chk) -> () *)
  let addBinding (cidProg, loc) (tau, e_ann) =
    Hashtbl.add recTypes (cidProg, loc) (tau, e_ann)
  

  let storeEntry (cidProg, loc) =
    let compEntry = Cid.Comp.get cidProg in
    let tau = compEntry.Cid.Comp.typ in 
    let compName = compEntry.Cid.Comp.name in
    let e_ann = Hashtbl.find annotatedProofs compName in
    addBinding (cidProg, loc) (tau, e_ann)

  let robStore () =
    try
      List.iter storeEntry !(DynArray.get Cid.Comp.entry_list !(Modules.current));
    with
    | _ -> ()

  (* clearIndex () = ()
    Empty the local storage.
   *)
  let clearIndex () = 
    Hashtbl.clear recTypes;
    Hashtbl.clear annotatedProofs

end


module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index
  open Store

  (* get the derivation names from the exp_chk in order to factor them into our theorem statement *)
  let rec parse_fun e l =
    match e with
    (* function -> add the name x *)
    | Comp.Fun (_, x, e') ->
       parse_fun e' (l @ [x])
    (* mlam -> continue traversing *)
    | Comp.MLam (_, _, e') ->
       parse_fun e' l
    (* no more functions to come, return our list *)
    | Comp.Case _ -> l
     

  let theoremToLatex tau cidProg =
    let sCl = Latexinductive.Convert.typToClause tau in
    let entry = Cid.Comp.get cidProg in
    let name = Id.string_of_name_latex entry.Cid.Comp.name in
    let Comp.RecValue (cidProg, e, msub, env) = entry.Cid.Comp.prog in
    (* list of derivation names to be factored into our theorem statement *)
    let l = parse_fun e [] in
    sprintf "\\begin{theorem}\n[%s] %s\n\\end{theorem}"
      name (Latexinductive.Printer.clauseToLatex sCl l)
      

  (* printArguments n = "#1#2 ... #n" - only called with n > 0 *)
  (* CARE : we don't print \; as in other maccros since we put the \; in expSynToString 
            in Annotate.ml, it is much easier to handle the $ in LaTeX this way *)
  let rec printArguments n = match n with
    | 1 -> "#1"
    | n -> (printArguments (n-1)) ^ (sprintf "#%d" n)

  let cidProgToMaccro cidProg =
    (* get name of prog constant *)
    let compEntry = Cid.Comp.get cidProg in
    let compName = compEntry.Cid.Comp.name in
    let name = Id.string_of_name_latex compName in
    let cleanName = Id.cleanup_name_latex name in
    (* get number of arguments  *)
    let n = Cid.Comp.args_of_name compName in
    match n with 
      | 0 -> sprintf "\\newcommand{\\COMP%s}{\\mathsf{%s}}" 
              cleanName name
      | n -> sprintf "\\newcommand{\\COMP%s}[%d]{\\mathsf{%s}%s}" 
              cleanName n name (printArguments n)


  let proofToLatex e_ann cidProg =
    print_string "[Latex Rec] proofToLatex called";
    sprintf "\\begin{proof}\n%s\n\\end{proof}" (Latexproof.parse e_ann cidProg)
    

  let printSignatureLatex mainFile maccrosFile =
    let outMaccros = 
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 maccrosFile
    in
    let outMain =
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 mainFile
    in
    (* takes as input one binding (k, v) of recTypes : 
       k : (Id.cid_prog * Loc.t), v : (Syntax.Int.Comp.typ * Annotated.Comp.exp_chk) 
     *)
    let recToLatex (cidProg, loc) (tau, e_ann) =
    	fprintf outMain "%s\n\n%s\n\n" (theoremToLatex tau cidProg) (proofToLatex e_ann cidProg);
      fprintf outMaccros "%s\n\n" (cidProgToMaccro cidProg)
   	in 
    (* debugging *)
    printf "number of elem in recTypes : %d\n" (Hashtbl.length recTypes);
    (*************)
   	Hashtbl.iter recToLatex recTypes;
   	close_out outMaccros;
    close_out outMain

    let printRecLatex mainFile maccrosFile =
      robStore ();
      printSignatureLatex mainFile maccrosFile;
      clearIndex ()


end









